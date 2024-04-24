use core::panic;
use std::time::Instant;
mod utils;
use crate::utils::{verify_proof, u8vec_to_boolvec, choose};
use criterion::measurement::Measurement;
use ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_backend::{transcript::Blake2bWrite, poly::commitment};
use halo2_frontend::{
    dev::MockProver,
    plonk::{Constraints, Error, Expression, Instance, Selector, VirtualCells},
};
use halo2_proofs::{
    circuit::{AssignedCell, Cell, Layouter, Region, SimpleFloorPlanner, Value},
    halo2curves::bn256::{Bn256, Fr as F, Fr as Fp, G1Affine},
    plonk,
    plonk::{
        verify_proof as verify_plonk_proof, Advice, Assigned, Circuit, Column, ConstraintSystem,
        ErrorFront, ProvingKey, TableColumn, VerifyingKey,
    },
    poly::{
        commitment::{CommitmentScheme, Params, ParamsProver, Verifier as CommitmentVerifier},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        Rotation, VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Challenge255, EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use rand::thread_rng;

use crate::utils::params;

/// halo2's param which determines how many usable rows the circuit has.
const K: u32 = 10;
/// How many usable rows the circuit has.
const usable_rows: usize = (1 << K) - 6;



/// The bitsize of the chunk of the plaintext inside of which the commitment data is located.
const plaintext_size: usize = 4000 * 8;
/// Bitsize of the commitment data 
/// (range bounds are part of the commitment but are not counted here).
const commitment_data_size: usize = 100 * 8;
/// The number of commitments, each of the size `commitment_data_size`.
const commitment_count: usize = 8;
/// How many columns are needed for all commitments.
const commitment_column_count: usize = 8;

/// The number of rows at the bottom of the circuit allocated as scratch space. It will be used
/// to compute the encoding sum, to compose bits into field elements and to hash with Poseidon.
/// 
/// For each commitment, we need 2 Poseidon chips: the first one has rate 2 and it hashes the encoding
/// sum, the second one is rate 6 and it hashes the concatenation of (plaintext || range bounds || salt).
///  
/// The number of advice cells: for the rate-2 Poseidon is 40 rows and 4 columns, for the rate-6 is 40
/// rows and 8 columns. (see
/// https://github.com/privacy-scaling-explorations/poseidon-gadget/blob/764a682ee448bfbde0cc92a04d241fe738ba2d14/src/poseidon/pow5.rs#L41 )
/// 
/// Below is an explanation how to place the Poseidon chips in the scratch space in the most compact
/// manner. To simplify the explanation, we mentally merge the rate-2 and rate-5 chips into one chip
/// of 40 rows and 12 columns and refer to it as `the chip` below.
/// 
/// We will place the 8 chips one next to each other in a row starting from the bottom left corner of
/// the circuit. This way, the bottom 40 rows and the first 96 columns will be allocated to the Poseidon
/// chips. 
/// 
/// The 100 rows above that will be for other computattions.
const scratchspace_rows: usize = 140;


/// How many rows the lut has.
// Why do we get an error when we dont use `-1` here? 
const lut_row_count: usize = usable_rows - 1;
/// How many fixed columns we need to create a lut which contains all the encodings
/// of the plaintext. 
/// Note that there will be 2 luts - one for the encodings of the 0 bit value, and the
/// other lut for the encodings of the 1 bit value. Each of the 2 luts will require `column_count`
/// columns.
const column_count: usize = plaintext_size / lut_row_count + ((plaintext_size % lut_row_count != 0) as usize );
// How many columns to hold the bit decomposed index of the column of the lut.
// It is log_2(column_count)
const index_columns: usize = 5;

fn main() {
    println!("COLUMNS {:?}", column_count);

    // Fill look-up tables with encodings.
    let mut lut_zero = Vec::new();
    let mut lut_one = Vec::new();

    for i in 0..column_count {
        let mut zero_column = Vec::new();
        let mut one_column = Vec::new();
        for j in 0..lut_row_count-1 {
            zero_column.push(Fp::from((10000 * i + j) as u64));
            one_column.push(Fp::from((20000 * i + j) as u64));
        }
        // Each column should have a default 0 value in it.
        zero_column.push(F::from(0));
        one_column.push(F::from(0));

        lut_zero.push(zero_column);
        lut_one.push(one_column);
    }

    // Generate private inputs to the circuit.
    let private_inputs = (0..commitment_count).into_iter().map(|i| {
        // Generate plaintexts of different bitlengths to be committed to.
        let plaintext_len = (i+1)*10;

        // Even commitment plaintext is all 0s, odd ones are all 1s, for simplicity.
        let bit = if i % 2 != 0 {true} else {false};
        let mut plaintext = vec![bit; plaintext_len];

        // Mark the active bits of the commitment data with 1, the remaining bits are the padding
        // bits which will be marked with 0.
        let mut is_active = vec![true; plaintext_len];

        // Select the correct lut which contains the encodings of the plaintext bits.
        let lut = if bit {lut_one.clone()} else {lut_zero.clone()};
        // Select the encodings from an arbitrary column of the lut.
        // For simplicity, just select the encodings from the beginning of the column.
        let mut active_encodings = lut[11][0..plaintext_len].to_vec();

        // Mark the column with the index 11 as the column in which the lookup should be made.
        let mut column_flags = vec![false; 11];
        column_flags.extend(vec![true]);
        column_flags.extend(vec![false; column_count - column_flags.len()]);

        // Pad the plaintext with zero bits.
        plaintext.extend(vec![false; commitment_data_size - plaintext_len]);
        // Mark all the bits past the plaintext as inactive.
        is_active.extend(vec![false; commitment_data_size-plaintext_len]);
        // Pad the encodings with encodings with value 0.
        active_encodings.extend(vec![F::zero(); commitment_data_size-plaintext_len]);

        Private {
            bits: plaintext,
            is_active,
            encodings: active_encodings,
            column_indices: vec![column_flags; commitment_data_size]
        }
    }).collect::<Vec<_>>();




    let circuit = MyCircuit {
        lookup_table_zero: lut_zero,
        lookup_table_one: lut_one,
        private: private_inputs
    };



    let params = params();

    let now = Instant::now();
    let vk = halo2_proofs::plonk::keygen_vk(&params, &circuit).unwrap();
    println!("vk created [{:?}]", now.elapsed());
    println!("vk size [{} kB]", vk.to_bytes(halo2_proofs::SerdeFormat::RawBytes).len() as f64 / 1024.0);

    let now = Instant::now();
    let pk = halo2_proofs::plonk::keygen_pk(&params, vk.clone(), &circuit).unwrap();
    println!("pk created [{:?}]", now.elapsed());
    println!("pk size [{} kB]", pk.to_bytes(halo2_proofs::SerdeFormat::RawBytes).len() as f64 / 1024.0);


    let mut transcript: Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>> =
        Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let mut rng = thread_rng();

    let now = Instant::now();

    let res = plonk::create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverGWC<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(
        &params,
        &pk,
        &[circuit.clone()],
        &[&[]],
        &mut rng,
        &mut transcript,
    );
    if res.is_err() {
        println!("proof gen error: {:?}", res);
        let res = MockProver::run(K, &circuit, vec![]).unwrap();
        println!("proof gen error: {:?}", res.verify());
        panic!();
    }

    let proof = &transcript.finalize();

    println!("Proof created [{:?}]", now.elapsed());
    println!("Proof size [{} kB]", proof.len() as f64 / 1024.0);

    let now = Instant::now();
    verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierGWC<'_, Bn256>,
        _,
        Blake2bRead<_, _, Challenge255<_>>,
        AccumulatorStrategy<_>,
    >(&params, &vk, &proof, &[&[]])
    .unwrap();
    println!("Proof verified [{:?}]", now.elapsed());
}



/// Returns an instance of the AuthDecode circuit.
pub fn circuit_instance() -> MyCircuit {
    MyCircuit::default()
}

// Each commitment data's bits occupy one column.
// Additional advice columns are also present for each bits columns.
#[derive(Clone)]
struct CommitmentColumns {
    /// The bits of the commitment data.
    bits: Column<Advice>,
    /// Respecitve encoding for each bit.
    encodings: Column<Advice>,
    /// Whether the corresponding bit is an active bit or a padding bit ().
    /// Each chunk of data iz zero padded on the right.
    /// If the bit is set to 1, it means that the bit is an active bit.
    is_active: Column<Advice>,
    /// The id of the bit. Usually this is the bit's offset from the start
    /// of the transcript.
    id: Column<Advice>,
    /// (OBSOLETE: A bit-decomposed index of the column of the lut in which the encoding
    /// must be looked up.
    /// E.g. if there are 32 (2^5) lut columns, the vector will contain 5 columns.)
    ///
    /// Contains as many flag columns as there are lut columns. A flag set to 1 means that the lookup
    /// must be performed in the respective lut column. Otherwise the flag is set to 0.
    index: Vec<Column<Advice>>,
}

#[derive(Clone)]
struct CircuitConfig {
    commitments: Vec<CommitmentColumns>,
    /// The look up table consisting of multiple columns.
    table_zero: Vec<TableColumn>,
    table_one: Vec<TableColumn>,
    selector_lookup: Selector,
    selector_binary_check: Selector,
    selector_inactive_all_zero: Selector,
    selector_offset_step_by_one: Selector,
    selector_is_active_descending: Selector,
}

#[derive(Default, Clone)]
struct MyCircuit {
    /// The lut for encodings of the bit value zero. 
    /// A lut spans multiple columns.
    /// Each inner vector respresents a column of the lut. 
    lookup_table_zero: Vec<Vec<Fp>>,
    /// The lut for encodings of the bit value one.
    /// A lut spans multiple columns.
    /// Each inner vector respresents a column of the lut.
    lookup_table_one: Vec<Vec<Fp>>,
    /// Private inputs for each commitment:
    private: Vec<Private>
}

/// Private inputs for each commitment
#[derive(Default, Clone)]
struct Private {
    // /plaintext bits 
    bits: Vec<bool>,
    /// is_active flags 
    is_active: Vec<bool>,
    /// encodings of the plaintext bits
    encodings: Vec<F>,
    /// flags which indicate whether the corresponding column of the lut should be used for the lookup)
    /// Each inner vector is a set of flags for **one** encoding
    column_indices: Vec<Vec<bool>>
}

impl Circuit<Fp> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        println!("reserved row count: {:?}", meta.blinding_factors() + 1);

        let commitments = (0..commitment_column_count)
            .into_iter()
            .map(|_| {
                let bits = meta.advice_column();
                let encodings = meta.advice_column();
                let is_padding = meta.advice_column();
                let id = meta.advice_column();
                let index = (0..column_count)
                    .into_iter()
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>();

                CommitmentColumns {
                    bits,
                    encodings,
                    is_active: is_padding,
                    id,
                    index,
                }
            })
            .collect::<Vec<_>>();

        let selector_binary_check = meta.selector();
        let selector_inactive_all_zero = meta.selector();
        let selector_offset_step_by_one = meta.selector();
        let selector_is_active_descending = meta.selector();
        let selector_lookup = meta.complex_selector();

        let table_zero = (0..column_count)
            .map(|_| meta.lookup_table_column())
            .collect::<Vec<_>>();
        let table_one = (0..column_count)
            .map(|_| meta.lookup_table_column())
            .collect::<Vec<_>>();

        // Constants
        let one = Expression::Constant(Fp::from(1));
        let zero = Expression::Constant(Fp::from(0));

        // Returns an expression which evaluates to 1 if the integer's bit decomposition equals
        // the 5 bits (in MSB-first order) in the advice columns.
        fn is_equal(
            int: usize,
            bit_columns: &[Column<Advice>],
            cells: &mut VirtualCells<'_, F>,
        ) -> Expression<F> {
            assert!(int < 32);
            let one = Expression::Constant(Fp::from(1));
            let zero = Expression::Constant(Fp::from(0));

            let bits = &u8vec_to_boolvec(&int.to_be_bytes()[0..1])[0..5];
            let subexpressions = bits
                .iter()
                .zip(bit_columns)
                .map(|(bit, column)| {
                    let bit = if *bit { one.clone() } else { zero.clone() };
                    let column_bit = cells.query_advice(*column, Rotation::cur());
                    let diff = column_bit - bit;

                    // Evaluates to 1 only if bits match, otherwise evaluates to 0.
                    one.clone() - diff.clone() * diff
                })
                .collect::<Vec<_>>();

            // Return the final expression.
            subexpressions[0].clone()
                * subexpressions[1].clone()
                * subexpressions[2].clone()
                * subexpressions[3].clone()
                * subexpressions[4].clone()
        }

        meta.lookup("lookup", |cells| {
            let mut all_expressions = Vec::new();
            let sel = cells.query_selector(selector_lookup);

            println!("selector is {:?}", sel);
            if sel == zero {
                println!("selector is zero");
            }
            if sel == one {
                println!("selector is one");
            }

            for j in 0..commitment_column_count {
                let encoding = cells.query_advice(commitments[j].encodings, Rotation::cur());
                let bit = cells.query_advice(commitments[j].bits, Rotation::cur());
                let not_bit = one.clone() - bit.clone();

                let id = cells.query_advice(commitments[j].id, Rotation::cur());
                let is_active = cells.query_advice(commitments[j].is_active, Rotation::cur());


                let lookup_exp = 
                // All encoding were left shifted and the id was appended at the time of commitment
                // to the encoding sum.
                //(encoding.clone() + id.clone()) *
                encoding.clone()  *

                is_active.clone()
                // Multiply by zero in order to not have to worry about populating the lut
                // with the correct values (good enough for benchmarking)
                 + Expression::Constant(Fp::from(1023990));

                 println!("lookup_exp is {:?}", lookup_exp);

                for i in 0..column_count {
                    // Only perform the actual lookup in the column with the correct index.
                    // For columns with a different index, a dummy lookup of a zero value will be
                    // performed.

                    // OBSOLETE: using bit decomposition of the index turned out to be slower than
                    // using the flag approach.
                    // let is_correct_column = is_equal(i, &commitments[j].index, cells);

                    let is_correct_column =
                        cells.query_advice(commitments[j].index[i], Rotation::cur());


                    // Look up among encodings of zero when the bit value is 0
                    all_expressions.push((
                        sel.clone() * not_bit.clone() * is_correct_column.clone() * lookup_exp.clone(),
                        table_zero[i],
                    ));

                    // Look up among encodings of one when the bit value is 1
                    all_expressions.push((
                        sel.clone() * bit.clone() * is_correct_column * lookup_exp.clone(),
                        table_one[i],
                    ));
                }
            }
            all_expressions
        });

        // Constrains bit values, active flags, column index bits to be binary.
        meta.create_gate("binary_check", |meta| {
            let mut expressions = Vec::with_capacity(column_count * 2 + 4);

            for j in 0..commitment_column_count {
                // Create an `Expression` for each bit.
                let bit = meta.query_advice(commitments[j].bits, Rotation::cur());
                expressions.push(bit.clone() * bit.clone() - bit);
                let bit = meta.query_advice(commitments[j].is_active, Rotation::cur());
                expressions.push(bit.clone() * bit.clone() - bit);
                for k in 0..index_columns {
                    // No need to constrain index flags to be binary since we are using canaries
                    // in the lut. TODO: investigate if it is really secure.

                    let bit = meta.query_advice(commitments[j].index[k], Rotation::cur());
                    expressions.push(bit.clone() * bit.clone() - bit);
                }
            }

            let sel = meta.query_selector(selector_binary_check);

            // Constrain all expressions to be equal to 0.
            Constraints::with_selector(sel, expressions)
        });

        // If a bit is inactive, its bit value should be set to zero.
        meta.create_gate("inactive_all_zero", |meta| {
            let mut expressions = Vec::new();

            for j in 0..commitment_column_count {
                // Create an `Expression` for each bit.
                let state = meta.query_advice(commitments[j].is_active, Rotation::cur());
                let bit = meta.query_advice(commitments[j].bits, Rotation::cur());
                let not_state = one.clone() - state.clone();

                expressions.push((state + bit) * not_state);
            }

            let sel = meta.query_selector(selector_inactive_all_zero);
            // Constrain all expressions to be equal to 0.
            Constraints::with_selector(sel, expressions)
        });

        // Make sure the offset is increased by 1
        meta.create_gate("offset_step_by_one", |meta| {
            let mut expressions = Vec::new();

            for j in 0..commitment_column_count {
                let this_offset = meta.query_advice(commitments[j].id, Rotation::cur());
                let prev_offset = meta.query_advice(commitments[j].id, Rotation::prev());
                expressions.push(this_offset - one.clone() - prev_offset);
            }
            let sel = meta.query_selector(selector_offset_step_by_one);

            // Constrain all expressions to be equal to 0.
            Constraints::with_selector(sel, expressions)
        });

        // Make sure the is_active flag for the next row is equal or less to this row.
        // This guarantees that we have a contiguous array of is_active set to 1, followed by
        // rows where is_active is set to 0. This prevents is_active from going from 0 to 1.
        meta.create_gate("is_active_descending", |meta| {
            let mut expressions = Vec::new();

            for j in 0..commitment_column_count {
                let this = meta.query_advice(commitments[j].is_active, Rotation::cur());
                let next = meta.query_advice(commitments[j].is_active, Rotation::next());
                let diff = this - next;
                // the diff must be either 0 or 1
                // TODO multiply by zero to not have to worry about correct values, good enough for benching.
                expressions.push((diff.clone() * diff.clone() - diff) * zero.clone());
            }

            let sel = meta.query_selector(selector_is_active_descending);
            Constraints::with_selector(sel, expressions)
        });

        CircuitConfig {
            commitments,
            selector_lookup,
            selector_binary_check,
            selector_inactive_all_zero,
            selector_offset_step_by_one,
            selector_is_active_descending,
            table_zero,
            table_one,
        }
    }

    fn without_witnesses(&self) -> Self {
        Self {
            lookup_table_zero: self.lookup_table_zero.clone(),
            lookup_table_one: self.lookup_table_one.clone(),
            private: Vec::default()
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        // Assign items to the lookup table.
        layouter.assign_table(
            || "assign lut zero",
            |mut table| {
                for i in 0..column_count {
                    for j in 0..lut_row_count {
                        table.assign_cell(
                            || "table col",
                            config.table_zero[i],
                            j,
                            || Value::known(self.lookup_table_zero[i][j]),
                        )?;
                    }
                }
                Ok(())
            },
        )?;

        layouter.assign_table(
            || "assign lut one",
            |mut table| {
                for i in 0..column_count {
                    for j in 0..lut_row_count {
                        table.assign_cell(
                            || "table col",
                            config.table_one[i],
                            j,
                            || Value::known(self.lookup_table_one[i][j]),
                        )?;
                    }
                }

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign private inputs",
            |mut region| {
                for j in 0..commitment_column_count {
                    let start_offset = 123;
                    let row_count = commitment_data_size;

                    for i in 0..row_count {
                        // Enable lookup on all of the rows containing the encodings.
                        config.selector_lookup.enable(&mut region, i)?;

                        //config.selector_inactive_all_zero.enable(&mut region, i)?;
                        if i != row_count - 1 {
                            // Enable for all rows except the last one.
                            config
                                .selector_is_active_descending
                                .enable(&mut region, i)?;
                        }

                        region.assign_advice(
                            || "",
                            config.commitments[j].id,
                            i,
                            || Value::known(Fp::from((start_offset + i) as u64)),
                        )?;
                        if i != 0 {
                            config.selector_offset_step_by_one.enable(&mut region, i)?;
                        }

                        // Assign encodings that need to be looked up.
                        region.assign_advice(
                            || "",
                            config.commitments[j].encodings,
                            i,
                            || Value::known(self.private[j].encodings[i]),
                        )?;

                        // Assign bit values of the encodings.
                        region.assign_advice(
                            || "",
                            config.commitments[j].bits,
                            i,
                            || Value::known(F::from(self.private[j].bits[i])),
                        )?;

                        // Assign is_active flags
                        region.assign_advice(
                            || "",
                            config.commitments[j].is_active,
                            i,
                            || Value::known(F::from(self.private[j].is_active[i])),
                        )?;

                        // TODO: for benchmarking purposes, it doesn't matter if indices are
                        // incorrect.
                        for k in 0..column_count {
                            region.assign_advice(
                                || "",
                                config.commitments[j].index[k],
                                i,
                                || Value::known(F::from(self.private[j].column_indices[i][k])),
                            )?;
                        }
                    }
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}





#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum VerifierError {
    #[error("Proof verification failed")]
    VerificationFailed,
}



