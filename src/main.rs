#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(private_interfaces)]
use core::panic;
use std::time::Instant;
mod utils;
use crate::utils::verify_proof;
use ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_backend::{poly::commitment, transcript::Blake2bWrite};
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

fn main() {
    // Create a lut 4 items: 0,1,2,3
    let mut lut = Vec::new();
    for i in 0..4 {
        lut.push(Fp::from(i));
    }

    let circuit = MyCircuit { lut };

    let params = params();

    let vk = halo2_proofs::plonk::keygen_vk(&params, &circuit).unwrap();

    let pk = halo2_proofs::plonk::keygen_pk(&params, vk.clone(), &circuit).unwrap();

    let mut transcript: Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>> =
        Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let mut rng = thread_rng();

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

#[derive(Clone)]
struct CircuitConfig {
    // Values to be looked up.
    values: Column<Advice>,
    /// The look up table.
    lut: TableColumn,
    selector_lookup: Selector,
}

#[derive(Default, Clone)]
struct MyCircuit {
    /// The lut for encodings of the bit value zero.
    /// A lut spans multiple columns.
    /// Each inner vector respresents a column of the lut.
    lut: Vec<Fp>,
}

impl Circuit<Fp> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let config = CircuitConfig {
            values: meta.advice_column(),
            selector_lookup: meta.complex_selector(),
            lut: meta.lookup_table_column(),
        };

        meta.lookup("lookup", |cells| {
            let sel = cells.query_selector(config.selector_lookup);
            let value = cells.query_advice(config.values, Rotation::cur());
            vec![(sel.clone() * value.clone(), config.lut)]
        });

        config
    }

    fn without_witnesses(&self) -> Self {
        Self {
            lut: self.lut.clone(),
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
                for j in 0..4 {
                    table.assign_cell(
                        || "table col",
                        config.lut,
                        j,
                        || Value::known(self.lut[j]),
                    )?;
                }

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign values to look up",
            |mut region| {
                // Enable lookup only on the first row.
                config.selector_lookup.enable(&mut region, 0)?;
                // The value 123 will be looked up which is NOT in the lut.
                region.assign_advice(|| "", config.values, 0, || Value::known(F::from(123)))?;
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
