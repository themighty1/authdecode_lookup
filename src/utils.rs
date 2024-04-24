use core::panic;
use std::time::Instant;

use criterion::measurement::Measurement;
use ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_backend::transcript::Blake2bWrite;
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

use crate::{circuit_instance, VerifierError, K};

/// Unzips a slice of pairs, returning items corresponding to choice
pub fn choose<T: Clone>(items: &[[T; 2]], choice: &[bool]) -> Vec<T> {
    assert!(items.len() == choice.len(), "arrays are different length");
    items
        .iter()
        .zip(choice)
        .map(|(items, choice)| items[*choice as usize].clone())
        .collect()
}

pub fn verification_key(params: ParamsKZG<Bn256>) -> VerifyingKey<G1Affine> {
    // It is safe to `unwrap` since we are inputting deterministic params and circuit.
    plonk::keygen_vk(&params, &circuit_instance()).unwrap()
}

pub fn proving_key(params: ParamsKZG<Bn256>) -> ProvingKey<G1Affine> {
    // It is safe to `unwrap` since we are inputting deterministic params and circuit.
    plonk::keygen_pk(
        &params,
        verification_key(params.clone()),
        &circuit_instance(),
    )
    .unwrap()
}

pub fn params() -> ParamsKZG<Bn256> {
    ParamsKZG::new(K)
}

pub fn verify_proof<
    'a,
    'params,
    Scheme: CommitmentScheme<Scalar = halo2_proofs::halo2curves::bn256::Fr>,
    V: CommitmentVerifier<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    T: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
    Strategy: VerificationStrategy<'params, Scheme, V, Output = Strategy>,
>(
    params_verifier: &'params Scheme::ParamsVerifier,
    vk: &VerifyingKey<Scheme::Curve>,
    proof: &'a [u8],
    instances: &[&[&[F]]],
) -> Result<(), VerifierError>
where
    Scheme::Scalar: Ord + WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let mut transcript = T::init(proof);

    let strategy = Strategy::new(params_verifier);
    let strategy = verify_plonk_proof(params_verifier, vk, strategy, instances, &mut transcript);

    if strategy.is_err() {
        return Err(VerifierError::VerificationFailed);
    }

    let str = strategy.unwrap();

    if !str.finalize() {
        return Err(VerifierError::VerificationFailed);
    }

    Ok(())
}

/// Converts BE bytes into bits in MSB-first order, left-padding with zeroes
/// to the nearest multiple of 8.
pub fn u8vec_to_boolvec(v: &[u8]) -> Vec<bool> {
    let mut bv = Vec::with_capacity(v.len() * 8);
    for byte in v.iter() {
        for i in 0..8 {
            bv.push(((byte >> (7 - i)) & 1) != 0);
        }
    }
    bv
}

/// Converts BE bytes into bits in MSB-first order without padding,
pub fn u8vec_to_boolvec_no_pad(v: &[u8]) -> Vec<bool> {
    let mut padded = u8vec_to_boolvec(v);
    while !padded.is_empty() {
        if !padded.first().unwrap() {
            // Remove the leading zero.
            padded.remove(0);
        } else {
            break;
        }
    }

    if padded.is_empty() {
        // The input was zero.
        return vec![false];
    }
    padded
}
