use std::cmp;

use class_group::primitives::cl_dl_lcm::Ciphertext;
use class_group::primitives::cl_dl_lcm::Witness;
use class_group::primitives::cl_dl_lcm::{CLDLProof,  HSMCL};
// use class_group::primitives::cl_dl_lcm::{CLDLProofPublicSetup, HSMCl};
use curv::arithmetic::traits::*;
use curv::cryptographic_primitives::commitments::hash_commitment::HashCommitment;
use curv::cryptographic_primitives::commitments::traits::Commitment;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::cryptographic_primitives::proofs::sigma_dlog::*;
use curv::cryptographic_primitives::proofs::sigma_ec_ddh::*;
use curv::cryptographic_primitives::proofs::ProofError;
use curv::elliptic::curves::traits::*;
use curv::BigInt;
use curv::FE;
use curv::GE;
use crate::*;
use serde::{Deserialize, Serialize};
use protocols::asiaccs_zk::ZK_AsiaCCS_19;
use protocols::mpaillier::Pallier_AsiaCCS_19;
use protocols::hsmcl_zk::CLDLProof_modified;

use crate::Error::{self, InvalidSig};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Signer_EcKeyPair {
    pub public_share: GE,
    pub secret_share: FE, // should be private variable, changed for test
}

impl Signer_EcKeyPair {
    pub fn s1_generate_K1() -> Self {
        let base: GE = ECPoint::generator();
        let secret_share: FE = ECScalar::new_random();
        let public_share = base.scalar_mul(&secret_share.get_element());
        Self{
            public_share,
            secret_share,
        }
    }
}

pub fn s3_scal_and_eval(C1: &BigInt, C2: &BigInt, k1: &BigInt, sk: &BigInt, bitsize: &usize) -> BigInt{
    let q = FE::q();
    let k1_inv = k1.invert(&q).unwrap();
    let key = Pallier_AsiaCCS_19::keygen(bitsize.clone());
    let c2sk = C2.powm(sk, &key.N_square);
}