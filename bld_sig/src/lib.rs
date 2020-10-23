#![feature(test)]
// #![feature(globs)]
pub mod protocols;

extern crate test;
extern crate class_group;
extern crate paillier;
extern crate libc;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;
extern crate criterion;

use serde::{Deserialize, Serialize};
use class_group::primitives::cl_dl_lcm::jacobi;
use class_group::primitives::cl_dl_lcm::HSMCL;
use class_group::primitives::cl_dl_lcm::PK;
use class_group::primitives::cl_dl_lcm::next_probable_small_prime;
use class_group::primitives::cl_dl_lcm::next_probable_prime;
use class_group::bn_to_gen;
use class_group::isprime;
use class_group::pari_init;
use class_group::primitives::is_prime;
use class_group::BinaryQF;
use class_group::primitives::numerical_log;
use class_group::primitives::prng;
use curv::arithmetic::traits::Modulo;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::arithmetic::traits::Samplable;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use curv::{FE, GE};
use std::os::raw::c_int;
use paillier::keygen::PrimeSampable;
use protocols::mpaillier::Pallier_AsiaCCS_19;
use protocols::asiaccs_zk::ZK_AsiaCCS_19;
use protocols::ggm_zk::zkPoKEncProof_v0;
use protocols::ggm_zk::zkPoKEncProof;

pub const SECURITY_PARAMETER: usize = 80;
pub const C: usize = 1;

#[derive(Debug)]
pub struct ProofError;

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum Error {
    InvalidKey,
    InvalidCom,
    InvalidSig,
    InvalidProof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Response {
    pub m2: BigInt,
    pub r2: BigInt,
}


fn main() {

    let bitsize: usize = 2048;
    let message = BigInt::from(1234);
    let r = BigInt::from(1222);
    let key = Pallier_AsiaCCS_19::keygen(bitsize);
    let ciphertext = Pallier_AsiaCCS_19::encrypt(
        &message,
        &r,
        &key.N, 
        &key.N_square, 
        &key.g, 
        &key.q
    );
    let m_recover = Pallier_AsiaCCS_19::decrypt(
        &ciphertext, 
        key.clone()
    );
    println!("{}", m_recover);

    let proof = ZK_AsiaCCS_19::prove(
        key.N.clone(),
        key.N_square.clone(),
        key.q.clone(),
        key.g.clone(),
        ciphertext.clone(),
        message.clone(), 
        r.clone(),
    );

    let flag = proof.verify();
    assert_eq!(flag, true);

    println!("Hello Ecdsa!")
}




