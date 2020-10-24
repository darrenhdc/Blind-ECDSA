use std::cmp;

use class_group::primitives::cl_dl_lcm::Ciphertext;
use class_group::primitives::cl_dl_lcm::{CLDLProof, U1U2, HSMCL};
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
use serde::{Deserialize, Serialize};
use crate::*;
use paillier::keygen::PrimeSampable;

use crate::Error::{self, InvalidSig};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TTriplets {
    pub t1: BinaryQF,
    pub t2: BinaryQF,
    pub T: GE,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CLDLProof_modified {
    pub seed: BigInt,
    pub pk: PK,
    pub ciphertext: Ciphertext,
    q: GE,
    t_vec: Vec<TTriplets>,
    u_vec: Vec<U1U2>,
}

#[derive(Clone, Debug, Serialize, Deserialize)] //reload and add clone feature
pub struct Witness {
    pub r: BigInt,
    pub x: BigInt,
}

// forked from Zen-Go's code, fix a problem in && operation
impl CLDLProof_modified {
    pub fn prove(w: Witness, pk: PK, ciphertext: Ciphertext, q: GE, seed: BigInt, c: usize,) -> Self {
        unsafe { pari_init(100000000, 2) };
        // let repeat = SECURITY_PARAMETER / C + 1;
        let repeat = 80 / c;
        let triplets_and_fs_and_r_vec = (0..repeat)
            .map(|_| {
                // let r1 = BigInt::sample_below(
                //     &(&pk.stilde
                //         * BigInt::from(2).pow(40)
                //         * BigInt::from(2).pow(C as u32)
                //         * BigInt::from(2).pow(40)),
                // );
                let r1 = BigInt::sample_below(
                    &(&pk.stilde
                        * BigInt::from(2).pow(80)
                        * BigInt::from(2).pow(C as u32)
                        * BigInt::from(2).pow(80)),
                );
                let r2_fe: FE = FE::new_random();
                let r2 = r2_fe.to_big_int();
                let fr2 = BinaryQF::expo_f(&pk.q, &pk.delta_q, &r2);
                let pkr1 = pk.h.exp(&r1);
                let t2 = fr2.compose(&pkr1).reduce();
                let T = GE::generator() * r2_fe;
                let t1 = pk.gq.exp(&r1);
                let fs = HSha256::create_hash(&[
                    &BigInt::from(&t1.to_bytes()[..]),
                    &BigInt::from(&t2.to_bytes()[..]),
                    &T.bytes_compressed_to_big_int(),
                ]);
                (TTriplets { t1, t2, T }, fs, r1, r2)
            })
            .collect::<Vec<(TTriplets, BigInt, BigInt, BigInt)>>();
        let triplets_vec = (0..repeat)
            .map(|i| triplets_and_fs_and_r_vec[i].0.clone())
            .collect::<Vec<TTriplets>>();
        let fiat_shamir_vec = (0..repeat)
            .map(|i| &triplets_and_fs_and_r_vec[i].1)
            .collect::<Vec<&BigInt>>();
        let r1_vec = (0..repeat)
            .map(|i| triplets_and_fs_and_r_vec[i].2.clone())
            .collect::<Vec<BigInt>>();
        let r2_vec = (0..repeat)
            .map(|i| triplets_and_fs_and_r_vec[i].3.clone())
            .collect::<Vec<BigInt>>();
        // using Fiat Shamir transform
        let k = HSha256::create_hash(&fiat_shamir_vec);
        // println!("k:{}",k);

        // let ten = BigInt::from(C as u32);
        // println!("ten:{}", ten); //original version seems not correct should be 2^10

        let two: i32 = 2;
        let two_pow_ten = two.pow(C as u32);
        let ten_1_bits_string = BigInt::from(two_pow_ten - 1);
        
        let u1u2_vec = (0..repeat)
            .map(|i| {
                let k_slice_i = (k.clone() >> (i * C)) & ten_1_bits_string.clone();
                // println!("k_slice_i:{}",k_slice_i);
                // let and_c = (k.clone() >> (i * C));
                // println!("and_c:{}",and_c);
                let u1 = r1_vec[i].clone() + &k_slice_i * &w.r;
                let u2 = BigInt::mod_add(&r2_vec[i], &(&k_slice_i * &w.x), &FE::q());
                U1U2 { u1, u2 }
            })
            .collect::<Vec<U1U2>>();
        CLDLProof_modified {
            seed,
            pk,
            ciphertext,
            q,
            t_vec: triplets_vec,
            u_vec: u1u2_vec,
        }
    }

    pub fn verify(&self, c: usize,) -> Result<(), ProofError> {
        unsafe { pari_init(100000000, 2) };
        let mut flag = true;

        // if HSMCL::setup_verify(&self.pk, &self.seed).is_err() {
        //     flag = false;
        // }

        // reconstruct k
        // let repeat = SECURITY_PARAMETER / C + 1;
        let repeat = 80 / c;
        let fs_vec = (0..repeat)
            .map(|i| {
                HSha256::create_hash(&[
                    &BigInt::from(&self.t_vec[i].t1.to_bytes()[..]),
                    &BigInt::from(&self.t_vec[i].t2.to_bytes()[..]),
                    &self.t_vec[i].T.bytes_compressed_to_big_int(),
                ])
            })
            .collect::<Vec<BigInt>>();
        let fs_t_vec = (0..repeat).map(|i| &fs_vec[i]).collect::<Vec<&BigInt>>();
        let mut flag = true;
        let k = HSha256::create_hash(&fs_t_vec[..]);
        // let ten = BigInt::from(C as u32);

        let two: i32 = 2;
        let two_pow_ten = two.pow(C as u32);
        let ten_1_bits_string = BigInt::from(two_pow_ten - 1);  // if C = 1, then this string is "1"

        // let sample_size = &self.pk.stilde
        //     * (BigInt::from(2).pow(40))
        //     * BigInt::from(2).pow(C as u32)
        //     * (BigInt::from(2).pow(40) + BigInt::one());
        let sample_size = &self.pk.stilde
            * (BigInt::from(2).pow(80))
            * BigInt::from(2).pow(C as u32)
            * (BigInt::from(2).pow(80) + BigInt::one());
        for i in 0..repeat {
            let k_slice_i = (k.clone() >> (i * C)) & ten_1_bits_string.clone();
            //length test u1:
            if &self.u_vec[i].u1 > &sample_size || &self.u_vec[i].u1 < &BigInt::zero() {
                flag = false;
            }
            // length test u2:
            if &self.u_vec[i].u2 > &FE::q() || &self.u_vec[i].u2 < &BigInt::zero() {
                flag = false;
            }
            let c1k = self.ciphertext.c1.exp(&k_slice_i);
            let t1c1k = self.t_vec[i].t1.compose(&c1k).reduce();
            let gqu1 = self.pk.gq.exp(&&self.u_vec[i].u1);
            if t1c1k != gqu1 {
                flag = false;
            };

            let k_slice_i_bias_fe: FE = ECScalar::from(&(k_slice_i.clone() + BigInt::one()));
            let g = GE::generator();
            let t2kq = (self.t_vec[i].T + self.q.clone() * k_slice_i_bias_fe)
                .sub_point(&self.q.get_element());
            let u2p = &g * &ECScalar::from(&self.u_vec[i].u2);
            if t2kq != u2p {
                flag = false;
            }

            let pku1 = self.pk.h.exp(&self.u_vec[i].u1);
            let fu2 = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_vec[i].u2);
            let c2k = self.ciphertext.c2.exp(&k_slice_i);
            let t2c2k = self.t_vec[i].t2.compose(&c2k).reduce();
            let pku1fu2 = pku1.compose(&fu2).reduce();
            if t2c2k != pku1fu2 {
                flag = false;
            }
        }
        match flag {
            true => Ok(()),
            false => Err(ProofError),
        }
    }
}