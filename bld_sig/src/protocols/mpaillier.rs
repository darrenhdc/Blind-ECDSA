use crate::*;
use serde::{Deserialize, Serialize};
use curv::elliptic::curves::traits::ECScalar;
use curv::BigInt;
use curv::FE;
use paillier::keygen::PrimeSampable;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pallier_AsiaCCS_19{
    pub N: BigInt,
    pub N_square: BigInt,
    pub g: BigInt,
    pub p: BigInt,
    pub q: BigInt,
    pub t: BigInt,
}

impl Pallier_AsiaCCS_19{
    pub fn keygen(bitsize: usize) -> Self {
    let q = FE::q(); // ECDSA's q
    let size_left = bitsize - q.bit_length();
    let mut p = BigInt::sample_prime(size_left / 2);
    let mut t = BigInt::sample_prime(size_left / 2);
    let mut p_minus_1 = &p - &BigInt::one();
    let mut t_minus_1 = &p - &BigInt::one();

    while q.gcd(&t_minus_1) != BigInt::one() || q.gcd(&p_minus_1) != BigInt::one() {
        p = BigInt::sample_prime(size_left / 2);
        t = BigInt::sample_prime(size_left / 2);
        t_minus_1 = &p - &BigInt::from(1);
        p_minus_1 = &p - &BigInt::from(1);
    }
    let N = &p *&q *&t;
    let N_square = &N * &N;
    let pt = &p * &t;
    let N_plus_1 = &N + &BigInt::from(1);
    let g = N_plus_1.powm(&pt, &N_square);
    // println!("{}\n{}\n{}",p,q,t);

    Self{
        N,
        N_square,
        g,
        p,
        q,
        t,
    }
    }

    pub fn encrypt(
        message: &BigInt, 
        r: &BigInt,
        N: &BigInt,
        N_square: &BigInt,
        g: &BigInt,
        q: &BigInt,
    ) -> BigInt {
        let gm = g.powm(&message, &N_square);
        let rN = r.powm(&N, & N_square);
        let gmrN = &gm * &rN;
        gmrN.mod_floor(&N_square)
    }

    pub fn decrypt(
        ciphertext: &BigInt,
        key: Self,
    ) -> BigInt {
        let p_minus_1 = &key.p - &BigInt::one();
        let q_minus_1 = &key.q - &BigInt::one();
        let t_minus_1 = &key.t - &BigInt::one();
        let exp = &p_minus_1 * &q_minus_1 * &t_minus_1;
        let exp_inv_modq = exp.invert(&key.q).unwrap();
        let D = ciphertext.powm(&exp, &key.N_square);
        let D_minus_1 = &D - &BigInt::one();
        let Npt = &key.N * &key.p * &key.t;
        let f = &D_minus_1 / &Npt;
        let m_recover_ = &f * &exp_inv_modq;
        m_recover_.mod_floor(&key.q)
    }
}