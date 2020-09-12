#![feature(test)]
extern crate test;
extern crate class_group;
extern crate paillier;
extern crate libc;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;
extern crate criterion;

use test::Bencher;
use criterion::criterion_main;

use serde::{Deserialize, Serialize};
use class_group::primitives::ErrorReason;
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

const SECURITY_PARAMETER: usize = 80;
const C: usize = 1;


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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pallier_AsiaCCS_19{
    pub N: BigInt,
    pub N_square: BigInt,
    pub g: BigInt,
    p: BigInt,
    q: BigInt,
    t: BigInt,
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZK_AsiaCCS_19{
    pub C: BigInt, //ciphertext C = g^m r^N mod N^2
    pub N: BigInt, 
    pub N_square: BigInt,
    pub g: BigInt, 
    C1_vec: Vec<BigInt>, // commit C1 = g^m1 r1^N mod N^2
    Response_vec: Vec<Response>, // response m2 = m1 + b * m and r2 = r1 + b * r
}

// HSM-CL Encryption Well-formedness ZKPoK
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct zkPoKEncProof_v0 {
    pub seed: BigInt,
    pub pk: PK,
    pub x1: BinaryQF,
    pub x2: BinaryQF,
    pub y1: BinaryQF,
    pub y2: BinaryQF,

    S1: BinaryQF,
    S2: BinaryQF,
    S3: BinaryQF,
    S4: BinaryQF,

    D1: BinaryQF,
    D2: BinaryQF,
    D3: BinaryQF,
    D4: BinaryQF,

    u_x: BigInt,
    u_h: BigInt,
    e_1: BigInt,
    e_2: BigInt,

    Q1: BinaryQF,
    Q2: BinaryQF,
    Q3: BinaryQF,
    Q4: BinaryQF,

    gamma_1: BigInt,
    gamma_2: BigInt,
}

// HSM-CL Encryption Well-formedness ZKPoK
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct zkPoKEncProof {
    pub seed: BigInt,
    pub pk: PK,
    pub x1: BinaryQF,
    pub x2: BinaryQF,
    pub y1: BinaryQF,
    pub y2: BinaryQF,
    pub PK: GE,//ECC: G^SK

    S_hat: GE,
    S1: BinaryQF,
    S2: BinaryQF,
    S3: BinaryQF,
    S4: BinaryQF,
    S5: BinaryQF,

    D1: BinaryQF,
    D2: BinaryQF,
    D3: BinaryQF,
    D4: BinaryQF,
    D5: BinaryQF,

    u_rho: BigInt,
    u_x: BigInt,
    u_h: BigInt,
    e_1: BigInt,
    e_2: BigInt,
    e_k: BigInt,

    Q1: BinaryQF,
    Q2: BinaryQF,
    Q3: BinaryQF,
    Q4: BinaryQF,
    Q5: BinaryQF,

    gamma_1: BigInt,
    gamma_2: BigInt,
    gamma_k: BigInt,
}

impl zkPoKEncProof_v0 {
    pub fn prove(g: GE, 
            hsmcl: HSMCL, 
            h: BigInt, 
            Kx: BigInt, 
            r1: BigInt, 
            r2: BigInt, 
            x1: BinaryQF, 
            x2: BinaryQF, 
            y1: BinaryQF, 
            y2: BinaryQF, 
            B: BigInt, 
            minus_B: BigInt, 
            seed: BigInt
        ) -> Self {

        unsafe { pari_init(10000000, 2) };
        let s_1 = BigInt::sample_range(&minus_B, &B);
        let s_2 = BigInt::sample_range(&minus_B, &B);
        let s_h = BigInt::sample_range(&minus_B, &B); // for h
        let s_x = BigInt::sample_range(&minus_B, &B); // for Kx

        // calculate commit
        let fsh = BinaryQF::expo_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &s_h);
        let fsx = BinaryQF::expo_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &s_x);
        let pks1 = hsmcl.pk.h.clone().exp(&s_1); // pk^s_1
        let pks2 = hsmcl.pk.h.clone().exp(&s_2); // pk^s_2

        let S1 = hsmcl.pk.gq.exp(&s_1);
        let S2 = fsh.compose(&pks1).reduce();
        let S3 = hsmcl.pk.gq.exp(&s_2);   
        let S4 = fsx.compose(&pks2).reduce();
        
        //use fiat shamir transform to calculate challenge c
        let fs1 = HSha256::create_hash(&[
            &BigInt::from(&S1.to_bytes()[..]),
            &BigInt::from(&S2.to_bytes()[..]),
            &BigInt::from(&S3.to_bytes()[..]),
            &BigInt::from(&S4.to_bytes()[..]),

        ]);
        let c = HSha256::create_hash(&[&fs1]).mod_floor(&hsmcl.pk.q);

        let u_1 = s_1 + &c * &r1;
        let u_2 = s_2 + &c * &r2;
        let u_h = s_h + &c * &h;
        let u_x = s_x + &c * &Kx;

        let d_1 = u_1.div_floor(&hsmcl.pk.q);
        let d_2 = u_2.div_floor(&hsmcl.pk.q);

        let e_1 = u_1.mod_floor(&hsmcl.pk.q);
        let e_2 = u_2.mod_floor(&hsmcl.pk.q);
        let e_h = u_h.mod_floor(&hsmcl.pk.q);
        let e_x = u_x.mod_floor(&hsmcl.pk.q);

        let D1 = hsmcl.pk.gq.exp(&d_1);
        let D2 = hsmcl.pk.h.clone().exp(&d_1);
        let D3 = hsmcl.pk.gq.exp(&d_2);
        let D4 = hsmcl.pk.h.clone().exp(&d_2);

        //use fiat shamir transform to calculate l
        let fs2 = HSha256::create_hash(&[
            &BigInt::from(&D1.to_bytes()[..]),
            &BigInt::from(&D2.to_bytes()[..]),
            &BigInt::from(&D3.to_bytes()[..]),
            &BigInt::from(&D4.to_bytes()[..]),
            &u_h,
            &u_x,
            &e_1,
            &e_2,

        ]);

        let ell_bits = 87; 
        let two_pow_ellbits = BigInt::ui_pow_ui(2,ell_bits);
        let r = HSha256::create_hash(&[&fs2]).mod_floor(&two_pow_ellbits);
        let l = next_probable_small_prime(&r);

        let q_1 = u_1.div_floor(&l);
        let q_2 = u_2.div_floor(&l);
        let gamma_1 = u_1.mod_floor(&l);
        let gamma_2 = u_2.mod_floor(&l);

        let Q1 = hsmcl.pk.gq.exp(&q_1);
        let Q2 = hsmcl.pk.h.exp(&q_1); 
        let Q3 = hsmcl.pk.gq.exp(&q_2);
        let Q4 = hsmcl.pk.h.exp(&q_2); 

        let pk = hsmcl.pk.clone();

        zkPoKEncProof_v0  {
            seed,
            pk,
            x1,
            x2,
            y1,
            y2,

            S1,
            S2,
            S3,
            S4,

            D1,
            D2,
            D3,
            D4,

            u_h,
            u_x,
            e_1,
            e_2,

            Q1,
            Q2,
            Q3,
            Q4,

            gamma_1,
            gamma_2,
        }
    }

    pub fn verify(&self) -> Result<(), ProofError>{
        unsafe { pari_init(100000000, 2) };
        let mut flag = true;

        //use fiat shamir transform to calculate challenge c
        let fs1 = HSha256::create_hash(&[
            &BigInt::from(&self.S1.to_bytes()[..]),
            &BigInt::from(&self.S2.to_bytes()[..]),
            &BigInt::from(&self.S3.to_bytes()[..]),
            &BigInt::from(&self.S4.to_bytes()[..]),
        ]);
        let c = HSha256::create_hash(&[&fs1]).mod_floor(&self.pk.q);

        // VERIFY STEP 4
        if &self.e_1 > &&FE::q()   
            || &self.e_1 < &BigInt::zero()
            || &self.e_2 > &&FE::q()   
            || &self.e_2 < &BigInt::zero()
        {
            flag = false;
        }

        // intermediate variables
        let c_bias_fe: FE = ECScalar::from(&(c.clone() + BigInt::one()));
        let fuh = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_h);
        let fux = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_x);
        let pke1 = self.pk.h.clone().exp(&self.e_1);
        let pke2 = self.pk.h.clone().exp(&self.e_2);
        let pke1fuh = fuh.compose(&pke1).reduce();
        let pke2fux = fux.compose(&pke2).reduce();
        let d1q = self.D1.exp(&self.pk.q);
        let d2q = self.D2.exp(&self.pk.q);
        let d3q = self.D3.exp(&self.pk.q);
        let d4q = self.D4.exp(&self.pk.q);
        let gqe1 = self.pk.gq.exp(&self.e_1);
        let gqe2 = self.pk.gq.exp(&self.e_2);
        let x1c = self.x1.exp(&c);
        let s1x1c = x1c.compose(&self.S1).reduce();
        let x2c = self.x2.exp(&c);
        let s2x2c = x2c.compose(&self.S2).reduce();
        let y1c = self.y1.exp(&c);
        let s3y1c = y1c.compose(&self.S3).reduce();
        let y2c = self.y2.exp(&c);
        let s4y2c = y2c.compose(&self.S4).reduce();

        let d1qgqe1 = gqe1.compose(&d1q).reduce();
        if d1qgqe1 != s1x1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d2qpke1fuh = pke1fuh.compose(&d2q).reduce();
        if d2qpke1fuh != s2x2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d3qgqe2 = gqe2.compose(&d3q).reduce();
        if d3qgqe2 != s3y1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d4qpke2fux = pke2fux.compose(&d4q).reduce();
        if d4qpke2fux != s4y2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        //use fiat shamir transform
        let fs2 = HSha256::create_hash(&[
            &BigInt::from(&self.D1.to_bytes()[..]),
            &BigInt::from(&self.D2.to_bytes()[..]),
            &BigInt::from(&self.D3.to_bytes()[..]),
            &BigInt::from(&self.D4.to_bytes()[..]),
            &self.u_h,
            &self.u_x,
            &self.e_1,
            &self.e_2,
        ]);

        let ell_bits = 87;
        let two_pow_ellbits = BigInt::ui_pow_ui(2,ell_bits);
        let r = HSha256::create_hash(&[&fs2]).mod_floor(&two_pow_ellbits);
        let l = next_probable_small_prime(&r);

        //VERIFY STEP 6
        if self.gamma_1 < BigInt::zero() 
            || self.gamma_1 > l 
            || self.gamma_2 < BigInt::zero() 
            || self.gamma_2 > l 
        {
            flag = false;
        }

        // intermediate variables
        let pkgamma1 = self.pk.h.clone().exp(&self.gamma_1);
        let pkgamma2 = self.pk.h.clone().exp(&self.gamma_2);
        let pkgamma1fuh = fuh.compose(&pkgamma1).reduce();
        let pkgamma2fux = fux.compose(&pkgamma2).reduce();
        let q1l = self.Q1.exp(&l);
        let q2l = self.Q2.exp(&l);
        let q3l = self.Q3.exp(&l);
        let q4l = self.Q4.exp(&l);
        let gqgamma1 = self.pk.gq.exp(&self.gamma_1);
        let gqgamma2 = self.pk.gq.exp(&self.gamma_2);

        let q1lgqgamma1 = gqgamma1.compose(&q1l).reduce();
        if q1lgqgamma1 != s1x1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q2lpkgamma1fuh = pkgamma1fuh.compose(&q2l).reduce();
        if q2lpkgamma1fuh != s2x2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q3lgqgamma2 = gqgamma2.compose(&q3l).reduce();
        if q3lgqgamma2 != s3y1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q4lpkgamma2fux = pkgamma2fux.compose(&q4l).reduce();
        if q4lpkgamma2fux != s4y2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        match flag {
            true => Ok(()),
            false => Err(ProofError),
        }
    }
}


impl ZK_AsiaCCS_19{
    pub fn prove(
            N: BigInt, 
            N_square: BigInt,
            q: BigInt,
            g: BigInt,
            ciphertext: BigInt, 
            m: BigInt,     
            r: BigInt, 
        ) -> Self{
        unsafe { pari_init(10000000000, 2) };
        let repeat = SECURITY_PARAMETER / C;
        let C1_and_fs_and_m2_r2_vec = (0..repeat)
            .map(|_| {
                let m1 = BigInt::sample_below(&q);
                let r1 = BigInt::sample_below(&N_square);
                let gm1 = g.powm(&m1, &N_square);
                let r1N = r1.powm(&N, &N_square);
                let gm1r1N = &gm1 * &r1N;
                let C1 = gm1r1N.mod_floor(&N_square); // C'
                // fiat-shamir transform
                let fs = HSha256::create_hash(&[
                    &C1,
                ]);
                (C1, fs, m1, r1)
            })
            .collect::<Vec<(BigInt, BigInt, BigInt, BigInt)>>();

        let C1_vec = (0..repeat)
            .map(|i| C1_and_fs_and_m2_r2_vec[i].0.clone())
            .collect::<Vec<BigInt>>();
        let fiat_shamir_vec = (0..repeat)
            .map(|i| &C1_and_fs_and_m2_r2_vec[i].1)
            .collect::<Vec<&BigInt>>();
        let m1_vec = (0..repeat)
            .map(|i| C1_and_fs_and_m2_r2_vec[i].2.clone())
            .collect::<Vec<BigInt>>();
        let r1_vec = (0..repeat)
            .map(|i| C1_and_fs_and_m2_r2_vec[i].3.clone())
            .collect::<Vec<BigInt>>();

        // using Fiat Shamir transform
        let k = HSha256::create_hash(&fiat_shamir_vec);
        let two: i32 = 2;
        let two_pow_ten = two.pow(C as u32);
        let ten_1_bits_string = BigInt::from(two_pow_ten - 1);
        
        let m2r2_vec = (0..repeat)
            .map(|i| {        
                let k_slice_i = (k.clone() >> (i * C)) & ten_1_bits_string.clone(); // output 0 or 1
                let m2_ = &m1_vec[i] + &k_slice_i * &m;
                let r2_ = &r1_vec[i] * &r.powm(&k_slice_i, &N_square);
                let m2 = m2_.mod_floor(&q);
                let r2 = r2_.mod_floor(&N_square);
                Response { m2, r2 }
            })
            .collect::<Vec<Response>>();

        ZK_AsiaCCS_19{
            C: ciphertext,
            N: N,
            N_square: N_square,
            g: g,
            C1_vec: C1_vec,
            Response_vec: m2r2_vec,
        }
    }

    pub fn verify(&self) -> bool {
        let mut flag = true;
        unsafe { pari_init(10000000000, 2) };
        
        // reconstruct k
        let repeat = SECURITY_PARAMETER / C;
        let fs_vec = (0..repeat)
            .map(|i| HSha256::create_hash(&[&self.C1_vec[i]]))
            .collect::<Vec<BigInt>>();
        let fs_t_vec = (0..repeat)
            .map(|i| &fs_vec[i])
            .collect::<Vec<&BigInt>>();
        let mut flag = true;
        let k = HSha256::create_hash(&fs_t_vec[..]);

        let two: i32 = 2;
        let two_pow_ten = two.pow(C as u32);
        let ten_1_bits_string = BigInt::from(two_pow_ten - 1);
        for i in 0..repeat {
            let k_slice_i = (k.clone() >> (i * C)) & ten_1_bits_string.clone();
            let Cb = self.C.powm(&k_slice_i, &self.N_square);
            let CbC1 = &Cb * &self.C1_vec[i]; // C^b * C'
            let eq_left = CbC1.mod_floor(&self.N_square);
            let gm2 = &self.g.powm(&self.Response_vec[i].m2, &self.N_square);
            let r2N = &self.Response_vec[i].r2.powm(&self.N, &self.N_square);
            let gm2r2N = gm2 * r2N;
            let eq_right = gm2r2N.mod_floor(&self.N_square);

            if &eq_left != &eq_right {
                flag = false;
            };
            assert_eq!(flag, true);
        }
        flag
    }
}


impl zkPoKEncProof{
    pub fn prove(g: GE, 
            hsmcl: HSMCL, 
            h: BigInt, 
            Kx: BigInt, 
            r1: BigInt, 
            r2: BigInt, 
            x1: BinaryQF, 
            x2: BinaryQF, 
            y1: BinaryQF, 
            y2: BinaryQF, 
            PK: GE, 
            SK: BigInt, 
            B: BigInt, 
            minus_B: BigInt, 
            seed: BigInt
        ) -> Self {

        unsafe { pari_init(10000000, 2) };
        let s_1 = BigInt::sample_range(&minus_B, &B);
        let s_2 = BigInt::sample_range(&minus_B, &B);
        let s_k = BigInt::sample_range(&minus_B, &B); // for sk
        let s_h = BigInt::sample_range(&minus_B, &B); // for h
        let s_x = BigInt::sample_range(&minus_B, &B); // for Kx
        let srho_fe: FE = FE::new_random();
        let s_rho = srho_fe.to_big_int(); //according to line 519

        // calculate commit
        let fsh = BinaryQF::expo_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &s_h);
        let fsx = BinaryQF::expo_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &s_x);
        let pks1 = hsmcl.pk.h.clone().exp(&s_1); // pk^s_1
        let pks2 = hsmcl.pk.h.clone().exp(&s_2); // pk^s_2

        let S_hat = &g * &srho_fe; 
        let S1 = hsmcl.pk.gq.exp(&s_1);
        let S2 = fsh.compose(&pks1).reduce();
        let S3 = hsmcl.pk.gq.exp(&s_2);   
        let S4 = fsx.compose(&pks2).reduce();
        let S5 = hsmcl.pk.gq.exp(&s_k);
        

        //use fiat shamir transform to calculate challenge c
        let fs1 = HSha256::create_hash(&[
            &S_hat.bytes_compressed_to_big_int(),
            &BigInt::from(&S1.to_bytes()[..]),
            &BigInt::from(&S2.to_bytes()[..]),
            &BigInt::from(&S3.to_bytes()[..]),
            &BigInt::from(&S4.to_bytes()[..]),
            &BigInt::from(&S5.to_bytes()[..]),
        ]);
        let c = HSha256::create_hash(&[&fs1]).mod_floor(&hsmcl.pk.q);

        let u_1 = s_1 + &c * &r1;
        let u_2 = s_2 + &c * &r2;
        let u_k = s_k + &c * &hsmcl.sk;
        let u_h = s_h + &c * &h;
        let u_x = s_x + &c * &Kx;
        let u_rho = BigInt::mod_add(&s_rho, &(&c * &SK), &FE::q());

        let d_1 = u_1.div_floor(&hsmcl.pk.q);
        let d_2 = u_2.div_floor(&hsmcl.pk.q);
        let d_k = u_k.div_floor(&hsmcl.pk.q);
        // let d_h = u_h.div_floor(&hsmcl.pk.q);
        // let d_x = u_x.div_floor(&hsmcl.pk.q);

        let e_1 = u_1.mod_floor(&hsmcl.pk.q);
        let e_2 = u_2.mod_floor(&hsmcl.pk.q);
        let e_k = u_k.mod_floor(&hsmcl.pk.q);
        let e_h = u_h.mod_floor(&hsmcl.pk.q);
        let e_x = u_x.mod_floor(&hsmcl.pk.q);

        let D1 = hsmcl.pk.gq.exp(&d_1);
        let D2 = hsmcl.pk.h.clone().exp(&d_1);
        let D3 = hsmcl.pk.gq.exp(&d_2);
        let D4 = hsmcl.pk.h.clone().exp(&d_2);
        let D5 = hsmcl.pk.gq.exp(&d_k);

        //use fiat shamir transform to calculate l
        let fs2 = HSha256::create_hash(&[
            &BigInt::from(&D1.to_bytes()[..]),
            &BigInt::from(&D2.to_bytes()[..]),
            &BigInt::from(&D3.to_bytes()[..]),
            &BigInt::from(&D4.to_bytes()[..]),
            &BigInt::from(&D5.to_bytes()[..]),
            &u_rho,
            &u_h,
            &u_x,
            &e_1,
            &e_2,
            &e_k,
            // &e_h,
            // &e_x,
        ]);

        // reconstruct prime l <- Primes(87), 
        // For our case, we need to ensure that we have 2^80 primes 
        // in the challenge set. In order to generate enough prime, 
        // we need to find X such that "80 = X - log_2 X”. 
        // Then X is the number of bits outputted by the Primes() function.
        // X \in (86, 87), so we adopt 87

        let ell_bits = 87; 
        let two_pow_ellbits = BigInt::ui_pow_ui(2,ell_bits);
        let r = HSha256::create_hash(&[&fs2]).mod_floor(&two_pow_ellbits);
        let l = next_probable_small_prime(&r);

        let q_1 = u_1.div_floor(&l);
        let q_2 = u_2.div_floor(&l);
        let q_k = u_k.div_floor(&l);
        let gamma_1 = u_1.mod_floor(&l);
        let gamma_2 = u_2.mod_floor(&l);
        let gamma_k = u_k.mod_floor(&l);

        let Q1 = hsmcl.pk.gq.exp(&q_1);
        let Q2 = hsmcl.pk.h.exp(&q_1); 
        let Q3 = hsmcl.pk.gq.exp(&q_2);
        let Q4 = hsmcl.pk.h.exp(&q_2); 
        let Q5 = hsmcl.pk.gq.exp(&q_k);

        let pk = hsmcl.pk.clone();

        zkPoKEncProof {
            seed,
            pk,
            x1,
            x2,
            y1,
            y2,
            PK, //ECC: G^SK
        
            S_hat,
            S1,
            S2,
            S3,
            S4,
            S5,
        
            D1,
            D2,
            D3,
            D4,
            D5,
        
            u_rho,
            u_h,
            u_x,
            e_1,
            e_2,
            e_k,
        
            Q1,
            Q2,
            Q3,
            Q4,
            Q5,
        
            gamma_1,
            gamma_2,
            gamma_k,
        }
    }

    pub fn verify(&self) -> Result<(), ProofError>{
        unsafe { pari_init(100000000, 2) };
        let mut flag = true;

        //use fiat shamir transform to calculate challenge c
        let fs1 = HSha256::create_hash(&[
            &self.S_hat.bytes_compressed_to_big_int(),
            &BigInt::from(&self.S1.to_bytes()[..]),
            &BigInt::from(&self.S2.to_bytes()[..]),
            &BigInt::from(&self.S3.to_bytes()[..]),
            &BigInt::from(&self.S4.to_bytes()[..]),
            &BigInt::from(&self.S5.to_bytes()[..]),
        ]);
        let c = HSha256::create_hash(&[&fs1]).mod_floor(&self.pk.q);

        // VERIFY STEP 4
        if &self.u_rho > &FE::q() 
            || &self.u_rho < &BigInt::zero() 
            || &self.e_1 > &&FE::q()   
            || &self.e_1 < &BigInt::zero()
            || &self.e_2 > &&FE::q()   
            || &self.e_2 < &BigInt::zero()
            || &self.e_k > &&FE::q()  
            || &self.e_k < &BigInt::zero() 
        {
            flag = false;
        }

        // intermediate variables
        let urho_fe: FE = ECScalar::from(&self.u_rho);
        let ghatum = GE::generator() * urho_fe;
        let c_bias_fe: FE = ECScalar::from(&(c.clone() + BigInt::one()));
        let shatpkc = (self.S_hat + self.PK.clone() * c_bias_fe).sub_point(&self.PK.get_element());
        let fuh = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_h);
        let fux = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_x);
        let pke1 = self.pk.h.clone().exp(&self.e_1);
        let pke2 = self.pk.h.clone().exp(&self.e_2);
        let pke1fuh = fuh.compose(&pke1).reduce();
        let pke2fux = fux.compose(&pke2).reduce();
        let d1q = self.D1.exp(&self.pk.q);
        let d2q = self.D2.exp(&self.pk.q);
        let d3q = self.D3.exp(&self.pk.q);
        let d4q = self.D4.exp(&self.pk.q);
        let d5q = self.D5.exp(&self.pk.q);
        let gqe1 = self.pk.gq.exp(&self.e_1);
        let gqe2 = self.pk.gq.exp(&self.e_2);
        let gqek = self.pk.gq.exp(&self.e_k);
        let x1c = self.x1.exp(&c);
        let s1x1c = x1c.compose(&self.S1).reduce();
        let x2c = self.x2.exp(&c);
        let s2x2c = x2c.compose(&self.S2).reduce();
        let y1c = self.y1.exp(&c);
        let s3y1c = y1c.compose(&self.S3).reduce();
        let y2c = self.y2.exp(&c);
        let s4y2c = y2c.compose(&self.S4).reduce();

        if shatpkc != ghatum { // ECC equation
            flag = false;
        }
        assert!(flag == true, "verification failed");


        let d1qgqe1 = gqe1.compose(&d1q).reduce();
        if d1qgqe1 != s1x1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d2qpke1fuh = pke1fuh.compose(&d2q).reduce();
        if d2qpke1fuh != s2x2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d3qgqe2 = gqe2.compose(&d3q).reduce();
        if d3qgqe2 != s3y1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d4qpke2fux = pke2fux.compose(&d4q).reduce();
        if d4qpke2fux != s4y2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let d5qgqek = gqek.compose(&d5q).reduce();
        let pkc = self.pk.h.exp(&c);
        let s5pkc = pkc.compose(&self.S5).reduce();
        if d5qgqek != s5pkc {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        //use fiat shamir transform
        let fs2 = HSha256::create_hash(&[
            &BigInt::from(&self.D1.to_bytes()[..]),
            &BigInt::from(&self.D2.to_bytes()[..]),
            &BigInt::from(&self.D3.to_bytes()[..]),
            &BigInt::from(&self.D4.to_bytes()[..]),
            &BigInt::from(&self.D5.to_bytes()[..]),
            &self.u_rho,
            &self.u_h,
            &self.u_x,
            &self.e_1,
            &self.e_2,
            &self.e_k,
            // &self.e_h,
            // &self.e_x,
        ]);

        let ell_bits = 87;
        let two_pow_ellbits = BigInt::ui_pow_ui(2,ell_bits);
        let r = HSha256::create_hash(&[&fs2]).mod_floor(&two_pow_ellbits);
        let l = next_probable_small_prime(&r);

        //VERIFY STEP 6
        if self.gamma_1 < BigInt::zero() 
            || self.gamma_1 > l 
            || self.gamma_2 < BigInt::zero() 
            || self.gamma_2 > l 
            || self.gamma_k < BigInt::zero() 
            || self.gamma_k > l
        {
            flag = false;
        }

        // intermediate variables
        let pkgamma1 = self.pk.h.clone().exp(&self.gamma_1);
        let pkgamma2 = self.pk.h.clone().exp(&self.gamma_2);
        let pkgamma1fuh = fuh.compose(&pkgamma1).reduce();
        let pkgamma2fux = fux.compose(&pkgamma2).reduce();
        let q1l = self.Q1.exp(&l);
        let q2l = self.Q2.exp(&l);
        let q3l = self.Q3.exp(&l);
        let q4l = self.Q4.exp(&l);
        let q5l = self.Q5.exp(&l);
        let gqgamma1 = self.pk.gq.exp(&self.gamma_1);
        let gqgamma2 = self.pk.gq.exp(&self.gamma_2);
        let gqgammak = self.pk.gq.exp(&self.gamma_k);

        let q1lgqgamma1 = gqgamma1.compose(&q1l).reduce();
        if q1lgqgamma1 != s1x1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q2lpkgamma1fuh = pkgamma1fuh.compose(&q2l).reduce();
        if q2lpkgamma1fuh != s2x2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q3lgqgamma2 = gqgamma2.compose(&q3l).reduce();
        if q3lgqgamma2 != s3y1c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q4lpkgamma2fux = pkgamma2fux.compose(&q4l).reduce();
        if q4lpkgamma2fux != s4y2c {
            flag = false;
        }
        assert!(flag == true, "verification failed");

        let q5lgqgammak = gqgammak.compose(&q5l).reduce();
        if q5lgqgammak != s5pkc {
            flag = false;
        }
        assert!(flag == true, "verification failed");


        match flag {
            true => Ok(()),
            false => Err(ProofError),
        }
    }
}

// fn main() {

//     let bitsize: usize = 2048;
//     let message = BigInt::from(1234);
//     let r = BigInt::from(1222);
//     let key = Pallier_AsiaCCS_19::keygen(bitsize);
//     let ciphertext = Pallier_AsiaCCS_19::encrypt(
//         &message,
//         &r,
//         &key.N, 
//         &key.N_square, 
//         &key.g, 
//         &key.q
//     );
//     let m_recover = Pallier_AsiaCCS_19::decrypt(
//         &ciphertext, 
//         key.clone()
//     );
//     println!("{}", m_recover);

//     let proof = ZK_AsiaCCS_19::prove(
//         key.N.clone(),
//         key.N_square.clone(),
//         key.q.clone(),
//         key.g.clone(),
//         ciphertext.clone(),
//         message.clone(), 
//         r.clone(),
//     );

//     let flag = proof.verify();
//     assert_eq!(flag, true);

//     println!("Hello Ecdsa!")
// }

/*************** Benchmarking Program ****************/
mod bench {
    use criterion::{criterion_group, Criterion};
    use crate::*;
    use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use curv::BigInt;

    pub fn AsiaCCS_nizk_prove_2048(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_prove_2048", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(2048 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            b.iter(||
                ZK_AsiaCCS_19::prove(
                    key.N.clone(),
                    key.N_square.clone(),
                    key.q.clone(),
                    key.g.clone(),
                    ciphertext.clone(),
                    message.clone(), 
                    r.clone(),
                )       
            )
        });
    }
    pub fn AsiaCCS_nizk_prove_3072(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_prove_3072", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(3072 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            b.iter(||
                ZK_AsiaCCS_19::prove(
                    key.N.clone(),
                    key.N_square.clone(),
                    key.q.clone(),
                    key.g.clone(),
                    ciphertext.clone(),
                    message.clone(), 
                    r.clone(),
                )       
            )
        });
    }
    pub fn AsiaCCS_nizk_prove_4096(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_prove_4096", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(4096 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            b.iter(||
                ZK_AsiaCCS_19::prove(
                    key.N.clone(),
                    key.N_square.clone(),
                    key.q.clone(),
                    key.g.clone(),
                    ciphertext.clone(),
                    message.clone(), 
                    r.clone(),
                )       
            )
        });
    }

    pub fn AsiaCCS_nizk_verify_2048(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_verify_2048", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(2048 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            let proof =  ZK_AsiaCCS_19::prove(
                key.N.clone(),
                key.N_square.clone(),
                key.q.clone(),
                key.g.clone(),
                ciphertext.clone(),
                message.clone(), 
                r.clone(),
            );
            b.iter(||proof.verify());
        });
    }
    pub fn AsiaCCS_nizk_verify_3072(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_verify_3072", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(3072 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            let proof =  ZK_AsiaCCS_19::prove(
                key.N.clone(),
                key.N_square.clone(),
                key.q.clone(),
                key.g.clone(),
                ciphertext.clone(),
                message.clone(), 
                r.clone(),
            );
            b.iter(||proof.verify());
        });
    }
    pub fn AsiaCCS_nizk_verify_4096(c: &mut Criterion) {
        c.bench_function("AsiaCCS_nizk_verify_4096", move |b| {
            let key = Pallier_AsiaCCS_19::keygen(4096 as usize);
            let r = HSha256::create_hash(&[&BigInt::from(123)]).mod_floor(&key.q);
            let message = HSha256::create_hash(&[&BigInt::from(111)]).mod_floor(&key.q);
            let ciphertext = Pallier_AsiaCCS_19::encrypt(
                &message,
                &r,
                &key.N, 
                &key.N_square, 
                &key.g, 
                &key.q
            );
            let proof =  ZK_AsiaCCS_19::prove(
                key.N.clone(),
                key.N_square.clone(),
                key.q.clone(),
                key.g.clone(),
                ciphertext.clone(),
                message.clone(), 
                r.clone(),
            );
            b.iter(||proof.verify());
        });
    }

    pub fn hsmcl_nizk_prove_112(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_prove_112", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();

            let hsmcl = HSMCL::keygen_with_setup(&q, &1348, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let SK_fe: FE = FE::new_random();
            let SK = SK_fe.to_big_int();
            let g = GE::generator(); // ECC generator
            let PK = g.clone() * SK_fe;
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B

            b.iter(||
                zkPoKEncProof::prove(
                    g.clone(), 
                    hsmcl.clone(), 
                    h.clone(),
                    Kx.clone(),
                    r1.clone(),
                    r2.clone(),
                    x1.clone(),
                    x2.clone(),
                    y1.clone(),
                    y2.clone(),
                    PK.clone(),
                    SK.clone(),
                    B.clone(),
                    minus_B.clone(),
                    seed.clone(),
                )
            )
        });
    }

    pub fn hsmcl_nizk_prove_128(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_prove_128", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();
            let hsmcl = HSMCL::keygen_with_setup(&q, &1827, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let SK_fe: FE = FE::new_random();
            let SK = SK_fe.to_big_int();
            let g = GE::generator(); // ECC generator
            let PK = g.clone() * SK_fe;
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B

            b.iter(||
                zkPoKEncProof::prove(
                    g.clone(), 
                    hsmcl.clone(), 
                    h.clone(),
                    Kx.clone(),
                    r1.clone(),
                    r2.clone(),
                    x1.clone(),
                    x2.clone(),
                    y1.clone(),
                    y2.clone(),
                    PK.clone(),
                    SK.clone(),
                    B.clone(),
                    minus_B.clone(),
                    seed.clone(),
                )
            )
        });
    }

    pub fn hsmcl_nizk_verify_112(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_verify_112", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();

            let hsmcl = HSMCL::keygen_with_setup(&q, &1348, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let SK_fe: FE = FE::new_random();
            let SK = SK_fe.to_big_int();
            let g = GE::generator(); // ECC generator
            let PK = g.clone() * SK_fe;
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B
            let proof = zkPoKEncProof::prove(
                g.clone(), 
                hsmcl.clone(), 
                h.clone(),
                Kx.clone(),
                r1.clone(),
                r2.clone(),
                x1.clone(),
                x2.clone(),
                y1.clone(),
                y2.clone(),
                PK.clone(),
                SK.clone(),
                B.clone(),
                minus_B.clone(),
                seed.clone(),
            );
            b.iter(||proof.verify());
        });
    }

    pub fn hsmcl_nizk_verify_128(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_verify_128", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();
            let hsmcl = HSMCL::keygen_with_setup(&q, &1827, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let SK_fe: FE = FE::new_random();
            let SK = SK_fe.to_big_int();
            let g = GE::generator(); // ECC generator
            let PK = g.clone() * SK_fe;
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B
            let proof = zkPoKEncProof::prove(
                g.clone(), 
                hsmcl.clone(), 
                h.clone(),
                Kx.clone(),
                r1.clone(),
                r2.clone(),
                x1.clone(),
                x2.clone(),
                y1.clone(),
                y2.clone(),
                PK.clone(),
                SK.clone(),
                B.clone(),
                minus_B.clone(),
                seed.clone(),
            );
            b.iter(||proof.verify());
        });
    } 
    pub fn hsmcl_nizk_prove_112_v0(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_prove_112_v0", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();

            let hsmcl = HSMCL::keygen_with_setup(&q, &1348, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let g = GE::generator(); // ECC generator
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B

            b.iter(||
                zkPoKEncProof_v0::prove(
                    g.clone(), 
                    hsmcl.clone(), 
                    h.clone(),
                    Kx.clone(),
                    r1.clone(),
                    r2.clone(),
                    x1.clone(),
                    x2.clone(),
                    y1.clone(),
                    y2.clone(),
                    B.clone(),
                    minus_B.clone(),
                    seed.clone(),
                )
            )
        });
    }

    pub fn hsmcl_nizk_prove_128_v0(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_prove_128_v0", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();
            let hsmcl = HSMCL::keygen_with_setup(&q, &1827, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let g = GE::generator(); // ECC generator
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B

            b.iter(||
                zkPoKEncProof_v0::prove(
                    g.clone(), 
                    hsmcl.clone(), 
                    h.clone(),
                    Kx.clone(),
                    r1.clone(),
                    r2.clone(),
                    x1.clone(),
                    x2.clone(),
                    y1.clone(),
                    y2.clone(),
                    B.clone(),
                    minus_B.clone(),
                    seed.clone(),
                )
            )
        });
    }

    pub fn hsmcl_nizk_verify_112_v0(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_verify_112_v0", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();

            let hsmcl = HSMCL::keygen_with_setup(&q, &1348, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let g = GE::generator(); // ECC generator
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B
            let proof = zkPoKEncProof_v0::prove(
                g.clone(), 
                hsmcl.clone(), 
                h.clone(),
                Kx.clone(),
                r1.clone(),
                r2.clone(),
                x1.clone(),
                x2.clone(),
                y1.clone(),
                y2.clone(),
                B.clone(),
                minus_B.clone(),
                seed.clone(),
            );
            b.iter(||proof.verify());
        });
    }

    pub fn hsmcl_nizk_verify_128_v0(c: &mut Criterion) {
        c.bench_function("hsmcl_nizk_verify_128_v0", move |b| {
            unsafe { pari_init(10000000000, 2) };
            let q = str::parse(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            )
            .unwrap();
            let seed = str::parse(
                "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
            ).unwrap();
            let hsmcl = HSMCL::keygen_with_setup(&q, &1827, &seed);
            let h = HSha256::create_hash(&[&BigInt::from(111)]);
            let Kx = HSha256::create_hash(&[&BigInt::from(222)]);
            let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
            let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
            let x1 = Enc_h.c1.clone();
            let x2 = Enc_h.c2.clone();
            let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
            let y1 = Enc_Kx.c1.clone();
            let y2 = Enc_Kx.c2.clone();
            let g = GE::generator(); // ECC generator
            let exp = (SECURITY_PARAMETER as u32) + 80 + 2; // epsilon_d = 80
            let two_pow_exp = BigInt::ui_pow_ui(2, exp);
            let B = &two_pow_exp * &hsmcl.pk.stilde;
            let minus_one = BigInt::from(-1);
            let minus_B = &minus_one * &B; // = -B
            let proof = zkPoKEncProof_v0::prove(
                g.clone(), 
                hsmcl.clone(), 
                h.clone(),
                Kx.clone(),
                r1.clone(),
                r2.clone(),
                x1.clone(),
                x2.clone(),
                y1.clone(),
                y2.clone(),
                B.clone(),
                minus_B.clone(),
                seed.clone(),
            );
            b.iter(||proof.verify());
        });
    } 
    criterion_group! {
        name = benchmarks;
        config = Criterion::default().sample_size(10);
        targets = 
        self::AsiaCCS_nizk_prove_2048,
        self::AsiaCCS_nizk_prove_3072,
        self::AsiaCCS_nizk_prove_4096,

        self::AsiaCCS_nizk_verify_2048,
        self::AsiaCCS_nizk_verify_3072,
        self::AsiaCCS_nizk_verify_4096,

        self::hsmcl_nizk_prove_112_v0,
        self::hsmcl_nizk_prove_128_v0,

        self::hsmcl_nizk_verify_112_v0,
        self::hsmcl_nizk_verify_128_v0,

        // self::hsmcl_nizk_prove_112,
        // self::hsmcl_nizk_prove_128,

        // self::hsmcl_nizk_verify_112,
        // self::hsmcl_nizk_verify_128,
    }
}

criterion_main!(bench::benchmarks);

