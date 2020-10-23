use crate::*;
use serde::{Deserialize, Serialize};
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::arithmetic::traits::Samplable;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::BigInt;


#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZK_AsiaCCS_19{
    pub C: BigInt, //ciphertext C = g^m r^N mod N^2
    pub N: BigInt, 
    pub N_square: BigInt,
    pub g: BigInt, 
    C1_vec: Vec<BigInt>, // commit C1 = g^m1 r1^N mod N^2
    Response_vec: Vec<Response>, // response m2 = m1 + b * m and r2 = r1 + b * r
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