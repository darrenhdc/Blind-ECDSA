use crate::*;
use serde::{Deserialize, Serialize};
use class_group::primitives::cl_dl_lcm::HSMCL;
use class_group::primitives::cl_dl_lcm::PK;
use class_group::primitives::cl_dl_lcm::next_probable_small_prime;
use class_group::BinaryQF;
use curv::arithmetic::traits::Modulo;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::arithmetic::traits::Samplable;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use curv::{FE, GE};

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

// add PK well-formedness
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