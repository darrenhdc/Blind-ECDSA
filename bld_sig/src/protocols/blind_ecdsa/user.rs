use std::cmp;

use class_group::primitives::cl_dl_lcm::Ciphertext;
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
use serde::{Deserialize, Serialize};
use crate::*;
use paillier::keygen::PrimeSampable;

use crate::Error::{self, InvalidSig};

use protocols::asiaccs_zk::ZK_AsiaCCS_19;
use protocols::mpaillier::Pallier_AsiaCCS_19;
use protocols::hsmcl_zk::CLDLProof_modified;
use protocols::hsmcl_zk::Witness;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct User_EcKeyPair {
    pub public_share: GE,
    pub secret_share: FE, // should be private variable, changed for test
    pub Kx: BigInt,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct User_Enc_and_NIZK_mpaillier_version {
    pub C1: BigInt,
    pub C2: BigInt, // should be private variable, changed for test
    pub p1: ZK_AsiaCCS_19,
    pub p2: ZK_AsiaCCS_19,
}


#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct User_Enc_and_NIZK_hsmcl_version {
    pub Enc_h: Ciphertext,
    pub Enc_Kx: Ciphertext, // should be private variable, changed for test
    pub p1: CLDLProof_modified, // for Enc(h)
    pub p2: CLDLProof_modified, // for Enc(Kx)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct User_Enc_and_NIZK_hsmcl_GGM {
    pub Enc_h: Ciphertext,
    pub Enc_Kx: Ciphertext, // should be private variable, changed for test
    pub proof: zkPoKEncProof,
}

impl User_EcKeyPair {
    pub fn s2_generate_K(K1: &GE) -> Self {
        let secret_share: FE = ECScalar::new_random();
        let public_share = K1.scalar_mul(&secret_share.get_element());
        let Kx = public_share.x_coor().unwrap().mod_floor(&FE::q());
        Self{
            public_share,
            secret_share,
            Kx,
        }
    }
}

impl User_Enc_and_NIZK_mpaillier_version {
    pub fn s2_mpaillier_encrypt_and_nizk(h: &BigInt, Kx: &BigInt, bitsize: &usize) -> Self {
        let key = Pallier_AsiaCCS_19::keygen(bitsize.clone());
        let r1_fe: FE = ECScalar::new_random();
        let r2_fe: FE = ECScalar::new_random();
        let r1 = r1_fe.to_big_int();
        let r2 = r2_fe.to_big_int();
        let C1 = Pallier_AsiaCCS_19::encrypt(h, &r1, &key.N, &key.N_square, &key.g, &key.q);
        let C2 = Pallier_AsiaCCS_19::encrypt(Kx, &r2, &key.N, &key.N_square, &key.g, &key.q);
        let p1 =  ZK_AsiaCCS_19::prove(
            key.N.clone(),
            key.N_square.clone(),
            key.q.clone(),
            key.g.clone(),
            C1.clone(),
            h.clone(), 
            r1.clone(),
        );
        let p2 =  ZK_AsiaCCS_19::prove(
            key.N.clone(),
            key.N_square.clone(),
            key.q.clone(),
            key.g.clone(),
            C2.clone(),
            Kx.clone(), 
            r2.clone(),
        );
        Self {
            C1,
            C2,
            p1,
            p2,
        }
    }
}


impl User_Enc_and_NIZK_hsmcl_version {
    pub fn s2_hsmcl_encrypt_and_ggm_nizk(h: &BigInt, Kx: &BigInt, lam: &usize) -> Self {
        unsafe { pari_init(10000000000, 2) };
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        // digits of pi
        let seed = str::parse(
            "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
        ).unwrap();
    
        let hsmcl = HSMCL::keygen_with_setup(&q, lam, &seed);
        let r1 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
        let r2 = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(80)));
        let Enc_h = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &h, &r1);
        let Enc_Kx = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &Kx, &r2);
        let witness = Witness { x: h.clone(), r: r1.clone(), };
        let witness = Witness { x: Kx.clone(), r: r2.clone(), };
        let h_fe: FE = ECScalar::from(&h);
        let Kx_fe: FE = ECScalar::from(&Kx);
        let gh = GE::generator() * h_fe;
        let gKx = GE::generator() * Kx_fe;
        let c: usize = 10;
        let p1 = CLDLProof_modified::prove(witness.clone(), hsmcl.pk.clone(), Enc_h.clone(), gh, seed.clone(), c.clone());
        let p2 = CLDLProof_modified::prove(witness, hsmcl.pk.clone(), Enc_Kx.clone(), gKx, seed, c.clone());

        Self {
            Enc_h,
            Enc_Kx,
            p1,
            p2,
        }
        
    }

}

impl User_Enc_and_NIZK_hsmcl_GGM {
    pub fn s2_hsmcl_encrypt_and_ggm_nizk(h: &BigInt, Kx: &BigInt, lam: &usize) -> Self {
        unsafe { pari_init(10000000000, 2) };
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        let seed = str::parse(
            "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848"
        ).unwrap();

        let hsmcl = HSMCL::keygen_with_setup(&q, lam, &seed);
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
        let proof = zkPoKEncProof::prove( // contain pk well-formedness
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
        Self {
            Enc_h,
            Enc_Kx,
            proof,
        }
        
    }

}

pub fn s4_sig_by_mpaillier(k2: BigInt, c: BigInt, key: Pallier_AsiaCCS_19) -> BigInt {
    let q = FE::q();
    let dec = Pallier_AsiaCCS_19::decrypt(&c, key);
    let k2_inv = k2.invert(&q).unwrap();
    let prod_ = dec * &k2_inv;
    let prod = prod_.div_floor(&q);
    prod
}