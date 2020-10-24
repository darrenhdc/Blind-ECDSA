use class_group::primitives::cl_dl_lcm::HSMCL;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use curv::{FE, GE};
use crate::*;
use super::signer::*;
use super::user::*;

pub fn test_sign_mpaillier(bitsize: &usize, message: &BigInt) -> (BigInt, BigInt) {
    let ec_key1: Signer_EcKeyPair = Signer_EcKeyPair::s1_generate_K1(); // K1 and k1
    let K1 = ec_key1.public_share;
    let k1 = ec_key1.secret_share.to_big_int();
    let ec_key2: User_EcKeyPair = User_EcKeyPair::s2_generate_K(&K1); // K and k2
    let K = ec_key2.public_share;
    let k2 = ec_key2.secret_share.to_big_int();
    let Kx = ec_key2.Kx;
    let h = HSha256::create_hash(&[&message]);
    let s2_user: User_Enc_and_NIZK_mpaillier_version = 
    User_Enc_and_NIZK_mpaillier_version::s2_mpaillier_encrypt_and_nizk(&h, &Kx, &bitsize);
    assert!(s2_user.p1.verify(), true);
    assert!(s2_user.p2.verify(), true);
    let sk_fe: FE = ECScalar::new_random();
    let sk = sk_fe.to_big_int();
    let s3_signer: BigInt = s3_partial_sig_mpaillier(&s2_user.C1, &s2_user.C2, &k1, &sk, &bitsize);
    let k2_inv = k2.invert(&FE::q()).unwrap();
    let s = s4_sig_by_mpaillier(&k2_inv, &s3_signer, &s2_user.key);
    (Kx, s)
}

pub fn test_sign_hsmcl(lam: &usize, message: &BigInt) -> (BigInt, BigInt) {
    let ec_key1: Signer_EcKeyPair = Signer_EcKeyPair::s1_generate_K1(); // K1 and k1
    let K1 = ec_key1.public_share;
    let k1 = ec_key1.secret_share.to_big_int();
    let ec_key2: User_EcKeyPair = User_EcKeyPair::s2_generate_K(&K1); // K and k2
    let K = ec_key2.public_share;
    let k2 = ec_key2.secret_share.to_big_int();
    let Kx = ec_key2.Kx;
    let h = HSha256::create_hash(&[&message]);
    let s2_user: User_Enc_and_NIZK_hsmcl_version = 
    User_Enc_and_NIZK_hsmcl_version::s2_hsmcl_encrypt_and_nizk(&h, &Kx, &lam);
    assert!(s2_user.p1.verify(C).is_ok());
    assert!(s2_user.p2.verify(C).is_ok());
    let sk_fe: FE = ECScalar::new_random();
    let sk = sk_fe.to_big_int();
    let s3_signer = s3_partial_sig_hsmcl(&s2_user.Enc_h, &s2_user.Enc_Kx, &k1, &sk, &lam);
    let k2_inv = k2.invert(&FE::q()).unwrap();
    let hsmcl = HSMCL::keygen(&FE::q(), &lam);
    let s = s4_sig_by_hsmcl(&s3_signer, &k2_inv, &s2_user.hsmcl);
    (Kx, s)
}

pub fn test_sign_hsmcl_ggm(lam: &usize, message: &BigInt) -> (BigInt, BigInt) {
    let ec_key1: Signer_EcKeyPair = Signer_EcKeyPair::s1_generate_K1(); // K1 and k1
    let K1 = ec_key1.public_share;
    let k1 = ec_key1.secret_share.to_big_int();
    let ec_key2: User_EcKeyPair = User_EcKeyPair::s2_generate_K(&K1); // K and k2
    let K = ec_key2.public_share;
    let k2 = ec_key2.secret_share.to_big_int();
    let Kx = ec_key2.Kx;
    let h = HSha256::create_hash(&[&message]);
    let s2_user: User_Enc_and_NIZK_hsmcl_GGM = 
    User_Enc_and_NIZK_hsmcl_GGM::s2_hsmcl_encrypt_and_ggm_nizk(&h, &Kx, &lam);
    assert!(s2_user.proof.verify().is_ok());
    let sk_fe: FE = ECScalar::new_random();
    let sk = sk_fe.to_big_int();
    let s3_signer = s3_partial_sig_hsmcl(&s2_user.Enc_h, &s2_user.Enc_Kx, &k1, &sk, &lam);
    let k2_inv = k2.invert(&FE::q()).unwrap();
    let hsmcl = HSMCL::keygen(&FE::q(), &lam);
    let s = s4_sig_by_hsmcl(&s3_signer, &k2_inv, &s2_user.hsmcl);
    (Kx, s)
}