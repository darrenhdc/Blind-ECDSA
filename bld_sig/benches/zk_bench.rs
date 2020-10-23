use class_group::primitives::cl_dl_lcm::HSMCL;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::arithmetic::traits::Samplable;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::{FE, GE};

use test::Bencher;
use criterion::criterion_main;

mod bench {
    use criterion::{criterion_group, Criterion};
    use crate::*;
    use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use curv::BigInt;
    use blind_ecdsa::protocols::mpaillier::Pallier_AsiaCCS_19;
    use blind_ecdsa::protocols::asiaccs_zk::ZK_AsiaCCS_19;
    use blind_ecdsa::protocols::ggm_zk::zkPoKEncProof_v0;
    use blind_ecdsa::protocols::ggm_zk::zkPoKEncProof;

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