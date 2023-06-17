use std::{
    error::Error,
    sync::{Arc, Mutex},
    thread::available_parallelism,
};

use ark_secp256k1::{Fr, Projective};
use ark_serialize::CanonicalSerialize;
use futures::future::join_all;
use merlin::Transcript;
use num::{bigint::RandBigInt, BigUint, One, Zero};
use num_modular::{ModularCoreOps, ModularPow, ModularSymbols, ModularUnaryOps};
use num_prime::{nt_funcs::is_prime, RandPrime};
use rand::{thread_rng, Rng};

use crate::signatures::Signature;

pub struct PK {
    pub n: BigUint,
    pub y: BigUint,
    pub g: BigUint,
}

pub struct SK {
    pub p: BigUint,
    pub mu: BigUint,
    pub y_to_neg_mu: BigUint,
    pub pk: PK,
}

pub struct JL<const B: usize>;

impl<const B: usize> JL<B> {
    pub fn key_gen<R: Rng + ?Sized>(mut rng: &mut R, lambda: usize) -> SK {
        let (mu, p) = loop {
            let mu: BigUint = rng.gen_prime_exact(lambda / 2 - B, None);
            let p = (&mu << B) + BigUint::one();
            if is_prime(&p, None).probably() {
                break (mu, p);
            }
        };
        let q = rng.gen_safe_prime_exact(lambda / 2);
        let n = &p * &q;
        let y = loop {
            let y: BigUint = rng.gen_biguint_below(&n);
            if y.jacobi(&n) == 1 && y.legendre(&p) != 1 && y.legendre(&q) != 1 {
                break y;
            }
        };
        let y_to_neg_mu = y.clone().powm(&mu, &p).invm(&p).unwrap();
        let alpha = rng.gen_biguint_below(&(&n * &n));
        let g = y.clone().powm(&(alpha << B), &p);
        SK {
            p,
            mu,
            y_to_neg_mu,
            pk: PK { n, y, g },
        }
    }

    pub async fn key_gen_par<R: Rng + ?Sized>(rng: &mut R, lambda: usize) -> SK {
        let threads = available_parallelism().unwrap().get();
        let l = Arc::new(Mutex::new(None));
        join_all((0..threads).map(|_| {
            let l = l.clone();
            tokio::spawn(async move {
                let rng = &mut thread_rng();
                while l.lock().unwrap().is_none() {
                    let mu: BigUint = rng.gen_prime_exact(lambda / 2 - B, None);
                    let p = (&mu << B) + BigUint::one();
                    if is_prime(&p, None).probably() {
                        *l.lock().unwrap() = Some((mu, p));
                        break;
                    }
                }
            })
        }))
        .await;
        let (mu, p) = l.lock().unwrap().clone().unwrap();
        let l = Arc::new(Mutex::new(None));
        join_all((0..threads).map(|_| {
            let l = l.clone();
            tokio::spawn(async move {
                let rng = &mut thread_rng();
                while l.lock().unwrap().is_none() {
                    let p = rng.gen_prime_exact(lambda / 2, None);
                    if is_prime(&(&p >> 1u8), None).probably() {
                        *l.lock().unwrap() = Some(p);
                        return;
                    }
                    let p2 = (p << 1u8) + 1u8;
                    if is_prime(&p2, None).probably() {
                        *l.lock().unwrap() = Some(p2);
                        return;
                    }
                }
            })
        }))
        .await;
        let q = l.lock().unwrap().clone().unwrap();
        let n = &p * &q;
        let y = loop {
            let y: BigUint = rng.gen_biguint_below(&n);
            if y.jacobi(&n) == 1 && y.legendre(&p) != 1 && y.legendre(&q) != 1 {
                break y;
            }
        };
        let y_to_neg_mu = y.clone().powm(&mu, &p).invm(&p).unwrap();
        let alpha = rng.gen_biguint_below(&(&n * &n));
        let g = y.clone().powm(&(alpha << B), &p);
        SK {
            p,
            mu,
            y_to_neg_mu,
            pk: PK { n, y, g },
        }
    }

    pub fn encrypt<R: Rng + ?Sized>(rng: &mut R, pk: &PK, m: &BigUint) -> BigUint {
        Self::encrypt_with_r(pk, m, &rng.gen_biguint_below(&pk.n))
    }

    pub fn encrypt_with_r(pk: &PK, m: &BigUint, r: &BigUint) -> BigUint {
        assert!(m.bits() as usize <= B);
        (&pk.y).powm(m, &pk.n).mulm((&pk.g).powm(r, &pk.n), &pk.n)
    }

    pub fn decrypt(sk: &SK, c: &BigUint) -> BigUint {
        let mut d = c.powm(&sk.mu, &sk.p);
        let mut t = sk.y_to_neg_mu.clone();
        let mut m = BigUint::zero();

        for i in 0..B {
            if (&d).powm(&(BigUint::one() << (B - i - 1)), &sk.p) != BigUint::one() {
                m.set_bit(i as u64, true);
                d = d.mulm(&t, &sk.p);
            }
            t = t.sqm(&sk.p);
        }
        m
    }

    pub fn prove<R: Rng + ?Sized, const K: usize>(
        rng: &mut R,
        pk_enc: &PK,
        beta: &BigUint,
        sig2: &Fr,
        b: &Projective,
    ) -> Result<(BigUint, BigUint, BigUint), Box<dyn Error>> {
        let mut tx = Transcript::new(b"JL");
        let sig2: BigUint = sig2.clone().into();
        let rho_s = rng.gen_biguint_below(&(BigUint::one() << (40 + B + K)));
        let rho_beta =
            rng.gen_biguint_below(&(BigUint::one() << (pk_enc.n.bits() as usize + 40 + K)));
        let t1 = *b * Fr::from(rho_s.clone());
        let t2 = (&pk_enc.y)
            .powm(&rho_s, &pk_enc.n)
            .mulm(&(&pk_enc.g).powm(&rho_beta, &pk_enc.n), &pk_enc.n);
        tx.append_message(b"t1", &{
            let mut r = vec![];
            t1.serialize_uncompressed(&mut r)?;
            r
        });
        tx.append_message(b"t2", &t2.to_bytes_le());
        let x = {
            let mut x = vec![0; K / 8];
            tx.challenge_bytes(b"x", &mut x);
            BigUint::from_bytes_le(&x)
        };
        let z1 = rho_s + sig2 * &x;
        let z2 = rho_beta + beta * &x;
        Ok((x, z1, z2))
    }

    pub fn verify<S: Signature, const K: usize>(
        pk_enc: &PK,
        pk_sig: &Projective,
        m: &[u8],
        c: &BigUint,
        sig1: &Projective,
        z: &(BigUint, BigUint, BigUint),
    ) -> Result<bool, Box<dyn Error>> {
        assert!(z.1.bits() as usize <= 40 + B + K);
        let mut tx = Transcript::new(b"JL");
        let a = S::compute_a(pk_sig, m, sig1)?;
        let b = S::compute_b(pk_sig, m, sig1)?;
        let t1 = b * Fr::from(z.1.clone()) - a * Fr::from(z.0.clone());
        let t2 = (&pk_enc.y)
            .powm(&z.1, &pk_enc.n)
            .mulm(&(&pk_enc.g).powm(&z.2, &pk_enc.n), &pk_enc.n)
            .mulm(c.powm(&z.0, &pk_enc.n).invm(&pk_enc.n).unwrap(), &pk_enc.n);
        tx.append_message(b"t1", &{
            let mut r = vec![];
            t1.serialize_uncompressed(&mut r)?;
            r
        });
        tx.append_message(b"t2", &t2.to_bytes_le());
        let x = {
            let mut x = vec![0; K / 8];
            tx.challenge_bytes(b"x", &mut x);
            BigUint::from_bytes_le(&x)
        };
        Ok(z.0 == x)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::signatures::{ecdsa::ECDSA, schnorr::Schnorr};
    use ark_ec::Group;
    use ark_std::UniformRand;
    use rand::thread_rng;

    use super::*;

    #[test]
    fn test() {
        let rng = &mut thread_rng();
        const B: usize = 256;
        let sk = JL::<B>::key_gen(rng, 2048);
        let m = rng.gen_biguint_below(&(BigUint::one() << B));
        let c = JL::<B>::encrypt(rng, &sk.pk, &m);
        let now = Instant::now();
        assert_eq!(JL::<B>::decrypt(&sk, &c), m);
        println!("{:?}", now.elapsed());
    }

    async fn test_zk<S: Signature>() {
        const B: usize = 256;
        const K: usize = 80;
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = Fr::rand(rng);
        let pk_sig = Projective::generator() * sk_sig;
        let (r, s) = S::sign(rng, &sk_sig, &m).unwrap();

        let sk_enc = JL::<B>::key_gen_par(rng, 2048).await;
        let beta = rng.gen_biguint_below(&sk_enc.pk.n);
        let c = JL::<B>::encrypt_with_r(&sk_enc.pk, &s.into(), &beta);

        let b = S::compute_b(&pk_sig, &m, &r).unwrap();

        let now = Instant::now();
        let pi = JL::<B>::prove::<_, K>(rng, &sk_enc.pk, &beta, &s, &b).unwrap();
        println!("{:?}", now.elapsed());

        println!("{}", pi.0.bits() / 8);
        println!("{}", pi.1.bits() / 8);
        println!("{}", pi.2.bits() / 8);
        println!("{}", c.bits() / 8);
        println!(
            "{}",
            (pi.0.bits() + pi.1.bits() + pi.2.bits() + c.bits() + 256) / 8
        );

        let now = Instant::now();
        assert!(JL::<B>::verify::<S, K>(&sk_enc.pk, &pk_sig, &m, &c, &r, &pi).unwrap());
        println!("{:?}", now.elapsed());
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn test_zk_ecdsa() {
        test_zk::<ECDSA>().await
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn test_zk_schnorr() {
        test_zk::<Schnorr>().await
    }

    fn bench_prove<S: Signature>(bencher: &mut test::Bencher) {
        const B: usize = 256;
        const K: usize = 80;
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = Fr::rand(rng);
        let pk_sig = Projective::generator() * sk_sig;

        let sk_enc = JL::<B>::key_gen(rng, 2048);
        let beta = rng.gen_biguint_below(&sk_enc.pk.n);

        bencher.iter(|| {
            let (r, s) = S::sign(rng, &sk_sig, &m).unwrap();
            let b = S::compute_b(&pk_sig, &m, &r).unwrap();
            JL::<B>::encrypt_with_r(&sk_enc.pk, &s.into(), &beta);
            JL::<B>::prove::<_, K>(rng, &sk_enc.pk, &beta, &s, &b).unwrap()
        });
    }

    #[bench]
    fn bench_prove_ecdsa(b: &mut test::Bencher) {
        bench_prove::<ECDSA>(b)
    }

    #[bench]
    fn bench_prove_schnorr(b: &mut test::Bencher) {
        bench_prove::<Schnorr>(b)
    }

    fn bench_verify<S: Signature>(bencher: &mut test::Bencher) {
        const B: usize = 256;
        const K: usize = 80;
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = Fr::rand(rng);
        let pk_sig = Projective::generator() * sk_sig;
        let (r, s) = ECDSA::sign(rng, &sk_sig, &m).unwrap();
        let b = S::compute_b(&pk_sig, &m, &r).unwrap();

        let sk_enc = JL::<B>::key_gen(rng, 2048);
        let beta = rng.gen_biguint_below(&sk_enc.pk.n);
        let c = JL::<B>::encrypt_with_r(&sk_enc.pk, &s.into(), &beta);

        let pi = JL::<B>::prove::<_, K>(rng, &sk_enc.pk, &beta, &s, &b).unwrap();

        bencher.iter(|| JL::<B>::verify::<ECDSA, K>(&sk_enc.pk, &pk_sig, &m, &c, &r, &pi).unwrap());
    }

    #[bench]
    fn bench_verify_ecdsa(b: &mut test::Bencher) {
        bench_verify::<ECDSA>(b)
    }

    #[bench]
    fn bench_verify_schnorr(b: &mut test::Bencher) {
        bench_verify::<Schnorr>(b)
    }
}
