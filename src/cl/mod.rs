use std::{
    error::Error,
    f64::consts::{LOG10_2, PI},
    str::FromStr,
    sync::{mpsc, Arc},
    thread,
};

use merlin::Transcript;
use num::{
    bigint::{RandBigInt, ToBigInt},
    BigUint, Integer, One, Signed, Zero,
};
use num_modular::{ModularPow, ModularSymbols, ModularUnaryOps};
use num_prime::{nt_funcs::next_prime, RandPrime};
use rand::Rng;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use secp256k1::{
    hashes::{sha256, Hash},
    PublicKey, Scalar, SecretKey, SECP256K1,
};

use crate::class_group::{mpz::Mpz, ClassCtx, ClassElem};

fn tonelli_shanks(a: &BigUint, p: &BigUint) -> Option<BigUint> {
    let mut q = p - BigUint::one();
    let mut r = 0;
    while q.is_even() {
        q >>= 1u8;
        r += 1;
    }

    let mut n = BigUint::one();
    while n.legendre(p) != -1 {
        n += BigUint::one();
    }
    let mut y = n.powm(&q, p);

    let mut x = a.powm(&q >> 1u8, p);
    let mut b = a * &x * &x % p;
    x = a * &x % p;

    loop {
        if b.is_one() {
            return Some(x);
        }
        let mut m = 1;
        let mut c = &b * &b % p;
        loop {
            if m == r {
                return None;
            }
            if c.is_one() {
                break;
            }
            m += 1;
            c = c.sqm(p);
        }
        let t = y.powm(BigUint::one() << (r - m - 1), p);
        y = &t * &t % p;
        r = m;
        x = &t * &x % p;
        b = &y * &b % p;
    }
}

pub fn exp_f(ctx: &mut ClassCtx, p: &BigUint, k: &BigUint) -> ClassElem {
    if k.is_zero() {
        return ctx.id();
    }
    let k_inv = k.invm(p).unwrap();
    let p = p.to_bigint().unwrap();
    let mut k_inv = k_inv.to_bigint().unwrap();
    if k_inv.is_even() {
        k_inv -= &p;
    };

    ctx.bqf(
        Mpz::from_bytes(&(&p * &p).magnitude().to_bytes_be()),
        Mpz::from_str(&(k_inv * &p).to_string()).unwrap(),
    )
}

pub fn log_f(ctx: &mut ClassCtx, p: &BigUint, c: &ClassElem) -> BigUint {
    if c == &ctx.id() {
        BigUint::zero()
    } else {
        let lk = (c.b.to_bigint().div_floor(&p.to_bigint().unwrap()) + p.to_bigint().unwrap())
            .to_biguint()
            .unwrap();
        lk.invm(&p).unwrap()
    }
}

pub struct CL {
    q: BigUint,
    delta_q: ClassCtx,
    g_q_powers: Arc<Vec<Vec<ClassElem>>>,
    s_tilde: BigUint,
}

impl CL {
    pub fn group_gen<R: Rng + ?Sized>(
        mut rng: &mut R,
        lambda: usize,
        q: &BigUint,
    ) -> (ClassCtx, ClassCtx) {
        let mu = q.bits() as usize;
        assert!(lambda >= mu + 2);
        let abs_delta_k = loop {
            let q_tilde: BigUint = rng.gen_prime_exact(lambda - mu, None);
            let abs_delta_k = q * &q_tilde;
            if &abs_delta_k % BigUint::from(4u8) == BigUint::from(3u8) && q.legendre(&q_tilde) == 1
            {
                break abs_delta_k;
            }
        };
        let delta_q = ClassCtx::from_discriminant(
            &Mpz::from_str(&format!("-{}", (&abs_delta_k * q * q).to_string())).unwrap(),
        );
        let delta_k = ClassCtx::from_discriminant(
            &Mpz::from_str(&format!("-{}", abs_delta_k.to_string())).unwrap(),
        );

        (delta_k, delta_q)
    }

    pub fn param_gen(delta_k: &mut ClassCtx, mut delta_q: ClassCtx, q: &BigUint) -> Self {
        let abs_delta_k = delta_k.D.to_bigint().abs().to_biguint().unwrap();
        let s_tilde = {
            let sqrt_delta_k = {
                let t = abs_delta_k.sqrt();
                if abs_delta_k.eq(&(&t * &t)) {
                    t
                } else {
                    t + BigUint::one()
                }
            };
            BigUint::from((abs_delta_k.bits() as f64 * LOG10_2 / PI).ceil() as u64) * sqrt_delta_k
        };
        let mut r = BigUint::from(3u8);
        loop {
            if abs_delta_k.legendre(&r)
                == if &r % BigUint::from(4u8) == BigUint::from(3u8) {
                    -1
                } else {
                    1
                }
            {
                break;
            }
            r = next_prime(&r, None).unwrap();
        }
        let b_r = {
            let t = tonelli_shanks(&(&r - abs_delta_k % &r), &r).unwrap();
            if t.is_even() {
                &r - &t
            } else {
                t
            }
        };
        let mut t = delta_k.bqf(
            Mpz::from_str(&r.to_string()).unwrap(),
            Mpz::from_str(&b_r.to_string()).unwrap(),
        );

        let g_q = {
            delta_k.square(&mut t);
            let b = &t.b.to_bigint() * &q.to_bigint().unwrap() % (&t.a.to_bigint() << 1u8);
            let tmp = delta_q.bqf(t.a, Mpz::from_str(&b.to_string()).unwrap());
            delta_q.pow(&tmp, &q)
        };

        let g_q_powers = {
            let k = 10;
            let mut r = vec![];
            {
                let mut aa = g_q.clone();
                delta_q.square(&mut aa);
                let mut base_powers = vec![delta_q.id(), g_q.clone(), aa];
                for _ in 3..(1 << k) {
                    base_powers.push(delta_q.op(base_powers.last().unwrap(), &g_q));
                }
                r.push(base_powers);
            }
            for _ in 0..1500 / k {
                r.push(
                    r.last()
                        .unwrap()
                        .par_iter()
                        .map(|i| {
                            let mut i = i.clone();
                            let mut t = delta_q.clone();
                            for _ in 0..k {
                                t.square(&mut i);
                            }
                            i
                        })
                        .collect(),
                );
            }
            r
        };

        Self {
            q: q.clone(),
            g_q_powers: Arc::new(g_q_powers),
            s_tilde,
            delta_q,
        }
    }

    pub fn key_gen<R: Rng + ?Sized>(&mut self, rng: &mut R) -> (BigUint, Vec<Vec<ClassElem>>) {
        let sk = rng.gen_biguint_below(&(&self.s_tilde << 40u8));
        let pk = self.delta_q.pow_precomputed(&self.g_q_powers, &sk);

        let pk_powers = {
            let k = 10;
            let mut r = vec![];
            {
                let mut aa = pk.clone();
                self.delta_q.square(&mut aa);
                let mut base_powers = vec![self.delta_q.id(), pk.clone(), aa];
                for _ in 3..(1 << k) {
                    base_powers.push(self.delta_q.op(base_powers.last().unwrap(), &pk));
                }
                r.push(base_powers);
            }
            for _ in 0..1500 / k {
                r.push(
                    r.last()
                        .unwrap()
                        .par_iter()
                        .map(|i| {
                            let mut i = i.clone();
                            let mut t = self.delta_q.clone();
                            for _ in 0..k {
                                t.square(&mut i);
                            }
                            i
                        })
                        .collect(),
                );
            }
            r
        };

        (sk, pk_powers)
    }

    pub fn encrypt<R: Rng + ?Sized>(
        &mut self,
        rng: &mut R,
        pk: Arc<Vec<Vec<ClassElem>>>,
        m: &BigUint,
    ) -> (ClassElem, ClassElem) {
        let r = rng.gen_biguint_below(&(&self.s_tilde << 40u8));
        self.encrypt_with_r(pk, m, &r)
    }

    pub fn encrypt_with_r(
        &mut self,
        pk: Arc<Vec<Vec<ClassElem>>>,
        m: &BigUint,
        r: &BigUint,
    ) -> (ClassElem, ClassElem) {
        assert!(m.le(&self.q));
        let (s1, r1) = mpsc::channel();
        {
            let tmp1 = exp_f(&mut self.delta_q, &self.q, &m);
            let mut delta_q = self.delta_q.clone();
            let r = r.clone();
            thread::spawn(move || {
                let tmp2 = delta_q.pow_precomputed(&pk, &r);
                s1.send(delta_q.op(&tmp1, &tmp2)).unwrap();
            });
        }
        (
            self.delta_q.pow_precomputed(&self.g_q_powers, r),
            r1.recv().unwrap(),
        )
    }

    pub fn decrypt(&mut self, sk: &BigUint, c: &(ClassElem, ClassElem)) -> BigUint {
        let tmp = self.delta_q.pow(&c.0, sk);
        let tmp = self.delta_q.op(&ClassCtx::inv(&tmp), &c.1);
        log_f(&mut self.delta_q, &self.q, &tmp)
    }

    pub fn prove<R: Rng + ?Sized>(
        &mut self,
        rng: &mut R,
        pk_enc: Arc<Vec<Vec<ClassElem>>>,
        beta: &BigUint,
        s: &SecretKey,
        rr: &PublicKey,
    ) -> Result<(BigUint, SecretKey, BigUint), Box<dyn Error>> {
        let (s1, r1) = mpsc::channel();
        let mut tx = Transcript::new(b"CL");
        let rho_s = SecretKey::new(rng);
        let rho_s_bn = BigUint::from_bytes_be(&rho_s.secret_bytes());
        let rho_beta = rng.gen_biguint_below(&(&self.s_tilde << 160u8));
        {
            let tmp1 = exp_f(&mut self.delta_q, &self.q, &rho_s_bn);
            let mut delta_q = self.delta_q.clone();
            let s1 = s1.clone();
            let rho_beta = rho_beta.clone();
            thread::spawn(move || {
                let tmp2 = delta_q.pow_precomputed(&pk_enc, &rho_beta);
                s1.send(delta_q.op(&tmp1, &tmp2)).unwrap();
            });
        }
        let t1 = rr.mul_tweak(SECP256K1, &rho_s.into())?;
        let t2 = self.delta_q.pow_precomputed(&self.g_q_powers, &rho_beta);
        let t3 = r1.recv().unwrap();
        tx.append_message(b"t1", &t1.serialize());
        tx.append_message(b"t2", &t2.to_bytes());
        tx.append_message(b"t3", &t3.to_bytes());
        let x = {
            let mut x = [0; 10];
            tx.challenge_bytes(b"x", &mut x);
            BigUint::from_bytes_le(&x)
        };
        let z1 = rho_s.add_tweak(
            &s.mul_tweak(&Scalar::from_le_bytes({
                let mut x = x.to_bytes_le();
                x.resize(32, 0);
                x.try_into().unwrap()
            })?)?
            .into(),
        )?;
        let z2 = rho_beta + &x * beta;

        Ok((x, z1, z2))
    }

    pub fn verify(
        &mut self,
        pk_enc: Arc<Vec<Vec<ClassElem>>>,
        pk_sig: &PublicKey,
        m: &[u8],
        c: &(ClassElem, ClassElem),
        rr: &PublicKey,
        z: &(BigUint, SecretKey, BigUint),
    ) -> Result<bool, Box<dyn Error>> {
        let (s1, r1) = mpsc::channel();
        let (s2, r2) = mpsc::channel();
        let mut tx = Transcript::new(b"CL");
        assert!(z.2 <= &self.s_tilde << 160u8);

        {
            let mut delta_q = self.delta_q.clone();
            let z0 = z.0.clone();
            let c0 = c.0.clone();
            let s1 = s1.clone();
            thread::spawn(move || {
                s1.send(ClassCtx::inv(&delta_q.pow(&c0, &z0))).unwrap();
            });
        }
        {
            let mut delta_q = self.delta_q.clone();
            let g_q_powers = self.g_q_powers.clone();
            let z2 = z.2.clone();
            thread::spawn(move || {
                s1.send(delta_q.pow_precomputed(&g_q_powers, &z2)).unwrap();
            });
        }
        {
            let mut delta_q = self.delta_q.clone();
            let z0 = z.0.clone();
            let c1 = c.1.clone();
            let s2 = s2.clone();
            thread::spawn(move || {
                s2.send(ClassCtx::inv(&delta_q.pow(&c1, &z0))).unwrap();
            });
        }
        {
            let tmp1 = exp_f(
                &mut self.delta_q,
                &self.q,
                &BigUint::from_bytes_be(&z.1.secret_bytes()),
            );
            let mut delta_q = self.delta_q.clone();
            let z2 = z.2.clone();
            thread::spawn(move || {
                let tmp2 = delta_q.pow_precomputed(&pk_enc, &z2);
                s2.send(delta_q.op(&tmp1, &tmp2)).unwrap();
            });
        }
        let t1 = pk_sig
            .mul_tweak(
                SECP256K1,
                &Scalar::from_be_bytes(rr.x_only_public_key().0.serialize())?,
            )?
            .add_exp_tweak(
                SECP256K1,
                &Scalar::from_be_bytes(sha256::Hash::hash(&m).into_inner())?,
            )?
            .mul_tweak(
                SECP256K1,
                &SecretKey::from_slice(&{
                    let mut x = z.0.to_bytes_le();
                    x.resize(32, 0);
                    x.reverse();
                    x
                })?
                .negate()
                .into(),
            )?
            .combine(&rr.mul_tweak(SECP256K1, &z.1.into())?)?;
        let t2 = self.delta_q.op(&r1.recv().unwrap(), &r1.recv().unwrap());
        let t3 = self.delta_q.op(&r2.recv().unwrap(), &r2.recv().unwrap());
        tx.append_message(b"t1", &t1.serialize());
        tx.append_message(b"t2", &t2.to_bytes());
        tx.append_message(b"t3", &t3.to_bytes());
        let x = {
            let mut x = [0; 10];
            tx.challenge_bytes(b"x", &mut x);
            BigUint::from_bytes_le(&x)
        };
        Ok(z.0 == x)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use rand::thread_rng;
    use secp256k1::constants::CURVE_ORDER;

    use crate::ecdsa::sign;

    use super::*;

    #[test]
    fn test() {
        let rng = &mut thread_rng();
        let q = rng.gen_prime_exact(256, None);
        let m = rng.gen_biguint_below(&q);
        let (mut g_k, g_q) = CL::group_gen(rng, 1026, &q);
        let mut p = CL::param_gen(&mut g_k, g_q, &q);
        let (sk, pk) = p.key_gen(rng);
        let c = p.encrypt(rng, Arc::new(pk), &m);
        assert_eq!(p.decrypt(&sk, &c), m);
    }

    #[test]
    fn test_zk() {
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = SecretKey::new(rng);
        let pk_sig = sk_sig.public_key(SECP256K1);
        let now = Instant::now();
        let (rr, s) = sign(rng, &sk_sig, &m).unwrap();
        println!("{:?}", now.elapsed());

        let q = BigUint::from_bytes_be(&CURVE_ORDER);
        let (mut g_k, g_q) = CL::group_gen(rng, 1827, &q);
        let mut p = CL::param_gen(&mut g_k, g_q, &q);
        let (_, pk_enc) = p.key_gen(rng);
        println!("{}", (&p.s_tilde << 40u8).bits());
        let beta = rng.gen_biguint_below(&(&p.s_tilde << 40u8));

        let pk_enc = Arc::new(pk_enc);

        let now = Instant::now();
        let c = p.encrypt_with_r(
            pk_enc.clone(),
            &BigUint::from_bytes_be(&s.secret_bytes()),
            &beta,
        );
        println!("{:?}", now.elapsed());

        let now = Instant::now();
        let pi = p.prove(rng, pk_enc.clone(), &beta, &s, &rr).unwrap();
        println!("{:?}", now.elapsed());

        println!("{}", pi.0.bits());
        println!(
            "{}",
            (pi.0.bits()
                + 256
                + pi.2.bits()
                + (c.0.a.bit_length()
                    + c.0.b.bit_length()
                    + c.1.a.bit_length()
                    + c.1.b.bit_length()) as u64
                + 256)
                / 8
        );

        let now = Instant::now();
        assert!(p.verify(pk_enc.clone(), &pk_sig, &m, &c, &rr, &pi).unwrap());
        println!("{:?}", now.elapsed());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = SecretKey::new(rng);

        let q = BigUint::from_bytes_be(&CURVE_ORDER);
        let (mut g_k, g_q) = CL::group_gen(rng, 1827, &q);
        let mut p = CL::param_gen(&mut g_k, g_q, &q);
        let (_, pk_enc) = p.key_gen(rng);
        let beta = rng.gen_biguint_below(&(&p.s_tilde << 40u8));

        let pk_enc = Arc::new(pk_enc);

        b.iter(|| {
            let (rr, s) = sign(rng, &sk_sig, &m).unwrap();
            p.encrypt_with_r(
                pk_enc.clone(),
                &BigUint::from_bytes_be(&s.secret_bytes()),
                &beta,
            );
            p.prove(rng, pk_enc.clone(), &beta, &s, &rr).unwrap()
        });
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();
        let m = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let sk_sig = SecretKey::new(rng);
        let pk_sig = sk_sig.public_key(SECP256K1);
        let (rr, s) = sign(rng, &sk_sig, &m).unwrap();

        let q = BigUint::from_bytes_be(&CURVE_ORDER);
        let (mut g_k, g_q) = CL::group_gen(rng, 1827, &q);
        let mut p = CL::param_gen(&mut g_k, g_q, &q);
        let (_, pk_enc) = p.key_gen(rng);
        let beta = rng.gen_biguint_below(&(&p.s_tilde << 40u8));

        let pk_enc = Arc::new(pk_enc);

        let c = p.encrypt_with_r(
            pk_enc.clone(),
            &BigUint::from_bytes_be(&s.secret_bytes()),
            &beta,
        );

        let pi = p.prove(rng, pk_enc.clone(), &beta, &s, &rr).unwrap();

        b.iter(|| p.verify(pk_enc.clone(), &pk_sig, &m, &c, &rr, &pi).unwrap());
    }
}
