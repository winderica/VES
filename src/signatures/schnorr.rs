use std::error::Error;

use ark_ec::Group;
use ark_secp256k1::{Fr, Projective};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use num::BigUint;
use sha2::{Digest, Sha256};

use super::Signature;

pub struct Schnorr;

impl Signature for Schnorr {
    fn sign<R: rand::Rng + ?Sized>(
        rng: &mut R,
        sk: &Fr,
        m: &[u8],
    ) -> Result<(Projective, Fr), Box<dyn Error>> {
        let k = Fr::rand(rng);
        let r = Projective::generator() * k;
        let h = Fr::from(BigUint::from_bytes_le(&{
            let mut hasher = Sha256::new();
            r.serialize_compressed(&mut hasher)?;
            hasher.update(m);
            hasher.finalize()
        }));

        let s = k - sk * &h;

        Ok((r, s))
    }

    fn compute_a(
        pk: &Projective,
        m: &[u8],
        sig1: &Projective,
    ) -> Result<Projective, Box<dyn Error>> {
        let h = Fr::from(BigUint::from_bytes_le(&{
            let mut hasher = Sha256::new();
            sig1.serialize_compressed(&mut hasher)?;
            hasher.update(m);
            hasher.finalize()
        }));
        Ok(sig1 - *pk * h)
    }

    fn compute_b(
        _pk: &Projective,
        _m: &[u8],
        _sig1: &Projective,
    ) -> Result<Projective, Box<dyn Error>> {
        Ok(Projective::generator())
    }
}
