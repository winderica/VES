use std::error::Error;

use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::fields::Field;
use ark_secp256k1::{Fr, Projective};
use ark_std::UniformRand;
use num::BigUint;
use rand::Rng;
use sha2::{Digest, Sha256};

use super::Signature;

pub struct ECDSA;

impl Signature for ECDSA {
    fn sign<R: Rng + ?Sized>(
        rng: &mut R,
        sk: &Fr,
        m: &[u8],
    ) -> Result<(Projective, Fr), Box<dyn Error>> {
        let k = Fr::rand(rng);
        let k_inv = k.inverse().unwrap();
        let h = Fr::from(BigUint::from_bytes_le(&Sha256::digest(&m)));
        let rr = Projective::generator() * k;
        let r = Fr::from(rr.into_affine().x().unwrap().0);
        let s = (sk * &r + h) * &k_inv;

        Ok((rr, s))
    }

    fn compute_a(
        pk: &Projective,
        m: &[u8],
        sig1: &Projective,
    ) -> Result<Projective, Box<dyn Error>> {
        let h = Fr::from(BigUint::from_bytes_le(&Sha256::digest(&m)));
        Ok(Projective::generator() * h + *pk * Fr::from(sig1.into_affine().x().unwrap().0))
    }

    fn compute_b(
        _pk: &Projective,
        _m: &[u8],
        sig1: &Projective,
    ) -> Result<Projective, Box<dyn Error>> {
        Ok(sig1.clone())
    }
}
