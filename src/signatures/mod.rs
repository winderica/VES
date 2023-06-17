use std::error::Error;

use rand::Rng;
use ark_secp256k1::{Fr, Projective};

pub mod ecdsa;
pub mod schnorr;

pub trait Signature {
    fn sign<R: Rng + ?Sized>(
        rng: &mut R,
        sk: &Fr,
        m: &[u8],
    ) -> Result<(Projective, Fr), Box<dyn Error>>;

    fn compute_a(pk: &Projective, m: &[u8], sig1: &Projective)
        -> Result<Projective, Box<dyn Error>>;

    fn compute_b(pk: &Projective, m: &[u8], sig1: &Projective)
        -> Result<Projective, Box<dyn Error>>;
}
