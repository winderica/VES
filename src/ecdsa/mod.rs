use std::error::Error;

use num::{BigUint, bigint::RandBigInt};
use num_modular::ModularUnaryOps;
use rand::Rng;
use secp256k1::{SecretKey, PublicKey, constants::CURVE_ORDER, Scalar, SECP256K1, hashes::{sha256, Hash}};

pub fn sign<R: Rng + ?Sized>(
    rng: &mut R,
    sk: &SecretKey,
    m: &[u8],
) -> Result<(PublicKey, SecretKey), Box<dyn Error>> {
    let q = BigUint::from_bytes_be(&CURVE_ORDER);
    let k = rng.gen_biguint_below(&q);
    let k_inv = k.clone().invm(&q).unwrap();
    let mut k_bytes = k.to_bytes_le();
    k_bytes.resize(32, 0);
    k_bytes.reverse();
    let k = SecretKey::from_slice(&k_bytes)?;
    let k_inv = Scalar::from_le_bytes({
        let mut x = k_inv.to_bytes_le();
        x.resize(32, 0);
        x.try_into().unwrap()
    })?;
    let h = Scalar::from_be_bytes(sha256::Hash::hash(&m).into_inner())?;
    let rr = k.public_key(SECP256K1);
    let r = Scalar::from_be_bytes(rr.x_only_public_key().0.serialize())?;
    let s = sk.mul_tweak(&r)?.add_tweak(&h)?.mul_tweak(&k_inv)?;

    Ok((rr, s))
}
