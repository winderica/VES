//! Mpz wrappers.

use gmp_mpfr_sys::gmp::{self, limb_t, mpz_t};
use num::BigInt;
use std::cmp::Ordering;
use std::ffi::CString;
use std::hash::{Hash, Hasher};
use std::mem::MaybeUninit;
use std::slice;
use std::str::FromStr;

#[derive(Debug)]
#[cfg_attr(repr_transparent, repr(transparent))]
pub struct Mpz {
    pub inner: mpz_t,
}

unsafe impl Send for Mpz {}
unsafe impl Sync for Mpz {}
impl Eq for Mpz {}

impl Default for Mpz {
    fn default() -> Self {
        let inner = unsafe {
            let mut ret = MaybeUninit::uninit();
            gmp::mpz_init(ret.as_mut_ptr());
            ret.assume_init()
        };
        Self { inner }
    }
}

impl Clone for Mpz {
    fn clone(&self) -> Self {
        let mut ret = Mpz::default();
        ret.set(&self);
        ret
    }
}

impl PartialEq for Mpz {
    fn eq(&self, other: &Mpz) -> bool {
        self.cmp_mpz(&other) == 0
    }
}

impl PartialOrd for Mpz {
    fn partial_cmp(&self, other: &Mpz) -> Option<Ordering> {
        match self.cmp_mpz(&other) {
            x if x < 0 => Some(Ordering::Less),
            0 => Some(Ordering::Equal),
            _ => Some(Ordering::Greater),
        }
    }
}

impl Ord for Mpz {
    fn cmp(&self, other: &Mpz) -> Ordering {
        match self.cmp_mpz(&other) {
            x if x < 0 => Ordering::Less,
            0 => Ordering::Equal,
            _ => Ordering::Greater,
        }
    }
}

impl Hash for Mpz {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let size = self.inner.size;
        size.hash(state);
        if size != 0 {
            let limbs = size.checked_abs().expect("overflow") as usize;
            let slice = unsafe { slice::from_raw_parts(self.inner.d.as_ptr(), limbs) };
            slice.hash(state);
        }
    }
}

impl From<u64> for Mpz {
    fn from(x: u64) -> Self {
        let mut ret = Mpz::default();
        unsafe { gmp::mpz_set_ui(&mut ret.inner, x) };
        ret
    }
}

impl FromStr for Mpz {
    type Err = std::ffi::NulError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut ret = Mpz::default();
        let c_str = CString::new(s)?;
        ret.set_cstr(&c_str);
        Ok(ret)
    }
}

impl Mpz {
    pub fn to_bigint(&self) -> BigInt {
        let l = unsafe { gmp::mpz_sizeinbase(&self.inner, 10) + 2 };
        let mut c_str = vec![];
        c_str.resize(l, 0);
        unsafe {
            gmp::mpz_get_str(c_str.as_mut_ptr() as *mut i8, 10, &self.inner);
        }
        while c_str[c_str.len() - 2] == 0 {
            c_str.pop();
        }

        BigInt::from_str(CString::from_vec_with_nul(c_str).unwrap().to_str().unwrap()).unwrap()
    }
}

// Defines wrappers around gmp_mpfr_sys.  Functions ending
// with `_mut` correspond to giving the underlying GMP function
// the same Mpz variable for the first two arguments, e.g.
// to provide an interface for operations like x += y or x /= y.
impl Mpz {
    #[inline]
    pub fn abs(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_abs(&mut self.inner, &x.inner) }
    }

    #[inline]
    pub fn add(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_add(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn add_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_add(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn sub_mul(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_submul(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn cmp_mpz(&self, other: &Mpz) -> i32 {
        unsafe { gmp::mpz_cmp(&self.inner, &other.inner) }
    }

    #[inline]
    pub fn cmpabs(&self, other: &Mpz) -> i32 {
        unsafe { gmp::mpz_cmpabs(&self.inner, &other.inner) }
    }

    #[inline]
    pub fn cmp_si(&self, val: i64) -> i32 {
        unsafe { gmp::mpz_cmp_si(&self.inner, val) }
    }

    #[inline]
    pub fn cdiv_q(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_cdiv_q(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn cdiv_r(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_cdiv_r(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn divexact(&mut self, n: &Mpz, d: &Mpz) {
        unsafe { gmp::mpz_divexact(&mut self.inner, &n.inner, &d.inner) }
    }

    #[inline]
    pub fn divexact_mut(&mut self, d: &Mpz) {
        unsafe {
            gmp::mpz_divexact(&mut self.inner, &self.inner, &d.inner);
        }
    }

    #[inline]
    pub fn fdiv_q(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_fdiv_q(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn fdiv_q_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_fdiv_q(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn fdiv_r(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_fdiv_r(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn fdiv_r_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_fdiv_r(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn fdiv_qr(&mut self, r: &mut Mpz, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_fdiv_qr(&mut self.inner, &mut r.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn fdiv_q_ui(&mut self, x: &Mpz, val: u64) {
        unsafe {
            gmp::mpz_fdiv_q_ui(&mut self.inner, &x.inner, val);
        }
    }

    #[inline]
    pub fn fdiv_q_ui_mut(&mut self, val: u64) {
        unsafe {
            gmp::mpz_fdiv_q_ui(&mut self.inner, &self.inner, val);
        }
    }

    #[inline]
    pub fn tdiv_q_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_tdiv_q(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn fits_slong_p(&self) -> i32 {
        unsafe { gmp::mpz_fits_slong_p(&self.inner) }
    }

    #[inline]
    pub fn gcd(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_gcd(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn gcd_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_gcd(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn gcdext(&mut self, d: &mut Mpz, e: &mut Mpz, a: &Mpz, m: &Mpz) {
        unsafe {
            gmp::mpz_gcdext(
                &mut self.inner,
                &mut d.inner,
                &mut e.inner,
                &a.inner,
                &m.inner,
            )
        }
    }

    #[inline]
    pub fn get_si(&self) -> i64 {
        unsafe { gmp::mpz_get_si(&self.inner) }
    }

    #[inline]
    pub fn modulo(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_mod(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn modulo_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_mod(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn mul(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_mul(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn mul_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_mul(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn mul_ui(&mut self, x: &Mpz, val: u64) {
        unsafe { gmp::mpz_mul_ui(&mut self.inner, &x.inner, val) }
    }
    #[inline]
    pub fn mul_si(&mut self, x: &Mpz, val: i64) {
        unsafe { gmp::mpz_mul_si(&mut self.inner, &x.inner, val) }
    }

    #[inline]
    pub fn mul_ui_mut(&mut self, val: u64) {
        unsafe { gmp::mpz_mul_ui(&mut self.inner, &self.inner, val) }
    }

    #[inline]
    pub fn neg(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_neg(&mut self.inner, &x.inner) }
    }
    #[inline]
    pub fn neg_mut(&mut self) {
        unsafe { gmp::mpz_neg(&mut self.inner, &self.inner) }
    }

    #[inline]
    pub fn odd(&self) -> i32 {
        unsafe { gmp::mpz_odd_p(&self.inner) }
    }

    #[inline]
    pub fn root_mut(&mut self, x: u64) -> i32 {
        unsafe { gmp::mpz_root(&mut self.inner, &self.inner, x) }
    }

    #[inline]
    pub fn set(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_set(&mut self.inner, &x.inner) }
    }

    #[inline]
    pub fn set_cstr(&mut self, cs: &CString) {
        unsafe {
            gmp::mpz_set_str(&mut self.inner, cs.as_ptr(), 10);
        }
    }

    #[inline]
    pub fn set_si(&mut self, val: i64) {
        unsafe { gmp::mpz_set_si(&mut self.inner, val) }
    }

    #[inline]
    pub fn set_ui(&mut self, val: u64) {
        unsafe { gmp::mpz_set_ui(&mut self.inner, val) }
    }

    #[inline]
    pub fn sgn(&self) -> i32 {
        unsafe { gmp::mpz_sgn(&self.inner) }
    }

    #[inline]
    pub fn square_mut(&mut self) {
        unsafe { gmp::mpz_mul(&mut self.inner, &self.inner, &self.inner) }
    }

    #[inline]
    pub fn sub(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_sub(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn submul(&mut self, x: &Mpz, y: &Mpz) {
        unsafe { gmp::mpz_submul(&mut self.inner, &x.inner, &y.inner) }
    }

    #[inline]
    pub fn sub_mut(&mut self, x: &Mpz) {
        unsafe { gmp::mpz_sub(&mut self.inner, &self.inner, &x.inner) }
    }

    #[inline]
    pub fn swap(&mut self, a: &mut Mpz) {
        unsafe { gmp::mpz_swap(&mut self.inner, &mut a.inner) }
    }

    #[inline]
    pub fn tdiv_q_2exp(&mut self, op1: &Mpz, op2: u64) {
        unsafe { gmp::mpz_tdiv_q_2exp(&mut self.inner, &op1.inner, op2) }
    }

    #[inline]
    pub fn bit_length(&self) -> usize {
        unsafe { gmp::mpz_sizeinbase(&self.inner, 2) as usize }
    }

    #[inline]
    pub fn is_neg(&self) -> bool {
        self.sgn() < 0
    }

    #[inline]
    pub fn size(&self) -> usize {
        unsafe { gmp::mpz_size(&self.inner) }
    }

    #[inline]
    pub fn getlimbn(&self, n: i64) -> limb_t {
        unsafe { gmp::mpz_getlimbn(&self.inner, n) }
    }

    #[inline]
    pub fn add_mul(&mut self, x: &Mpz, y: &Mpz) {
        unsafe {
            gmp::mpz_addmul(&mut self.inner, &x.inner, &y.inner);
        }
    }

    #[inline]
    pub fn from_bytes(data: &[u8]) -> Self {
        raw_import(data)
    }
}

fn raw_import(buf: &[u8]) -> Mpz {
    let mut obj = Mpz::default();

    unsafe {
        gmp::mpz_import(
            &mut obj.inner,
            buf.len(),
            1,
            1,
            1,
            0,
            buf.as_ptr() as *const _,
        )
    }
    obj
}
