//! Reusable memory context for class groups.

pub mod lin_congruence_ctx;
pub mod mpz;
pub mod partial;

use gmp_mpfr_sys::gmp;
use mpz::Mpz;

use lin_congruence_ctx::LinCongruenceCtx;
use num::{BigUint, Integer, Zero, ToPrimitive};
use num_prime::BitTest;

#[derive(Clone)]
pub struct OpCtx {
    pub inner: (
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
        Mpz,
    ),
}

impl Default for OpCtx {
    fn default() -> Self {
        Self {
            inner: (
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
            ),
        }
    }
}

#[derive(Clone)]
pub struct ClassCtx {
    pub L: Mpz,

    // Discrimenant
    pub D: Mpz,

    // Context for general class group ops implemented in mod.rs
    pub op_ctx: OpCtx,

    // Context that knows how to solve linear congruences.
    pub lin_cong_ctx: LinCongruenceCtx,

    // Context that handles partial extended GCD.
    pub partial_context: partial::PartialGCDContext,
}

impl ClassCtx {
    pub fn from_discriminant(disc: &Mpz) -> Self {
        let mut s = Self {
            L: Mpz::default(),
            D: disc.clone(),
            op_ctx: OpCtx::default(),
            lin_cong_ctx: LinCongruenceCtx::default(),
            partial_context: Default::default(),
        };

        // Precomputation needed for NUDULP.
        s.L.abs(disc);
        s.L.root_mut(4);
        s
    }
}

#[allow(clippy::stutter)]
#[derive(Debug)]
pub struct ClassElem {
    pub a: Mpz,
    pub b: Mpz,
    pub c: Mpz,
}

impl ClassElem {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend(self.a.to_bigint().to_signed_bytes_le());
        bytes.extend(self.b.to_bigint().to_signed_bytes_le());
        bytes.extend(self.c.to_bigint().to_signed_bytes_le());
        bytes
    }
}

impl Default for ClassElem {
    fn default() -> Self {
        ClassElem {
            a: Mpz::default(),
            b: Mpz::default(),
            c: Mpz::default(),
        }
    }
}

impl Clone for ClassElem {
    fn clone(&self) -> Self {
        let mut ret = ClassElem::default();
        ret.a = self.a.clone();
        ret.b = self.b.clone();
        ret.c = self.c.clone();
        ret
    }
}

impl PartialEq for ClassElem {
    fn eq(&self, other: &ClassElem) -> bool {
        // ClassElems only ever exist in reduced form, unless manually
        // instantiated with ClassElem {...}
        self.a == other.a && self.b == other.b && self.c == other.c
    }
}

impl Eq for ClassElem {}
unsafe impl Send for ClassElem {}
unsafe impl Sync for ClassElem {}

use std::{cell::RefCell, str::FromStr};

const EXP_THRESH: usize = 31;
const THRESH: i64 = ((1 as u64) << 31) as i64;

#[inline]
pub fn signed_shift(op: u64, shift: i64) -> u64 {
    match shift {
        x if x > 0 => op << shift,
        x if x <= -64 => 0,
        _ => op >> (-shift),
    }
}

#[inline]
pub fn mpz_get_si_2exp(op: &Mpz) -> (i64, usize) {
    let size = op.size();
    let last = op.getlimbn((size - 1) as i64);
    let lg2 = last.bits();
    let mut ret = signed_shift(last, 63 - lg2 as i64);
    if size > 1 {
        let prev = op.getlimbn((size - 2) as i64);
        ret += signed_shift(prev, (-1 - lg2 as i32) as i64);
    }
    if op.is_neg() {
        return (-(ret as i64), op.bit_length());
    }
    (ret as i64, op.bit_length())
}

#[inline]
pub fn test_reduction(x: &mut ClassElem) -> bool {
    let a_b = x.a.cmpabs(&x.b);
    let c_b = x.c.cmpabs(&x.b);

    if a_b < 0 || c_b < 0 {
        return false;
    }

    let a_c = x.a.cmp_mpz(&x.c);

    if a_c > 0 {
        x.a.swap(&mut x.c);
        x.b.neg_mut();
    }
    if a_c == 0 && x.b.is_neg() {
        x.b.neg_mut();
    }
    true
}

impl ClassCtx {
    fn discriminant(&mut self, a: &Mpz, b: &Mpz, c: &Mpz) -> Mpz {
        let scratch = &mut self.op_ctx.inner.0;

        let mut d = Mpz::default();
        d.mul(&b, &b);
        scratch.mul(&a, &c);
        scratch.mul_ui_mut(4);
        d.sub_mut(&scratch);
        d
    }

    #[allow(non_snake_case)]
    pub fn square(&mut self, x: &mut ClassElem) {
        // Jacobson, Michael J., and Alfred J. Van Der Poorten. "Computational aspects of NUCOMP."
        // Algorithm 2 (Alg 2).

        (|| {
            let (
                G_sq_op,
                scratch,
                y_sq_op,
                By_sq_op,
                Dy_sq_op,
                bx_sq_op,
                by_sq_op,
                dx_sq_op,
                q_sq_op,
                t_sq_op,
                ax_sq_op,
                ay_sq_op,
                Q1_sq_op,
                x_sq_op,
                z_sq_op,
                dy_sq_op,
                _,
            ) = &mut self.op_ctx.inner;

            let L_sq_op = &mut self.L;

            // Step 1 in Alg 2.
            G_sq_op.gcdext(scratch, y_sq_op, &x.a, &x.b);
            By_sq_op.divexact(&x.a, &G_sq_op);
            Dy_sq_op.divexact(&x.b, &G_sq_op);

            // Step 2 in Alg 2.
            bx_sq_op.mul(&y_sq_op, &x.c);
            bx_sq_op.modulo_mut(&By_sq_op);
            by_sq_op.set(&By_sq_op);

            if by_sq_op.cmpabs(&L_sq_op) <= 0 {
                // Step 4 in Alg 2.
                dx_sq_op.mul(&bx_sq_op, &Dy_sq_op);
                dx_sq_op.sub_mut(&x.c);
                dx_sq_op.divexact_mut(&By_sq_op);
                x.a.mul(&by_sq_op, &by_sq_op);
                x.c.mul(&bx_sq_op, &bx_sq_op);
                t_sq_op.add(&bx_sq_op, &by_sq_op);
                t_sq_op.square_mut();

                x.b.sub_mut(&t_sq_op);
                x.b.add_mut(&x.a);
                x.b.add_mut(&x.c);
                t_sq_op.mul(&G_sq_op, &dx_sq_op);
                x.c.sub_mut(&t_sq_op);
                return;
            }

            // Subroutine as handled by top entry to the Chia VDF competition "bulaiden."
            // Lehmer partial extended GCD.
            self.partial_context
                .xgcd_partial(y_sq_op, x_sq_op, by_sq_op, bx_sq_op, &L_sq_op); //L should be const

            x_sq_op.neg_mut();
            if x_sq_op.sgn() > 0 {
                y_sq_op.neg_mut();
            } else {
                by_sq_op.neg_mut();
            }

            ax_sq_op.mul(&G_sq_op, &x_sq_op);
            ay_sq_op.mul(&G_sq_op, &y_sq_op);

            // Step 5 in Alg 2.
            t_sq_op.mul(&Dy_sq_op, &bx_sq_op);
            t_sq_op.submul(&x.c, &x_sq_op);
            dx_sq_op.divexact(&t_sq_op, &By_sq_op);
            Q1_sq_op.mul(&y_sq_op, &dx_sq_op);
            dy_sq_op.add(&Q1_sq_op, &Dy_sq_op);
            x.b.add(&dy_sq_op, &Q1_sq_op);
            x.b.mul_mut(&G_sq_op);
            dy_sq_op.divexact_mut(&x_sq_op);
            x.a.mul(&by_sq_op, &by_sq_op);
            x.c.mul(&bx_sq_op, &bx_sq_op);
            t_sq_op.add(&bx_sq_op, &by_sq_op);
            x.b.submul(&t_sq_op, &t_sq_op);
            x.b.add_mut(&x.a);
            x.b.add_mut(&x.c);
            x.a.submul(&ay_sq_op, &dy_sq_op);
            x.c.submul(&ax_sq_op, &dx_sq_op);
        })();

        self.reduce_mut(x);
    }

    #[inline]
    fn reduce_mut(&mut self, x: &mut ClassElem) {
        self.normalize_mut(x);
        self.reduce(x);
        self.normalize_mut(x);
    }

    #[inline]
    fn reduce(&mut self, elem: &mut ClassElem) {
        let (
            x,
            s,
            ra,
            rb,
            h,
            g,
            j,
            k,
            rw,
            l,
            r_norm,
            denom_norm,
            mu_norm,
            s_norm,
            ra_norm,
            rb_norm,
            _,
        ) = &mut self.op_ctx.inner;

        while !test_reduction(elem) {
            let (mut a, a_exp) = mpz_get_si_2exp(&elem.a);
            let (mut b, b_exp) = mpz_get_si_2exp(&elem.b);
            let (mut c, c_exp) = mpz_get_si_2exp(&elem.c);

            let mut max_exp = a_exp;
            let mut min_exp = a_exp;

            use std::cmp::max;
            use std::cmp::min;

            max_exp = max(max_exp, b_exp);
            max_exp = max(max_exp, c_exp);
            min_exp = min(min_exp, b_exp);
            min_exp = min(min_exp, c_exp);

            //println!("about to check normalize");

            if max_exp - min_exp > EXP_THRESH {
                //Self::normalize_mut(elem);
                Self::normalizer(elem, r_norm, denom_norm, mu_norm, s_norm, ra_norm, rb_norm);
                //g.normalize_(&mut elem.a, &mut elem.b, &mut elem.c);
                continue;
            }
            //  println!("a: {}", x.a);
            //  println!("b: {}", x.b);
            //  println!("c: {}", x.c);
            max_exp += 1; // for overflow safety
            a >>= max_exp - a_exp;
            b >>= max_exp - b_exp;
            c >>= max_exp - c_exp;

            let mut u_ = 1;
            let mut v_ = 0;
            let mut w_ = 0;
            let mut y_ = 1;

            let mut u;
            let mut v;
            let mut w;
            let mut y;

            //    println!("starting do-while loop");
            loop {
                //println!("start of loop");
                u = u_;
                v = v_;
                w = w_;
                y = y_;
                let delta = if b >= 0 {
                    //      println!("top");
                    (b + c) / (c << 1)
                } else {
                    //      println!("bottom");
                    -(-b + c) / (c << 1)
                };
                let c_ = c * delta;
                (a, b, c) = (c, -b + (c_ << 1), a - delta * (b - c_));

                u_ = v;
                v_ = -u + delta * v;
                w_ = y;
                y_ = -w + delta * y;
                if !((v_.abs() | y_.abs()) <= THRESH && a > c && c > 0) {
                    break;
                }
            }
            //println!("finished loop");
            if (v_.abs() | y_.abs()) <= THRESH {
                u = u_;
                v = v_;
                w = w_;
                y = y_;
            }
            let aa = u * u;
            //println!("aa: {}", aa);
            let ab = u * w;
            //println!("ab: {}", ab);
            let ac = w * w;
            //println!("ac: {}", ac);
            let ba = (u * v) << 1;
            //println!("ba: {}", ba);
            let bb = u * y + v * w;
            //println!("bb: {}", bb);
            let bc = (w * y) << 1;
            //println!("bc: {}", bc);
            let ca = v * v;
            //println!("ca: {}", ca);
            let cb = v * y;
            //println!("cb: {}", cb);
            let cc = y * y;
            //sprintln!("cc: {}", cc);

            ra.mul_si(&elem.a, aa); // a = faa
            rb.mul_si(&elem.b, ab); // b = fab
            h.mul_si(&elem.c, ac); // h = fac

            g.mul_si(&elem.a, ba); // g = fba
            j.mul_si(&elem.b, bb); // j = fbb
            k.mul_si(&elem.c, bc); // k = fbc

            s.mul_si(&elem.a, ca); // s = fca
            rw.mul_si(&elem.b, cb); // w = fcb
            l.mul_si(&elem.c, cc); // l = fcc

            elem.a.add(&ra, &rb);
            elem.a.add_mut(&h);

            elem.b.add(&g, &j);
            elem.b.add_mut(&k);

            elem.c.add(&s, &rw);
            elem.c.add_mut(&l);
        }
    }

    fn normalize_mut(&mut self, x: &mut ClassElem) {
        let already_normal = {
            let scratch = &mut self.op_ctx.inner.0;
            if Self::elem_is_normal(scratch, &x.a, &x.b, &x.c) {
                true
            } else {
                false
            }
        };

        if !already_normal {
            self.normalize(&mut x.a, &mut x.b, &mut x.c);
        }
    }

    fn normalize(&mut self, a: &mut Mpz, b: &mut Mpz, c: &mut Mpz) {
        let r = &mut self.op_ctx.inner.0;
        let denom = &mut self.op_ctx.inner.1;
        let ra = &mut self.op_ctx.inner.3;

        // Binary Quadratic Forms, 5.1.1
        r.sub(&a, &b);
        denom.mul_ui(&a, 2);
        r.fdiv_q_mut(&denom);

        ra.mul(&r, &a);
        c.add_mul(&ra, r);
        c.add_mul(&r, &b);
        b.add_mut(&ra);
        b.add_mut(&ra);
    }

    fn normalizer(
        elem: &mut ClassElem,
        r: &mut Mpz,
        denom: &mut Mpz,
        mu: &mut Mpz,
        s: &mut Mpz,
        ra: &mut Mpz,
        rb: &mut Mpz,
    ) {
        mu.add(&elem.b, &elem.c);
        s.mul_ui(&elem.c, 2);

        denom.fdiv_q(&mu, &s);

        ra.set(&elem.c);

        s.mul_ui(&denom, 2);
        rb.neg(&elem.b);
        rb.add_mul(&elem.c, &s);

        r.set(&elem.a);
        r.submul(&elem.b, &denom);
        denom.square_mut();
        r.add_mul(&elem.c, &denom);

        elem.a.set(&ra);
        elem.b.set(&rb);
        elem.c.set(&r);
    }

    #[inline]
    pub fn op(&mut self, x: &ClassElem, y: &ClassElem) -> ClassElem {
        let (g, h, j, w, s, t, u, a, b, l, m, mu, v, lambda, sigma, k, ..) = &mut self.op_ctx.inner;

        // Binary Quadratic Forms, 6.1.1
        g.add(&x.b, &y.b);
        unsafe {
            gmp::mpz_fdiv_q_2exp(&mut g.inner, &g.inner, 1);
        }
        h.sub(&y.b, &g);

        w.gcd(&x.a, &y.a);
        w.gcd_mut(&g);
        j.set(&w);
        s.divexact(&x.a, &w);
        t.divexact(&y.a, &w);
        u.divexact(&g, &w);
        a.mul(&t, &u);
        b.mul(&h, &u);
        b.add_mul(&s, &x.c);
        m.mul(&s, &t);
        self.lin_cong_ctx
            .solve_linear_congruence(mu, v, &a, &b, &m)
            .unwrap();

        a.mul(&t, &v);
        m.mul(&t, &mu);
        b.sub(&h, &m);
        m.set(&s);
        self.lin_cong_ctx
            .solve_linear_congruence(lambda, sigma, &a, &b, &m)
            .unwrap();

        a.mul(&v, &lambda);
        k.add(&mu, &a);
        l.mul(&k, &t);
        l.sub_mut(&h);
        l.fdiv_q_mut(&s);
        m.mul(&t, &u);
        m.mul_mut(&k);
        m.sub_mul(h, &u);
        m.sub_mul(&x.c, &s);
        a.mul(&s, &t);
        m.fdiv_q_mut(&a);

        let mut ret = ClassElem::default();

        ret.a.mul(&s, &t);

        ret.b.mul(&j, &u);
        ret.b.sub_mul(k, &t);
        ret.b.sub_mul(&l, &s);

        ret.c.mul(&k, &l);
        ret.c.sub_mul(&j, &m);

        self.reduce_mut(&mut ret);
        ret
    }

    pub fn id(&mut self) -> ClassElem {
        let a = &mut self.op_ctx.inner.0;

        // Binary Quadratic Forms, Definition 5.4
        // The identity is the Principal Form of Discriminant d.
        let mut ret = ClassElem::default();
        ret.a.set_ui(1);
        ret.b.set_ui(1);
        a.sub(&ret.b, &self.D);
        unsafe {
            gmp::mpz_fdiv_q_2exp(&mut ret.c.inner, &a.inner, 2);
        }

        ret
    }

    pub fn inv(x: &ClassElem) -> ClassElem {
        let mut ret = ClassElem::default();
        ret.a.set(&x.a);
        ret.b.neg(&x.b);
        ret.c.set(&x.c);
        ret
    }

    pub fn pow(&mut self, a: &ClassElem, n: &BigUint) -> ClassElem {
        let e = n.to_radix_le(2);
        let k = 4;
        let mut aa = a.clone();
        self.square(&mut aa);
        let mut base_powers = vec![self.id(), a.clone(), aa];
        for _ in 3..(1 << k) {
            base_powers.push(self.op(base_powers.last().unwrap(), &a));
        }
        let mut r = self.id();

        for (i, chunk) in e.rchunks(k).enumerate() {
            let k = chunk.len();
            if i != 0 {
                for _ in 0..k {
                    self.square(&mut r);
                }
            }
            let mut t = 0;
            for i in chunk.iter().rev() {
                t <<= 1;
                t += i;
            }
            if i != 0 {
                r = self.op(&r, &base_powers[t as usize]);
            } else {
                r = base_powers[t as usize].clone();
            }
        }
        r
    }

    pub fn pow_precomputed(&mut self, base_powers: &[Vec<ClassElem>], n: &BigUint) -> ClassElem {
        let mut n = n.clone();
        let l = (base_powers[0].len() - 1).bits();
        let q = BigUint::from(base_powers[0].len() - 1);
        let mut r = base_powers[0][(&n & &q).to_usize().unwrap()].clone();
        n >>= l;

        let mut i = 1;
        while !n.is_zero() {
            r = self.op(&r, &base_powers[i][(&n & &q).to_usize().unwrap() as usize]);
            n >>= l;
            i += 1;
        }

        r
    }

    /// The generator element
    pub fn unknown_order_elem(&mut self) -> ClassElem {
        // Binary Quadratic Forms, Definition 5.4
        let mut ret = ClassElem::default();
        ret.a.set_ui(2);
        ret.b.set_ui(1);
        ret.c.set_ui(1);
        ret.c.sub_mut(&self.D);
        unsafe {
            gmp::mpz_fdiv_q_2exp(&mut ret.c.inner, &ret.c.inner, 3);
        }

        self.reduce(&mut ret);
        ClassElem {
            a: ret.a,
            b: ret.b,
            c: ret.c,
        }
    }

    /// The generator element
    pub fn unknown_order_elem_disc(&mut self, disc: &Mpz) -> ClassElem {
        // Binary Quadratic Forms, Definition 5.4
        let mut ret = ClassElem::default();
        ret.a.set_ui(2);
        ret.b.set_ui(1);
        ret.c.set_ui(1);
        ret.c.sub_mut(disc);
        unsafe {
            gmp::mpz_fdiv_q_2exp(&mut ret.c.inner, &ret.c.inner, 3);
        }

        self.reduce(&mut ret);
        ClassElem {
            a: ret.a,
            b: ret.b,
            c: ret.c,
        }
    }

    fn validate(&mut self, a: &Mpz, b: &Mpz, c: &Mpz) -> bool {
        self.discriminant(a, b, c) == self.D
    }

    fn elem_is_normal(scratch: &mut Mpz, a: &Mpz, b: &Mpz, _c: &Mpz) -> bool {
        scratch.neg(&a);
        *scratch < *b && b <= a
    }

    pub fn elem(&mut self, abc: (Mpz, Mpz, Mpz)) -> ClassElem {
        let mut el = ClassElem {
            a: abc.0,
            b: abc.1,
            c: abc.2,
        };
        self.reduce(&mut el);

        // Ideally, this should return an error and the
        // return type of ElemFrom should be Result<Self::Elem, Self:err>,
        // but this would require a lot of ugly "unwraps" in the accumulator
        // library. Besides, users should not need to create new class group
        // elements, so an invalid ElemFrom here should signal a severe internal error.
        assert!(self.validate(&el.a, &el.b, &el.c));

        el
    }

    pub fn bqf(&mut self, a: Mpz, b: Mpz) -> ClassElem {
        let mut c = Mpz::default();
        let mut d = Mpz::default();
        d.mul(&b, &b);
        c.sub(&d, &self.D);
        d.divexact(&c, &a);
        unsafe {
            gmp::mpz_fdiv_q_2exp(&mut c.inner, &d.inner, 2);
        }
        let mut el = ClassElem { a, b, c };
        self.reduce(&mut el);

        el
    }
}

//  Caveat: tests that use "ground truth" use outputs from
//  Chia's sample implementation in python:
//    https://github.com/Chia-Network/vdf-competition/blob/master/inkfish/classgroup.py.
#[cfg(test)]
mod tests {
    use num::One;

    use super::*;
    use std::{str::FromStr, time::Instant};

    const DISCRIMINANT2048_DECIMAL: &str =
  "-30616069034807523947093657516320815215492876376165067902716988657802400037331914448218251590830\
  1102189519215849430413184776658192481976276720778009261808832630304841711366872161223643645001916\
  6969493423497224870506311710491233557329479816457723381368788734079933165653042145718668727765268\
  0575673207678516369650123480826989387975548598309959486361425021860161020248607833276306314923730\
  9854570972702350567411779734372573754840570138310317754359137013512655926325773048926718050691092\
  9453371727344087286361426404588335160385998280988603297435639020911295652025967761702701701471162\
  3966286152805654229445219531956098223";

    // Makes a class elem tuple but does not reduce.
    fn construct_raw_elem_from_strings(a: &str, b: &str, c: &str) -> ClassElem {
        ClassElem {
            a: Mpz::from_str(a).unwrap(),
            b: Mpz::from_str(b).unwrap(),
            c: Mpz::from_str(c).unwrap(),
        }
    }

    #[test]
    fn test_elem_from() {
        let a1 = Mpz::from_str("16").unwrap();
        let b1 = Mpz::from_str("105").unwrap();
        let c1 = Mpz::from_str(
      "47837607866886756167333839869251273774207619337757918597995294777816250058331116325341018110\
      672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194319\
      531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526854\
      198871332313399489386997681827578317938792170918711794684859311697439726596656501594138449739\
      494228617068329664776714484742276158090583495714649193839084110987149118615158361352488488402\
      038894799695420483272708933239751363849397287571692736881031223140446926522431859701738994562\
      9057462766047140854869124473221137588347335081555186814207",
    )
    .unwrap();

        let a2 = Mpz::from_str("16").unwrap();
        let b2 = Mpz::from_str("9").unwrap();
        let c2 = Mpz::from_str(
      "47837607866886756167333839869251273774207619337757918597995294777816250058331116325341018110\
      672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194319\
      531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526854\
      198871332313399489386997681827578317938792170918711794684859311697439726596656501594138449739\
      494228617068329664776714484742276158090583495714649193839084110987149118615158361352488488402\
      038894799695420483272708933239751363849397287571692736881031223140446926522431859701738994562\
      9057462766047140854869124473221137588347335081555186814036",
    )
    .unwrap();

        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());

        let reduced_elem = g.elem((a1, b1, c1));
        let also_reduced_elem = g.elem((a2, b2, c2));
        assert_eq!(reduced_elem, also_reduced_elem);
    }

    #[test]
    fn test_equality() {
        let mut not_reduced = construct_raw_elem_from_strings(
      "16",
      "105",
      "47837607866886756167333839869251273774207619337757918597995294777816250058331116325341018110\
      672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194319\
      531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526854\
      198871332313399489386997681827578317938792170918711794684859311697439726596656501594138449739\
      494228617068329664776714484742276158090583495714649193839084110987149118615158361352488488402\
      038894799695420483272708933239751363849397287571692736881031223140446926522431859701738994562\
      9057462766047140854869124473221137588347335081555186814207"
    );

        let reduced_ground_truth = construct_raw_elem_from_strings(
      "16",
      "9",
      "47837607866886756167333839869251273774207619337757918597995294777816250058331116325341018110\
      672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194319\
      531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526854\
      198871332313399489386997681827578317938792170918711794684859311697439726596656501594138449739\
      494228617068329664776714484742276158090583495714649193839084110987149118615158361352488488402\
      038894799695420483272708933239751363849397287571692736881031223140446926522431859701738994562\
      9057462766047140854869124473221137588347335081555186814036"
    );

        let diff_elem = construct_raw_elem_from_strings(
      "4",
      "1",
      "19135043146754702466933535947700509509683047735103167439198117911126500023332446530136407244\
      268818886844950990589400824048541137030123517295048625578863052039394052606960429510076477727\
      812619793559333896857655440664448190570209733309248852860771133554929587999582285331513410741\
      679548532925359795754799072731031327175516868367484717873943724678975890638662600637655379895\
      797691446827331865910685793896910463236233398285859677535633644394859647446063344540995395360\
      815557919878168193309083573295900545539758915028677094752412489256178770608972743880695597825\
      16229851064188563419476497892884550353389340326220747256139"
    );

        assert!(not_reduced != reduced_ground_truth);
        assert!(not_reduced == not_reduced.clone());
        assert!(reduced_ground_truth == reduced_ground_truth.clone());
        assert!(not_reduced != diff_elem);
        assert!(reduced_ground_truth != diff_elem);
        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        g.reduce(&mut not_reduced);
        assert!(not_reduced == reduced_ground_truth);
    }

    #[test]
    fn test_reduce_basic() {
        let mut to_reduce = construct_raw_elem_from_strings(
      "59162244921619725812008939143220718157267937427074598447911241410131470159247784852210767449\
      675610037288729551814191198624164179866076352187405442496568188988272422133088755036699145362\
      385840772236403043664778415471196678638241785773530531198720497580622741709880533724904220122\
      358854068046553219863419609777498761804625479650772123754523807001976654588225908928022367436\
      8",
      "18760351095004839755193532164856605650590306627169248964100884295652838905828158941233738613\
      175821849253748329102319504958410190952820220503570113920576542676928659211807590199941027958\
      195895385446372444261885022800653454209101497963588809819572703579484085278913354621371362285\
      341138299691587953249270188429393417132110841259813122945626515477865766896056280729710478647\
      13",
      "14872270891432803054791175727694631095755964943358394411314110783404577714102170379700365256\
      599679049493824862742803590079461712691146098397470840896560034332315858221821103076776907123\
      277315116632337385101204055232891361405428635972040596205450316747012080794838691280547894128\
      246741601088755087359234554141346980837292342320288111397175220296098629890108459305643419353\
      36"
    );

        let reduced_ground_truth = construct_raw_elem_from_strings(
      "26888935961824081232597112540509824504614070059776273347136888921115497522070287009841688662\
      983066376019079593372296556420848446780369918809384119124783870290778875424468497961559643807\
      918398860928578027038014112641529893817109240852544158309292025321122680747989987560029531021\
      808743313150630063377037854944",
      "14529985196481999393995154363327100184407232892559561136140792409262328867440167480822808496\
      853924547751298342980606034124112579835255733824790020119078588372593288210628255956605240171\
      744703418426092073347584357826862813733154338737148962212641444735717023402201569115323580814\
      54099903972209626147819759991",
      "28467266502267127591420289007165819749231433586093061478772560429058231137856046130384492811\
      816456933286039468940950129263300933723839212086399375780796041634531383342902918719073416087\
      614456845205980227091403964285870107268917183244016635907926846271829374679124848388403486656\
      1564478239095738726823372184204"
    );

        let already_reduced = reduced_ground_truth.clone();
        assert_eq!(already_reduced, reduced_ground_truth);
        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        assert_ne!(to_reduce, reduced_ground_truth);
        g.reduce(&mut to_reduce);
        assert_eq!(to_reduce, reduced_ground_truth);
    }

    #[test]
    fn test_normalize_basic() {
        let mut unnorm_a = Mpz::from_str("16").unwrap();
        let mut unnorm_b = Mpz::from_str("105").unwrap();
        let mut unnorm_c = Mpz::from_str(
      "4783760786688675616733383986925127377420761933775791859799529477781625005833111632534101811\
       0672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194\
       3195315494838983347421441386016611204764255243332731221321519278338873239699989557133287835\
       2685419887133231339948938699768182757831793879217091871179468485931169743972659665650159413\
       8449739494228617068329664776714484742276158090583495714649193839084110987149118615158361352\
       4884884020388947996954204832727089332397513638493972875716927368810312231404469265224318597\
       017389945629057462766047140854869124473221137588347335081555186814207",
    )
    .unwrap();

        let norm_a = Mpz::from_str("16").unwrap();
        let norm_b = Mpz::from_str("9").unwrap();
        let norm_c = Mpz::from_str(
      "4783760786688675616733383986925127377420761933775791859799529477781625005833111632534101811\
       06720472171123774764735020601213528425753087932376215639471576300984851315174010737751911943\
       19531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526\
       85419887133231339948938699768182757831793879217091871179468485931169743972659665650159413844\
       97394942286170683296647767144847422761580905834957146491938390841109871491186151583613524884\
       88402038894799695420483272708933239751363849397287571692736881031223140446926522431859701738\
       9945629057462766047140854869124473221137588347335081555186814036",
    )
    .unwrap();
        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        g.normalize(&mut unnorm_a, &mut unnorm_b, &mut unnorm_c);
        assert_eq!((norm_a, norm_b, norm_c), (unnorm_a, unnorm_b, unnorm_c));
    }

    #[test]
    fn test_discriminant_across_ops() {
        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let id = g.id();
        let g1 = g.unknown_order_elem();
        let g2 = g.op(&g1, &g1);
        let g3 = g.op(&id, &g2);
        let g3_inv = ClassCtx::inv(&g3);

        assert!(g.validate(&id.a, &id.b, &id.c));
        assert!(g.validate(&g1.a, &g1.b, &g1.c));
        assert!(g.validate(&g2.a, &g2.b, &g2.c));
        assert!(g.validate(&g3.a, &g3.b, &g3.c));
        assert!(g.validate(&g3_inv.a, &g3_inv.b, &g3_inv.c));
    }

    #[test]
    fn test_op_single() {
        let a = construct_raw_elem_from_strings(
      "4",
      "1",
      "19135043146754702466933535947700509509683047735103167439198117911126500023332446530136407244\
      268818886844950990589400824048541137030123517295048625578863052039394052606960429510076477727\
      812619793559333896857655440664448190570209733309248852860771133554929587999582285331513410741\
      679548532925359795754799072731031327175516868367484717873943724678975890638662600637655379895\
      797691446827331865910685793896910463236233398285859677535633644394859647446063344540995395360\
      815557919878168193309083573295900545539758915028677094752412489256178770608972743880695597825\
      16229851064188563419476497892884550353389340326220747256139"
    );

        let b = construct_raw_elem_from_strings(
      "16",
      "41",
      "47837607866886756167333839869251273774207619337757918597995294777816250058331116325341018110\
      672047217112377476473502060121352842575308793237621563947157630098485131517401073775191194319\
      531549483898334742144138601661120476425524333273122132151927833887323969998955713328783526854\
      198871332313399489386997681827578317938792170918711794684859311697439726596656501594138449739\
      494228617068329664776714484742276158090583495714649193839084110987149118615158361352488488402\
      038894799695420483272708933239751363849397287571692736881031223140446926522431859701738994562\
      9057462766047140854869124473221137588347335081555186814061"
    );

        let ground_truth = construct_raw_elem_from_strings(
      "64",
      "9",
      "11959401966721689041833459967312818443551904834439479649498823694454062514582779081335254527\
      668011804278094369118375515030338210643827198309405390986789407524621282879350268443797798579\
      882887370974583685536034650415280119106381083318280533037981958471830992499738928332195881713\
      549717833078349872346749420456894579484698042729677948671214827924359931649164125398534612434\
      873557154267082416194178621185569039522645873928662298459771027746787279653789590338122122100\
      50972369992385512081817723330993784096234932189292318422025780578511173163060796492543474864\
      07264365691511785213717281118305284397086833770388796703509"
    );
        let mut g = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        assert_eq!(g.op(&a, &b), ground_truth);
    }

    #[test]
    fn test_op_alternating() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g_anchor = h.unknown_order_elem();
        let mut g = h.id();
        let mut g_star = h.id();

        // g
        g = h.op(&g_anchor, &g);

        // g^2, g^* = g^2
        g = h.op(&g_anchor, &g);
        g_star = h.op(&g, &g_star);

        // g^3
        g = h.op(&g_anchor, &g);

        // g^4, g^* = g^2 * g^4 = g^6
        g = h.op(&g_anchor, &g);
        g_star = h.op(&g, &g_star);

        let ground_truth = construct_raw_elem_from_strings(
      "64",
      "9",
      "11959401966721689041833459967312818443551904834439479649498823694454062514582779081335254527\
      668011804278094369118375515030338210643827198309405390986789407524621282879350268443797798579\
      882887370974583685536034650415280119106381083318280533037981958471830992499738928332195881713\
      549717833078349872346749420456894579484698042729677948671214827924359931649164125398534612434\
      873557154267082416194178621185569039522645873928662298459771027746787279653789590338122122100\
      509723699923855120818177233309937840962349321892923184220257805785111731630607964925434748640\
      7264365691511785213717281118305284397086833770388796703509"
    );

        assert_eq!(ground_truth, g_star);
    }

    #[test]
    fn test_op_complex() {
        // 1. Take g^100, g^200, ..., g^1000.
        // 2. Compute g^* = g^100 * ... * g^1000.
        // 3. For each of g^100, g^200, ..., g^1000 compute the inverse of that element and assert that
        //    g^* * current_inverse = product of g^100, g^200, ..., g^1000 without the inversed-out
        //    element.
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g_anchor = h.unknown_order_elem();
        let mut g = h.id();

        let mut gs = vec![];
        let mut gs_invs = vec![];

        let mut g_star = h.id();
        for i in 1..=1000 {
            g = h.op(&g_anchor, &g);
            assert!(h.validate(&g.a, &g.b, &g.c));
            if i % 100 == 0 {
                gs.push(g.clone());
                gs_invs.push(ClassCtx::inv(&g));
                g_star = h.op(&g, &g_star);
                assert!(h.validate(&g.a, &g.b, &g.c));
            }
        }

        let elems_n_invs = gs.iter().zip(gs_invs.iter());
        for (g_elem, g_inv) in elems_n_invs {
            assert!(h.validate(&g_elem.a, &g_elem.b, &g_elem.c));
            assert!(h.validate(&g_inv.a, &g_inv.b, &g_inv.c));
            let mut curr_prod = h.id();
            for elem in &gs {
                if elem != g_elem {
                    curr_prod = h.op(&curr_prod, &elem);
                    assert!(h.validate(&curr_prod.a, &curr_prod.b, &curr_prod.c));
                }
            }
            assert_eq!(h.id(), h.op(&g_inv, &g_elem));
            assert_eq!(curr_prod, h.op(&g_inv, &g_star));
        }
    }

    #[test]
    fn test_id_basic() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g = h.unknown_order_elem();
        let id = h.id();
        assert_eq!(g, h.op(&g, &id));
        assert_eq!(g, h.op(&id, &g));
        assert_eq!(id, h.op(&id, &id));
    }

    #[test]
    fn test_id_repeated() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let mut id = h.id();
        let g_anchor = h.unknown_order_elem();
        let mut g = h.unknown_order_elem();
        for _ in 0..1000 {
            id = h.op(&id, &id);
            assert_eq!(id, h.id());
            let id = h.id();
            g = h.op(&g, &id);
            assert_eq!(g, g_anchor);
        }
    }

    #[test]
    fn test_inv() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let id = h.id();
        let g_anchor = h.unknown_order_elem();
        let mut g = h.unknown_order_elem();

        for _ in 0..1000 {
            g = h.op(&g, &g_anchor);
            let g_inv = ClassCtx::inv(&g);
            assert_eq!(id, h.op(&g_inv, &g));
            assert_eq!(id, h.op(&g, &g_inv));
            assert_eq!(g, ClassCtx::inv(&g_inv));
        }
    }

    #[test]
    fn test_exp_basic() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g_anchor = h.unknown_order_elem();
        let mut g = h.id();

        for i in 1..=1000u64 {
            g = h.op(&g, &g_anchor);
            assert_eq!(&g, &h.pow(&g_anchor, &BigUint::from(i)));
        }
    }

    #[test]
    fn test_exp() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g_anchor = h.unknown_order_elem();
        let now = Instant::now();
        h.pow(&g_anchor, &(BigUint::one() << 1024u32));
        println!("Time: {:?}", now.elapsed());
    }

    #[test]
    fn test_square() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let mut g_anchor = h.unknown_order_elem();
        let now = Instant::now();
        h.square(&mut g_anchor);
        println!("Time: {:?}", now.elapsed());
    }

    #[test]
    fn test_square_basic() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let g = h.unknown_order_elem();
        let mut g4 = h.id();

        // g^4
        for _ in 0..4 {
            g4 = h.op(&g, &g4);
        }

        // g^2
        let mut g2 = g.clone();
        // g^4
        h.square(&mut g2);
        h.square(&mut g2);

        assert_eq!(&g2, &g4);
    }

    #[test]
    fn test_square_repeated() {
        let mut h = ClassCtx::from_discriminant(&Mpz::from_str(DISCRIMINANT2048_DECIMAL).unwrap());
        let mut g = h.unknown_order_elem();
        let g_ = g.clone();

        for i in 0..12 {
            h.square(&mut g);
            let mut base = h.id();

            for _ in 0..(2i32.pow(i + 1)) {
                base = h.op(&g_, &base);
            }

            assert_eq!(g, base);
        }
    }
}
