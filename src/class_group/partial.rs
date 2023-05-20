//! Partial Euclidean algorithm.
///
/// Lehmer's version for computing GCD
/// (for Book's version of NUCOMP, NUDUPL, and NUCUBE algorithm).
///
/// Input:  R2 = R_{-1} , R1 = R_{0}, bound
///  - R_i is the R - sequence from "Solving the Pell Equation"
///   ( R_i = R_{i-2}-q_i R_{i-1} )
/// Output: R2 = R_{i-1}, R1 = R_i, C2 = C_{i-1}, C1 = C_i,
///  - R_i = 0 or R_i <= bound < R_{i-1}
///  - C_i sequence from "Solving the Pell Equation" defined as
///     C_{-1}=0, C_{1}=-1  C_i=C_{i-2}-q_i C_{i-1}
///
use super::mpz::Mpz;
use gmp_mpfr_sys::gmp;

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PartialGCDContext {
    pub q: Mpz,
    pub r: Mpz,
    pub t1: Mpz,
    pub t2: Mpz,
}

impl Default for PartialGCDContext {
    fn default() -> Self {
        Self {
            q: Mpz::default(),
            r: Mpz::default(),
            t1: Mpz::default(),
            t2: Mpz::default(),
        }
    }
}

impl PartialGCDContext {
    /// This function is an implementation of Lehmer extended GCD with early termination.
    /// It terminates early when remainders fall below the specified bound.
    /// The initial values r1 and r2 are treated as successive remainders in the Euclidean algorithm
    /// and are replaced with the last two remainders computed. The values _co1 and _co2 are the last two
    /// cofactors and satisfy the identity _co2*r1 - _co1*r2 == +/- r2_orig upon termination, where
    /// r2_orig is the starting value of r2 supplied, and r1 and r2 are the final values.
    pub fn xgcd_partial(
        &mut self,
        c2: &mut Mpz,
        c1: &mut Mpz,
        r2: &mut Mpz,
        r1: &mut Mpz,
        bound: &Mpz,
    ) {
        c1.set_si(-1);
        c2.set_si(0);

        //loop index
        let mut _index = 0;

        while r1.sgn() != 0 && r1.cmp_mpz(&bound) > 0 {
            let mut _t = r2.bit_length();
            let mut _t1 = r1.bit_length();

            let bits = ((std::cmp::max(_t, _t1)) - (gmp::LIMB_BITS as usize) + 1) as u64;

            self.r.tdiv_q_2exp(&r2, bits);
            let mut rr2 = self.r.get_si();

            self.r.tdiv_q_2exp(&r1, bits);
            let mut rr1 = self.r.get_si();

            self.r.tdiv_q_2exp(&bound, bits);

            let bb: i64 = self.r.get_si();

            //reset values
            let mut a1: i64 = 1;
            let mut a2: i64 = 0;
            let mut b1: i64 = 0;
            let mut b2: i64 = 1;

            //reset inner loop index
            _index = 0;

            // Euclidean Step
            while rr1 != 0 && rr1 > bb {
                //println!("test_partical_gcd ");

                let qq: i64 = rr2 / rr1;

                //t1
                let t1 = rr2 - (qq * rr1);

                //t2
                let t2 = a2 - (qq * a1);

                //t3
                let t3 = b2 - (qq * b1);

                //check if it is even or odd
                if _index % 2 != 0 {
                    //index & 1
                    //its odd
                    if t1 < -t3 || rr1 - t1 < t2 - a1 {
                        break;
                    }
                } else {
                    //its even
                    if t1 < -t2 || rr2 - t1 < t3 - b1 {
                        break;
                    }
                }

                rr2 = rr1;
                rr1 = t1;

                a2 = a1;
                a1 = t2;

                b2 = b1;
                b1 = t3;

                //increment index
                _index += 1;
            }

            if _index == 0 {
                // multiprecision step
                let tmp = r2.clone();
                self.q.fdiv_qr(r2, &tmp, &r1); //i r2 is taken here what we do
                r2.swap(r1);
                c2.sub_mul(&c1, &self.q);
                c2.swap(c1);
            } else {
                // recombination
                // r = R2*B2 + R1*A2;  R1 = R2*B1 + R1*A1;  R2 = r;

                self.t1.mul_si(&r2, b2);
                self.t2.mul_si(&r1, a2);
                self.r.add(&self.t1, &self.t2);
                self.t1.mul_si(&r2, b1);
                self.t2.mul_si(&r1, a1);
                r1.add(&self.t1, &self.t2);
                r2.set(&self.r);
                self.t1.mul_si(&c2, b2);
                self.t2.mul_si(&c1, a2);
                self.r.add(&self.t1, &self.t2);
                self.t1.mul_si(&c2, b1);
                self.t2.mul_si(&c1, a1);
                c1.add(&self.t1, &self.t2);

                //
                c2.set(&self.r);

                // make sure R1 and R2 are positive
                if r1.sgn() < 0 {
                    r1.neg_mut();
                    c1.neg_mut();
                }

                if r2.sgn() < 0 {
                    r2.neg_mut();
                    c2.neg_mut();
                }
            }
        } //while loop end

        // make sure R2 is positive
        if r2.sgn() < 0 {
            r2.neg_mut();
            c1.neg_mut();
            c2.neg_mut();
        }
    } //function end
}
