//! Reusable memory context for solving linear congruences.
use super::mpz::Mpz;

#[derive(Clone)]
pub struct LinCongruenceCtx {
    pub inner: (Mpz, Mpz, Mpz, Mpz),
}

impl Default for LinCongruenceCtx {
    fn default() -> Self {
        Self {
            inner: (
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
                Mpz::default(),
            ),
        }
    }
}

impl LinCongruenceCtx {
    #[inline]
    pub fn solve_linear_congruence(
        &mut self,
        mu: &mut Mpz,
        v: &mut Mpz,
        a: &Mpz,
        b: &Mpz,
        m: &Mpz,
    ) -> Option<()> {
        let (g, d, e, q) = &mut self.inner;

        // Binary Quadratic Forms, 7.4.1
        g.gcdext(d, e, a, m);
        q.divexact(b, &g);

        mu.mul(&q, &d);
        mu.modulo_mut(m);
        v.divexact(m, &g);
        Some(())
    }
}
