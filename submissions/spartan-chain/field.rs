//! The fields (BLUEPRINT-R1, notation): `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` (CompPoly's
//! `BF64`, leanVM's `F64`, `R64 = 0x1B`), bit `i` of the word is the coefficient of `x^i`; and
//! `E = K[y]/(y^3 + y + 1)` (CompPoly's `Ext3`, leanVM's `F192`), limbs `c0 + c1 y + c2 y^2`.
//!
//! Conventions follow leanVM `crates/primitives/src/field/{gf2_64,gf2_64x3}.rs` (pin `a386121f`,
//! MIT/Apache-2.0, itself credited to binius64): same modulus, same limb order, Karatsuba for `E`.
//! The code is written fresh: this machine has no carry-less multiply instruction, so the product
//! is a 4-bit windowed shift-and-add, and products by a fixed scalar go through byte tables
//! (`KTab`, `ETab`), as recommended by notes/E3 §0.

use std::ops::{Add, AddAssign, Mul, MulAssign};

/// `x^64 = x^4 + x^3 + x + 1` in `K`.
pub const R64: u64 = 0x1B;

/// Carry-less product of two 64-bit words (128-bit result), 4-bit windows.
#[inline(always)]
pub fn clmul(a: u64, b: u64) -> u128 {
    let a = a as u128;
    let mut t = [0u128; 16];
    t[1] = a;
    t[2] = a << 1;
    t[3] = t[2] ^ a;
    t[4] = a << 2;
    t[5] = t[4] ^ a;
    t[6] = t[4] ^ t[2];
    t[7] = t[6] ^ a;
    t[8] = a << 3;
    t[9] = t[8] ^ a;
    t[10] = t[8] ^ t[2];
    t[11] = t[10] ^ a;
    t[12] = t[8] ^ t[4];
    t[13] = t[12] ^ a;
    t[14] = t[12] ^ t[2];
    t[15] = t[14] ^ a;
    let mut r: u128 = 0;
    let mut i = 60i32;
    while i >= 0 {
        r = (r << 4) ^ t[((b >> i) & 15) as usize];
        i -= 4;
    }
    r
}

/// Reduce a 128-bit polynomial modulo `x^64 + x^4 + x^3 + x + 1`.
#[inline(always)]
pub fn reduce(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64 as u128;
    let t = hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4);
    let o = (t >> 64) as u64;
    lo ^ (t as u64) ^ o ^ (o << 1) ^ (o << 3) ^ (o << 4)
}

#[inline(always)]
fn spread32(x: u32) -> u64 {
    let mut x = x as u64;
    x = (x | (x << 16)) & 0x0000_FFFF_0000_FFFF;
    x = (x | (x << 8)) & 0x00FF_00FF_00FF_00FF;
    x = (x | (x << 4)) & 0x0F0F_0F0F_0F0F_0F0F;
    x = (x | (x << 2)) & 0x3333_3333_3333_3333;
    x = (x | (x << 1)) & 0x5555_5555_5555_5555;
    x
}

/// An element of `K`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct K(pub u64);

impl K {
    pub const ZERO: K = K(0);
    pub const ONE: K = K(1);
    /// The generator `x`.
    pub const X: K = K(2);
    #[inline(always)]
    pub fn sq(self) -> K {
        let lo = spread32(self.0 as u32) as u128;
        let hi = spread32((self.0 >> 32) as u32) as u128;
        K(reduce(lo | (hi << 64)))
    }
    pub fn pow(self, mut e: u128) -> K {
        let mut b = self;
        let mut r = K::ONE;
        while e > 0 {
            if e & 1 == 1 {
                r = r * b;
            }
            b = b.sq();
            e >>= 1;
        }
        r
    }
    pub fn to_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }
    pub fn from_bytes(b: &[u8]) -> K {
        K(u64::from_le_bytes(b[..8].try_into().unwrap()))
    }
}

impl Add for K {
    type Output = K;
    #[inline(always)]
    fn add(self, o: K) -> K {
        K(self.0 ^ o.0)
    }
}
impl AddAssign for K {
    #[inline(always)]
    fn add_assign(&mut self, o: K) {
        self.0 ^= o.0;
    }
}
impl Mul for K {
    type Output = K;
    #[inline(always)]
    fn mul(self, o: K) -> K {
        K(reduce(clmul(self.0, o.0)))
    }
}
impl MulAssign for K {
    #[inline(always)]
    fn mul_assign(&mut self, o: K) {
        *self = *self * o;
    }
}

/// An element `c[0] + c[1] y + c[2] y^2` of `E`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct E(pub [u64; 3]);

impl E {
    pub const ZERO: E = E([0, 0, 0]);
    pub const ONE: E = E([1, 0, 0]);
    pub const Y: E = E([0, 1, 0]);
    #[inline(always)]
    pub fn from_k(k: K) -> E {
        E([k.0, 0, 0])
    }
    #[inline(always)]
    pub fn from_bit(b: bool) -> E {
        E([b as u64, 0, 0])
    }
    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        (self.0[0] | self.0[1] | self.0[2]) == 0
    }
    /// `a^2` (the Frobenius): `a0^2 + a2^2 y + (a1^2 + a2^2) y^2`.
    #[inline(always)]
    pub fn sq(self) -> E {
        let a0 = K(self.0[0]).sq().0;
        let a1 = K(self.0[1]).sq().0;
        let a2 = K(self.0[2]).sq().0;
        E([a0, a2, a1 ^ a2])
    }
    /// `a^(2^k)`, `k` squarings.
    pub fn frob(self, k: usize) -> E {
        let mut a = self;
        for _ in 0..k {
            a = a.sq();
        }
        a
    }
    /// `a · k` for `k ∈ K` (three `K` products).
    #[inline(always)]
    pub fn mul_k(self, k: K) -> E {
        E([
            reduce(clmul(self.0[0], k.0)),
            reduce(clmul(self.0[1], k.0)),
            reduce(clmul(self.0[2], k.0)),
        ])
    }
    pub fn pow(self, mut e: u128) -> E {
        let mut b = self;
        let mut r = E::ONE;
        while e > 0 {
            if e & 1 == 1 {
                r = r * b;
            }
            b = b.sq();
            e >>= 1;
        }
        r
    }
    /// The 24 bytes `c0 ‖ c1 ‖ c2`, each 8 little-endian bytes (BLUEPRINT-R1 §7).
    pub fn to_bytes(self) -> [u8; 24] {
        let mut o = [0u8; 24];
        for i in 0..3 {
            o[8 * i..8 * i + 8].copy_from_slice(&self.0[i].to_le_bytes());
        }
        o
    }
    pub fn from_bytes(b: &[u8]) -> E {
        let w = |i: usize| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
        E([w(0), w(1), w(2)])
    }
}

impl Add for E {
    type Output = E;
    #[inline(always)]
    fn add(self, o: E) -> E {
        E([self.0[0] ^ o.0[0], self.0[1] ^ o.0[1], self.0[2] ^ o.0[2]])
    }
}
impl AddAssign for E {
    #[inline(always)]
    fn add_assign(&mut self, o: E) {
        self.0[0] ^= o.0[0];
        self.0[1] ^= o.0[1];
        self.0[2] ^= o.0[2];
    }
}
impl Mul for E {
    type Output = E;
    /// Karatsuba: six carry-less products, then `y^3 = y + 1`, `y^4 = y^2 + y`.
    #[inline(always)]
    fn mul(self, o: E) -> E {
        let [a0, a1, a2] = self.0;
        let [b0, b1, b2] = o.0;
        let p0 = clmul(a0, b0);
        let p1 = clmul(a1, b1);
        let p2 = clmul(a2, b2);
        let p01 = clmul(a0 ^ a1, b0 ^ b1);
        let p02 = clmul(a0 ^ a2, b0 ^ b2);
        let p12 = clmul(a1 ^ a2, b1 ^ b2);
        let c0 = p0;
        let c1 = p01 ^ p0 ^ p1;
        let c2 = p02 ^ p0 ^ p2 ^ p1;
        let c3 = p12 ^ p1 ^ p2;
        let c4 = p2;
        E([reduce(c0 ^ c3), reduce(c1 ^ c3 ^ c4), reduce(c2 ^ c4)])
    }
}
impl MulAssign for E {
    #[inline(always)]
    fn mul_assign(&mut self, o: E) {
        *self = *self * o;
    }
}

/// Multiplication by a fixed `K` element through eight 256-entry byte tables.
pub struct KTab {
    t: Box<[[u64; 256]; 8]>,
}

impl KTab {
    pub fn new(a: K) -> KTab {
        let mut t = Box::new([[0u64; 256]; 8]);
        let mut base = a.0; // a · x^(8i)
        for i in 0..8 {
            let mut pw = [0u64; 8];
            let mut cur = base;
            for b in 0..8 {
                pw[b] = cur;
                cur = reduce((cur as u128) << 1);
            }
            for v in 1..256usize {
                let low = v.trailing_zeros() as usize;
                t[i][v] = t[i][v & (v - 1)] ^ pw[low];
            }
            base = reduce((base as u128) << 8);
        }
        KTab { t }
    }
    #[inline(always)]
    pub fn mul(&self, b: u64) -> u64 {
        let t = &self.t;
        t[0][(b & 255) as usize]
            ^ t[1][((b >> 8) & 255) as usize]
            ^ t[2][((b >> 16) & 255) as usize]
            ^ t[3][((b >> 24) & 255) as usize]
            ^ t[4][((b >> 32) & 255) as usize]
            ^ t[5][((b >> 40) & 255) as usize]
            ^ t[6][((b >> 48) & 255) as usize]
            ^ t[7][((b >> 56) & 255) as usize]
    }
}

/// Multiplication of `E` elements by a fixed `E` element `r`: `a·r = a0·r + a1·(r y) + a2·(r y^2)`,
/// each `K × E` product through byte tables of `E` values.
pub struct ETab {
    t: Vec<[u64; 3]>, // [limb c][byte position i][byte v] -> E
}

impl ETab {
    pub fn new(r: E) -> ETab {
        let ry = r * E::Y;
        let ry2 = ry * E::Y;
        let mults = [r, ry, ry2];
        let mut t = vec![[0u64; 3]; 3 * 8 * 256];
        for c in 0..3 {
            for coord in 0..3 {
                let kt = KTab::new(K(mults[c].0[coord]));
                for i in 0..8 {
                    for v in 0..256usize {
                        t[(c * 8 + i) * 256 + v][coord] = kt.t[i][v];
                    }
                }
            }
        }
        ETab { t }
    }
    #[inline(always)]
    pub fn mul(&self, a: E) -> E {
        let mut r = [0u64; 3];
        for c in 0..3 {
            let w = a.0[c];
            let base = c * 8 * 256;
            for i in 0..8 {
                let e = &self.t[base + i * 256 + ((w >> (8 * i)) & 255) as usize];
                r[0] ^= e[0];
                r[1] ^= e[1];
                r[2] ^= e[2];
            }
        }
        E(r)
    }
}

/// Field challenge from an oracle answer (BLUEPRINT-R1 §6.1): `E.ofBytes(a[0..24))`.
pub fn ch_e(a: &[u8; 32]) -> E {
    E::from_bytes(&a[..24])
}

pub fn hex_k(k: K) -> String {
    format!("{:016x}", k.0)
}
pub fn hex_e(e: E) -> String {
    format!("{:016x}.{:016x}.{:016x}", e.0[0], e.0[1], e.0[2])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn naive_mul(a: u64, b: u64) -> u64 {
        let mut r: u128 = 0;
        for i in 0..64 {
            if (b >> i) & 1 == 1 {
                r ^= (a as u128) << i;
            }
        }
        for i in (64..128).rev() {
            if (r >> i) & 1 == 1 {
                r ^= ((R64 as u128) | (1u128 << 64)) << (i - 64);
            }
        }
        r as u64
    }

    #[test]
    fn k_mul_matches_naive() {
        let mut s = 0x1234_5678_9abc_def0u64;
        for _ in 0..2000 {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let a = s;
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let b = s;
            assert_eq!((K(a) * K(b)).0, naive_mul(a, b));
            assert_eq!(K(a).sq().0, naive_mul(a, a));
            assert_eq!(KTab::new(K(a)).mul(b), naive_mul(a, b));
        }
        // x^64 = x^4 + x^3 + x + 1
        assert_eq!(K::X.pow(64).0, R64);
    }

    #[test]
    fn e_field_laws() {
        let mut s = 7u64;
        let mut nx = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        // y^3 = y + 1
        assert_eq!(E::Y * E::Y * E::Y, E([1, 1, 0]));
        for _ in 0..500 {
            let a = E([nx(), nx(), nx()]);
            let b = E([nx(), nx(), nx()]);
            let c = E([nx(), nx(), nx()]);
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a.sq(), a * a);
            assert_eq!(ETab::new(b).mul(a), a * b);
            let k = K(nx());
            assert_eq!(a.mul_k(k), a * E::from_k(k));
        }
        // |E| - 1 = 2^192 - 1 divides; a^(2^192) = a: frob 192 is the identity
        let a = E([nx(), nx(), nx()]);
        assert_eq!(a.frob(192), a);
        assert_ne!(a.frob(64), a);
    }
}
