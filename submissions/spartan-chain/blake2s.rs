//! BLAKE2s-256 (RFC 7693), unkeyed, 32-byte output: the contract's `blake2sDigest`
//! (`Contract/Hash/Blake2s.lean`), and the relation's hashes and oracle
//! (`Contract/Relation.lean`, `Contract/Certificate.lean`). Written fresh from the RFC.

pub const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

pub const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

#[inline(always)]
fn g(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(12);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(8);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(7);
}

/// The compression function `compress h m t f0 f1` (`f1 = 0`).
pub fn compress(h: &[u32; 8], m: &[u32; 16], t: u64, f0: u32) -> [u32; 8] {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    v[14] ^= f0;
    for s in SIGMA.iter() {
        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    let mut o = [0u32; 8];
    for i in 0..8 {
        o[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    o
}

/// The parameter-block-adjusted initial chaining value: `iv[0] ^= 0x01010020`.
pub fn h0() -> [u32; 8] {
    let mut h = IV;
    h[0] ^= 0x0101_0020;
    h
}

/// Streaming BLAKE2s-256.
#[derive(Clone)]
pub struct Blake2s {
    h: [u32; 8],
    buf: [u8; 64],
    len: usize,
    t: u64,
}

impl Default for Blake2s {
    fn default() -> Self {
        Self::new()
    }
}

impl Blake2s {
    pub fn new() -> Self {
        Blake2s { h: h0(), buf: [0; 64], len: 0, t: 0 }
    }
    fn block(&mut self, last: bool) {
        let mut m = [0u32; 16];
        for i in 0..16 {
            m[i] = u32::from_le_bytes(self.buf[4 * i..4 * i + 4].try_into().unwrap());
        }
        self.h = compress(&self.h, &m, self.t, if last { 0xFFFF_FFFF } else { 0 });
    }
    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.len == 64 {
                // a full buffer is compressed only when more data follows
                self.t += 64;
                self.block(false);
                self.len = 0;
            }
            let k = (64 - self.len).min(data.len());
            self.buf[self.len..self.len + k].copy_from_slice(&data[..k]);
            self.len += k;
            data = &data[k..];
        }
        self
    }
    pub fn finalize(&mut self) -> [u8; 32] {
        self.t += self.len as u64;
        for b in self.buf[self.len..].iter_mut() {
            *b = 0;
        }
        self.block(true);
        let mut o = [0u8; 32];
        for i in 0..8 {
            o[4 * i..4 * i + 4].copy_from_slice(&self.h[i].to_le_bytes());
        }
        o
    }
}

pub fn blake2s256(data: &[u8]) -> [u8; 32] {
    Blake2s::new().update(data).finalize()
}

pub type Digest = [u8; 32];

pub const TAG_CHAIN: u8 = 0x43;
pub const TAG_LEAF: u8 = 0x4C;
pub const TAG_NODE: u8 = 0x4E;
pub const TAG_RO: u8 = 0x52;

pub fn chain_step(d: &Digest) -> Digest {
    Blake2s::new().update(&[TAG_CHAIN]).update(d).finalize()
}

pub fn chain_end(s: &Digest, n: u64) -> Digest {
    let mut h = *s;
    for _ in 0..n {
        h = chain_step(&h);
    }
    h
}

pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    Blake2s::new().update(&[TAG_LEAF]).update(h).update(&n.to_le_bytes()).finalize()
}

pub fn node_stmt(c1: &Digest, c2: &Digest) -> Digest {
    Blake2s::new().update(&[TAG_NODE]).update(c1).update(c2).finalize()
}

/// The oracle `H(q) = blake2s256(0x52 ‖ q)`, with `q` given in pieces.
pub fn oracle(parts: &[&[u8]]) -> Digest {
    let mut st = Blake2s::new();
    st.update(&[TAG_RO]);
    for p in parts {
        st.update(p);
    }
    st.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }
    #[test]
    fn rfc_vectors() {
        assert_eq!(
            hex(&blake2s256(b"")),
            "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
        );
        assert_eq!(
            hex(&blake2s256(b"abc")),
            "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
        );
        // streaming across block boundaries agrees with one-shot
        let data: Vec<u8> = (0..300u32).map(|i| (i * 7 + 3) as u8).collect();
        for cut in [0, 1, 63, 64, 65, 128, 200, 300] {
            let mut st = Blake2s::new();
            st.update(&data[..cut]).update(&data[cut..]);
            assert_eq!(st.finalize(), blake2s256(&data));
        }
        let mut st = Blake2s::new();
        for b in &data[..128] {
            st.update(&[*b]);
        }
        assert_eq!(st.finalize(), blake2s256(&data[..128]));
    }
}
