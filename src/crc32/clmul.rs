use crate::{
    table::{crc32_clmul_consts, ClMulConsts32},
    util::crc32,
    Algorithm, ClMul, Crc, Digest,
};

use super::{finalize, init};

use core::arch::x86_64::*;

impl Crc<ClMul<u32>> {
    pub const fn new(algorithm: &'static Algorithm<u32>) -> Self {
        Self {
            algorithm,
            table: crc32_clmul_consts(algorithm.width, algorithm.poly, algorithm.refin),
        }
    }

    pub fn checksum(&self, bytes: &[u8]) -> u32 {
        let mut crc = init(self.algorithm, self.algorithm.init);
        crc = self.update(crc, bytes);
        finalize(self.algorithm, crc)
    }

    fn update(&self, crc: u32, bytes: &[u8]) -> u32 {
        update_clmul(crc, self.algorithm, &self.table, bytes)
    }

    pub const fn digest(&self) -> Digest<ClMul<u32>> {
        self.digest_with_initial(self.algorithm.init)
    }

    /// Construct a `Digest` with a given initial value.
    ///
    /// This overrides the initial value specified by the algorithm.
    /// The effects of the algorithm's properties `refin` and `width`
    /// are applied to the custom initial value.
    pub const fn digest_with_initial(&self, initial: u32) -> Digest<ClMul<u32>> {
        let value = init(self.algorithm, initial);
        Digest::new(self, value)
    }
}

impl<'a> Digest<'a, ClMul<u32>> {
    const fn new(crc: &'a Crc<ClMul<u32>>, value: u32) -> Self {
        Digest { crc, value }
    }

    pub fn update(&mut self, bytes: &[u8]) {
        self.value = self.crc.update(self.value, bytes);
    }

    pub const fn finalize(self) -> u32 {
        finalize(self.crc.algorithm, self.value)
    }
}

fn update_clmul(
    mut crc: u32,
    algorithm: &Algorithm<u32>,
    consts: &ClMulConsts32,
    bytes: &[u8],
) -> u32 {
    let mut i = 0;
    let mut accu: __m128i;
    let k_128: __m128i;
    let k_192: __m128i;
    let k_96: __m128i;
    let k_64: __m128i;
    let flip_bytes: __m128i =
        unsafe { _mm_set_epi32(0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F) };
    if algorithm.refin {
        while i < bytes.len() {
            panic!("Reflected is for later");
        }
    } else {
        while i < bytes.len() && unsafe { bytes.as_ptr().add(i) as usize % 16 != 0 } {
            let to_crc = ((crc >> 24) ^ bytes[i] as u32) & 0xFF;
            crc = crc32(algorithm.poly, algorithm.refin, to_crc) ^ (crc << 8);
            i += 1;
        }
        if bytes.len() - i >= 16 {
            unsafe {
                k_128 = _mm_set_epi64x(0, consts.k_128 as _);
                k_192 = _mm_set_epi64x(0, consts.k_192 as _);
                k_96 = _mm_set_epi64x(0, consts.k_96 as _);
                k_64 = _mm_set_epi64x(0, consts.k_64 as _);
            }
            
            unsafe {
                let next = _mm_load_si128(bytes.as_ptr().add(i).cast());
                let next = _mm_shuffle_epi8(next, flip_bytes);
                accu = _mm_xor_si128(next, _mm_set_epi32(crc as i32, 0, 0, 0));
                i += 16;
            }

            while i + 16 < bytes.len() {
                unsafe {
                    let clmul_hi = _mm_clmulepi64_si128(accu, k_192, 0x01);
                    let clmul_lo = _mm_clmulepi64_si128(accu, k_128, 0x00);
                    let next = _mm_load_si128(bytes.as_ptr().add(i).cast());
                    i += 16;
                    accu = _mm_xor_si128(clmul_lo, clmul_hi);
                    let next = _mm_shuffle_epi8(next, flip_bytes);
                    accu = _mm_xor_si128(accu, next);
                }
            }

            unsafe {
                // Reduce upper 64 down to 96
                let clmul = _mm_clmulepi64_si128(accu, k_96, 0x01);
                // shift in 4 zeroes
                accu = _mm_slli_si128::<4>(accu);
                // clear upper 32 bits
                accu = _mm_and_si128(accu, _mm_set_epi32(0, u32::MAX as _, u32::MAX as _, 0));
                accu = _mm_xor_si128(accu, clmul);

                // Reduce upper 32 down to 64
                let clmul = _mm_clmulepi64_si128(accu, k_64, 0x01);
                accu = _mm_xor_si128(accu, clmul);
            }

            let accu: u64 = unsafe { _mm_extract_epi64(accu, 0) as u64 };
            crc = barret_reduce(accu, consts.px, consts.mu);
        }
        while i < bytes.len() {
            let to_crc = ((crc >> 24) ^ bytes[i] as u32) & 0xFF;
            crc = crc32(algorithm.poly, algorithm.refin, to_crc) ^ (crc << 8);
            i += 1;
        }
    }
    crc
}

/// Calc x^degree mod poly
pub(crate) const fn calc_k(mut degreee: usize, poly: u32) -> u32 {
    // First step always takes the polynom
    let mut result = poly;
    while degreee > 32 {
        degreee -= 1;
        if result & 0x80000000 != 0 {
            result = (result << 1) ^ poly;
        } else {
            result <<= 1;
        }
    }

    result
}

/// Calc x^64 / poly ignoring the residual
pub(crate) const fn calc_mu(poly: u32) -> u64 {
    // First step always takes the polynom
    let mut residual = poly;
    let mut result = 1;
    let mut degreee = 64;
    while degreee > 32 {
        degreee -= 1;
        result <<= 1;
        if residual & 0x80000000 != 0 {
            residual = (residual << 1) ^ poly;
            result |= 1;
        } else {
            residual <<= 1;
        }
    }

    result
}

/// The same a clmul but allows u64 as the second argument.
/// Note that this only allows operands that will not overflow the resulting u64
fn clmul_u64(a: u32, b: u64) -> u64 {
    if a == 0 || b == 0 {
        return 0;
    }
    unsafe {
        let res = _mm_clmulepi64_si128(
            _mm_set_epi32(0, 0, 0, a as i32),
            _mm_set_epi64x(0, b as i64),
            0x00,
        );
        _mm_extract_epi64(res, 0) as u64
    }
}

/// Calculates rx mod px
fn barret_reduce(rx: u64, px: u64, mu: u64) -> u32 {
    let t1 = clmul_u64((rx >> 32) as u32, mu);
    let t2 = clmul_u64((t1 >> 32) as u32, px);
    (rx ^ t2) as u32
}

#[cfg(test)]
mod test {
    use crate::crc32::{
        clmul::{calc_k, calc_mu, clmul_u64},
        update_nolookup,
    };
    use crc_catalog::Algorithm;

    use super::barret_reduce;

    #[test]
    fn test_calc_k() {
        let poly = 0x04C11DB7;
        assert_eq!(calc_k(64, poly), 0x490D678D);
        assert_eq!(calc_k(96, poly), 0xF200AA66);
        assert_eq!(calc_k(128, poly), 0xE8A45605);
        assert_eq!(calc_k(128 + 64, poly), 0xC5B9CD4C);
        assert_eq!(calc_k(128 * 4, poly), 0xE6228B11);
        assert_eq!(calc_k(128 * 4 + 64, poly), 0x8833794C);
    }

    #[test]
    fn test_barret_reduction() {
        pub const CRC_32_ISCSI_NONREFLEX: Algorithm<u32> = Algorithm {
            width: 32,
            poly: 0x1edc6f41,
            init: 0xffffffff,
            // This is the only flag that affects the optimized code path
            refin: false,
            refout: true,
            xorout: 0xffffffff,
            check: 0xe3069283,
            residue: 0xb798b438,
        };

        let poly = CRC_32_ISCSI_NONREFLEX.poly;
        let px = 1 << 32 | poly as u64;
        let rx = 0xFF_0F_F0_00_04_03_02_01;

        // add implied zeroes at the end of the message polynom
        let next_bytes = 0;
        let accu_hi = (rx >> 32) as u32;
        let clmul = clmul_u64(accu_hi, calc_k(64, poly) as u64);
        let to_barret_reduce = clmul ^ ((rx << 32) | next_bytes as u64);

        let barret = barret_reduce(to_barret_reduce, px, calc_mu(poly));
        let no_lookup = update_nolookup(0, &CRC_32_ISCSI_NONREFLEX, &rx.to_be_bytes());
        assert_eq!(barret, no_lookup);
    }

    #[test]
    fn test_calc_mu() {
        let poly = 0x04C11DB7;
        assert_eq!(calc_mu(poly), 0x104D101DF);
    }

    #[test]
    fn test_clmul_64() {
        assert_eq!(clmul_u64(0, 0), 0);
        assert_eq!(clmul_u64(1, 0), 0);
        assert_eq!(clmul_u64(0, 1), 0);
        assert_eq!(clmul_u64(1, 1), 1);
        assert_eq!(clmul_u64(1, 2), 2);
        assert_eq!(clmul_u64(0b11, 0b11), 0b101);
        assert_eq!(clmul_u64(0b1001, 0b11), 0b11011);
        assert_eq!(clmul_u64(0x1010, 0x1F0000000), 0x1F1F00000000);
    }
}
