use std::eprintln;

use crate::util::crc32;
use crc_catalog::Algorithm;

mod bytewise;
mod clmul;
mod default;
mod nolookup;
mod slice16;

// init is shared between all impls
const fn init(algorithm: &Algorithm<u32>, initial: u32) -> u32 {
    if algorithm.refin {
        initial.reverse_bits() >> (32u8 - algorithm.width)
    } else {
        initial << (32u8 - algorithm.width)
    }
}

// finalize is shared between all impls
const fn finalize(algorithm: &Algorithm<u32>, mut crc: u32) -> u32 {
    if algorithm.refin ^ algorithm.refout {
        crc = crc.reverse_bits();
    }
    if !algorithm.refout {
        crc >>= 32u8 - algorithm.width;
    }
    crc ^ algorithm.xorout
}

const fn update_nolookup(mut crc: u32, algorithm: &Algorithm<u32>, bytes: &[u8]) -> u32 {
    let poly = if algorithm.refin {
        let poly = algorithm.poly.reverse_bits();
        poly >> (32u8 - algorithm.width)
    } else {
        algorithm.poly << (32u8 - algorithm.width)
    };

    let mut i = 0;
    if algorithm.refin {
        while i < bytes.len() {
            let to_crc = (crc ^ bytes[i] as u32) & 0xFF;
            crc = crc32(poly, algorithm.refin, to_crc) ^ (crc >> 8);
            i += 1;
        }
    } else {
        while i < bytes.len() {
            let to_crc = ((crc >> 24) ^ bytes[i] as u32) & 0xFF;
            crc = crc32(poly, algorithm.refin, to_crc) ^ (crc << 8);
            i += 1;
        }
    }
    crc
}

fn update_clmul(mut crc: u32, algorithm: &Algorithm<u32>, bytes: &[u8]) -> u32 {
    let mut i = 0;
    let mut accu;
    if algorithm.refin {
        while i < bytes.len() {
            panic!("Reflected is for later");
        }
    } else {
        let k = calc_k(64, algorithm.poly);
        if bytes.len() >= 8 {
            accu = u64::from_le_bytes([
                bytes[i],
                bytes[i + 1],
                bytes[i + 2],
                bytes[i + 3],
                bytes[i + 4],
                bytes[i + 5],
                bytes[i + 6],
                bytes[i + 7],
            ]);
            i = 8;
            while i + 4 < bytes.len() {
                let next_bytes =
                    u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
                i += 4;
                let accu_hi = (accu >> 32) as u32;
                let clmul = clmul(accu_hi, k);
                accu = clmul ^ ((accu << 32) | next_bytes as u64);
            }
            let px = (1 << 32) | (algorithm.poly as u64);
            let mu = calc_mu(algorithm.poly);
            crc = barret_reduce(accu, px, mu);
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
const fn calc_k(mut degreee: usize, poly: u32) -> u32 {
    // First step always takes the polynom
    let mut result = poly;
    while degreee > 32 {
        degreee -= 1;
        if result & 0x80000000 != 0 {
            result = (result << 1) ^ poly;
        } else {
            result = result << 1;
        }
    }

    result
}

// Calc x^64 / poly ignoring the residual
const fn calc_mu(poly: u32) -> u64 {
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

const fn clmul(a: u32, b: u32) -> u64 {
    let a = a as u64;
    let b = b as u64;
    let mut res = 0;

    let mut idx = 0;
    while idx < 32 {
        if (a >> idx) & 0x1 == 1 {
            res ^= b << idx;
        }
        idx += 1;
    }
    res
}

/// make sure that the bits used in a and b do not exceed 64
const fn clmul_u64(a: u32, b: u64) -> u64 {
    let bits_a = 32 - a.leading_zeros();
    let bits_b = 64 - b.leading_zeros();
    debug_assert!(bits_a + bits_b <= 64);
    let a = a as u64;
    let b = b as u64;
    let mut res = 0;

    let mut idx = 0;
    while idx < 32 {
        if (a >> idx) & 0x1 == 1 {
            res ^= b << idx;
        }
        idx += 1;
    }
    res
}

fn barret_reduce(rx: u64, px: u64, mu: u64) -> u32 {
    eprintln!("R {rx:X} P {px:X} M {mu:X}");
    eprintln!("R >> 32 {:X}", rx >> 32);
    let t1 = clmul_u64((rx >> 32) as u32, mu);
    eprintln!("T1 {t1:X}");
    eprintln!("T1 >> 32 {:X}", t1 >> 32);
    let t2 = clmul_u64((t1 >> 32) as u32, px);
    (rx ^ t2) as u32
}

const fn update_bytewise(mut crc: u32, reflect: bool, table: &[u32; 256], bytes: &[u8]) -> u32 {
    let mut i = 0;
    if reflect {
        while i < bytes.len() {
            let table_index = ((crc ^ bytes[i] as u32) & 0xFF) as usize;
            crc = table[table_index] ^ (crc >> 8);
            i += 1;
        }
    } else {
        while i < bytes.len() {
            let table_index = (((crc >> 24) ^ bytes[i] as u32) & 0xFF) as usize;
            crc = table[table_index] ^ (crc << 8);
            i += 1;
        }
    }
    crc
}

const fn update_slice16(
    mut crc: u32,
    reflect: bool,
    table: &[[u32; 256]; 16],
    bytes: &[u8],
) -> u32 {
    let mut i = 0;
    if reflect {
        while i + 16 <= bytes.len() {
            let mut current_slice = [bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]];

            current_slice[0] ^= crc as u8;
            current_slice[1] ^= (crc >> 8) as u8;
            current_slice[2] ^= (crc >> 16) as u8;
            current_slice[3] ^= (crc >> 24) as u8;

            crc = table[0][bytes[i + 15] as usize]
                ^ table[1][bytes[i + 14] as usize]
                ^ table[2][bytes[i + 13] as usize]
                ^ table[3][bytes[i + 12] as usize]
                ^ table[4][bytes[i + 11] as usize]
                ^ table[5][bytes[i + 10] as usize]
                ^ table[6][bytes[i + 9] as usize]
                ^ table[7][bytes[i + 8] as usize]
                ^ table[8][bytes[i + 7] as usize]
                ^ table[9][bytes[i + 6] as usize]
                ^ table[10][bytes[i + 5] as usize]
                ^ table[11][bytes[i + 4] as usize]
                ^ table[12][current_slice[3] as usize]
                ^ table[13][current_slice[2] as usize]
                ^ table[14][current_slice[1] as usize]
                ^ table[15][current_slice[0] as usize];

            i += 16;
        }

        // Last few bytes
        while i < bytes.len() {
            let table_index = ((crc ^ bytes[i] as u32) & 0xFF) as usize;
            crc = table[0][table_index] ^ (crc >> 8);
            i += 1;
        }
    } else {
        while i + 16 <= bytes.len() {
            let mut current_slice = [bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]];

            current_slice[0] ^= (crc >> 24) as u8;
            current_slice[1] ^= (crc >> 16) as u8;
            current_slice[2] ^= (crc >> 8) as u8;
            current_slice[3] ^= crc as u8;

            crc = table[0][bytes[i + 15] as usize]
                ^ table[1][bytes[i + 14] as usize]
                ^ table[2][bytes[i + 13] as usize]
                ^ table[3][bytes[i + 12] as usize]
                ^ table[4][bytes[i + 11] as usize]
                ^ table[5][bytes[i + 10] as usize]
                ^ table[6][bytes[i + 9] as usize]
                ^ table[7][bytes[i + 8] as usize]
                ^ table[8][bytes[i + 7] as usize]
                ^ table[9][bytes[i + 6] as usize]
                ^ table[10][bytes[i + 5] as usize]
                ^ table[11][bytes[i + 4] as usize]
                ^ table[12][current_slice[3] as usize]
                ^ table[13][current_slice[2] as usize]
                ^ table[14][current_slice[1] as usize]
                ^ table[15][current_slice[0] as usize];

            i += 16;
        }

        // Last few bytes
        while i < bytes.len() {
            let table_index = (((crc >> 24) ^ bytes[i] as u32) & 0xFF) as usize;
            crc = table[0][table_index] ^ (crc << 8);
            i += 1;
        }
    }
    crc
}

#[cfg(test)]
mod test {
    use crate::{
        crc32::{calc_k, calc_mu, clmul},
        Bytewise, ClMul, Crc, Implementation, NoTable, Slice16,
    };
    use crc_catalog::{Algorithm, CRC_32_ISCSI};

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
    fn test_calc_mu() {
        let poly = 0x04C11DB7;
        assert_eq!(calc_mu(poly), 0x104D101DF);
    }

    #[test]
    fn test_clmul() {
        assert_eq!(clmul(0, 0), 0);
        assert_eq!(clmul(1, 0), 0);
        assert_eq!(clmul(0, 1), 0);
        assert_eq!(clmul(1, 1), 1);
        assert_eq!(clmul(1, 2), 2);
        assert_eq!(clmul(0b11, 0b11), 0b101);
        assert_eq!(clmul(0b1001, 0b11), 0b11011);
        assert_eq!(clmul(0xF0000000, 0x1010), 0xF0F00000000);
    }

    #[test]
    fn default_table_size() {
        const TABLE_SIZE: usize = core::mem::size_of::<<u32 as Implementation>::Table>();
        const BYTES_PER_ENTRY: usize = 4;
        #[cfg(all(
            feature = "no-table-mem-limit",
            feature = "bytewise-mem-limit",
            feature = "slice16-mem-limit"
        ))]
        {
            const EXPECTED: usize = 0;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }
        #[cfg(all(
            feature = "no-table-mem-limit",
            feature = "bytewise-mem-limit",
            not(feature = "slice16-mem-limit")
        ))]
        {
            const EXPECTED: usize = 0;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }
        #[cfg(all(
            feature = "no-table-mem-limit",
            not(feature = "bytewise-mem-limit"),
            feature = "slice16-mem-limit"
        ))]
        {
            const EXPECTED: usize = 0;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }
        #[cfg(all(
            feature = "no-table-mem-limit",
            not(feature = "bytewise-mem-limit"),
            not(feature = "slice16-mem-limit")
        ))]
        {
            const EXPECTED: usize = 0;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }

        #[cfg(all(
            not(feature = "no-table-mem-limit"),
            feature = "bytewise-mem-limit",
            feature = "slice16-mem-limit"
        ))]
        {
            const EXPECTED: usize = 256 * BYTES_PER_ENTRY;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }
        #[cfg(all(
            not(feature = "no-table-mem-limit"),
            feature = "bytewise-mem-limit",
            not(feature = "slice16-mem-limit")
        ))]
        {
            const EXPECTED: usize = 256 * BYTES_PER_ENTRY;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }

        #[cfg(all(
            not(feature = "no-table-mem-limit"),
            not(feature = "bytewise-mem-limit"),
            feature = "slice16-mem-limit"
        ))]
        {
            const EXPECTED: usize = 256 * 16 * BYTES_PER_ENTRY;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }

        #[cfg(all(
            not(feature = "no-table-mem-limit"),
            not(feature = "bytewise-mem-limit"),
            not(feature = "slice16-mem-limit")
        ))]
        {
            const EXPECTED: usize = 256 * BYTES_PER_ENTRY;
            let _ = EXPECTED;
            const _: () = assert!(EXPECTED == TABLE_SIZE);
        }
        let _ = TABLE_SIZE;
        let _ = BYTES_PER_ENTRY;
    }

    /// Test this optimized version against the well known implementation to ensure correctness
    #[test]
    fn correctness() {
        let data: &[&str] = &[
        "",
        "1",
        "1234",
        "123456789",
        "0123456789ABCDE",
        "01234567890ABCDEFGHIJK",
        "01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK01234567890ABCDEFGHIJK",
    ];

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

        let algs_to_test = [&CRC_32_ISCSI_NONREFLEX];

        for alg in algs_to_test {
            for data in data {
                let crc_slice16 = Crc::<Slice16<u32>>::new(alg);
                let crc_nolookup = Crc::<NoTable<u32>>::new(alg);
                let crc_clmul = Crc::<ClMul<u32>>::new(alg);
                let expected = Crc::<Bytewise<u32>>::new(alg).checksum(data.as_bytes());

                // Check that doing all at once works as expected
                assert_eq!(crc_slice16.checksum(data.as_bytes()), expected);
                assert_eq!(crc_nolookup.checksum(data.as_bytes()), expected);
                assert_eq!(
                    crc_clmul.checksum(data.as_bytes()),
                    expected,
                    "Input: {:?}",
                    data
                );

                let mut digest = crc_slice16.digest();
                digest.update(data.as_bytes());
                assert_eq!(digest.finalize(), expected);

                let mut digest = crc_nolookup.digest();
                digest.update(data.as_bytes());
                assert_eq!(digest.finalize(), expected);

                // Check that we didn't break updating from multiple sources
                if data.len() > 2 {
                    let data = data.as_bytes();
                    let data1 = &data[..data.len() / 2];
                    let data2 = &data[data.len() / 2..];
                    let mut digest = crc_slice16.digest();
                    digest.update(data1);
                    digest.update(data2);
                    assert_eq!(digest.finalize(), expected);
                    let mut digest = crc_nolookup.digest();
                    digest.update(data1);
                    digest.update(data2);
                    assert_eq!(digest.finalize(), expected);
                }
            }
        }
    }
}
