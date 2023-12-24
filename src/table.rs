use crate::util::*;

pub(crate) const fn crc8_table(width: u8, poly: u8, reflect: bool) -> [u8; 256] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (8u8 - width)
    } else {
        poly << (8u8 - width)
    };

    let mut table = [0u8; 256];
    let mut i = 0;
    while i < table.len() {
        table[i] = crc8(poly, reflect, i as u8);
        i += 1;
    }
    table
}

pub(crate) const fn crc8_table_slice_16(width: u8, poly: u8, reflect: bool) -> [[u8; 256]; 16] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (8u8 - width)
    } else {
        poly << (8u8 - width)
    };

    let mut table = [[0u8; 256]; 16];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc8(poly, reflect, i as u8);
        i += 1;
    }

    let mut i = 0;
    while i < 256 {
        let mut e = 1;
        while e < 16 {
            let one_lower = table[e - 1][i];
            table[e][i] = table[0][one_lower as usize];
            e += 1;
        }
        i += 1;
    }
    table
}

pub(crate) const fn crc16_table(width: u8, poly: u16, reflect: bool) -> [u16; 256] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (16u8 - width)
    } else {
        poly << (16u8 - width)
    };

    let mut table = [0u16; 256];
    let mut i = 0;
    while i < table.len() {
        table[i] = crc16(poly, reflect, i as u16);
        i += 1;
    }
    table
}

pub(crate) const fn crc16_table_slice_16(width: u8, poly: u16, reflect: bool) -> [[u16; 256]; 16] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (16u8 - width)
    } else {
        poly << (16u8 - width)
    };

    let mut table = [[0u16; 256]; 16];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc16(poly, reflect, i as u16);
        i += 1;
    }

    let mut i = 0;
    while i < 256 {
        let mut e = 1;
        while e < 16 {
            let one_lower = table[e - 1][i];
            if reflect {
                table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xFF) as usize];
            } else {
                table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 8) & 0xFF) as usize];
            }
            e += 1;
        }
        i += 1;
    }
    table
}

pub(crate) const fn crc32_table(width: u8, poly: u32, reflect: bool) -> [u32; 256] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (32u8 - width)
    } else {
        poly << (32u8 - width)
    };

    let mut table = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        table[i] = crc32(poly, reflect, i as u32);
        i += 1;
    }

    table
}

pub(crate) const fn crc32_table_slice_16(width: u8, poly: u32, reflect: bool) -> [[u32; 256]; 16] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (32u8 - width)
    } else {
        poly << (32u8 - width)
    };

    let mut table = [[0u32; 256]; 16];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc32(poly, reflect, i as u32);
        i += 1;
    }

    let mut i = 0;
    while i < 256 {
        let mut e = 1;
        while e < 16 {
            let one_lower = table[e - 1][i];
            if reflect {
                table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xFF) as usize];
            } else {
                table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 24) & 0xFF) as usize];
            }
            e += 1;
        }
        i += 1;
    }
    table
}

pub struct ClMulConsts32 {
    pub k_64: u32,
    pub k_96: u32,
    pub k_128: u32,
    pub k_192: u32,
    pub px: u64,
    pub mu: u64,
}
pub(crate) const fn crc32_clmul_consts(width: u8, poly: u32, reflect: bool) -> ClMulConsts32 {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (32u8 - width)
    } else {
        poly << (32u8 - width)
    };

    use crate::crc32::clmul::{calc_k, calc_mu};
    ClMulConsts32 {
        k_64: calc_k(64, poly),
        k_96: calc_k(96, poly),
        k_128: calc_k(128, poly),
        k_192: calc_k(192, poly),
        mu: calc_mu(poly),
        px: poly as u64 | 1 << 32,
    }
}

pub(crate) const fn crc64_table(width: u8, poly: u64, reflect: bool) -> [u64; 256] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (64u8 - width)
    } else {
        poly << (64u8 - width)
    };

    let mut table = [0u64; 256];
    let mut i = 0;
    while i < table.len() {
        table[i] = crc64(poly, reflect, i as u64);
        i += 1;
    }
    table
}

pub(crate) const fn crc64_table_slice_16(width: u8, poly: u64, reflect: bool) -> [[u64; 256]; 16] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (64u8 - width)
    } else {
        poly << (64u8 - width)
    };

    let mut table = [[0u64; 256]; 16];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc64(poly, reflect, i as u64);
        i += 1;
    }

    let mut i = 0;
    while i < 256 {
        let mut e = 1;
        while e < 16 {
            let one_lower = table[e - 1][i];
            if reflect {
                table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xFF) as usize];
            } else {
                table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 56) & 0xFF) as usize];
            }
            e += 1;
        }
        i += 1;
    }
    table
}

pub(crate) const fn crc128_table(width: u8, poly: u128, reflect: bool) -> [u128; 256] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (128u8 - width)
    } else {
        poly << (128u8 - width)
    };

    let mut table = [0u128; 256];
    let mut i = 0;
    while i < table.len() {
        table[i] = crc128(poly, reflect, i as u128);
        i += 1;
    }
    table
}

pub(crate) const fn crc128_table_slice_16(
    width: u8,
    poly: u128,
    reflect: bool,
) -> [[u128; 256]; 16] {
    let poly = if reflect {
        let poly = poly.reverse_bits();
        poly >> (128u8 - width)
    } else {
        poly << (128u8 - width)
    };

    let mut table = [[0u128; 256]; 16];
    let mut i = 0;
    while i < 256 {
        table[0][i] = crc128(poly, reflect, i as u128);
        i += 1;
    }

    let mut i = 0;
    while i < 256 {
        let mut e = 1;
        while e < 16 {
            let one_lower = table[e - 1][i];
            if reflect {
                table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xFF) as usize];
            } else {
                table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 120) & 0xFF) as usize];
            }
            e += 1;
        }
        i += 1;
    }
    table
}
