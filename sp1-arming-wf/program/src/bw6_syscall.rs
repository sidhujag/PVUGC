//! BW6-761 arithmetic backed by SP1 precompile syscalls.
//!
//! Goal: avoid executing BW6 big-integer field arithmetic in the RV32 trace. Instead, represent
//! base-field elements as 24x u32 limbs (little-endian) and use SP1's `BW6761_FP_{ADD,SUB,MUL}`
//! precompiles for modular arithmetic.
//!
//! This module is intentionally minimal: it implements exactly what's needed by the arming
//! well-formedness guest:
//! - BW6-761 base field Fq (mod q) operations via syscalls
//! - Fq3 arithmetic where u^3 = -4
//! - Fq6 arithmetic where v^2 = u (Fp6_2over3 over the above Fq3)
//! - G2 Jacobian arithmetic for y^2 = x^3 + 4 over Fq3 (A=0, B=4)
//!
//! Soundness note: these syscalls are constrained by SP1 precompile AIR, i.e. using them does not
//! trust the host.

use ark_serialize::CanonicalSerialize;

use sp1_zkvm::syscalls::{
    syscall_bw6761_fp_addmod, syscall_bw6761_fp_mulmod, syscall_bw6761_fp_submod,
    syscall_bw6761_fq3_addmod, syscall_bw6761_fq3_mulmod, syscall_bw6761_fq3_submod,
    syscall_bw6761_fq6_mulmod, syscall_bw6761_fq6_squaremod, syscall_bw6761_g2_add,
    syscall_bw6761_g2_double,
};

/// # of 32-bit words for BW6-761 Fq (96 bytes = 24 u32 words).
pub const FQ_WORDS: usize = 24;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Fq(pub [u32; FQ_WORDS]);

impl Fq {
    #[inline(always)]
    pub fn zero() -> Self {
        Self([0u32; FQ_WORDS])
    }

    #[inline(always)]
    pub fn one() -> Self {
        let mut w = [0u32; FQ_WORDS];
        w[0] = 1;
        Self(w)
    }

    #[inline(always)]
    pub fn from_u32(x: u32) -> Self {
        let mut w = [0u32; FQ_WORDS];
        w[0] = x;
        Self(w)
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|&x| x == 0)
    }

    #[inline(always)]
    pub fn add_assign(&mut self, other: &Self) {
        syscall_bw6761_fp_addmod(self.0.as_mut_ptr(), other.0.as_ptr());
    }

    #[inline(always)]
    pub fn sub_assign(&mut self, other: &Self) {
        syscall_bw6761_fp_submod(self.0.as_mut_ptr(), other.0.as_ptr());
    }

    #[inline(always)]
    pub fn mul_assign(&mut self, other: &Self) {
        syscall_bw6761_fp_mulmod(self.0.as_mut_ptr(), other.0.as_ptr());
    }

    #[inline(always)]
    pub fn add(&self, other: &Self) -> Self {
        let mut t = *self;
        t.add_assign(other);
        t
    }

    #[inline(always)]
    pub fn sub(&self, other: &Self) -> Self {
        let mut t = *self;
        t.sub_assign(other);
        t
    }

    #[inline(always)]
    pub fn mul(&self, other: &Self) -> Self {
        let mut t = *self;
        t.mul_assign(other);
        t
    }

    #[inline(always)]
    pub fn neg(&self) -> Self {
        let mut z = Self::zero();
        z.sub_assign(self);
        z
    }

    #[inline(always)]
    pub fn double(&self) -> Self {
        let mut t = *self;
        t.add_assign(self);
        t
    }

    #[inline(always)]
    pub fn square(&self) -> Self {
        let mut t = *self;
        t.mul_assign(self);
        t
    }

    /// Multiply by -4 in Fq. (BW6 Fq3 NONRESIDUE = -4)
    #[inline(always)]
    pub fn mul_by_minus4(&self) -> Self {
        // -4*x = -(2*(2*x))
        let t = self.double().double();
        t.neg()
    }

    pub fn to_bytes_le(&self) -> [u8; 96] {
        let mut out = [0u8; 96];
        for i in 0..FQ_WORDS {
            out[i * 4..i * 4 + 4].copy_from_slice(&self.0[i].to_le_bytes());
        }
        out
    }

    pub fn from_ark<F: CanonicalSerialize>(x: &F) -> Self {
        let mut bytes = Vec::new();
        x.serialize_compressed(&mut bytes).expect("serialize field");
        assert_eq!(bytes.len(), 96, "BW6 Fq must serialize to 96 bytes");
        let mut words = [0u32; FQ_WORDS];
        for i in 0..FQ_WORDS {
            let j = i * 4;
            words[i] = u32::from_le_bytes(bytes[j..j + 4].try_into().unwrap());
        }
        Self(words)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Fq3 {
    pub c0: Fq,
    pub c1: Fq,
    pub c2: Fq,
}

impl Fq3 {
    #[inline(always)]
    pub fn zero() -> Self {
        Self { c0: Fq::zero(), c1: Fq::zero(), c2: Fq::zero() }
    }

    #[inline(always)]
    pub fn one() -> Self {
        Self { c0: Fq::one(), c1: Fq::zero(), c2: Fq::zero() }
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    #[inline(always)]
    pub fn add_assign(&mut self, other: &Self) {
        #[cfg(target_os = "zkvm")]
        {
            syscall_bw6761_fq3_addmod(self as *mut Self as *mut u32, other as *const Self as *const u32);
        }

        #[cfg(not(target_os = "zkvm"))]
        {
            self.c0.add_assign(&other.c0);
            self.c1.add_assign(&other.c1);
            self.c2.add_assign(&other.c2);
        }
    }

    #[inline(always)]
    pub fn sub_assign(&mut self, other: &Self) {
        #[cfg(target_os = "zkvm")]
        {
            syscall_bw6761_fq3_submod(self as *mut Self as *mut u32, other as *const Self as *const u32);
        }

        #[cfg(not(target_os = "zkvm"))]
        {
            self.c0.sub_assign(&other.c0);
            self.c1.sub_assign(&other.c1);
            self.c2.sub_assign(&other.c2);
        }
    }

    #[inline(always)]
    pub fn neg(&self) -> Self {
        Self { c0: self.c0.neg(), c1: self.c1.neg(), c2: self.c2.neg() }
    }

    /// Multiply by u where u^3 = -4 (Fq3 NONRESIDUE).
    #[inline(always)]
    pub fn mul_by_u(&self) -> Self {
        // (c0 + c1 u + c2 u^2) * u = c2 * u^3 + c0 u + c1 u^2
        // = (-4*c2) + c0 u + c1 u^2
        Self { c0: self.c2.mul_by_minus4(), c1: self.c0, c2: self.c1 }
    }

    #[inline(always)]
    pub fn mul(&self, other: &Self) -> Self {
        #[cfg(target_os = "zkvm")]
        {
            let mut t = *self;
            t.mul_assign(other);
            t
        }

        #[cfg(not(target_os = "zkvm"))]
        {
            self.mul_host(other)
        }
    }

    #[inline(always)]
    pub fn square(&self) -> Self {
        self.mul(self)
    }

    #[inline(always)]
    pub fn mul_assign(&mut self, other: &Self) {
        #[cfg(target_os = "zkvm")]
        {
            // Treat `self` and `other` as contiguous `[u32]` for the syscall ABI.
            syscall_bw6761_fq3_mulmod(self as *mut Self as *mut u32, other as *const Self as *const u32);
        }

        #[cfg(not(target_os = "zkvm"))]
        {
            *self = self.mul_host(other);
        }
    }

    #[cfg(not(target_os = "zkvm"))]
    fn mul_host(&self, other: &Self) -> Self {
        // Naive multiply with reduction using u^3 = -4.
        let a0 = self.c0;
        let a1 = self.c1;
        let a2 = self.c2;
        let b0 = other.c0;
        let b1 = other.c1;
        let b2 = other.c2;

        let mut a0b0 = a0;
        a0b0.mul_assign(&b0);
        let mut a0b1 = a0;
        a0b1.mul_assign(&b1);
        let mut a0b2 = a0;
        a0b2.mul_assign(&b2);
        let mut a1b0 = a1;
        a1b0.mul_assign(&b0);
        let mut a1b1 = a1;
        a1b1.mul_assign(&b1);
        let mut a1b2 = a1;
        a1b2.mul_assign(&b2);
        let mut a2b0 = a2;
        a2b0.mul_assign(&b0);
        let mut a2b1 = a2;
        a2b1.mul_assign(&b1);
        let mut a2b2 = a2;
        a2b2.mul_assign(&b2);

        let mut t = a1b2;
        t.add_assign(&a2b1);
        let t = t.mul_by_minus4();
        let mut c0 = a0b0;
        c0.add_assign(&t);

        let mut c1 = a0b1;
        c1.add_assign(&a1b0);
        let t = a2b2.mul_by_minus4();
        c1.add_assign(&t);

        let mut c2 = a0b2;
        c2.add_assign(&a1b1);
        c2.add_assign(&a2b0);

        Self { c0, c1, c2 }
    }

    pub fn from_ark_fq3<F0: CanonicalSerialize, F1: CanonicalSerialize, F2: CanonicalSerialize>(
        c0: &F0,
        c1: &F1,
        c2: &F2,
    ) -> Self {
        Self { c0: Fq::from_ark(c0), c1: Fq::from_ark(c1), c2: Fq::from_ark(c2) }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Fq6 {
    pub c0: Fq3,
    pub c1: Fq3,
}

impl Fq6 {
    #[inline(always)]
    pub fn zero() -> Self {
        Self { c0: Fq3::zero(), c1: Fq3::zero() }
    }

    #[inline(always)]
    pub fn one() -> Self {
        Self { c0: Fq3::one(), c1: Fq3::zero() }
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    #[inline(always)]
    pub fn is_one(&self) -> bool {
        self.c0 == Fq3::one() && self.c1.is_zero()
    }

    #[inline(always)]
    pub fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
    }

    #[inline(always)]
    pub fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
    }

    #[inline(always)]
    pub fn neg(&self) -> Self {
        Self { c0: self.c0.neg(), c1: self.c1.neg() }
    }

    /// Multiply by the quadratic nonresidue v^2 = u (where u = (0,1,0) in Fq3).
    #[inline(always)]
    fn mul_fp3_by_nonresidue(fe: &Fq3) -> Fq3 {
        fe.mul_by_u()
    }

    #[inline(always)]
    pub fn mul(&self, other: &Self) -> Self {
        #[cfg(target_os = "zkvm")]
        {
            let mut out = *self;
            syscall_bw6761_fq6_mulmod(&mut out as *mut Self as *mut u32, other as *const Self as *const u32);
            return out;
        }

        #[cfg(not(target_os = "zkvm"))]
        {
            // (a0 + a1 v)(b0 + b1 v) where v^2 = u.
            // Karatsuba:
            // t0 = a0*b0
            // t1 = a1*b1
            // c0 = t0 + nr*t1
            // c1 = (a0+a1)(b0+b1) - t0 - t1
            let a0 = self.c0;
            let a1 = self.c1;
            let b0 = other.c0;
            let b1 = other.c1;

            let t0 = a0.mul(&b0);
            let t1 = a1.mul(&b1);

            let mut c0 = t0;
            let nr_t1 = Self::mul_fp3_by_nonresidue(&t1);
            c0.add_assign(&nr_t1);

            let mut a0a1 = a0;
            a0a1.add_assign(&a1);
            let mut b0b1 = b0;
            b0b1.add_assign(&b1);

            let mut c1 = a0a1.mul(&b0b1);
            c1.sub_assign(&t0);
            c1.sub_assign(&t1);

            Self { c0, c1 }
        }
    }

    #[inline(always)]
    pub fn square(&self) -> Self {
        #[cfg(target_os = "zkvm")]
        {
            let mut out = *self;
            syscall_bw6761_fq6_squaremod(&mut out as *mut Self as *mut u32, core::ptr::null());
            return out;
        }

        #[cfg(not(target_os = "zkvm"))]
        self.mul(self)
    }

    pub fn to_bytes_le_vec(&self) -> Vec<u8> {
        // CanonicalSerialize for Fp6/Fp3/Fp is (c0.c0, c0.c1, c0.c2, c1.c0, c1.c1, c1.c2),
        // each as little-endian bytes for Fq (96 bytes).
        let mut out = Vec::with_capacity(6 * 96);
        out.extend_from_slice(&self.c0.c0.to_bytes_le());
        out.extend_from_slice(&self.c0.c1.to_bytes_le());
        out.extend_from_slice(&self.c0.c2.to_bytes_le());
        out.extend_from_slice(&self.c1.c0.to_bytes_le());
        out.extend_from_slice(&self.c1.c1.to_bytes_le());
        out.extend_from_slice(&self.c1.c2.to_bytes_le());
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2Jacobian {
    pub x: Fq,
    pub y: Fq,
    pub z: Fq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct G2Affine {
    pub x: Fq,
    pub y: Fq,
}

impl G2Affine {
    #[inline(always)]
    pub fn from_jacobian_assume_affine(p: &G2Jacobian) -> Self {
        debug_assert!(p.z == Fq::one(), "expected affine Jacobian input (z=1)");
        Self { x: p.x, y: p.y }
    }

    #[inline(always)]
    pub fn to_jacobian(&self) -> G2Jacobian {
        G2Jacobian::from_affine(self.x, self.y)
    }

    #[inline(always)]
    pub fn add_assign(&mut self, other: &Self) {
        syscall_bw6761_g2_add(self as *mut Self as *mut u32, other as *const Self as *const u32);
    }

    #[inline(always)]
    pub fn double_in_place(&mut self) {
        syscall_bw6761_g2_double(self as *mut Self as *mut u32);
    }
}

impl G2Jacobian {
    #[inline(always)]
    pub fn zero() -> Self {
        // Standard Jacobian infinity encoding: Z == 0.
        Self { x: Fq::zero(), y: Fq::one(), z: Fq::zero() }
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.z.is_zero()
    }

    #[inline(always)]
    pub fn from_affine(x: Fq, y: Fq) -> Self {
        Self { x, y, z: Fq::one() }
    }

    #[inline(always)]
    pub fn neg(&self) -> Self {
        if self.is_zero() {
            *self
        } else {
            Self { x: self.x, y: self.y.neg(), z: self.z }
        }
    }

    /// Point doubling for short Weierstrass curve with a=0.
    pub fn double_in_place(&mut self) {
        if self.is_zero() {
            return;
        }

        // Formula: http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        let a = self.x.square(); // A = X1^2
        let b = self.y.square(); // B = Y1^2
        let c = b.square(); // C = B^2

        // D = 2*((X1+B)^2 - A - C)
        let mut x1_plus_b = self.x;
        x1_plus_b.add_assign(&b);
        let mut d = x1_plus_b.square();
        d.sub_assign(&a);
        d.sub_assign(&c);
        d = d.add(&d);

        // E = 3*A
        let mut e = a;
        e = e.add(&a);
        e.add_assign(&a);

        // F = E^2
        let f = e.square();

        // X3 = F - 2*D
        let mut x3 = f;
        let two_d = d.add(&d);
        x3.sub_assign(&two_d);

        // Y3 = E*(D-X3) - 8*C
        let mut y3 = d;
        y3.sub_assign(&x3);
        y3 = e.mul(&y3);
        // 8*C = 2*(2*(2*C))
        let mut eight_c = c;
        eight_c = eight_c.add(&eight_c);
        eight_c = eight_c.add(&eight_c);
        eight_c = eight_c.add(&eight_c);
        y3.sub_assign(&eight_c);

        // Z3 = 2*Y1*Z1
        let mut z3 = self.y.mul(&self.z);
        z3 = z3.add(&z3);

        self.x = x3;
        self.y = y3;
        self.z = z3;
    }

    /// Full Jacobian addition (works for all inputs; not optimized).
    pub fn add_assign(&mut self, other: &Self) {
        if other.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = *other;
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
        let z1z1 = self.z.square();
        let z2z2 = other.z.square();

        let u1 = self.x.mul(&z2z2);
        let u2 = other.x.mul(&z1z1);

        let z2_cub = z2z2.mul(&other.z);
        let s1 = self.y.mul(&z2_cub);

        let z1_cub = z1z1.mul(&self.z);
        let s2 = other.y.mul(&z1_cub);

        let mut h = u2;
        h.sub_assign(&u1);
        let mut r = s2;
        r.sub_assign(&s1);
        // `add-2007-bl` uses r = 2*(S2 - S1).
        r = r.add(&r);

        if h.is_zero() {
            if r.is_zero() {
                // self == other
                self.double_in_place();
            } else {
                // self == -other
                *self = Self::zero();
            }
            return;
        }

        let hh = h.square();
        let mut i = hh.add(&hh);
        i = i.add(&i); // I = (2H)^2 = 4*H^2
        let j = h.mul(&i);

        let v = u1.mul(&i);

        let rr = r.square();
        let mut x3 = rr;
        x3.sub_assign(&j);
        let two_v = v.add(&v);
        x3.sub_assign(&two_v);

        let mut y3 = v;
        y3.sub_assign(&x3);
        y3 = r.mul(&y3);
        let mut s1_j = s1.mul(&j);
        s1_j = s1_j.add(&s1_j);
        y3.sub_assign(&s1_j);

        let mut z3 = self.z.add(&other.z);
        z3 = z3.square();
        z3.sub_assign(&z1z1);
        z3.sub_assign(&z2z2);
        z3 = z3.mul(&h);

        self.x = x3;
        self.y = y3;
        self.z = z3;
    }

    pub fn sub_assign(&mut self, other: &Self) {
        self.add_assign(&other.neg());
    }
}

// Helper ops for Fq3 / Fq6 (by-value to keep callsites readable).
trait Fq3Ops {
    fn add(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
}

impl Fq3Ops for Fq3 {
    #[inline(always)]
    fn add(&self, other: &Self) -> Self {
        let mut t = *self;
        t.add_assign(other);
        t
    }

    #[inline(always)]
    fn mul(&self, other: &Self) -> Self {
        Fq3::mul(self, other)
    }
}

trait Fq6Ops {
    fn mul(&self, other: &Self) -> Self;
}

impl Fq6Ops for Fq6 {
    #[inline(always)]
    fn mul(&self, other: &Self) -> Self {
        Fq6::mul(self, other)
    }
}

