use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    boolean::Boolean,
    cmp::CmpGadget,
    fields::emulated_fp::{params::OptimizationType, AllocatedEmulatedFpVar, EmulatedFpVar},
    prelude::*,
    uint8::UInt8,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
#[cfg(test)]
use ark_secp256k1::Fr as SecpFr;
use ark_secp256k1::{Affine as SecpAffine, Fq as SecpFq, Projective as SecpProj};
use ark_std::{ops::Neg, Zero};
use array_init::array_init;
use k256::{
    elliptic_curve::{
        group::prime::PrimeCurveAffine,
        sec1::{FromEncodedPoint, ToEncodedPoint},
    },
    EncodedPoint, FieldBytes,
};
use once_cell::sync::Lazy;

const WINDOW_SIZE: usize = 6;
const NUM_WINDOWS: usize = (256 + WINDOW_SIZE - 1) / WINDOW_SIZE;
const MAG_SIZE: usize = WINDOW_SIZE - 1;
const TABLE_LEN: usize = 1 << MAG_SIZE; // 32 entries for magnitudes 0..=31

static FIXED_G_TABLE: Lazy<[[SecpAffine; TABLE_LEN]; NUM_WINDOWS]> = Lazy::new(|| {
    let mut table = array_init(|_| array_init(|_| SecpAffine::identity()));
    let mut base = SecpProj::generator();
    for window in 0..NUM_WINDOWS {
        table[window][0] = SecpAffine::identity();
        let mut accum = SecpProj::zero();
        for mag in 1..TABLE_LEN {
            accum += base;
            table[window][mag] = accum.into_affine();
        }
        for _ in 0..WINDOW_SIZE {
            base.double_in_place();
        }
    }
    table
});

type SecpBaseVar<CF> = EmulatedFpVar<SecpFq, CF>;

fn scalar_bits_le(bytes: &[u8; 32]) -> [bool; 256] {
    let mut bits = [false; 256];
    let mut idx = 0usize;
    for byte in bytes.iter().rev() {
        for bit in 0..8 {
            bits[idx] = ((byte >> bit) & 1) == 1;
            idx += 1;
        }
    }
    bits
}

fn recode_signed_window6_inner(bits: &[bool]) -> ([i8; NUM_WINDOWS], [u8; NUM_WINDOWS + 1]) {
    let mut digits = [0i8; NUM_WINDOWS];
    let mut carries = [0u8; NUM_WINDOWS + 1];
    let mut carry: i32 = 0;
    carries[0] = 0;
    for window in 0..NUM_WINDOWS {
        let mut chunk = carry;
        for bit in 0..WINDOW_SIZE {
            let idx = window * WINDOW_SIZE + bit;
            if idx < bits.len() && bits[idx] {
                chunk += 1 << bit;
            }
        }
        let mut digit = chunk;
        if digit >= 1 << WINDOW_SIZE {
            digit -= 1 << WINDOW_SIZE;
        }
        if digit == 32 {
            digit = 0;
            carry = 1;
        } else if digit > 32 {
            digit -= 64;
        } else {
            carry = 0;
        }

        if carry == 0 {
            carry = (chunk - digit) >> WINDOW_SIZE;
        }
        debug_assert!(carry == 0 || carry == 1);
        digits[window] = digit as i8;
        carries[window + 1] = carry as u8;
    }
    debug_assert_eq!(carry, 0);
    (digits, carries)
}

fn recode_signed_window6(bytes: &[u8; 32]) -> ([i8; NUM_WINDOWS], [u8; NUM_WINDOWS + 1]) {
    let bits = scalar_bits_le(bytes);
    recode_signed_window6_inner(&bits)
}

#[derive(Clone)]
struct SecpJacVar<CF: PrimeField> {
    x: SecpBaseVar<CF>,
    y: SecpBaseVar<CF>,
    z: SecpBaseVar<CF>,
}

#[derive(Clone)]
struct SecpAffineVar<CF: PrimeField> {
    x: SecpBaseVar<CF>,
    y: SecpBaseVar<CF>,
}

impl<CF: PrimeField> SecpJacVar<CF> {
    fn infinity() -> Self {
        Self {
            x: SecpBaseVar::zero(),
            y: SecpBaseVar::one(),
            z: SecpBaseVar::zero(),
        }
    }

    fn double(&self) -> Result<Self, SynthesisError> {
        let xx = self.x.square()?;
        let yy = self.y.square()?;
        let yyyy = yy.square()?;

        let s = ((&self.x + &yy).square()? - &xx - &yyyy).double()?;
        let m = xx.double()? + &xx;
        let t = m.square()?;
        let x = &t - &s.double()?;
        let eight_c = yyyy.double()?.double()?.double()?;
        let y = m * (s - &x) - eight_c;
        let z = (&self.y * &self.z).double()?;
        Ok(Self { x, y, z })
    }

    fn add_mixed(&self, other: &SecpAffineVar<CF>) -> Result<Self, SynthesisError> {
        let (x1, y1, z1) = (&self.x, &self.y, &self.z);
        let (x2, y2) = (&other.x, &other.y);

        let z1_is_zero = z1.is_zero()?;
        let z1z1 = z1.square()?;
        let u2 = x2 * &z1z1;
        let s2 = y2 * z1 * &z1z1;

        let h = u2 - x1;
        let hh = h.square()?;
        let i = hh.double()?.double()?;
        let j = &h * &i;
        let r = (s2 - y1).double()?;
        let v = x1 * &i;

        let r2 = r.square()?;
        let x3 = &r2 - &j - v.double()?;
        let y3 = r.clone() * (v - &x3) - (y1 * &j).double()?;
        let z3 = (z1 + &h).square()? - z1z1 - hh;
        let add = Self {
            x: x3,
            y: y3,
            z: z3,
        };

        let h_is_zero = h.is_zero()?;
        let r_is_zero = r.is_zero()?;
        let h_and_r_zero = Boolean::kary_and(&[h_is_zero.clone(), r_is_zero.clone()])?;
        let h_zero_r_nonzero = Boolean::kary_and(&[h_is_zero.clone(), (!r_is_zero).clone()])?;

        let doubled = self.double()?;
        let infinity = Self::infinity();
        let add_or_inf = Self::conditional_select(&h_zero_r_nonzero, &infinity, &add)?;
        let add_or_double = Self::conditional_select(&h_and_r_zero, &doubled, &add_or_inf)?;

        let q_proj = Self {
            x: other.x.clone(),
            y: other.y.clone(),
            z: SecpBaseVar::one(),
        };
        Self::conditional_select(&z1_is_zero, &q_proj, &add_or_double)
    }

    fn conditional_select(
        cond: &Boolean<CF>,
        when_true: &Self,
        when_false: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = SecpBaseVar::conditionally_select(cond, &when_true.x, &when_false.x)?;
        let y = SecpBaseVar::conditionally_select(cond, &when_true.y, &when_false.y)?;
        let z = SecpBaseVar::conditionally_select(cond, &when_true.z, &when_false.z)?;
        Ok(Self { x, y, z })
    }
}

fn select_signed_affine<CF: PrimeField>(
    bits: &[Boolean<CF>; MAG_SIZE],
    sign: &Boolean<CF>,
    table: &[SecpAffine; TABLE_LEN],
) -> Result<(SecpBaseVar<CF>, SecpBaseVar<CF>), SynthesisError> {
    let zero = SecpBaseVar::zero();
    let one = SecpBaseVar::one();
    let x_consts: Vec<SecpBaseVar<CF>> = (0..TABLE_LEN)
        .map(|j| {
            if j == 0 {
                zero.clone()
            } else {
                SecpBaseVar::constant(table[j].x)
            }
        })
        .collect();
    let y_pos_consts: Vec<SecpBaseVar<CF>> = (0..TABLE_LEN)
        .map(|j| {
            if j == 0 {
                one.clone()
            } else {
                SecpBaseVar::constant(table[j].y)
            }
        })
        .collect();
    let y_neg_consts: Vec<SecpBaseVar<CF>> = (0..TABLE_LEN)
        .map(|j| {
            if j == 0 {
                one.clone()
            } else {
                SecpBaseVar::constant(-table[j].y)
            }
        })
        .collect();

    let x_sel = mux_tree(bits, x_consts)?;
    let y_pos = mux_tree(bits, y_pos_consts)?;
    let y_neg = mux_tree(bits, y_neg_consts)?;
    let y_sel = SecpBaseVar::conditionally_select(sign, &y_neg, &y_pos)?;
    Ok((x_sel, y_sel))
}

fn mux_tree<CF: PrimeField>(
    bits: &[Boolean<CF>],
    mut values: Vec<SecpBaseVar<CF>>,
) -> Result<SecpBaseVar<CF>, SynthesisError> {
    for bit in bits.iter() {
        let mut next = Vec::with_capacity((values.len() + 1) / 2);
        for chunk in values.chunks(2) {
            let false_val = chunk[0].clone();
            let true_val = chunk.get(1).cloned().unwrap_or_else(|| false_val.clone());
            let selected = SecpBaseVar::conditionally_select(bit, &true_val, &false_val)?;
            next.push(selected);
        }
        values = next;
    }
    debug_assert_eq!(values.len(), 1);
    Ok(values.remove(0))
}

pub fn alloc_point_public_inputs<CF: PrimeField>(
    cs: ConstraintSystemRef<CF>,
    point: &SecpAffine,
) -> Result<(SecpBaseVar<CF>, SecpBaseVar<CF>), SynthesisError> {
    let (tx_host, ty_host) = if point.is_zero() {
        (SecpFq::from(0u64), SecpFq::from(0u64))
    } else {
        (point.x, point.y)
    };
    let tx = SecpBaseVar::<CF>::new_input(cs.clone(), || Ok(tx_host))?;
    let ty = SecpBaseVar::<CF>::new_input(cs, || Ok(ty_host))?;
    Ok((tx, ty))
}

pub fn enforce_secp_fixed_base_mul<CF: PrimeField>(
    cs: ConstraintSystemRef<CF>,
    m_bytes: &[UInt8<CF>; 32],
    t_host: &SecpAffine,
    _scalar_hint: Option<&[u8; 32]>,
) -> Result<(), SynthesisError> {
    let (tx, ty) = alloc_point_public_inputs(cs.clone(), t_host)?;

    let mut scalar_bits = Vec::with_capacity(8 * m_bytes.len());
    for byte in m_bytes.iter().rev() {
        scalar_bits.extend(byte.to_bits_le()?);
    }
    let total_bits = scalar_bits.len();

    let chunk_threshold = UInt8::constant(32u8);
    let mut acc = SecpJacVar::infinity();
    let mut carry = Boolean::constant(false);

    for window_idx in 0..NUM_WINDOWS {
        let window_bits: [Boolean<CF>; WINDOW_SIZE] = array_init(|bit_idx| {
            let idx = window_idx * WINDOW_SIZE + bit_idx;
            if idx < total_bits {
                scalar_bits[idx].clone()
            } else {
                Boolean::constant(false)
            }
        });

        let mut chunk_bits = Vec::with_capacity(WINDOW_SIZE + 2);
        let mut carry_sum = carry.clone();
        for bit in window_bits.iter() {
            let sum_bit = bit ^ &carry_sum;
            chunk_bits.push(sum_bit);
            carry_sum = Boolean::kary_and(&[bit.clone(), carry_sum.clone()])?;
        }
        chunk_bits.push(carry_sum.clone());
        let chunk_bits_raw = chunk_bits.clone();
        chunk_bits.push(Boolean::constant(false));
        let chunk_bits_arr: [Boolean<CF>; 8] = chunk_bits.try_into().expect("chunk bits length");
        let chunk_u8 = UInt8::from_bits_le(&chunk_bits_arr);
        let chunk_eq_32 = chunk_u8.is_eq(&chunk_threshold)?;
        let chunk_gt_32 = chunk_u8.is_gt(&chunk_threshold)?;
        let carry_next = Boolean::kary_or(&[chunk_eq_32.clone(), chunk_gt_32.clone()])?;
        let sign = chunk_gt_32.clone();

        let pos_bits: [Boolean<CF>; MAG_SIZE] = array_init(|i| chunk_bits_raw[i].clone());
        let neg_bits = subtract_from_sixty_four(&chunk_bits_raw).map_err(|e| {
            eprintln!(
                "subtract_from_sixty_four failed at window {}: {:?}",
                window_idx, e
            );
            e
        })?;
        let mut mag_bits: [Boolean<CF>; MAG_SIZE] = array_init(|_| Boolean::constant(false));
        let not_gt = !chunk_gt_32.clone();
        let not_eq = !chunk_eq_32.clone();
        for i in 0..MAG_SIZE {
            let pos_active =
                Boolean::kary_and(&[not_gt.clone(), not_eq.clone(), pos_bits[i].clone()])?;
            let neg_active = Boolean::kary_and(&[chunk_gt_32.clone(), neg_bits[i].clone()])?;
            mag_bits[i] = Boolean::kary_or(&[pos_active, neg_active])?;
        }

        let (qx, qy) = select_signed_affine(&mag_bits, &sign, &FIXED_G_TABLE[window_idx])?;
        let mag_vec = mag_bits.to_vec();
        let should_add = Boolean::kary_or(&mag_vec)?;
        let q_affine = SecpAffineVar {
            x: qx.clone(),
            y: qy.clone(),
        };
        let added = acc.add_mixed(&q_affine)?;
        acc = SecpJacVar::conditional_select(&should_add, &added, &acc)?;
        carry = carry_next;
    }

    Boolean::enforce_equal(&carry, &Boolean::constant(false))?;

    let z_is_zero = acc.z.is_zero()?;
    let tx_is_zero = tx.is_zero()?;
    let ty_is_zero = ty.is_zero()?;
    let t_is_zero = Boolean::kary_and(&[tx_is_zero, ty_is_zero])?;
    Boolean::enforce_equal(&z_is_zero, &t_is_zero)?;

    let non_zero = !z_is_zero.clone();
    let z2 = acc.z.square()?;
    let z3 = &z2 * &acc.z;
    let lhs_x = &tx * &z2;
    let lhs_y = &ty * &z3;
    let dx = lhs_x - &acc.x;
    let dy = lhs_y - &acc.y;
    dx.conditional_enforce_equal(&SecpBaseVar::zero(), &non_zero)?;
    dy.conditional_enforce_equal(&SecpBaseVar::zero(), &non_zero)?;

    Ok(())
}

fn subtract_from_sixty_four<CF: PrimeField>(
    chunk_bits: &[Boolean<CF>],
) -> Result<[Boolean<CF>; MAG_SIZE], SynthesisError> {
    debug_assert_eq!(chunk_bits.len(), WINDOW_SIZE + 1);
    let mut borrow = Boolean::constant(false);
    let mut diff_bits = Vec::with_capacity(WINDOW_SIZE + 1);
    for (idx, chunk_bit) in chunk_bits.iter().enumerate() {
        let minuend_bit = if idx == WINDOW_SIZE {
            Boolean::constant(true)
        } else {
            Boolean::constant(false)
        };
        let tmp = &minuend_bit ^ chunk_bit;
        let diff = &tmp ^ &borrow;
        diff_bits.push(diff);
        let not_a = !minuend_bit.clone();
        let sub_or_borrow = Boolean::kary_or(&[chunk_bit.clone(), borrow.clone()])?;
        let term1 = Boolean::kary_and(&[not_a, sub_or_borrow])?;
        let term2 = Boolean::kary_and(&[chunk_bit.clone(), borrow.clone()])?;
        borrow = Boolean::kary_or(&[term1, term2])?;
    }
    Ok(array_init(|i| diff_bits[i].clone()))
}

pub fn decompress_secp_point(bytes: &[u8]) -> Option<SecpAffine> {
    let encoded = EncodedPoint::from_bytes(bytes).ok()?;
    let opt = k256::AffinePoint::from_encoded_point(&encoded);
    let q = Option::<k256::AffinePoint>::from(opt)?;
    if bool::from(q.is_identity()) {
        return None;
    }
    let uncompressed = q.to_encoded_point(false);
    let x_bytes = uncompressed.x()?;
    let y_bytes = uncompressed.y()?;
    let x = SecpFq::from_be_bytes_mod_order(x_bytes);
    let y = SecpFq::from_be_bytes_mod_order(y_bytes);
    let point = SecpAffine::new(x, y);
    if point.is_zero() {
        return None;
    }
    Some(point)
}

pub fn compress_secp_point(point: &SecpAffine) -> Vec<u8> {
    let x_big = point.x.into_bigint().to_bytes_be();
    let y_big = point.y.into_bigint().to_bytes_be();

    let mut x_bytes = FieldBytes::default();
    let mut y_bytes = FieldBytes::default();
    let x_offset = x_bytes.len() - x_big.len();
    let y_offset = y_bytes.len() - y_big.len();
    x_bytes[x_offset..].copy_from_slice(&x_big);
    y_bytes[y_offset..].copy_from_slice(&y_big);

    EncodedPoint::from_affine_coordinates(&x_bytes, &y_bytes, true)
        .as_bytes()
        .to_vec()
}

pub fn scalar_bytes_to_point(scalar_le: &[u8; 32]) -> SecpAffine {
    let (digits, _) = recode_signed_window6(scalar_le);
    let mut acc = SecpProj::zero();
    for (window_idx, digit) in digits.iter().enumerate() {
        let mag = i32::from(*digit).abs() as usize;
        if mag == 0 {
            continue;
        }
        let mut point = FIXED_G_TABLE[window_idx][mag].into_group();
        if *digit < 0 {
            point = point.neg();
        }
        acc += point;
    }
    acc.into_affine()
}

pub fn point_to_field_elements<CF: PrimeField>(point: &SecpAffine) -> Vec<CF> {
    let mut limbs = AllocatedEmulatedFpVar::<SecpFq, CF>::get_limbs_representations(
        &point.x,
        OptimizationType::Constraints,
    )
    .expect("limbs")
    .into_iter()
    .map(CF::from)
    .collect::<Vec<_>>();
    limbs.extend(
        AllocatedEmulatedFpVar::<SecpFq, CF>::get_limbs_representations(
            &point.y,
            OptimizationType::Constraints,
        )
        .expect("limbs")
        .into_iter()
        .map(CF::from),
    );
    limbs
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::Field;
    use ark_r1cs_std::uint8::UInt8;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn fixed_base_matches_host() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let scalar_bytes = [3u8; 32];
        let t_point = scalar_bytes_to_point(&scalar_bytes);
        let bytes_vars = UInt8::new_input_vec(cs.clone(), &scalar_bytes).unwrap();
        let arr: [UInt8<Fr>; 32] = bytes_vars.try_into().unwrap();
        enforce_secp_fixed_base_mul(cs.clone(), &arr, &t_point, Some(&scalar_bytes)).unwrap();
        println!("FIXED_BASE_CONSTRAINTS: {}", cs.num_constraints());
        let sat = cs.is_satisfied().unwrap();
        if !sat {
            println!("first unsatisfied: {:?}", cs.which_is_unsatisfied());
        }
        assert!(sat);
    }

    #[test]
    fn host_window_table_matches_scalar_mul() {
        let scalar_bytes = [3u8; 32];
        let scalar = SecpFr::from_be_bytes_mod_order(&scalar_bytes);
        let expected = (SecpProj::generator() * scalar).into_affine();
        let computed = scalar_bytes_to_point(&scalar_bytes);
        assert_eq!(computed, expected);
    }

    fn add_mixed_host(p: SecpProj, q: SecpAffine) -> SecpProj {
        if p.is_zero() {
            return q.into_group();
        }
        let (x1, y1, z1) = (p.x, p.y, p.z);
        let (x2, y2) = (q.x, q.y);

        let z1z1 = z1.square();
        let u2 = x2 * z1z1;
        let s2 = y2 * z1 * z1z1;

        let h = u2 - x1;
        let hh = h.square();
        let i = hh.double().double();
        let j = h * i;
        let r = (s2 - y1).double();
        let v = x1 * i;

        let r2 = r.square();
        let x3 = r2 - j - v.double();
        let y3 = r * (v - x3) - (y1 * j).double();
        let z3 = (z1 + h).square() - z1z1 - hh;
        let add = SecpProj::new_unchecked(x3, y3, z3);

        let h_is_zero = h.is_zero();
        let r_is_zero = r.is_zero();
        if h_is_zero && r_is_zero {
            return p.double();
        } else if h_is_zero {
            return SecpProj::zero();
        }
        add
    }

    #[test]
    fn host_add_mixed_matches_group() {
        let g = SecpProj::generator();
        let p = g * SecpFr::from(5u64);
        let q = (g * SecpFr::from(7u64)).into_affine();
        let expected = p + q;
        let computed = add_mixed_host(p, q);
        assert_eq!(computed.into_affine(), expected.into_affine());
    }

    #[test]
    #[ignore = "full Groth16 setup/prove/verify; run manually"]
    fn groth16_with_secp_check() {
        use ark_groth16::Groth16;
        use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
        use ark_snark::SNARK;
        use ark_std::rand::{rngs::StdRng, SeedableRng};

        #[derive(Clone)]
        struct TestCircuit {
            scalar: [u8; 32],
            t_point: SecpAffine,
        }

        impl ConstraintSynthesizer<Fr> for TestCircuit {
            fn generate_constraints(
                self,
                cs: ConstraintSystemRef<Fr>,
            ) -> Result<(), SynthesisError> {
                use ark_r1cs_std::uint8::UInt8;
                let public_bytes = UInt8::new_input_vec(cs.clone(), &self.scalar)?;
                let witness_bytes = UInt8::new_witness_vec(cs.clone(), &self.scalar)?;
                for (public, witness) in public_bytes.iter().zip(witness_bytes.iter()) {
                    public.enforce_equal(witness)?;
                }
                let arr: [UInt8<Fr>; 32] = witness_bytes.try_into().unwrap();
                enforce_secp_fixed_base_mul(cs.clone(), &arr, &self.t_point, Some(&self.scalar))?;
                crate::api::enforce_public_inputs_are_outputs(cs)?;
                Ok(())
            }
        }

        let scalar_bytes = [3u8; 32];
        let t_point = scalar_bytes_to_point(&scalar_bytes);
        let circuit = TestCircuit {
            scalar: scalar_bytes,
            t_point,
        };

        let mut rng = StdRng::seed_from_u64(0x1234);
        use ark_groth16::r1cs_to_qap::LibsnarkReduction;
        type E = ark_bls12_381::Bls12_381;
        let (pk, vk) =
            Groth16::<E, LibsnarkReduction>::circuit_specific_setup(circuit.clone(), &mut rng)
                .unwrap();

        let cs_extract = ConstraintSystem::<Fr>::new_ref();
        circuit
            .clone()
            .generate_constraints(cs_extract.clone())
            .unwrap();
        let public_inputs: Vec<_> = cs_extract
            .borrow()
            .unwrap()
            .instance_assignment
            .iter()
            .skip(1)
            .cloned()
            .collect();
        println!("Extracted {} public inputs", public_inputs.len());

        let proof = Groth16::<E, LibsnarkReduction>::prove(&pk, circuit, &mut rng).unwrap();

        let ok = Groth16::<E, LibsnarkReduction>::verify(&vk, &public_inputs, &proof).unwrap();
        println!("Groth16 verification with secp check: {}", ok);
        assert!(ok);
    }
}
