//! Fixed-parameter MNT6-298 curve with a non-singular twist.
//!
//! Arkworks' published MNT6-298 configuration encodes the twist as (0, 1, 0) ∈ Fq³,
//! which has zero norm under the specified cubic extension and therefore is not
//! invertible.  Preparing G₂ points requires the inverse of the twist, so pairing
//! precomputation panics when used in decapsulation-heavy flows such as the PVUGC
//! end-to-end test.
//!
//! This module mirrors the upstream curve parameters but swaps in an equivalent
//! twist (0, 0, 1) whose norm is non-zero.  All other constants are copied from the
//! ark-mnt6-298 crate.

use ark_ec::{
    mnt6,
    models::{
        mnt6::{MNT6Config, MNT6},
        short_weierstrass::SWCurveConfig,
        CurveConfig,
    },
};
use ark_ff::{biginteger::BigInteger320, fields::fp3::Fp3, AdditiveGroup, Field, MontFp};

use ark_mnt6_298::{Fq, Fq3, Fq3Config, Fq6Config, Fr};

/// MNT6-298 pairing engine with the corrected twist.
pub type FixedMNT6_298 = MNT6<Config>;

/// Curve parameters for the fixed MNT6-298 twist.
pub struct Config;

impl MNT6Config for Config {
    const TWIST: Fp3<Self::Fp3Config> = Fp3::<Self::Fp3Config>::new(Fq::ZERO, Fq::ZERO, Fq::ONE);
    const TWIST_COEFF_A: Fp3<Self::Fp3Config> =
        Fp3::<Self::Fp3Config>::new(Fq::ZERO, Fq::ZERO, g1::Config::COEFF_A);

    const ATE_LOOP_COUNT: &'static [i8] = ark_mnt6_298::Config::ATE_LOOP_COUNT;
    const ATE_IS_LOOP_COUNT_NEG: bool = ark_mnt6_298::Config::ATE_IS_LOOP_COUNT_NEG;
    const FINAL_EXPONENT_LAST_CHUNK_1: BigInteger320 =
        ark_mnt6_298::Config::FINAL_EXPONENT_LAST_CHUNK_1;
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool =
        ark_mnt6_298::Config::FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG;
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInteger320 =
        ark_mnt6_298::Config::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0;

    type Fp = Fq;
    type Fr = Fr;
    type Fp3Config = Fq3Config;
    type Fp6Config = Fq6Config;
    type G1Config = g1::Config;
    type G2Config = g2::Config;
}

/// G₁ configuration copied from ark-mnt6-298.
pub mod g1 {
    use super::*;

    pub type G1Affine = mnt6::G1Affine<super::Config>;
    #[derive(Clone, Default, PartialEq, Eq)]
    pub struct Config;

    impl CurveConfig for Config {
        type BaseField = Fq;
        type ScalarField = Fr;

        /// COFACTOR = 1
        const COFACTOR: &'static [u64] = &[1];

        /// COFACTOR^(-1) mod r = 1
        const COFACTOR_INV: Fr = Fr::ONE;
    }

    impl SWCurveConfig for Config {
        /// COEFF_A = 11
        const COEFF_A: Fq = MontFp!("11");

        /// COEFF_B = 106700080510851735677967319632585352256454251201367587890185989362936000262606668469523074
        const COEFF_B: Fq = MontFp!(
            "106700080510851735677967319632585352256454251201367587890185989362936000262606668469523074"
        );

        /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
        const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);
    }

    /// G1_GENERATOR_X =
    #[rustfmt::skip]
    pub const G1_GENERATOR_X: Fq = MontFp!(
        "336685752883082228109289846353937104185698209371404178342968838739115829740084426881123453"
    );

    /// G1_GENERATOR_Y =
    #[rustfmt::skip]
    pub const G1_GENERATOR_Y: Fq = MontFp!(
        "402596290139780989709332707716568920777622032073762749862342374583908837063963736098549800"
    );
}

/// G₂ configuration copied from ark-mnt6-298, referencing the fixed twist.
pub mod g2 {
    use super::*;

    pub type G2Affine = mnt6::G2Affine<super::Config>;
    #[derive(Clone, Default, PartialEq, Eq)]
    pub struct Config;

    impl CurveConfig for Config {
        type BaseField = Fq3;
        type ScalarField = Fr;

        /// COFACTOR =
        /// 226502022472576270196498690498308461791828762732602586162207535351960270082712694977333372361549082214519252261735048131889018501404377856786623430385820659037970876666767495659520
        #[rustfmt::skip]
        const COFACTOR: &'static [u64] = &[
            15308190245346869248,
            10669098443577192943,
            4561413759929581409,
            3680089780298582849,
            17336300687782721465,
            10745756320947240891,
            17479264233688728128,
            16828697388537672097,
            4184034152442024798,
            915787,
        ];

        /// COFACTOR^(-1) mod r =
        /// 79320381028210220958891541608841408590854146655427655872973753568875979721417185067925504
        const COFACTOR_INV: Fr = MontFp!(
            "79320381028210220958891541608841408590854146655427655872973753568875979721417185067925504"
        );
    }

    /// MUL_BY_A_C0 = NONRESIDUE * COEFF_A = 5 * 11
    pub const MUL_BY_A_C0: Fq = MontFp!("55");

    /// MUL_BY_A_C1 = NONRESIDUE * COEFF_A
    pub const MUL_BY_A_C1: Fq = MontFp!("55");

    /// MUL_BY_A_C2 = COEFF_A
    pub const MUL_BY_A_C2: Fq = g1::Config::COEFF_A;

    impl SWCurveConfig for Config {
        const COEFF_A: Fq3 = super::Config::TWIST_COEFF_A;
        const COEFF_B: Fq3 = Fq3::new(
            // 5 * G1::COEFF_B
            MontFp!(
                "57578116384997352636487348509878309737146377454014423897662211075515354005624851787652233"
            ),
            Fq::ZERO,
            Fq::ZERO,
        );

        /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
        const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

        #[inline(always)]
        fn mul_by_a(elt: Fq3) -> Fq3 {
            Fq3::new(
                MUL_BY_A_C0 * &elt.c1,
                MUL_BY_A_C1 * &elt.c2,
                MUL_BY_A_C2 * &elt.c0,
            )
        }
    }

    const G2_GENERATOR_X: Fq3 = Fq3::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1, G2_GENERATOR_X_C2);
    const G2_GENERATOR_Y: Fq3 = Fq3::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1, G2_GENERATOR_Y_C2);

    pub const G2_GENERATOR_X_C0: Fq = MontFp!(
        "421456435772811846256826561593908322288509115489119907560382401870203318738334702321297427"
    );
    pub const G2_GENERATOR_X_C1: Fq = MontFp!(
        "103072927438548502463527009961344915021167584706439945404959058962657261178393635706405114"
    );
    pub const G2_GENERATOR_X_C2: Fq = MontFp!(
        "143029172143731852627002926324735183809768363301149009204849580478324784395590388826052558"
    );

    pub const G2_GENERATOR_Y_C0: Fq = MontFp!(
        "464673596668689463130099227575639512541218133445388869383893594087634649237515554342751377"
    );
    pub const G2_GENERATOR_Y_C1: Fq = MontFp!(
        "100642907501977375184575075967118071807821117960152743335603284583254620685343989304941678"
    );
    pub const G2_GENERATOR_Y_C2: Fq = MontFp!(
        "123019855502969896026940545715841181300275180157288044663051565390506010149881373807142903"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn twist_is_invertible() {
        use ark_ff::Field;
        assert!(Config::TWIST.inverse().is_some());
    }
}
