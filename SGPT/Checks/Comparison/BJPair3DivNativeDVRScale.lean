import SGPT.Foundations.Envelope.Algebra.DiscreteValuationRealScale
import SGPT.Foundations.Envelope.Projective.Divisorial
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/NativeDVRScale.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Actual normalized DVR scales on every original ring coefficient
The scale parameter is the literal native positive rational weight after
coercion to nonnegative reals. The valuation is constructed from the actual
normalized DVR valuation and proved to have the expOrd coefficient formula.
-/
noncomputable section
open IsLocalRing IsDiscreteValuationRing
open scoped WithZero NNReal

namespace SGPT.NAPotential.BJ.Pair3Div.Native
open SGPT.Foundations.Envelope

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual normalized integer valuation takes a genuine uniformizer to
exp(-1), independently of any real-valued scale. -/
theorem normalized_uniformizer_value {π : R} (hπ : Irreducible π) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation F (algebraMap R F π) =
      WithZero.exp (-1) := by
  have ho : Ring.ordFrac R (algebraMap R F π) = WithZero.exp (1 : ℤ) :=
    Ring.ordFrac_irreducible hπ
  rw [Ring.ordFrac_eq_valuation_inv] at ho
  simpa only [inv_inv, ← WithZero.exp_neg] using congrArg Inv.inv ho

/-- The true whole scaled valuation has the exact original uniformizer value. -/
theorem scaled_normalized_uniformizer_value (s : ℝ≥0) {π : R} (hπ : Irreducible π) :
    DiscreteValuationRealScale.valuation ((IsDiscreteValuationRing.maximalIdeal R).valuation F) s
      (algebraMap R F π) = expNeg (s : ℝ) := by
  rw [DiscreteValuationRealScale.valuation_apply, normalized_uniformizer_value hπ]
  apply NNReal.eq
  have hz : DiscreteValuationRealScale.scale s (WithZero.exp (-1)) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr WithZero.exp_ne_zero).map (DiscreteValuationRealScale.scale s)).ne_zero
  have hp : 0 < ((DiscreteValuationRealScale.scale s (WithZero.exp (-1)) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hz)
  calc
    _ = Real.exp (Real.log ((DiscreteValuationRealScale.scale s
        (WithZero.exp (-1)) : ℝ≥0) : ℝ)) := (Real.exp_log hp).symm
    _ = Real.exp (-(s : ℝ)) := by
      rw [DiscreteValuationRealScale.log_scale_exp]
      congr 1
      ring

/-- EVERY actual original coefficient has precisely exp(-s ord), including
zero and units, for the genuinely constructed normalized DVR scale. -/
theorem scaled_normalized_algebraMap (s : ℝ≥0) (x : R) :
    DiscreteValuationRealScale.valuation ((IsDiscreteValuationRing.maximalIdeal R).valuation F) s
      (algebraMap R F x) = expOrd (expNeg (s : ℝ)) (addVal R x) := by
  by_cases hx : x = 0
  · subst x
    simp [expOrd]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  have hu : DiscreteValuationRealScale.valuation
      ((IsDiscreteValuationRing.maximalIdeal R).valuation F) s
      (algebraMap R F (u : R)) = 1 := by
    rw [DiscreteValuationRealScale.valuation_apply]
    have hh := Valuation.Integers.one_of_isUnit' u.isUnit
      (IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (IsDiscreteValuationRing.maximalIdeal R) (K := F))
    rw [hh, map_one]
  rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
    hu, one_mul, scaled_normalized_uniformizer_value s hπ, addVal_def' u hπ n, expOrd_coe]

end SGPT.NAPotential.BJ.Pair3Div.Native
