import SGPT.Checks.Comparison.BJPair3DivNativeDVRScale
import SGPT.Foundations.Envelope.Algebra.LocalDVRRealValuations

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/RationalDiscreteScale.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# Positive rational weights survive genuine DVR restriction

Compose the actual local integer-ring map with the strictly increasing
positive real scale. The cached whole-DVR scale producer supplies a unique
positive normalized scale. Evaluate a GENUINE uniformizer: its original
integer value makes that derived scale rational. All conclusions are
identities of valuations on every field element, including zero.
-/
noncomputable section
open IsLocalRing IsDiscreteValuationRing
open scoped WithZero NNReal

namespace SGPT.NAPotential.BJ.Pair3Div.Native
open SGPT.Foundations.Envelope

variable {K : Type*} [Field K]

/-- Every strictly positive original scale is genuinely strictly increasing. -/
theorem actualScale_strictMono {s : ℝ≥0} (hs : 0 < s) :
    StrictMono (DiscreteValuationRealScale.scale s) := by
  have hb : 1 < DiscreteValuationRealScale.expBase s := by
    change (1 : ℝ) < Real.exp (s : ℝ)
    exact Real.one_lt_exp_iff.mpr (NNReal.coe_pos.mpr hs)
  exact WithZeroMulInt.toNNReal_strictMono hb

/-- The actual integer ring maps to the true scaled valuation's integer ring. -/
def scaleBallHom (v : Valuation K ℤᵐ⁰) (s : ℝ≥0) :
    v.valuationSubring →+* (DiscreteValuationRealScale.valuation v s).valuationSubring where
  toFun a := ⟨a, by
    change DiscreteValuationRealScale.scale s (v (a : K)) ≤ 1
    simpa only [map_one] using DiscreteValuationRealScale.scale_monotone s a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Positivity derives locality of the actual whole integer-ring map. -/
theorem scaleBallHom_isLocalHom (v : Valuation K ℤᵐ⁰) {s : ℝ≥0} (hs : 0 < s) :
    IsLocalHom (scaleBallHom v s) := by
  constructor
  intro a ha
  have hscaled := (Valuation.valuationSubring.integers
    (DiscreteValuationRealScale.valuation v s)).isUnit_iff_valuation_eq_one.mp ha
  change DiscreteValuationRealScale.scale s (v (a : K)) = 1 at hscaled
  have hraw : v (a : K) = 1 := (actualScale_strictMono hs).injective (by
    simpa only [map_one] using hscaled)
  exact (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mpr hraw

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- An actual local DVR restriction retains a true positive RATIONAL
normalized weight, derived from its actual uniformizer value. -/
theorem exists_positive_rational_normalizedScale (v : Valuation K ℤᵐ⁰)
    (c : ℚ) (hc : 0 < c) (ρ : R →+* v.valuationSubring) [IsLocalHom ρ]
    (hρ : v.valuationSubring.toSubring.subtype.comp ρ = algebraMap R K) :
    ∃ (d : ℚ) (hd : 0 < d),
      DiscreteValuationRealScale.valuation v ⟨(c : ℝ), (by exact_mod_cast hc.le)⟩ =
        DiscreteValuationRealScale.valuation
          ((IsDiscreteValuationRing.maximalIdeal R).valuation K)
          ⟨(d : ℝ), (by exact_mod_cast hd.le)⟩ := by
  let s : ℝ≥0 := ⟨(c : ℝ), by exact_mod_cast hc.le⟩
  have hs : 0 < s := by
    change (0 : ℝ) < (c : ℝ)
    exact_mod_cast hc
  let := scaleBallHom_isLocalHom v hs
  let ρs := (scaleBallHom v s).comp ρ
  have hρs : (DiscreteValuationRealScale.valuation v s).valuationSubring.toSubring.subtype.comp ρs =
      algebraMap R K := by
    ext a
    exact RingHom.congr_fun hρ a
  obtain ⟨t, ht, hval⟩ := LocalDVRRealValuations.exists_positive_realScale
    (DiscreteValuationRealScale.valuation v s) ρs hρs
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  have hvπ : v (algebraMap R K π) ≠ 0 := (map_ne_zero v).mpr hπK
  let n := WithZero.log (v (algebraMap R K π))
  have hn : v (algebraMap R K π) = WithZero.exp n := (WithZero.exp_log hvπ).symm
  have hh := congrArg (fun w : Valuation K ℝ≥0 => Real.log (w (algebraMap R K π) : ℝ)) hval
  change Real.log (DiscreteValuationRealScale.scale s (v (algebraMap R K π)) : ℝ) =
    Real.log (DiscreteValuationRealScale.scale t
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K π)) : ℝ) at hh
  rw [hn, normalized_uniformizer_value hπ, DiscreteValuationRealScale.log_scale_exp,
    DiscreteValuationRealScale.log_scale_exp] at hh
  let d : ℚ := -c * (n : ℚ)
  have hdReal : (d : ℝ) = (t : ℝ) := by
    dsimp only [d]
    push_cast
    change (c : ℝ) * (n : ℝ) = (t : ℝ) * (-1 : ℤ) at hh
    norm_num at hh
    linarith
  have hd : 0 < d := by
    have hpos : (0 : ℝ) < (d : ℝ) := hdReal.symm ▸ (NNReal.coe_pos.mpr ht)
    exact_mod_cast hpos
  have htd : t = ⟨(d : ℝ), by exact_mod_cast hd.le⟩ := NNReal.eq hdReal.symm
  refine ⟨d, hd, ?_⟩
  rw [← htd]
  exact hval

end SGPT.NAPotential.BJ.Pair3Div.Native
