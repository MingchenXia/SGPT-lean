import SGPT.Checks.Literature.BJDivisorial.NativeModelFieldEmbedding
import SGPT.Checks.Literature.BJDivisorial.NativeDVRScale
import SGPT.Foundations.PublishedEnvelope.Global.Divisorial

/-!
# A native divisorial point has the ACTUAL scaled DVR field restriction

The native Gauss equation is converted to its exact multiplicative form.
The genuine normalized DVR scale on Frac(S[t]), restricted through the
model-generation field embedding, is proved to be M.fieldVal on EVERY
original field fraction. No valuation-correspondence certificate is used.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped NNReal

namespace SGPT.NAPotential.BJ.Divisorial.Native
open SGPT.Foundations.PublishedEnvelope

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  (M : MultiModel k K r)

/-- The actual whole scaled normalized valuation on the native Gauss field. -/
def scaledGaussDVRVal (R' : BirationalDVR k (Polynomial M.S)) (s : ℝ≥0) :
    Valuation (FractionRing (Polynomial M.S)) ℝ≥0 := by
  let := R'.isFractionRing
  exact DiscreteValuationRealScale.valuation
    ((IsDiscreteValuationRing.maximalIdeal R'.ring).valuation (FractionRing (Polynomial M.S))) s

/-- Its actual restriction along the genuine original model-field embedding. -/
def scaledModelFieldRestriction (R' : BirationalDVR k (Polynomial M.S)) (s : ℝ≥0) :
    Valuation K ℝ≥0 :=
  (scaledGaussDVRVal M R' s).comap (modelFieldToGauss M).toRingHom

/-- The native definition itself gives the exact Gauss coefficient values. -/
theorem nativeDivisorial_gauss_val_eq {v : M.an} (hv : M.IsDivisorial v) :
    ∃ (R' : BirationalDVR k (Polynomial M.S)) (c : ℚ), 0 < c ∧
      ∀ g, (M.gaussPt v.1).val g = expOrd (expNeg c) (R'.ord g) := by
  obtain ⟨R', c, hc, h⟩ := hv
  refine ⟨R', c, hc, fun g => ?_⟩
  have hg := h g
  rw [Berk.logAbs, ← log_expOrd_expNeg (by exact_mod_cast hc)] at hg
  exact ENNReal.coe_injective (ENNReal.log_injective hg)

/-- EVERY original field fraction has exactly the restricted native DVR
value with its actual positive rational weight. -/
theorem nativeDivisorial_fieldVal_eq {v : M.an} (hv : M.IsDivisorial v) :
    ∃ (R' : BirationalDVR k (Polynomial M.S)) (c : ℚ) (hc : 0 < c),
      scaledModelFieldRestriction M R' ⟨(c : ℝ), (by exact_mod_cast hc.le)⟩ =
        M.fieldVal v hv.hasGenericSupport := by
  obtain ⟨R', c, hc, hVal⟩ := nativeDivisorial_gauss_val_eq M hv
  let s : ℝ≥0 := ⟨(c : ℝ), by exact_mod_cast hc.le⟩
  have hCoeff (g : Polynomial M.S) :
      scaledGaussDVRVal M R' s (algebraMap (Polynomial M.S) (FractionRing (Polynomial M.S)) g) =
        (M.gaussPt v.1).val g := by
    let := R'.isFractionRing
    change DiscreteValuationRealScale.valuation
      ((IsDiscreteValuationRing.maximalIdeal R'.ring).valuation (FractionRing (Polynomial M.S))) s
      (algebraMap R'.ring (FractionRing (Polynomial M.S)) (R'.toRing g)) = _
    rw [scaled_normalized_algebraMap]
    exact (hVal g).symm
  refine ⟨R', c, hc, ?_⟩
  apply M.eq_fieldVal v hv.hasGenericSupport
  intro a f g hf hg hg0
  change scaledGaussDVRVal M R' s ((modelFieldToGauss M) (f / g)) = _
  rw [modelFieldToGauss_homogeneous_ratio M hf hg, map_div₀]
  change scaledGaussDVRVal M R' s
      (algebraMap (Polynomial M.S) (FractionRing (Polynomial M.S)) (Polynomial.C (M.ofPiece hf))) /
    scaledGaussDVRVal M R' s
      (algebraMap (Polynomial M.S) (FractionRing (Polynomial M.S)) (Polynomial.C (M.ofPiece hg))) = _
  rw [hCoeff, hCoeff, M.gaussPt_val_C, M.gaussPt_val_C]

end SGPT.NAPotential.BJ.Divisorial.Native
