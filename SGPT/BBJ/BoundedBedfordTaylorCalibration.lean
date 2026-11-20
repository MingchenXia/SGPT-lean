import SGPT.Foundations.Analysis.Pending.ActualBoundedScalarCurrentIdentity
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.ActualScalarCurrentKahlerTracePairing

set_option autoImplicit false

/-! # The actual one-variable bounded Bedford–Taylor coefficient

The local product-current trace and the alternating coefficient current have
the same normalization.  Consequently the genuine canonical bounded
Bedford–Taylor measure reads the same coefficient, without smoothness.
-/

noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere FirstPass.MixedMongeAmpere StronglyPositiveForms
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorSmoothTraceMeasure LocalBedfordTaylorCanonicalTraceMeasure
open ScalarLeviPositiveCurrent ActualBoundedScalarCurrentIdentity
open scoped Topology Distributions ContDiff

/-- In complex dimension one, the actual scalar-current trace is the actual
alternating coefficient on the canonical complex line. -/
lemma ddc_scalarTopCurrent_one_dim {V : Opens (ComplexModel 1)}
    (T : 𝓓'(V, ℝ)) (φ : 𝓓(V, ℝ)) :
    ddc (scalarTopCurrent T) (kahlerPower 1 0) φ =
      LocalCurrents.ddC T
        ![coordinateVector (0 : Fin 1), Complex.I • coordinateVector (0 : Fin 1)] φ := by
  rw [ActualScalarCurrentKahlerTracePairing.ddc_scalarTopCurrent_kahlerPower_eq_sum_levi
    (m := 0), LocalCurrents.ddC_complexLine]
  simp

/-- The actual canonical bounded one-variable Bedford–Taylor measure tests
the same regular-distribution coefficient, with no smoothness hypothesis. -/
theorem integral_canonicalBoundedBT_one_dim
    {Ω V : Opens (ComplexModel 1)} {u : ComplexModel 1 → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hV : RelativelyCompactIn V Ω)
    (φ : 𝓓(V, ℝ)) :
    let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
    ∫ x, φ x ∂MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure V
      (fun _ : Fin 1 => u) (fun _ => huV) =
      LocalCurrents.ddC
        (regularDistribution volume u (locallyIntegrableOn_of_plurisubharmonicOn_real huV.1))
        ![coordinateVector (0 : Fin 1), Complex.I • coordinateVector (0 : Fin 1)] φ := by
  dsimp only
  let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
  rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure (fun _ => huV)]
  rw [recursiveMixedTraceMeasure, IsPositive.integral_traceMeasure]
  change ddc (mulBorel (oneCurrent V) ((V : Set (ComplexModel 1)).indicator u))
      (kahlerPower 1 0) φ = _
  rw [← scalarTopCurrent_regularDistribution_eq_mulBorel_of_locallyBoundedPsh hu hV]
  exact ddc_scalarTopCurrent_one_dim _ φ

end SGPT.BBJ
