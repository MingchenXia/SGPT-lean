import SGPT.PSH.HermitianBalayageTraceDomination

/-!
# The actual fixed lower-trace comparison measure

Canonical mixed measures restrict to their original open subdomains.
The finite sum of the lower traces of one actual bounded PSH potential is
an actual positive measure, finite on every compact subset of its domain.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open MixedMongeAmpere LocalBedfordTaylorLocality LocalBedfordTaylorCanonicalTraceMeasure

/-- Actual canonical mixed measures restrict to every smaller open domain. -/
theorem canonicalMixedMeasure_restrict {N : ℕ} {Ω D : Opens (ComplexModel N)}
    {f : Fin N → ComplexModel N → ℝ} (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (hDΩ : D ≤ Ω) :
    (canonicalMixedBedfordTaylorMeasure Ω f hf).restrict (D : Set (ComplexModel N)) =
      canonicalMixedBedfordTaylorMeasure D f (fun i => isLocallyBoundedPshOn_mono (hf i) hDΩ) := by
  rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hf,
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
      (fun i => isLocallyBoundedPshOn_mono (hf i) hDΩ)]
  exact recursiveMixedTraceMeasure_restrict hf hDΩ

/-- The old-potential trace on a smaller domain is the restriction of the
same original trace measure. -/
theorem nearbyMixedMeasure_old_restrict {N : ℕ} {Ω D : Opens (ComplexModel N)}
    {w : ComplexModel N → ℝ} (hw : IsLocallyBoundedPshOn Ω w) (hDΩ : D ≤ Ω) (l : ℕ) :
    (nearbyMixedMeasure Ω w w hw hw l 0).restrict (D : Set (ComplexModel N)) =
      nearbyMixedMeasure D w w (isLocallyBoundedPshOn_mono hw hDΩ)
        (isLocallyBoundedPshOn_mono hw hDΩ) l 0 :=
  canonicalMixedMeasure_restrict (locallyBoundedPsh_mixedTuple hw hw l 0) hDΩ

/-- The fixed positive comparison measure is the actual sum of the lower
traces of one genuine bounded PSH potential. -/
def oldTraceSumMeasure {N : ℕ} (Ω : Opens (ComplexModel N)) (w : ComplexModel N → ℝ)
    (hw : IsLocallyBoundedPshOn Ω w) : Measure (ComplexModel N) :=
  ∑ l ∈ Finset.range N, nearbyMixedMeasure Ω w w hw hw l 0

/-- The actual fixed comparison measure is finite on compact subsets of
its original coordinate domain. -/
theorem oldTraceSumMeasure_finiteOnCompacts {N : ℕ} {Ω : Opens (ComplexModel N)}
    {w : ComplexModel N → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    oldTraceSumMeasure Ω w hw K < ⊤ := by
  rw [oldTraceSumMeasure, Measure.finsetSum_apply]
  exact ENNReal.sum_lt_top.mpr (fun l _ => nearbyMixedMeasure_finiteOnCompacts hw hw l 0 hK hKΩ)

/-- The finite real trace sum in the local mass estimate is exactly the
real mass of the fixed positive comparison measure. -/
theorem oldTraceSumMeasure_apply_toReal {N : ℕ} {Ω : Opens (ComplexModel N)}
    {w : ComplexModel N → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (oldTraceSumMeasure Ω w hw K).toReal =
      ∑ l ∈ Finset.range N, (nearbyMixedMeasure Ω w w hw hw l 0 K).toReal := by
  rw [oldTraceSumMeasure, Measure.finsetSum_apply, ENNReal.toReal_sum
    (fun l _ => (nearbyMixedMeasure_finiteOnCompacts hw hw l 0 hK hKΩ).ne)]

end SGPT.PSH.HermitianBalayage
