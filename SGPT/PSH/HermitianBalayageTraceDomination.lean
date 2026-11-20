import SGPT.PSH.HermitianBalayageFrozenBall
import SGPT.PSH.HermitianPasting

/-!
# Genuine ordinary trace domination by a common smooth correction

Positive Bedford--Taylor currents and their trace measures give canonical
measure domination when a PSH function is added to selected slots. Locality
handles the arbitrary extensions outside the coordinate domain. In the
frozen argument the added function is the actual smooth PSH difference
between the common dominating quadratic and the frozen correction.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorDecreasing
  LocalBedfordTaylorCalculus LocalBedfordTaylorCanonicalTraceMeasure MixedMongeAmpere BedfordTaylor
open scoped Topology ContDiff Distributions

private theorem positive_trace_congr {N k : ℕ} {Ω : Opens (ComplexModel N)}
    {A B : LocalProductCurrent N Ω k} (hA : IsPositive A) (hB : IsPositive B) (heq : A = B) :
    hA.traceMeasure = hB.traceMeasure := by subst heq; rfl

/-- The actual canonical mixed measure depends only on the potentials on
its open coordinate domain. -/
theorem canonicalMixedMeasure_congrOn {N : ℕ} {Ω : Opens (ComplexModel N)}
    {f g : Fin N → ComplexModel N → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (hg : ∀ i, IsLocallyBoundedPshOn Ω (g i))
    (hfg : ∀ i, EqOn (f i) (g i) Ω) :
    canonicalMixedBedfordTaylorMeasure Ω f hf = canonicalMixedBedfordTaylorMeasure Ω g hg := by
  rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hf,
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hg]
  apply positive_trace_congr
  exact btProduct_congr N 0 f g _ hfg

/-- Adding genuine bounded PSH functions in each slot increases the actual
canonical mixed measure, through positivity of the actual current difference. -/
theorem canonicalMixedMeasure_le_add {N : ℕ} {Ω : Opens (ComplexModel N)}
    (f g : Fin N → ComplexModel N → ℝ)
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (hg : ∀ i, IsLocallyBoundedPshOn Ω (g i)) :
    canonicalMixedBedfordTaylorMeasure Ω f hf ≤
      canonicalMixedBedfordTaylorMeasure Ω (fun i z => f i z + g i z)
        (fun i => isLocallyBoundedPshOn_add (hf i) (hg i)) := by
  rw [canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hf,
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
      (fun i => isLocallyBoundedPshOn_add (hf i) (hg i))]
  exact traceMeasure_btProduct_le_add f g hf hg _ _

/-- The old-potential traces are dominated by the corresponding traces of
a common potential whose difference is PSH on the original coordinate domain. -/
theorem nearbyMixedMeasure_old_le_of_psh_difference {N : ℕ} {Ω : Opens (ComplexModel N)}
    {u w g : ComplexModel N → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hw : IsLocallyBoundedPshOn Ω w) (hg : IsLocallyBoundedPshOn Ω g)
    (huw : ∀ z ∈ Ω, u z + g z = w z) (l : ℕ) :
    nearbyMixedMeasure Ω u u hu hu l 0 ≤ nearbyMixedMeasure Ω w w hw hw l 0 := by
  classical
  let f : Fin N → ComplexModel N → ℝ := mixedTuple u u HermitianProducts.flatQuadratic l 0
  let b : Fin N → ComplexModel N → ℝ := fun i z => if i.val < l then g z else 0
  have hf : ∀ i, IsLocallyBoundedPshOn Ω (f i) := locallyBoundedPsh_mixedTuple hu hu l 0
  have hb : ∀ i, IsLocallyBoundedPshOn Ω (b i) := by
    intro i
    dsimp only [b]
    split_ifs
    · exact hg
    · exact isLocallyBoundedPshOn_of_abs_le
        (fun z _ => plurisubharmonicAt_const 0 (by simp) z) (C := 0) (by simp)
  have heq : canonicalMixedBedfordTaylorMeasure Ω (fun i z => f i z + b i z)
      (fun i => isLocallyBoundedPshOn_add (hf i) (hb i)) = nearbyMixedMeasure Ω w w hw hw l 0 := by
    apply canonicalMixedMeasure_congrOn
    intro i z hz
    dsimp only [f, b, mixedTuple]
    by_cases hi : i.val < l
    · simp only [if_pos hi]
      exact huw z hz
    · simp only [if_neg hi, add_zero]
  exact (canonicalMixedMeasure_le_add f b hf hb).trans heq.le

/-- The smooth nonnegative Hessian condition manufactures the PSH
difference required for common-correction trace domination. -/
theorem nearbyMixedMeasure_old_le_of_smooth_difference {m : ℕ}
    {Ω : Opens (ComplexModel (m + 1))} {u w g : ComplexModel (m + 1) → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hw : IsLocallyBoundedPshOn Ω w)
    (hg : ContDiffOn ℝ ∞ g Ω)
    (hddc : ∀ z ∈ Ω, ∀ v : ComplexModel (m + 1), 0 ≤ smoothDDC g z ![v, Complex.I • v])
    (huw : ∀ z ∈ Ω, u z + g z = w z) (l : ℕ) :
    nearbyMixedMeasure Ω u u hu hu l 0 ≤ nearbyMixedMeasure Ω w w hw hw l 0 := by
  apply nearbyMixedMeasure_old_le_of_psh_difference hu hw _ huw l
  exact isLocallyBoundedPshOn_of_continuousOn
    (Hermitian.plurisubharmonicOn_coe_of_smoothDDC_nonneg Ω.isOpen hg hddc) hg.continuousOn

end SGPT.PSH.HermitianBalayage
