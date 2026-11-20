import SGPT.PSH.SourceSubgeodesicConvexity
import SGPT.Foundations.Analysis.Pending.SubgeodesicGluing

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- Assigning the actual original values at zero and one leaves the
ENTIRE original curve unchanged, at every point and every real time. -/
theorem sourceAssignedClosedTrace_self {X : Type*} (curve : ℝ → X → EReal) :
    closedSubgeodesicSlice curve (curve 0) (curve 1) = curve := by
  funext t
  by_cases h0 : t = 0
  · simp only [h0, closedSubgeodesicSlice_zero]
  by_cases h1 : t = 1
  · simp only [h1, closedSubgeodesicSlice_one]
  simp only [closedSubgeodesicSlice, if_neg h0, if_neg h1]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {curve replacement : ℝ → M → EReal}

omit [BorelSpace M] in
/-- Exact original closed-unit-interval normalization, without an extra
all-real-time PSH or endpoint-limit hypothesis. -/
theorem sourceSubgeodesicClosedInterval_unit_iff :
    SourceSubgeodesicClosedInterval omega θ 0 1 curve ↔
      SourceSubgeodesicFrom omega θ curve (curve 0) (curve 1) := by
  constructor
  · intro h
    simpa only [mul_one, mul_zero, add_zero] using h.2
  · intro h
    exact ⟨zero_le_one, by simpa only [mul_one, mul_zero, add_zero] using h⟩

/-- Actual original endpoint and genuine interior PSH produce EVERY
original closed slice, including both assigned endpoint values. -/
theorem SourceSubgeodesicClosedInterval.thetaPSH_unit
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (ofFixedModel n M).IsThetaPSH θ (curve t) := by
  have hs := sourceSubgeodesicClosedInterval_unit_iff.mp h
  by_cases h0 : t = 0
  · simpa only [h0] using hs.1
  by_cases h1 : t = 1
  · simpa only [h1] using hs.2.1
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve (curve 0) (curve 1)).mp hs
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (hn.interior.thetaPshPotential
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩)

/-- WHOLE original closed restriction proposition, on the SAME original
curve for EVERY 0≤a≤b≤1, including the closed degenerate case. Genuine
joint PSH and actual GLOBAL endpoint L1 are internally transported. -/
theorem SourceSubgeodesicClosedInterval.restrict_unit
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    SourceSubgeodesicClosedInterval omega θ a b curve := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    exact (sourceSubgeodesicClosedInterval_self_iff omega θ a curve).mpr
      (h.thetaPSH_unit ⟨ha, hb⟩)
  have hs := sourceSubgeodesicClosedInterval_unit_iff.mp h
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve (curve 0) (curve 1)).mp hs
  have hr := hn.closedAffineReparametrized ha hb hlt
  have hr' : IsSubgeodesicFrom (atlasClosedFormToNative θ).val
      (fun s ↦ curve (s * b + (1 - s) * a)) (curve a) (curve b) := by
    have heq : affineReparametrizedCurve curve a b =
        (fun s ↦ curve (s * b + (1 - s) * a)) := by
      funext s
      unfold affineReparametrizedCurve affineTimeReparam
      congr 1
      ring
    simpa only [sourceAssignedClosedTrace_self, heq] using hr
  exact ⟨hab, (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr hr'⟩

/-- LITERAL original piecewise replacement; keep the old curve at BOTH
seams and outside the open replacement interval. -/
def sourceSubgeodesicReplacementCurve {X : Type*}
    (curve replacement : ℝ → X → EReal) (a b : ℝ) : ℝ → X → EReal := by
  classical
  exact fun t ↦ if t ∈ Ioo a b then replacement t else curve t

/-- The actual source piecewise family is the ENTIRE genuine native
replacement after normalizing the original physical replacement curve.
Positive interval length justifies the inverse affine readback. -/
theorem sourceSubgeodesicReplacementCurve_eq_native {X : Type*}
    (curve replacement : ℝ → X → EReal) {a b : ℝ} (hab : a < b) :
    sourceSubgeodesicReplacementCurve curve replacement a b =
      SubgeodesicGluing.replacementCurve curve
        (fun s ↦ replacement (s * b + (1 - s) * a)) a b := by
  classical
  funext t
  unfold sourceSubgeodesicReplacementCurve SubgeodesicGluing.replacementCurve
  by_cases ht : t ∈ Ioo a b
  · simp only [if_pos ht]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  · simp only [if_neg ht]

/-- WHOLE original dominating replacement lemma: the SAME literal source
piecewise function has genuine full product PSH and actual GLOBAL endpoint
L1. Original endpoint matching/order are the ONLY replacement premises;
seam USC, PSH output and endpoint convergence are internally produced. -/
theorem source_subgeodesic_gluing
    (h : SourceSubgeodesicClosedInterval omega θ 0 1 curve)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hr : SourceSubgeodesicClosedInterval omega θ a b replacement)
    (hleft : replacement a = curve a) (hright : replacement b = curve b)
    (hdom : ∀ t ∈ Ioo a b, curve t ≤ replacement t) :
    SourceSubgeodesicClosedInterval omega θ 0 1
      (sourceSubgeodesicReplacementCurve curve replacement a b) := by
  have hs := sourceSubgeodesicClosedInterval_unit_iff.mp h
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve (curve 0) (curve 1)).mp hs
  have hrn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp hr.2
  rw [hleft, hright] at hrn
  have hrn' : IsSubgeodesicFrom (atlasClosedFormToNative θ).val
      (fun s ↦ replacement (s * b + (1 - s) * a))
      (closedSubgeodesicSlice curve (curve 0) (curve 1) a)
      (closedSubgeodesicSlice curve (curve 0) (curve 1) b) := by
    simpa only [sourceAssignedClosedTrace_self] using hrn
  have htime (t : ℝ) : ((t - a) / (b - a)) * b +
      (1 - (t - a) / (b - a)) * a = t := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hg := SubgeodesicGluing.isSubgeodesicFrom_replacementCurve hn ha hb hab hrn'
    (fun t ht ↦ by simpa only [htime] using hdom t ht)
  rw [← sourceSubgeodesicReplacementCurve_eq_native curve replacement hab] at hg
  have hsource := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr hg
  have h0 : (0 : ℝ) ∉ Ioo a b := fun ht ↦ (not_lt_of_ge ha) ht.1
  have h1 : (1 : ℝ) ∉ Ioo a b := fun ht ↦ (not_lt_of_ge hb) ht.2
  have he0 : sourceSubgeodesicReplacementCurve curve replacement a b 0 = curve 0 := by
    simp only [sourceSubgeodesicReplacementCurve, if_neg h0]
  have he1 : sourceSubgeodesicReplacementCurve curve replacement a b 1 = curve 1 := by
    simp only [sourceSubgeodesicReplacementCurve, if_neg h1]
  apply sourceSubgeodesicClosedInterval_unit_iff.mpr
  simpa only [he0, he1] using hsource

end SGPT.PSH.VariableComplexAtlas
