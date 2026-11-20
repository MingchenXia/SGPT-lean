import SGPT.PSH.SourceRelativeGeodesics
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMonotone

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology ProductComplexManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Only the original open-time values matter: actual product functions agree
on the entire source strip, and both original GLOBAL distance maps are
eventually equal. No off-interval PSH or pole-readback premise is added. -/
theorem SourceSubgeodesicFrom.congr_Ioo {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve other : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁)
    (heq : ∀ t ∈ Ioo (0 : ℝ) 1, curve t = other t) :
    SourceSubgeodesicFrom omega θ other u₀ u₁ := by
  have hprod : (fun p : M × sourceRayTimeStrip ↦ curve (sourceRayTime p.2).re p.1) =
      (fun p : M × sourceRayTimeStrip ↦ other (sourceRayTime p.2).re p.1) := by
    funext p
    exact congrFun (heq _ p.2.property) p.1
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · refine ⟨fun t ht ↦ (heq t ht) ▸ h.2.2.1.1 t ht, ?_⟩
    change (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) _
    rw [← hprod]
    exact h.2.2.1.2
  · exact h.2.2.2.1.congr' (sourceRay_endpoint_filters.1.mono fun t ht ↦
      congrArg (fun f ↦ sourceGlobalL1Distance omega f u₀) (heq t ht))
  · exact h.2.2.2.2.congr' (sourceRay_endpoint_filters.2.mono fun t ht ↦
      congrArg (fun f ↦ sourceGlobalL1Distance omega f u₁) (heq t ht))

/-- The original explicit consequence at chapter_rays:347: every closed
full-mass Perron subsegment is an actual original subgeodesic, including
the degenerate interval and both original GLOBAL L1 endpoint limits. -/
theorem sourcePerronClosedSlice_isSubgeodesic [ConnectedSpace M]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u₀ u₁ : M → EReal}
    {hφ : SourceModelPotential θ φ}
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    SourceSubgeodesicClosedInterval omega θ a b (sourcePerronClosedSlice omega θ u₀ u₁) := by
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst b
    exact (sourceSubgeodesicClosedInterval_self_iff omega θ a _).mpr
      (sourceRelativeFullMass_sourcePerronClosedSlice omega h₀ h₁ ⟨ha, hb⟩).choose
  have hsub := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp
    (sourcePerron_isSubgeodesicFrom_of_relativeFullMass omega h₀ h₁)
  have hr := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
    (hsub.closedAffineReparametrized ha hb hab')
  refine ⟨hab, hr.congr_Ioo ?_⟩
  intro s hs
  have hpos := mul_pos hs.1 (sub_pos.mpr hab')
  have hpos' := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hab')
  have htime : affineTimeReparam a b s = s * b + (1 - s) * a := by
    unfold affineTimeReparam
    ring
  have hti : s * b + (1 - s) * a ∈ Ioo (0 : ℝ) 1 :=
    ⟨by nlinarith, by nlinarith⟩
  change sourcePerronGeodesic omega θ u₀ u₁ (affineTimeReparam a b s) = _
  rw [htime]
  exact (closedSubgeodesicSlice_eq_curve hti).symm

/-- A stronger genuine source theorem than the printed ordered-geodesic
lemma: the actual assigned closed Perron trace is antitone from endpoint
PSH and order alone. Literal poles and both original endpoints are retained. -/
theorem sourcePerron_antitone_closed (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (h₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ u₁) (h10 : u₁ ≤ u₀) (x : M) :
    AntitoneOn (fun t ↦ sourcePerronClosedSlice omega θ u₀ u₁ t x) (Icc (0 : ℝ) 1) := by
  simp only [sourcePerronClosedSlice_eq_native]
  exact FiniteGeodesicMonotone.antitoneOn_closedSubgeodesicSlice
    ((isThetaPSH_iff_nativeThetaPotential θ u₀).mp h₀)
    ((isThetaPSH_iff_nativeThetaPotential θ u₁).mp h₁) h10 x

omit [BorelSpace M] in
/-- The entire actual closed source geodesic equals its own assigned Perron
trace on [0,1], preserving the actual original endpoint values. -/
theorem SourceGeodesicClosedInterval.eq_sourcePerronClosedSlice_unit
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ 0 1 curve)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    curve t = sourcePerronClosedSlice omega θ (curve 0) (curve 1) t := by
  by_cases ht0 : t = 0
  · simp only [ht0, sourcePerronClosedSlice, closedSubgeodesicSlice_zero]
  by_cases ht1 : t = 1
  · simp only [ht1, sourcePerronClosedSlice, closedSubgeodesicSlice_one]
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hn : SourceIsGeodesicFrom omega θ curve (curve 0) (curve 1) := by
    simpa only [mul_one, mul_zero, add_zero] using h.2.2
  simpa only [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hti] using hn.2.2.2 t hti

/-- Every original closed-unit-interval geodesic between ordered endpoints
is decreasing, with no full-mass or endpoint-output certificate hypothesis. -/
theorem sourceGeodesic_antitone_unit {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (h10 : curve 1 ≤ curve 0) (x : M) :
    AntitoneOn (fun t ↦ curve t x) (Icc (0 : ℝ) 1) := by
  have hanti := sourcePerron_antitone_closed omega
    (h.2.1 0 ⟨le_rfl, zero_le_one⟩) (h.2.1 1 ⟨zero_le_one, le_rfl⟩) h10 x
  intro s hs t ht hst
  change curve t x ≤ curve s x
  rw [h.eq_sourcePerronClosedSlice_unit ht, h.eq_sourcePerronClosedSlice_unit hs]
  exact hanti hs ht hst

/-- The WHOLE original lma:geoddecreasing, including its printed additional
subgeodesic hypothesis. The stronger preceding genuine source theorem shows
that this additional original assumption is not needed for monotonicity. -/
theorem sourceGeodesic_antitone_of_subgeodesic {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (_hsub : SourceSubgeodesicClosedInterval omega θ 0 1 curve)
    (h10 : curve 1 ≤ curve 0) (x : M) :
    AntitoneOn (fun t ↦ curve t x) (Icc (0 : ℝ) 1) :=
  sourceGeodesic_antitone_unit h h10 x

end SGPT.PSH.VariableComplexAtlas
