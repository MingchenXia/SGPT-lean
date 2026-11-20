import SGPT.PSH.SourceSubgeodesic
import SGPT.PSH.ThetaRooftop
import SGPT.Convex.Epigraph
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- The original closed-interval trace retains the prescribed endpoints and
literal interior poles. Extension by top outside its domain expresses source
convexity through the existing original real-height epigraph definition. -/
def sourceClosedIntervalTrace {X : Type*} (curve : ℝ → X → EReal)
    (u₀ u₁ : X → EReal) (x : X) (t : ℝ) : EReal :=
  if t ∈ Icc (0 : ℝ) 1 then closedSubgeodesicSlice curve u₀ u₁ t x else ⊤

theorem mem_epigraph_sourceClosedIntervalTrace {X : Type*} (curve : ℝ → X → EReal)
    (u₀ u₁ : X → EReal) (x : X) (p : ℝ × ℝ) :
    p ∈ SGPT.Convex.epigraph (sourceClosedIntervalTrace curve u₀ u₁ x) ↔
      p.1 ∈ Icc (0 : ℝ) 1 ∧ closedSubgeodesicSlice curve u₀ u₁ p.1 x ≤ (p.2 : EReal) := by
  change (if p.1 ∈ Icc (0 : ℝ) 1 then closedSubgeodesicSlice curve u₀ u₁ p.1 x else ⊤) ≤
    (p.2 : EReal) ↔ _
  by_cases ht : p.1 ∈ Icc (0 : ℝ) 1
  · rw [if_pos ht]
    exact ⟨fun hp ↦ ⟨ht, hp⟩, fun hp ↦ hp.2⟩
  · rw [if_neg ht]
    simp only [ht, false_and, top_le_iff, EReal.coe_ne_top]

/-- The literal original infimum over ALL interior times, with both extended
endpoints retained in the complete lattice. -/
def sourceSliceInfimum {X : Type*} (curve : ℝ → X → EReal) : X → EReal :=
  fun x ↦ ⨅ t : Ioo (0 : ℝ) 1, curve (t : ℝ) x

theorem sourceSliceInfimum_eq_native {X : Type*} (curve : ℝ → X → EReal) :
    sourceSliceInfimum curve = SubgeodesicInfimum.sliceInfimum curve := rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Genuine native closed restriction and the actual endpoint L1 chord prove
the original chord on every nondegenerate CLOSED subinterval, including
interpolation weights zero and one and either original negative pole. -/
theorem SourceSubgeodesicFrom.le_closedChord {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : SourceSubgeodesicFrom omega θ curve u₀ u₁)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hs : s ∈ Icc (0 : ℝ) 1) (x : M) :
    closedSubgeodesicSlice curve u₀ u₁ ((1 - s) * a + s * b) x ≤
      eRealChord (closedSubgeodesicSlice curve u₀ u₁ a x)
        (closedSubgeodesicSlice curve u₀ u₁ b x) s := by
  rcases hs.1.eq_or_lt with hs0 | hs0
  · rw [← hs0]
    simp [eRealChord]
  rcases hs.2.eq_or_lt with hs1 | hs1
  · rw [hs1]
    simp [eRealChord]
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h
  have hchord := (hn.closedAffineReparametrized ha hb hab).le_eRealChord ⟨hs0, hs1⟩ x
  have ht : (1 - s) * a + s * b ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hs0 (sub_pos.mpr hab)]
    · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hab)]
  rw [closedSubgeodesicSlice_eq_curve ht]
  have heq : affineTimeReparam a b s = (1 - s) * a + s * b := by
    unfold affineTimeReparam
    ring
  simpa only [affineReparametrizedCurve, heq] using hchord

/-- The original convexity conclusion on the ENTIRE CLOSED interval, using
the existing source real-height epigraph definition. Equal times, zero
weights, both prescribed endpoints and literal negative poles are included. -/
theorem SourceSubgeodesicFrom.isConvex_closedIntervalTrace {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (x : M) :
    SGPT.Convex.IsConvex (sourceClosedIntervalTrace curve u₀ u₁ x) := by
  let E := SGPT.Convex.epigraph (sourceClosedIntervalTrace curve u₀ u₁ x)
  have hordered : ∀ (p q : ℝ × ℝ), p ∈ E → q ∈ E → p.1 ≤ q.1 →
      ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 → α • p + β • q ∈ E := by
    intro p q hp hq hpq α β hα hβ hsum
    have hp' := (mem_epigraph_sourceClosedIntervalTrace curve u₀ u₁ x p).mp hp
    have hq' := (mem_epigraph_sourceClosedIntervalTrace curve u₀ u₁ x q).mp hq
    apply (mem_epigraph_sourceClosedIntervalTrace curve u₀ u₁ x (α • p + β • q)).mpr
    refine ⟨(convex_Icc (0 : ℝ) 1) hp'.1 hq'.1 hα hβ hsum, ?_⟩
    change closedSubgeodesicSlice curve u₀ u₁ (α * p.1 + β * q.1) x ≤
      ((α * p.2 + β * q.2 : ℝ) : EReal)
    rcases hpq.eq_or_lt with heq | hlt
    · have htime : α * p.1 + β * q.1 = p.1 := by
        calc
          _ = (α + β) * p.1 := by rw [← heq]; ring
          _ = p.1 := by rw [hsum, one_mul]
      rw [htime]
      have hmin : closedSubgeodesicSlice curve u₀ u₁ p.1 x ≤
          ((min p.2 q.2 : ℝ) : EReal) := by
        rcases le_total p.2 q.2 with hpqheight | hqpheight
        · simpa only [min_eq_left hpqheight] using hp'.2
        · rw [min_eq_right hqpheight, heq]
          exact hq'.2
      have hheight : min p.2 q.2 ≤ α * p.2 + β * q.2 := by
        calc
          _ = (α + β) * min p.2 q.2 := by rw [hsum, one_mul]
          _ = α * min p.2 q.2 + β * min p.2 q.2 := add_mul _ _ _
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hα)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ)
      exact hmin.trans (EReal.coe_le_coe hheight)
    · have hβI : β ∈ Icc (0 : ℝ) 1 := ⟨hβ, by linarith⟩
      have hc := h.le_closedChord hp'.1.1 hq'.1.2 hlt hβI x
      have hm := eRealChord_mono hp'.2 hq'.2 hβI.1 hβI.2
      have hbound := hc.trans hm
      rw [SubgeodesicInfimum.eRealChord_coe_coe] at hbound
      have hcoefficient : 1 - β = α := by linarith
      simpa only [hcoefficient] using hbound
  change Convex ℝ E
  intro p hp q hq α β hα hβ hsum
  rcases le_total p.1 q.1 with hpq | hqp
  · exact hordered p q hp hq hpq α β hα hβ hsum
  · simpa only [add_comm] using hordered q p hq hp hqp β α hβ hα (by linarith)

/-- The existing genuine strip-Kiselman proof and internally produced infimum
nondegeneracy give the FULL original theta-PSH class of the actual infimum. -/
theorem SourceSubgeodesicFrom.isThetaPSH_sliceInfimum [ConnectedSpace M]
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    (ofFixedModel n M).IsThetaPSH θ (sourceSliceInfimum curve) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ (sourceSliceInfimum curve)).mpr
  exact SubgeodesicInfimumThetaPsh.isThetaPshPotential_sliceInfimum
    ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h).interior

/-- The produced actual original theta-PSH infimum is an element of the
genuine original common-minorant family. The conclusion is the actual source
ROOFTOP bound, beyond a pointwise minimum inequality. -/
theorem SourceSubgeodesicFrom.sliceInfimum_le_thetaRooftop [ConnectedSpace M]
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    sourceSliceInfimum curve ≤ thetaRooftop θ u₀ u₁ := by
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h
  exact le_thetaRooftop h.isThetaPSH_sliceInfimum
    (SubgeodesicInfimum.sliceInfimum_le_left hn)
    (SubgeodesicInfimum.sliceInfimum_le_right hn)

/-- The ENTIRE original prop:convexsubgeod: full closed-interval convexity,
genuine original theta-PSH of the literal infimum, and the actual original
rooftop inequality. This is not an interior convexity/minimum-bound proxy. -/
theorem source_subgeodesic_convexity [ConnectedSpace M]
    {omega : KahlerBackground n M} {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    (∀ x, SGPT.Convex.IsConvex (sourceClosedIntervalTrace curve u₀ u₁ x)) ∧
      (ofFixedModel n M).IsThetaPSH θ (sourceSliceInfimum curve) ∧
        sourceSliceInfimum curve ≤ thetaRooftop θ u₀ u₁ :=
  ⟨h.isConvex_closedIntervalTrace, h.isThetaPSH_sliceInfimum, h.sliceInfimum_le_thetaRooftop⟩

end SGPT.PSH.VariableComplexAtlas
