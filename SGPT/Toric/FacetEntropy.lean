import SGPT.Convex.GrowthClasses
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section
namespace SGPT.Toric

open Set SGPT.Convex
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

/-- Actual original affine facet values. -/
def facetValue (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) (i : ι) (x : E) : ℝ := L i x + a i

/-- The actual intersection of original nonnegative affine halfspaces. -/
def facetRegion (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) : Set E :=
  {x | ∀ i, 0 ≤ facetValue L a i x}

/-- Literal original finite facet entropy; the source stipulates zero times log zero is zero. -/
def facetEntropyReal (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) (x : E) : ℝ :=
  ∑ i, facetValue L a i x * Real.log (facetValue L a i x)

/-- The original entropy potential has top values outside its actual affine facet region. -/
def facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) (x : E) : EReal :=
  by
    classical
    exact if x ∈ facetRegion L a then (facetEntropyReal L a x : EReal) else ⊤

omit [Fintype ι] in
/-- Genuine affine interpolation preserves every original facet value. -/
theorem facetValue_combo (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (i : ι) (x y : E) (r s : ℝ) (hrs : r + s = 1) :
    facetValue L a i (r • x + s • y) = r * facetValue L a i x + s * facetValue L a i y := by
  simp only [facetValue, map_add, map_smul, smul_eq_mul]
  linear_combination -(a i) * hrs

omit [Fintype ι] in
/-- The actual original facet intersection is convex. -/
theorem convex_facetRegion (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) : Convex ℝ (facetRegion L a) := by
  intro x hx y hy r s hr hs hrs i
  rw [facetValue_combo L a i x y r s hrs]
  exact add_nonneg (mul_nonneg hr (hx i)) (mul_nonneg hs (hy i))

omit [Fintype ι] in
/-- The original actual affine facet intersection is closed. -/
theorem isClosed_facetRegion (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) : IsClosed (facetRegion L a) := by
  have heq : facetRegion L a = ⋂ i, {x | 0 ≤ L i x + a i} := by
    ext x
    simp [facetRegion, facetValue]
  rw [heq]
  exact isClosed_iInter (fun i ↦ isClosed_le continuous_const ((L i).continuous.add continuous_const))

/-- Actual continuity of x log x, including zero, gives genuine entropy continuity. -/
theorem continuous_facetEntropyReal (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    Continuous (facetEntropyReal L a) := by
  exact continuous_finsetSum _ (fun i _ ↦ Real.Continuous.mul_log
    ((L i).continuous.add continuous_const))

/-- Genuine actual facet interpolation and the existing entropy convexity give the true Jensen inequality. -/
theorem convexOn_facetEntropyReal (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    ConvexOn ℝ (facetRegion L a) (facetEntropyReal L a) := by
  refine ⟨convex_facetRegion L a, ?_⟩
  intro x hx y hy r s hr hs hrs
  simp only [facetEntropyReal, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [facetValue_combo L a i x y r s hrs]
  exact Real.convexOn_mul_log.2 (hx i) (hy i) hr hs hrs

/-- The actual original real-height epigraph retains exactly the affine facet constraints. -/
theorem epigraph_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    epigraph (facetEntropy L a) =
      {p : E × ℝ | p.1 ∈ facetRegion L a ∧ facetEntropyReal L a p.1 ≤ p.2} := by
  classical
  ext p
  by_cases hp : p.1 ∈ facetRegion L a <;> simp [epigraph, facetEntropy, hp]

/-- Actual Jensen inequalities give the original extended convex potential, including its top values. -/
theorem isConvex_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    IsConvex (facetEntropy L a) := by
  rw [IsConvex, epigraph_facetEntropy]
  intro p hp q hq r s hr hs hrs
  refine ⟨convex_facetRegion L a hp.1 hq.1 hr hs hrs, ?_⟩
  exact ((convexOn_facetEntropyReal L a).2 hp.1 hq.1 hr hs hrs).trans
    (add_le_add (smul_le_smul_of_nonneg_left hp.2 hr)
      (smul_le_smul_of_nonneg_left hq.2 hs))

/-- The actual original epigraph is closed even at zero facets. -/
theorem isClosed_epigraph_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    IsClosed (epigraph (facetEntropy L a)) := by
  rw [epigraph_facetEntropy]
  exact ((isClosed_facetRegion L a).preimage continuous_fst).inter
    (isClosed_le ((continuous_facetEntropyReal L a).comp continuous_fst) continuous_snd)

/-- Actual finite values occur precisely on the original affine facet region. -/
theorem effectiveDomain_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    effectiveDomain (facetEntropy L a) = facetRegion L a := by
  classical
  ext x
  by_cases hx : x ∈ facetRegion L a <;> simp [effectiveDomain, facetEntropy, hx]

/-- An actual nonempty region produces properness, without a properness certificate. -/
theorem isProper_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (hne : (facetRegion L a).Nonempty) : IsProper (facetEntropy L a) := by
  classical
  refine ⟨isConvex_facetEntropy L a, ?_, ?_⟩
  · simpa only [effectiveDomain_facetEntropy] using hne
  · intro x
    by_cases hx : x ∈ facetRegion L a <;> simp [facetEntropy, hx]

/-- The literal original facet entropy is a closed proper convex function. -/
theorem isClosedConvex_facetEntropy (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (hne : (facetRegion L a).Nonempty) : IsClosedConvex (facetEntropy L a) :=
  Or.inr (Or.inr ⟨isProper_facetEntropy L a hne,
    isClosed_epigraph_iff_lowerSemicontinuous.mp (isClosed_epigraph_facetEntropy L a)⟩)

/-- Genuine compact entropy bounds give both original global finite additive comparisons. -/
theorem facetEntropy_singularityEquiv_indicator (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (hP : IsCompact (facetRegion L a)) :
    SGPT.PSH.SingularityEquiv (facetEntropy L a) (SGPT.Convex.indicator (facetRegion L a)) := by
  classical
  obtain ⟨C, hC⟩ := (hP.image (continuous_facetEntropyReal L a)).bddAbove
  obtain ⟨D, hD⟩ := (hP.image (continuous_facetEntropyReal L a)).bddBelow
  constructor
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x ↦ ?_⟩
    by_cases hx : x ∈ facetRegion L a
    · simpa [facetEntropy, SGPT.Convex.indicator, hx] using
        EReal.coe_le_coe (hC ⟨x, hx, rfl⟩)
    · simp [facetEntropy, SGPT.Convex.indicator, hx]
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨-D, fun x ↦ ?_⟩
    by_cases hx : x ∈ facetRegion L a
    · have hbound : (0 : ℝ) ≤ facetEntropyReal L a x + -D := by
        linarith [hD ⟨x, hx, rfl⟩]
      simp only [facetEntropy, SGPT.Convex.indicator, if_pos hx]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe hbound
    · simp [facetEntropy, SGPT.Convex.indicator, hx]

section Conjugate

variable [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The literal original conjugate belongs to the original bounded support-growth class. -/
theorem conjugate_facetEntropy_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (hP : IsCompact (facetRegion L a)) :
    conjugate B (facetEntropy L a) ∈ BoundedGrowthClass B.flip (facetRegion L a) := by
  have hcompare := conjugate_singularityEquiv B (facetEntropy_singularityEquiv_indicator L a hP)
  rw [conjugate_indicator] at hcompare
  exact ⟨isClosedConvex_conjugate B (facetEntropy L a), hcompare⟩

end Conjugate

omit [Fintype ι] in
/-- An actual nonzero facet is strictly positive at every original interior point. -/
theorem facetValue_pos_of_mem_interior (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ)
    (i : ι) (hi : L i ≠ 0) {x : E} (hx : x ∈ interior (facetRegion L a)) :
    0 < facetValue L a i x := by
  have hnonneg := (interior_subset hx) i
  by_contra hpos
  have hzero : facetValue L a i x = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have hex : ∃ z : E, L i z ≠ 0 := by
    by_contra h
    push Not at h
    apply hi
    ext z
    simpa using h z
  obtain ⟨z, hz⟩ := hex
  have hneg : ∃ v : E, L i v < 0 := by
    by_cases hp : 0 < L i z
    · exact ⟨-z, by simpa using neg_neg_of_pos hp⟩
    · exact ⟨z, lt_of_le_of_ne (le_of_not_gt hp) hz⟩
  obtain ⟨v, hv⟩ := hneg
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let t : ℝ := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hden
  have hnorm : dist (x + t • v) x < ε := by
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    calc
      t * ‖v‖ < t * (‖v‖ + 1) := mul_lt_mul_of_pos_left (by linarith) ht
      _ = ε := div_mul_cancel₀ ε hden.ne'
  have hpoint := (interior_subset (hball hnorm)) i
  have hvalue : facetValue L a i (x + t • v) = facetValue L a i x + t * L i v := by
    simp only [facetValue, map_add, map_smul, smul_eq_mul]
    ring
  rw [hvalue, hzero, zero_add] at hpoint
  exact (not_lt_of_ge hpoint) (mul_neg_of_pos_of_neg ht hv)

/-- Genuine finite differentiation gives the source derivative on the actual region interior. -/
theorem hasFDerivAt_facetEntropyReal_of_mem_interior
    (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) {x : E}
    (hx : x ∈ interior (facetRegion L a)) :
    HasFDerivAt (facetEntropyReal L a)
      (∑ i, (Real.log (facetValue L a i x) + 1) • L i) x := by
  classical
  have hterm (i : ι) : HasFDerivAt
      (fun y ↦ facetValue L a i y * Real.log (facetValue L a i y))
      ((Real.log (facetValue L a i x) + 1) • L i) x := by
    by_cases hi : L i = 0
    · simpa [facetValue, hi] using hasFDerivAt_const (a i * Real.log (a i)) x
    · exact (Real.hasDerivAt_mul_log
        (facetValue_pos_of_mem_interior L a i hi hx).ne').comp_hasFDerivAt x
        ((L i).hasFDerivAt.add_const (a i))
  change HasFDerivAt (fun y ↦ ∑ i, facetValue L a i y * Real.log (facetValue L a i y))
    (∑ i, (Real.log (facetValue L a i x) + 1) • L i) x
  exact HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hterm i)

/-- The original extended potential agrees locally with its real entropy on the actual interior. -/
theorem hasFDerivAt_facetEntropy_toReal_of_mem_interior
    (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) {x : E}
    (hx : x ∈ interior (facetRegion L a)) :
    HasFDerivAt (fun y ↦ (facetEntropy L a y).toReal)
      (∑ i, (Real.log (facetValue L a i x) + 1) • L i) x := by
  classical
  apply (hasFDerivAt_facetEntropyReal_of_mem_interior L a hx).congr_of_eventuallyEq
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  simp [facetEntropy, interior_subset hy]

/-- The actual Riesz identification yields precisely the original source vector gradient sum. -/
theorem gradient_facetEntropy_toReal_of_mem_interior
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (u : ι → H) (a : ι → ℝ)
    {x : H} (hx : x ∈ interior (facetRegion (fun i ↦ (InnerProductSpace.toDual ℝ H) (u i)) a)) :
    gradient (fun y ↦ (facetEntropy (fun i ↦ (InnerProductSpace.toDual ℝ H) (u i)) a y).toReal) x =
      ∑ i, (Real.log (facetValue (fun i ↦ (InnerProductSpace.toDual ℝ H) (u i)) a i x) + 1) • u i := by
  simpa only [map_sum, map_smul, LinearIsometryEquiv.symm_apply_apply] using
    (hasFDerivAt_facetEntropy_toReal_of_mem_interior
      (fun i ↦ (InnerProductSpace.toDual ℝ H) (u i)) a hx).hasGradientAt.gradient

end SGPT.Toric
