import SGPT.Toric.OriginalGuilleminCoordinateFaces

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting Filter
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- ONE actual zero facet with positive slack at an actual point of the SAME
face excludes a minimum. All other terms use the EXISTING convex secant bound;
only this chosen zero term needs the actual logarithm limit. -/
theorem not_isMinOn_originalCornerFace_of_zero_slack (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {x q : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v A)
    (hq : q ∈ originalVertexCornerFace γ hsmooth v A) (F : latticePolytopeFacets γ)
    (hzero : facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F x = 0)
    (hb : 0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F q) :
    ¬ IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
      (originalVertexCornerFace γ hsmooth v A) x := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  let L := originalCornerFaceTilt A y
  let b := facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) F q
  let f : latticePolytopeFacets γ → (Fin n → ℝ) → ℝ := fun G z =>
    facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) G z *
      Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
        (originalCornerFacetOffset γ hsmooth v) G z)
  let other := Finset.univ.erase F
  let C := b * Real.log b + (∑ G ∈ other, (f G q - f G x)) - (L q - L x)
  have hb' : 0 < b := hb
  have hlog : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.log t < -C / b :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot _
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, ht1⟩, htlog⟩ := ((hpos.and hsmall).and hlog).exists
  have hnegative : b * Real.log t + C < 0 := by
    have h := mul_lt_mul_of_pos_left htlog hb'
    have hc : b * (-C / b) = -C := by field_simp
    rw [hc] at h
    linarith
  let xt := (1 - t) • x + t • q
  have hxt : xt ∈ originalVertexCornerFace γ hsmooth v A :=
    convex_originalVertexCornerFace γ hsmooth v A hx hq (by linarith) ht.le (by ring)
  have hxf := (originalVertexCornerPoint_mem_iff γ hsmooth v x).mp hx.1
  have hqf := (originalVertexCornerPoint_mem_iff γ hsmooth v q).mp hq.1
  have hterm (G : latticePolytopeFacets γ) : f G xt - f G x ≤ t * (f G q - f G x) := by
    have h := Real.convexOn_mul_log.2 (hxf G) (hqf G) (by linarith : 0 ≤ 1 - t) ht.le
      (show 1 - t + t = 1 by ring)
    simp only [smul_eq_mul] at h
    rw [← facetValue_combo _ _ G x q (1 - t) t (by ring)] at h
    change f G xt ≤ (1 - t) * f G x + t * f G q at h
    nlinarith
  have hother : (∑ G ∈ other, (f G xt - f G x)) ≤ t * (∑ G ∈ other, (f G q - f G x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun G _ => hterm G)
  have hslack : facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F xt = t * b := by
    rw [facetValue_combo _ _ F x q (1 - t) t (by ring), hzero]
    simp [b]
  have hchosen : f F xt - f F x = t * (b * Real.log t + b * Real.log b) := by
    change facetValue (originalCornerFacetLinear γ hsmooth v)
        (originalCornerFacetOffset γ hsmooth v) F xt *
        Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F xt) -
      facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) F x *
        Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F x) = _
    rw [hslack, hzero, Real.log_mul ht.ne' hb'.ne']
    simp only [zero_mul, sub_zero]
    ring
  have hsplit (z : Fin n → ℝ) : originalVertexCornerEntropyReal γ hsmooth v z =
      (∑ G ∈ other, f G z) + f F z :=
    (Finset.sum_erase_add Finset.univ (fun G => f G z) (Finset.mem_univ F)).symm
  have hsumdiff : originalVertexCornerEntropyReal γ hsmooth v xt -
      originalVertexCornerEntropyReal γ hsmooth v x =
      (∑ G ∈ other, (f G xt - f G x)) + (f F xt - f F x) := by
    rw [hsplit xt, hsplit x, Finset.sum_sub_distrib]
    ring
  have htilt : L xt - L x = t * (L q - L x) := by
    simp only [xt, map_add, map_smul, smul_eq_mul]
    ring
  have hdiff : originalCornerFaceObjective γ hsmooth v A y xt -
      originalCornerFaceObjective γ hsmooth v A y x =
      (∑ G ∈ other, (f G xt - f G x)) + (f F xt - f F x) - t * (L q - L x) := by
    change (originalVertexCornerEntropyReal γ hsmooth v xt - L xt) -
      (originalVertexCornerEntropyReal γ hsmooth v x - L x) = _
    rw [← hsumdiff, ← htilt]
    ring
  have hbound : originalCornerFaceObjective γ hsmooth v A y xt -
      originalCornerFaceObjective γ hsmooth v A y x ≤ t * (b * Real.log t + C) := by
    rw [hdiff, hchosen]
    dsimp only [C]
    nlinarith [hother]
  intro hmin
  have hmin' : originalCornerFaceObjective γ hsmooth v A y x ≤
      originalCornerFaceObjective γ hsmooth v A y xt := hmin hxt
  have hneg := lt_of_le_of_lt hbound (mul_neg_of_pos_of_neg ht hnegative)
  linarith

/-- The actual manufactured strict point excludes EVERY inactive zero and
EVERY free selected zero of the actual minimizer. -/
theorem originalCornerFace_minimizer_strict (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v A)
    (hmin : IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
      (originalVertexCornerFace γ hsmooth v A) x) :
    x ∈ originalVertexCornerDomain γ hsmooth v ∧ ∀ j ∉ A, 0 < x j := by
  obtain ⟨q, hq, hqopen, hqfree⟩ := exists_originalVertexCornerFace_strictPoint γ hsmooth v A
  have hxf := (originalVertexCornerPoint_mem_iff γ hsmooth v x).mp hx.1
  have hopen : x ∈ originalVertexCornerOpen γ hsmooth v := by
    intro F
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) (hxf F.val)
    exact not_isMinOn_originalCornerFace_of_zero_slack γ hsmooth v A y hx hq F.val hz
      (hqopen F) hmin
  have hcoords (j : Fin n) : 0 ≤ x j := by
    have h := hxf (originalVertexActiveFacet γ hsmooth v j).val
    rwa [originalCornerFacetValue_selected] at h
  refine ⟨⟨hopen, hcoords⟩, ?_⟩
  intro j hj
  by_contra h
  have hz : x j = 0 := le_antisymm (le_of_not_gt h) (hcoords j)
  have hzero : facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) (originalVertexActiveFacet γ hsmooth v j).val x = 0 := by
    rwa [originalCornerFacetValue_selected]
  have hqpos : 0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) (originalVertexActiveFacet γ hsmooth v j).val q := by
    rw [originalCornerFacetValue_selected]
    exact hqfree j hj
  exact not_isMinOn_originalCornerFace_of_zero_slack γ hsmooth v A y hx hq _ hzero hqpos hmin

/-- The strong all-pattern minimizer is genuinely manufactured from the
original input, with its inactive/free positivity produced internally. -/
theorem existsUnique_originalCornerFace_strict_minimizer (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    ∃! x, x ∈ originalVertexCornerFace γ hsmooth v A ∧
      x ∈ originalVertexCornerDomain γ hsmooth v ∧ (∀ j ∉ A, 0 < x j) ∧
        IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
          (originalVertexCornerFace γ hsmooth v A) x := by
  obtain ⟨x, ⟨hx, hmin⟩, huniq⟩ := existsUnique_originalCornerFace_minimizer γ hsmooth v A y
  have hstrict := originalCornerFace_minimizer_strict γ hsmooth v A y hx hmin
  refine ⟨x, ⟨hx, hstrict.1, hstrict.2, hmin⟩, ?_⟩
  intro z hz
  exact huniq z ⟨hz.1, hz.2.2.2⟩

end SGPT.Toric
