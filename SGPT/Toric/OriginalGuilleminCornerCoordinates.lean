import SGPT.Toric.OriginalGuilleminConvexReference

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual real extension of the original ALL-edge integral basis,
bundled by the existing finite-dimensional continuous-linear equivalence. -/
def originalVertexCornerLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (integralRealBasis (originalVertexHalfspaceBasis γ hsmooth v)).equivFun.symm.toContinuousLinearEquiv

/-- Original vertex-centered corner coordinates on the SAME real lattice space. -/
def originalVertexCornerPoint (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  integerCast v.val + originalVertexCornerLinear γ hsmooth v x

omit [Nonempty K] in
theorem originalVertexCornerPoint_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    originalVertexCornerPoint γ hsmooth v 0 = integerCast v.val := by
  simp [originalVertexCornerPoint]

/-- Actual translation and the true basis inverse give a genuine homeomorphism,
including the empty coordinate family. -/
def originalVertexCornerHomeomorph (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun := originalVertexCornerPoint γ hsmooth v
  invFun := fun m => (originalVertexCornerLinear γ hsmooth v).symm (m - integerCast v.val)
  left_inv x := by simp [originalVertexCornerPoint]
  right_inv m := by simp [originalVertexCornerPoint]
  continuous_toFun := continuous_const.add (originalVertexCornerLinear γ hsmooth v).continuous
  continuous_invFun := (originalVertexCornerLinear γ hsmooth v).symm.continuous.comp
    (continuous_id.sub continuous_const)

/-- The actual affine facet linear part after the original basis change. -/
def originalCornerFacetLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (integralRealFunctional (originalFacetNormal γ hsmooth F)).comp
    (originalVertexCornerLinear γ hsmooth v).toContinuousLinearMap

/-- Its actual offset is the original slack at the original vertex. -/
def originalCornerFacetOffset (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) : ℝ :=
  integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
    F (integerCast v.val)

omit [Nonempty K] in
/-- Original corner unit vectors map to the SAME original integral edge vectors. -/
theorem originalVertexCornerLinear_basis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    originalVertexCornerLinear γ hsmooth v (Pi.basisFun ℝ (Fin n) j) =
      integerCast (originalVertexHalfspaceBasis γ hsmooth v j) := by
  change (integralRealBasis (originalVertexHalfspaceBasis γ hsmooth v)).equivFun.symm _ = _
  simp [Module.Basis.equivFun_symm_apply, Pi.basisFun_apply, Pi.single_apply, integralRealBasis_apply]

/-- Literal original integral normal evaluations are the actual corner coefficients. -/
theorem originalCornerFacetLinear_basis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) (j : Fin n) :
    originalCornerFacetLinear γ hsmooth v F (Pi.basisFun ℝ (Fin n) j) =
      (originalFacetNormal γ hsmooth F (originalVertexHalfspaceBasis γ hsmooth v j) : ℝ) := by
  change integralRealFunctional (originalFacetNormal γ hsmooth F)
    (originalVertexCornerLinear γ hsmooth v (Pi.basisFun ℝ (Fin n) j)) = _
  rw [originalVertexCornerLinear_basis, integralRealFunctional_integerCast]

/-- Exact original affine slack, before any real readback of extended entropy. -/
theorem originalCornerFacetValue_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) (x : Fin n → ℝ) :
    facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F x =
    integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
      F (originalVertexCornerPoint γ hsmooth v x) := by
  change integralRealFunctional (originalFacetNormal γ hsmooth F)
      (originalVertexCornerLinear γ hsmooth v x) +
      (integralRealFunctional (originalFacetNormal γ hsmooth F) (integerCast v.val) +
        (originalFacetOffset γ hsmooth F : ℝ)) =
    integralRealFunctional (originalFacetNormal γ hsmooth F)
      (integerCast v.val + originalVertexCornerLinear γ hsmooth v x) + _
  rw [map_add]
  ring

/-- The selected ACTUAL facet has literal coordinate slack x_j. -/
theorem originalCornerFacetValue_selected (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) (x : Fin n → ℝ) :
    facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v)
      (originalVertexActiveFacet γ hsmooth v j).val x = x j := by
  rw [originalCornerFacetValue_eq]
  change integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
    (originalVertexFacet γ hsmooth (v, j)) _ = _
  change integralRealFunctional
      (originalFacetNormal γ hsmooth (originalVertexFacet γ hsmooth (v, j)))
      (originalVertexCornerPoint γ hsmooth v x) +
      (originalFacetOffset γ hsmooth (originalVertexFacet γ hsmooth (v, j)) : ℝ) = x j
  rw [(originalFacet_pair_vertexFacet γ hsmooth (v, j)).1,
    (originalFacet_pair_vertexFacet γ hsmooth (v, j)).2]
  change integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
    (originalVertexHalfspaceOffset γ hsmooth) (v, j) _ = _
  rw [originalVertexHalfspaceValue_eq_coord]
  simp only [originalVertexCornerPoint, add_sub_cancel_left]
  change ((integralRealBasis (originalVertexHalfspaceBasis γ hsmooth v)).equivFun
    ((integralRealBasis (originalVertexHalfspaceBasis γ hsmooth v)).equivFun.symm x)) j = x j
  rw [LinearEquiv.apply_symm_apply]

/-- The complement of ALL actual facets containing v; no chosen incidence
or positivity data is supplied as an input. -/
def originalVertexInactiveFacets (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ) :=
  {F : latticePolytopeFacets γ // integerCast v.val ∉ F.val}

@[instance_reducible] def originalVertexInactiveFacetFintype (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Fintype (originalVertexInactiveFacets γ v) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  exact Subtype.fintype _

/-- EVERY actual inactive facet has genuine strict slack at zero. -/
theorem originalCornerInactiveFacetValue_zero_pos (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : originalVertexInactiveFacets γ v) :
    0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val 0 := by
  rw [originalCornerFacetValue_eq, originalVertexCornerPoint_zero]
  apply originalFacetValue_pos_of_not_selected γ hsmooth v F.val
  rintro ⟨j, hj⟩
  exact F.property (hj ▸ (originalVertexActiveFacet γ hsmooth v j).property)

/-- The genuine open set where EVERY inactive original facet stays positive. -/
def originalVertexCornerOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) : Set (Fin n → ℝ) :=
  {x | ∀ F : originalVertexInactiveFacets γ v,
    0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x}

theorem isOpen_originalVertexCornerOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    IsOpen (originalVertexCornerOpen γ hsmooth v) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  rw [originalVertexCornerOpen, Set.ofPred_forall]
  change IsOpen (⋂ F : originalVertexInactiveFacets γ v,
    {x | 0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x})
  exact isOpen_iInter_of_finite (fun F => isOpen_lt continuous_const
    ((originalCornerFacetLinear γ hsmooth v F.val).continuous.add continuous_const))

theorem convex_originalVertexCornerOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Convex ℝ (originalVertexCornerOpen γ hsmooth v) := by
  rw [originalVertexCornerOpen, Set.ofPred_forall]
  change Convex ℝ (⋂ F : originalVertexInactiveFacets γ v,
    {x | 0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x})
  apply convex_iInter
  intro F
  have heq : {x | 0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x} =
      {x | -originalCornerFacetOffset γ hsmooth v F.val <
        originalCornerFacetLinear γ hsmooth v F.val x} := by
    ext x
    change (0 < originalCornerFacetLinear γ hsmooth v F.val x +
      originalCornerFacetOffset γ hsmooth v F.val) ↔
      -originalCornerFacetOffset γ hsmooth v F.val < originalCornerFacetLinear γ hsmooth v F.val x
    constructor <;> intro h <;> linarith
  rw [heq]
  exact convex_halfSpace_gt (originalCornerFacetLinear γ hsmooth v F.val).toLinearMap.isLinear _

theorem zero_mem_originalVertexCornerOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    0 ∈ originalVertexCornerOpen γ hsmooth v :=
  originalCornerInactiveFacetValue_zero_pos γ hsmooth v

/-- Actual nonnegative selected coordinates, retaining strict inactive slacks. -/
def originalVertexCornerDomain (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) : Set (Fin n → ℝ) :=
  originalVertexCornerOpen γ hsmooth v ∩ {x | ∀ j, 0 ≤ x j}

/-- The original facet inequalities are preserved on the SAME real region. -/
theorem originalVertexCornerPoint_mem_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) :
    originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ ↔
      ∀ F : latticePolytopeFacets γ,
        0 ≤ facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F x := by
  rw [latticePolytope_eq_originalFacetRegion γ hsmooth]
  simp only [originalCornerFacetValue_eq]
  rfl

/-- Genuine active-facet exhaustion supplies actual membership in P. -/
theorem originalVertexCornerPoint_mem_of_mem_domain (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ := by
  rw [originalVertexCornerPoint_mem_iff]
  intro F
  by_cases hvF : integerCast v.val ∈ F.val
  · obtain ⟨j, hj⟩ := originalVertexActiveFacet_surjective γ hsmooth v ⟨F, hvF⟩
    have hF : (originalVertexActiveFacet γ hsmooth v j).val = F := congrArg Subtype.val hj
    rw [← hF, originalCornerFacetValue_selected]
    exact hx.2 j
  · exact (hx.1 ⟨F, hvF⟩).le

/-- Selected-coordinate nonnegativity is EXACTLY the original region condition
on the actual open corner set, with no supplied face-domain dictionary. -/
theorem originalVertexCornerDomain_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    originalVertexCornerDomain γ hsmooth v = originalVertexCornerOpen γ hsmooth v ∩
      originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v hx⟩
  · rintro ⟨hopen, hP⟩
    refine ⟨hopen, fun j => ?_⟩
    have h := (originalVertexCornerPoint_mem_iff γ hsmooth v x).mp hP
      (originalVertexActiveFacet γ hsmooth v j).val
    rwa [originalCornerFacetValue_selected] at h

/-- Only inactive facets enter the smooth remainder; it is the EXISTING
literal real facet entropy on the actual complementary finite family. -/
def originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) : (Fin n → ℝ) → ℝ :=
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  facetEntropyReal (fun F : originalVertexInactiveFacets γ v => originalCornerFacetLinear γ hsmooth v F.val)
    (fun F => originalCornerFacetOffset γ hsmooth v F.val)

/-- The existing zero-times-log-zero continuity theorem applies literally. -/
theorem continuous_originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Continuous (originalVertexCornerRemainder γ hsmooth v) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  exact continuous_facetEntropyReal _ _

/-- Genuine smooth logarithm, affine, product and finite-sum rules apply on
the PRODUCED open set, without a supplied smoothness certificate. -/
theorem contDiffOn_originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiffOn ℝ ∞ (originalVertexCornerRemainder γ hsmooth v)
      (originalVertexCornerOpen γ hsmooth v) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  change ContDiffOn ℝ ∞ (fun x => ∑ F : originalVertexInactiveFacets γ v,
    facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) F.val x *
      Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
        (originalCornerFacetOffset γ hsmooth v) F.val x)) _
  apply ContDiffOn.sum
  intro F _
  have hlin : ContDiffOn ℝ ∞ (fun x => facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x) (originalVertexCornerOpen γ hsmooth v) :=
    ((originalCornerFacetLinear γ hsmooth v F.val).contDiff.add contDiff_const).contDiffOn
  exact hlin.mul (hlin.log (fun x hx => (hx F).ne'))

/-- The prior actual entropy derivative theorem supplies the remainder's
first derivative after open-set membership produces genuine interior. -/
theorem hasFDerivAt_originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    let _ := originalVertexInactiveFacetFintype γ hsmooth v
    HasFDerivAt (originalVertexCornerRemainder γ hsmooth v)
      (∑ F : originalVertexInactiveFacets γ v,
        (Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F.val x) + 1) •
            originalCornerFacetLinear γ hsmooth v F.val) x := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  apply hasFDerivAt_facetEntropyReal_of_mem_interior
  apply mem_interior.mpr
  exact ⟨originalVertexCornerOpen γ hsmooth v,
    fun y hy F => (hy F).le, isOpen_originalVertexCornerOpen γ hsmooth v, hx⟩

/-- The actual finite entropy sum in original corner coordinates, defined
everywhere as a real function without reading any infinite extended value. -/
def originalVertexCornerEntropyReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) : (Fin n → ℝ) → ℝ :=
  let _ := originalPolytopeFacetFintype γ hsmooth
  facetEntropyReal (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v)

theorem continuous_originalVertexCornerEntropyReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Continuous (originalVertexCornerEntropyReal γ hsmooth v) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  exact continuous_facetEntropyReal _ _

/-- The actual active bijection reindexes the ALL-DISTINCT-facet sum; this
finite identity is valid even at zero slacks and in dimension zero. -/
theorem originalVertexCornerEntropyReal_split (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) :
    originalVertexCornerEntropyReal γ hsmooth v x =
      (∑ j, x j * Real.log (x j)) + originalVertexCornerRemainder γ hsmooth v x := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  let _ : Fintype (latticePolytopeActiveFacets γ v) := Subtype.fintype _
  let f : latticePolytopeFacets γ → ℝ := fun F =>
    facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) F x *
      Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
        (originalCornerFacetOffset γ hsmooth v) F x)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun F : latticePolytopeFacets γ => integerCast v.val ∈ F.val) f
  have hactive : (∑ F : latticePolytopeActiveFacets γ v, f F.val) =
      ∑ j, x j * Real.log (x j) := by
    have h := (originalVertexActiveFacetEquiv γ hsmooth v).sum_comp
      (fun F : latticePolytopeActiveFacets γ v => f F.val)
    simpa only [originalVertexActiveFacetEquiv_apply, f, originalCornerFacetValue_selected] using h.symm
  change (∑ F : latticePolytopeFacets γ, f F) = _
  rw [← hsplit]
  exact congrArg (fun z => z + ∑ F : originalVertexInactiveFacets γ v, f F.val) hactive

/-- Exact EXTENDED source formula at every actual point: true top outside
P is retained rather than silently converted to a real value. -/
theorem originalCanonicalEntropy_corner_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) :
    originalCanonicalEntropy γ hsmooth (originalVertexCornerPoint γ hsmooth v x) =
      if originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ then
        ((originalVertexCornerEntropyReal γ hsmooth v x : ℝ) : EReal) else ⊤ := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  rw [originalCanonicalEntropy_eq]
  simp only [originalVertexCornerEntropyReal, facetEntropyReal, originalCornerFacetValue_eq]

/-- Genuine original membership precedes the literal finite entropy split. -/
theorem originalCanonicalEntropy_corner_eq_of_mem_domain (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    originalCanonicalEntropy γ hsmooth (originalVertexCornerPoint γ hsmooth v x) =
      (((∑ j, x j * Real.log (x j)) + originalVertexCornerRemainder γ hsmooth v x : ℝ) : EReal) := by
  rw [originalCanonicalEntropy_corner_eq,
    if_pos (originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v hx),
    originalVertexCornerEntropyReal_split]

end SGPT.Toric
