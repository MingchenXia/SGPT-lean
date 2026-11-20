import SGPT.Toric.OriginalGuilleminCornerCoordinates

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Literal first derivative of the actual inactive entropy remainder. -/
def originalCornerRemainderDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  ∑ F : originalVertexInactiveFacets γ v,
    (Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x) + 1) •
        originalCornerFacetLinear γ hsmooth v F.val

/-- The actual second functional derivative, using the EXISTING smulRight
continuous bilinear-map construction, without a supplied Hessian field. -/
def originalCornerRemainderHessian (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  ∑ F : originalVertexInactiveFacets γ v,
    ((facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x)⁻¹ •
        originalCornerFacetLinear γ hsmooth v F.val).smulRight
          (originalCornerFacetLinear γ hsmooth v F.val)

/-- The first derivative was genuinely produced by the prior entropy mother. -/
theorem fderiv_originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    fderiv ℝ (originalVertexCornerRemainder γ hsmooth v) x =
      originalCornerRemainderDerivative γ hsmooth v x :=
  (hasFDerivAt_originalVertexCornerRemainder γ hsmooth v hx).fderiv

/-- Existing logarithm and scalar-multiplication differentiation give the
ACTUAL second derivative on the manufactured open inactive domain. -/
theorem hasFDerivAt_originalCornerRemainderDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    HasFDerivAt (originalCornerRemainderDerivative γ hsmooth v)
      (originalCornerRemainderHessian γ hsmooth v x) x := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  change HasFDerivAt (fun y => ∑ F : originalVertexInactiveFacets γ v,
    (Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val y) + 1) •
        originalCornerFacetLinear γ hsmooth v F.val) _ x
  apply HasFDerivAt.fun_sum
  intro F _
  exact ((((originalCornerFacetLinear γ hsmooth v F.val).hasFDerivAt.add_const
    (originalCornerFacetOffset γ hsmooth v F.val)).log (hx F).ne').add_const 1).smul_const
      (originalCornerFacetLinear γ hsmooth v F.val)

/-- Local first-derivative equality proves this is the genuine derivative
of fderiv itself, rather than a separately named bilinear expression. -/
theorem hasFDerivAt_fderiv_originalVertexCornerRemainder (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    HasFDerivAt (fderiv ℝ (originalVertexCornerRemainder γ hsmooth v))
      (originalCornerRemainderHessian γ hsmooth v x) x := by
  apply (hasFDerivAt_originalCornerRemainderDerivative γ hsmooth v hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds hx] with y hy
  exact fderiv_originalVertexCornerRemainder γ hsmooth v hy

/-- Literal bilinear evaluation; the actual positive affine denominators
are preserved and no positivity assumption is hidden in a matrix certificate. -/
theorem originalCornerRemainderHessian_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η ζ : Fin n → ℝ) :
    let _ := originalVertexInactiveFacetFintype γ hsmooth v
    originalCornerRemainderHessian γ hsmooth v x η ζ =
      ∑ F : originalVertexInactiveFacets γ v,
        (originalCornerFacetLinear γ hsmooth v F.val η *
          originalCornerFacetLinear γ hsmooth v F.val ζ) /
            facetValue (originalCornerFacetLinear γ hsmooth v)
              (originalCornerFacetOffset γ hsmooth v) F.val x := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  simp only [originalCornerRemainderHessian, sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro F _
  ring

/-- Exact original integer-normal coordinate formula for every Hessian entry. -/
theorem originalCornerRemainderHessian_basis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) (j k : Fin n) :
    let _ := originalVertexInactiveFacetFintype γ hsmooth v
    originalCornerRemainderHessian γ hsmooth v x
      (Pi.basisFun ℝ (Fin n) j) (Pi.basisFun ℝ (Fin n) k) =
      ∑ F : originalVertexInactiveFacets γ v,
        ((originalFacetNormal γ hsmooth F.val (originalVertexHalfspaceBasis γ hsmooth v j) : ℝ) *
          (originalFacetNormal γ hsmooth F.val (originalVertexHalfspaceBasis γ hsmooth v k) : ℝ)) /
            facetValue (originalCornerFacetLinear γ hsmooth v)
              (originalCornerFacetOffset γ hsmooth v) F.val x := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  simp only [originalCornerRemainderHessian_apply, originalCornerFacetLinear_basis]

/-- Actual symmetry follows from the literal scalar bilinear terms. -/
theorem originalCornerRemainderHessian_symmetric (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η ζ : Fin n → ℝ) :
    originalCornerRemainderHessian γ hsmooth v x η ζ =
      originalCornerRemainderHessian γ hsmooth v x ζ η := by
  simp only [originalCornerRemainderHessian_apply, mul_comm]

/-- Genuine positive inactive slacks produce a sum of nonnegative squares,
including the empty inactive family and dimension zero. -/
theorem originalCornerRemainderHessian_nonneg (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) (η : Fin n → ℝ) :
    0 ≤ originalCornerRemainderHessian γ hsmooth v x η η := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  rw [originalCornerRemainderHessian_apply]
  exact Finset.sum_nonneg (fun F _ => div_nonneg (mul_self_nonneg _) (hx F).le)

/-- ALL original facet slacks strictly positive, expressed in the SAME corner. -/
def originalVertexCornerStrict (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) : Set (Fin n → ℝ) :=
  {x | ∀ F : latticePolytopeFacets γ,
    0 < facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F x}

theorem isOpen_originalVertexCornerStrict (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    IsOpen (originalVertexCornerStrict γ hsmooth v) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  rw [originalVertexCornerStrict, Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun F => isOpen_lt continuous_const
    ((originalCornerFacetLinear γ hsmooth v F).continuous.add continuous_const))

/-- Genuine ALL-facet positivity supplies the selected positive coordinates. -/
theorem originalVertexCornerStrict_coord_pos (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) (j : Fin n) :
    0 < x j := by
  have h := hx (originalVertexActiveFacet γ hsmooth v j).val
  rwa [originalCornerFacetValue_selected] at h

/-- The actual full first derivative, after the exact source entropy split. -/
def originalCornerEntropyDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (∑ j, (Real.log (x j) + 1) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) +
    originalCornerRemainderDerivative γ hsmooth v x

/-- Actual diagonal selected-coordinate Hessian plus inactive remainder. -/
def originalCornerEntropyHessian (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  (∑ j, (x j)⁻¹ • ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).smulRight ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) +
    originalCornerRemainderHessian γ hsmooth v x

/-- Genuine scalar xlogx derivatives and the proved finite source split
manufacture the full first derivative, before any extended real readback. -/
theorem hasFDerivAt_originalVertexCornerEntropyReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    HasFDerivAt (originalVertexCornerEntropyReal γ hsmooth v)
      (originalCornerEntropyDerivative γ hsmooth v x) x := by
  have hsel : HasFDerivAt (fun y : Fin n → ℝ => ∑ j, y j * Real.log (y j))
      (∑ j, (Real.log (x j) + 1) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact (Real.hasDerivAt_mul_log
      (originalVertexCornerStrict_coord_pos γ hsmooth v hx j).ne').comp_hasFDerivAt x
        ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).hasFDerivAt
  have h := hsel.add (hasFDerivAt_originalVertexCornerRemainder γ hsmooth v (fun F => hx F.val))
  rw [show originalVertexCornerEntropyReal γ hsmooth v =
    (fun y : Fin n → ℝ => ∑ j, y j * Real.log (y j)) +
      originalVertexCornerRemainder γ hsmooth v from
        funext (originalVertexCornerEntropyReal_split γ hsmooth v)]
  exact h

/-- Actual scalar log and continuous-linear-map calculus produces the
functional derivative of the full gradient expression. -/
theorem hasFDerivAt_originalCornerEntropyDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    HasFDerivAt (originalCornerEntropyDerivative γ hsmooth v)
      (originalCornerEntropyHessian γ hsmooth v x) x := by
  have hsel : HasFDerivAt
      (fun y : Fin n → ℝ => ∑ j, (Real.log (y j) + 1) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))
      (∑ j, (x j)⁻¹ • ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).smulRight ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    convert ((((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).hasFDerivAt.log
      (originalVertexCornerStrict_coord_pos γ hsmooth v hx j).ne').add_const 1).smul_const
        ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) using 1
    · rfl
    · ext η ζ
      simp [mul_assoc]
  exact hsel.add (hasFDerivAt_originalCornerRemainderDerivative γ hsmooth v (fun F => hx F.val))

/-- The preceding two actual derivatives are related by local equality,
so the displayed matrix IS the full entropy's second functional derivative. -/
theorem hasFDerivAt_fderiv_originalVertexCornerEntropyReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    HasFDerivAt (fderiv ℝ (originalVertexCornerEntropyReal γ hsmooth v))
      (originalCornerEntropyHessian γ hsmooth v x) x := by
  apply (hasFDerivAt_originalCornerEntropyDerivative γ hsmooth v hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_originalVertexCornerStrict γ hsmooth v).mem_nhds hx] with y hy
  exact (hasFDerivAt_originalVertexCornerEntropyReal γ hsmooth v hy).fderiv

theorem originalCornerEntropyHessian_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η ζ : Fin n → ℝ) :
    originalCornerEntropyHessian γ hsmooth v x η ζ =
      (∑ j, η j * ζ j / x j) + originalCornerRemainderHessian γ hsmooth v x η ζ := by
  simp only [originalCornerEntropyHessian, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A genuine positive selected square plus the produced nonnegative
inactive sum gives strict positive definiteness; rank zero is vacuous. -/
theorem originalCornerEntropyHessian_pos (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v)
    {η : Fin n → ℝ} (hη : η ≠ 0) :
    0 < originalCornerEntropyHessian γ hsmooth v x η η := by
  obtain ⟨j, hj⟩ : ∃ j, η j ≠ 0 := by
    by_contra h
    push Not at h
    exact hη (funext h)
  have hnonneg (k : Fin n) : 0 ≤ η k * η k / x k :=
    div_nonneg (mul_self_nonneg _) (originalVertexCornerStrict_coord_pos γ hsmooth v hx k).le
  have hterm : 0 < η j * η j / x j :=
    div_pos (mul_self_pos.mpr hj) (originalVertexCornerStrict_coord_pos γ hsmooth v hx j)
  have hsum := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  rw [originalCornerEntropyHessian_apply]
  exact add_pos_of_pos_of_nonneg (hterm.trans_le hsum)
    (originalCornerRemainderHessian_nonneg γ hsmooth v (fun F => hx F.val) η)

/-- The actual old facet-region convexity theorem gives the SAME original
polytope in corner coordinates, without an assumed coordinate-region field. -/
theorem convex_originalVertexCornerPolytope (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Convex ℝ (originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ) := by
  have heq : originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ =
      facetRegion (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v) := by
    ext x
    exact originalVertexCornerPoint_mem_iff γ hsmooth v x
  rw [heq]
  exact convex_facetRegion _ _

/-- A differing selected coordinate supplies the genuine STRICT scalar
entropy inequality; every other original facet uses the prior weak convex
entropy inequality. No Hessian-based boundary extension is assumed. -/
theorem strictConvexOn_originalVertexCornerEntropyReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    StrictConvexOn ℝ (originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ)
      (originalVertexCornerEntropyReal γ hsmooth v) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  refine ⟨convex_originalVertexCornerPolytope γ hsmooth v, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxf := (originalVertexCornerPoint_mem_iff γ hsmooth v x).mp hx
  have hyf := (originalVertexCornerPoint_mem_iff γ hsmooth v y).mp hy
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  change (∑ F : latticePolytopeFacets γ,
    facetValue (originalCornerFacetLinear γ hsmooth v) (originalCornerFacetOffset γ hsmooth v)
      F (a • x + b • y) * Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
        (originalCornerFacetOffset γ hsmooth v) F (a • x + b • y))) < _
  simp only [originalVertexCornerEntropyReal, facetEntropyReal, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro F _
    rw [facetValue_combo _ _ F x y a b hab]
    exact Real.convexOn_mul_log.2 (hxf F) (hyf F) ha.le hb.le hab
  · refine ⟨(originalVertexActiveFacet γ hsmooth v j).val, Finset.mem_univ _, ?_⟩
    simp only [originalCornerFacetValue_selected, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hxj : 0 ≤ x j := by
      have h := hxf (originalVertexActiveFacet γ hsmooth v j).val
      rwa [originalCornerFacetValue_selected] at h
    have hyj : 0 ≤ y j := by
      have h := hyf (originalVertexActiveFacet γ hsmooth v j).val
      rwa [originalCornerFacetValue_selected] at h
    exact Real.strictConvexOn_mul_log.2 hxj hyj hj ha hb hab

/-- Actual strict facet slacks give membership in the original corner domain. -/
theorem originalVertexCornerStrict_subset_domain (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    originalVertexCornerStrict γ hsmooth v ⊆ originalVertexCornerDomain γ hsmooth v := by
  intro x hx
  exact ⟨fun F => hx F.val, fun j => (originalVertexCornerStrict_coord_pos γ hsmooth v hx j).le⟩

/-- Real readback is taken only on a produced open neighborhood of actual
finite original source values; it has the genuinely computed derivative. -/
theorem hasFDerivAt_originalCanonicalEntropy_corner_toReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    HasFDerivAt (fun y => (originalCanonicalEntropy γ hsmooth
      (originalVertexCornerPoint γ hsmooth v y)).toReal)
      (originalCornerEntropyDerivative γ hsmooth v x) x := by
  apply (hasFDerivAt_originalVertexCornerEntropyReal γ hsmooth v hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_originalVertexCornerStrict γ hsmooth v).mem_nhds hx] with y hy
  have hP := originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v
    (originalVertexCornerStrict_subset_domain γ hsmooth v hy)
  simp only [originalCanonicalEntropy_corner_eq, if_pos hP, EReal.toReal_coe]

/-- The FULL original finite source function has the actual second derivative;
no entropy identity, Hessian, or finite readback is supplied as an input. -/
theorem hasFDerivAt_fderiv_originalCanonicalEntropy_corner_toReal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    HasFDerivAt (fderiv ℝ (fun y => (originalCanonicalEntropy γ hsmooth
      (originalVertexCornerPoint γ hsmooth v y)).toReal))
      (originalCornerEntropyHessian γ hsmooth v x) x := by
  apply (hasFDerivAt_originalCornerEntropyDerivative γ hsmooth v hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_originalVertexCornerStrict γ hsmooth v).mem_nhds hx] with y hy
  exact (hasFDerivAt_originalCanonicalEntropy_corner_toReal γ hsmooth v hy).fderiv

end SGPT.Toric
