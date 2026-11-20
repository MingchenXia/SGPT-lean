import SGPT.Toric.OriginalGuilleminLegendreAttainment

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Actual source partial derivatives retain the genuine finite inactive
logarithmic formula, with original corner linear coefficients. -/
theorem originalCornerRemainderPartial_eq_sum (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) (x : Fin n → ℝ) :
    let _ := originalVertexInactiveFacetFintype γ hsmooth v
    originalCornerRemainderPartial γ hsmooth v j x =
      ∑ F : originalVertexInactiveFacets γ v,
        (Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F.val x) + 1) *
            originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  simp only [originalCornerRemainderPartial, originalCornerRemainderDerivative, sum_apply,
    smul_apply, smul_eq_mul]

/-- Existing smooth log/product/sum calculus on the ACTUAL open domain
gives genuine smoothness of the actual source partial, not an assumed field. -/
theorem contDiffOn_originalCornerRemainderPartial (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    ContDiffOn ℝ ∞ (originalCornerRemainderPartial γ hsmooth v j)
      (originalVertexCornerOpen γ hsmooth v) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  simp only [show originalCornerRemainderPartial γ hsmooth v j = fun x =>
      ∑ F : originalVertexInactiveFacets γ v,
        (Real.log (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F.val x) + 1) *
            originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j) from
    funext (originalCornerRemainderPartial_eq_sum γ hsmooth v j)]
  apply ContDiffOn.sum
  intro F _
  have hlin : ContDiffOn ℝ ∞ (fun x => facetValue (originalCornerFacetLinear γ hsmooth v)
      (originalCornerFacetOffset γ hsmooth v) F.val x) (originalVertexCornerOpen γ hsmooth v) :=
    ((originalCornerFacetLinear γ hsmooth v F.val).contDiff.add contDiff_const).contDiffOn
  exact ((hlin.log (fun x hx => (hx F).ne')).add contDiffOn_const).mul contDiffOn_const

/-- The ACTUAL source exponential corner map on the whole real ambient space.
Smoothness is asserted only on the produced open inactive domain. -/
def originalGuilleminCornerMap (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x)

theorem contDiffOn_originalGuilleminCornerMap (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiffOn ℝ ∞ (originalGuilleminCornerMap γ hsmooth v) (originalVertexCornerOpen γ hsmooth v) := by
  apply contDiffOn_pi.mpr
  intro j
  exact (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn.mul
    ((contDiffOn_const.add (contDiffOn_originalCornerRemainderPartial γ hsmooth v j)).exp)

/-- Actual positive exponentials preserve EVERY original coordinate zero. -/
theorem originalGuilleminCornerMap_coord_eq_zero_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) (j : Fin n) :
    originalGuilleminCornerMap γ hsmooth v x j = 0 ↔ x j = 0 := by
  simp [originalGuilleminCornerMap, Real.exp_ne_zero]

theorem originalGuilleminCornerMap_coord_pos_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) (j : Fin n) :
    0 < originalGuilleminCornerMap γ hsmooth v x j ↔ 0 < x j := by
  change 0 < x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) ↔ 0 < x j
  have he := Real.exp_pos (1 + originalCornerRemainderPartial γ hsmooth v j x)
  constructor
  · intro h
    by_contra hx
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) he.le
    linarith
  · exact fun h => mul_pos h he

/-- The literal logarithmic coordinate identity uses genuine positivity
before log multiplication and inverse readback. -/
theorem log_originalGuilleminCornerMap (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (j : Fin n) (hx : 0 < x j) :
    Real.log (originalGuilleminCornerMap γ hsmooth v x j) =
      Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x := by
  change Real.log (x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x)) = _
  rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- Genuine original stationarity is exponentiated only after BOTH actual
coordinates are positive, giving the exact original map value. -/
theorem originalGuilleminCornerMap_coord_eq_of_stationary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (j : Fin n) {s : ℝ} (hx : 0 < x j) (hs : 0 < s)
    (hstation : Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x = Real.log s) :
    originalGuilleminCornerMap γ hsmooth v x j = s := by
  have h := congrArg Real.exp hstation
  rw [show Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x =
    Real.log (x j) + (1 + originalCornerRemainderPartial γ hsmooth v j x) by ring,
    Real.exp_add, Real.exp_log hx, Real.exp_log hs] at h
  exact h

/-- The map genuinely preserves the whole closed nonnegative orthant
condition, including all selected coordinate zeros and dimension zero. -/
theorem originalGuilleminCornerMap_mapsTo (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    MapsTo (originalGuilleminCornerMap γ hsmooth v) (originalVertexCornerDomain γ hsmooth v)
      (Ici (0 : Fin n → ℝ)) := by
  intro x hx j
  exact mul_nonneg (hx.2 j) (Real.exp_pos _).le

/-- EVERY closed-orthant value has a UNIQUE actual original domain preimage.
The zero pattern, positive logarithmic parameters and actual minimizer equations
are all manufactured internally from the original input. -/
theorem existsUnique_originalGuilleminCornerMap_preimage (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s : Fin n → ℝ) (hs : ∀ j, 0 ≤ s j) :
    ∃! x, x ∈ originalVertexCornerDomain γ hsmooth v ∧ originalGuilleminCornerMap γ hsmooth v x = s := by
  let A : Set (Fin n) := {j | s j = 0}
  let y : {j : Fin n // j ∉ A} → ℝ := fun j => Real.log (s j.val)
  obtain ⟨x, ⟨hx, hdom, hpos, hstation⟩, huniq⟩ := existsUnique_originalCornerFace_stationary γ hsmooth v A y
  have hmap : originalGuilleminCornerMap γ hsmooth v x = s := by
    ext j
    by_cases hj : s j = 0
    · have hxj := hx.2 j hj
      simp [originalGuilleminCornerMap, hxj, hj]
    · apply originalGuilleminCornerMap_coord_eq_of_stationary γ hsmooth v j (hpos j hj)
        (lt_of_le_of_ne (hs j) (fun h => hj h.symm))
      exact hstation ⟨j, hj⟩
  refine ⟨x, ⟨hdom, hmap⟩, ?_⟩
  intro z hz
  have hzA : ∀ j ∈ A, z j = 0 := by
    intro j hj
    apply (originalGuilleminCornerMap_coord_eq_zero_iff γ hsmooth v z j).mp
    rw [hz.2]
    exact hj
  have hzQ : z ∈ originalVertexCornerFace γ hsmooth v A :=
    ⟨originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v hz.1, hzA⟩
  have hzpos : ∀ j ∉ A, 0 < z j := by
    intro j hj
    apply lt_of_le_of_ne (hz.1.2 j)
    intro hzero
    apply hj
    have h := (originalGuilleminCornerMap_coord_eq_zero_iff γ hsmooth v z j).mpr hzero.symm
    rwa [hz.2] at h
  have hzstation : ∀ j : {j : Fin n // j ∉ A}, Real.log (z j.val) + 1 +
      originalCornerRemainderPartial γ hsmooth v j.val z = y j := by
    intro j
    have h := log_originalGuilleminCornerMap γ hsmooth v j.val (hzpos j.val j.property)
    rw [hz.2] at h
    exact h.symm
  exact huniq z ⟨hzQ, hz.1, hzpos, hzstation⟩

/-- Actual original-map bijection, produced from the all-pattern minimizers;
no desired inverse, Jacobian or moment-map geometry is a premise. -/
theorem originalGuilleminCornerMap_bijOn (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    BijOn (originalGuilleminCornerMap γ hsmooth v) (originalVertexCornerDomain γ hsmooth v)
      (Ici (0 : Fin n → ℝ)) := by
  refine ⟨originalGuilleminCornerMap_mapsTo γ hsmooth v, ?_, ?_⟩
  · intro x hx z hz heq
    obtain ⟨w, _, huniq⟩ := existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v
      (originalGuilleminCornerMap γ hsmooth v x) (originalGuilleminCornerMap_mapsTo γ hsmooth v hx)
    exact (huniq x ⟨hx, rfl⟩).trans (huniq z ⟨hz, heq.symm⟩).symm
  · intro s hs
    obtain ⟨x, ⟨hx, hmap⟩, _⟩ := existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v s hs
    exact ⟨x, hx, hmap⟩

/-- Actual unique inverse on the CLOSED orthant, with no arbitrary extension
outside its genuine domain and no assumed continuity or smoothness. -/
def originalGuilleminCornerInverse (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s : Ici (0 : Fin n → ℝ)) : Fin n → ℝ :=
  (existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v s.val s.property).choose

theorem originalGuilleminCornerInverse_mem_domain (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s : Ici (0 : Fin n → ℝ)) :
    originalGuilleminCornerInverse γ hsmooth v s ∈ originalVertexCornerDomain γ hsmooth v :=
  (existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v s.val s.property).choose_spec.1.1

theorem originalGuilleminCornerMap_inverse (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s : Ici (0 : Fin n → ℝ)) :
    originalGuilleminCornerMap γ hsmooth v (originalGuilleminCornerInverse γ hsmooth v s) = s.val :=
  (existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v s.val s.property).choose_spec.1.2

theorem originalGuilleminCornerInverse_map (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    originalGuilleminCornerInverse γ hsmooth v
      ⟨originalGuilleminCornerMap γ hsmooth v x, originalGuilleminCornerMap_mapsTo γ hsmooth v hx⟩ = x := by
  exact ((existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v
    (originalGuilleminCornerMap γ hsmooth v x) (originalGuilleminCornerMap_mapsTo γ hsmooth v hx)).choose_spec.2
      x ⟨hx, rfl⟩).symm

theorem originalGuilleminCornerInverse_injective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Function.Injective (originalGuilleminCornerInverse γ hsmooth v) := by
  intro s t h
  apply Subtype.ext
  rw [← originalGuilleminCornerMap_inverse γ hsmooth v s,
    ← originalGuilleminCornerMap_inverse γ hsmooth v t, h]

end SGPT.Toric
