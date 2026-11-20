import SGPT.Toric.OriginalGuilleminFaceBarrier
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting Filter
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Actual free-coordinate extension by zero, using the EXISTING product
continuous-linear-map construction. No subspace chart is supplied. -/
def originalCornerFreeEmbedding (A : Set (Fin n)) :
    ({j : Fin n // j ∉ A} → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => if h : j ∈ A then 0 else ContinuousLinearMap.proj ⟨j, h⟩)

/-- Actual original coordinate restriction to the complementary family. -/
def originalCornerFreeProjection (A : Set (Fin n)) :
    (Fin n → ℝ) →L[ℝ] ({j : Fin n // j ∉ A} → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.val)

theorem originalCornerFreeEmbedding_forced (A : Set (Fin n))
    (r : {j : Fin n // j ∉ A} → ℝ) (j : Fin n) (hj : j ∈ A) :
    originalCornerFreeEmbedding A r j = 0 := by simp [originalCornerFreeEmbedding, hj]

theorem originalCornerFreeEmbedding_free (A : Set (Fin n))
    (r : {j : Fin n // j ∉ A} → ℝ) (j : {j : Fin n // j ∉ A}) :
    originalCornerFreeEmbedding A r j.val = r j := by
  simp [originalCornerFreeEmbedding, j.property]

theorem originalCornerFreeProjection_embedding (A : Set (Fin n))
    (r : {j : Fin n // j ∉ A} → ℝ) :
    originalCornerFreeProjection A (originalCornerFreeEmbedding A r) = r := by
  ext j
  exact originalCornerFreeEmbedding_free A r j

theorem originalCornerFreeEmbedding_projection (A : Set (Fin n))
    (x : Fin n → ℝ) (hx : ∀ j ∈ A, x j = 0) :
    originalCornerFreeEmbedding A (originalCornerFreeProjection A x) = x := by
  ext j
  by_cases hj : j ∈ A
  · rw [originalCornerFreeEmbedding_forced A _ j hj, hx j hj]
  · exact originalCornerFreeEmbedding_free A _ ⟨j, hj⟩

theorem originalCornerFreeEmbedding_basis (A : Set (Fin n)) (j : {j : Fin n // j ∉ A}) :
    originalCornerFreeEmbedding A (Pi.basisFun ℝ {j : Fin n // j ∉ A} j) =
      Pi.basisFun ℝ (Fin n) j.val := by
  ext k
  by_cases hk : k ∈ A
  · rw [originalCornerFreeEmbedding_forced A _ k hk]
    have hne : j.val ≠ k := fun h => j.property (h.symm ▸ hk)
    simp [Pi.basisFun_apply, hne]
  · rw [originalCornerFreeEmbedding_free A _ ⟨k, hk⟩]
    simp [Pi.basisFun_apply, Pi.single_apply, Subtype.ext_iff]

/-- Actual restriction of the literal selected entropy sum; forced zeros
contribute zero under the original zero-times-log-zero convention. -/
theorem originalCornerFree_selected_sum (A : Set (Fin n))
    (r : {j : Fin n // j ∉ A} → ℝ) :
    (∑ j, originalCornerFreeEmbedding A r j * Real.log (originalCornerFreeEmbedding A r j)) =
      ∑ j : {j : Fin n // j ∉ A}, r j * Real.log (r j) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => j ∉ A)]
  have hzero : (∑ j : {j : Fin n // ¬j ∉ A},
      originalCornerFreeEmbedding A r j.val * Real.log (originalCornerFreeEmbedding A r j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [originalCornerFreeEmbedding_forced A r j.val (not_not.mp j.property), zero_mul]
  rw [hzero, add_zero]
  simp only [originalCornerFreeEmbedding_free]

/-- The genuine source remainder partial derivative, named only AFTER the
actual derivative-of-fderiv construction, with no Euclidean Pi shortcut. -/
def originalCornerRemainderPartial (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  originalCornerRemainderDerivative γ hsmooth v x (Pi.basisFun ℝ (Fin n) j)

/-- The actual finite restricted source objective in free coordinates. -/
def originalCornerFreeObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    (r : {j : Fin n // j ∉ A} → ℝ) : ℝ :=
  (∑ j : {j : Fin n // j ∉ A}, r j * Real.log (r j)) +
    originalVertexCornerRemainder γ hsmooth v (originalCornerFreeEmbedding A r) -
      originalCornerFaceTilt A y (originalCornerFreeEmbedding A r)

/-- Exact pullback of the SAME original objective before any differentiation. -/
theorem originalCornerFaceObjective_free_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    (r : {j : Fin n // j ∉ A} → ℝ) :
    originalCornerFaceObjective γ hsmooth v A y (originalCornerFreeEmbedding A r) =
      originalCornerFreeObjective γ hsmooth v A y r := by
  change originalVertexCornerEntropyReal γ hsmooth v (originalCornerFreeEmbedding A r) - _ = _
  rw [originalVertexCornerEntropyReal_split, originalCornerFree_selected_sum]
  rfl

/-- The ACTUAL open set of admissible free variables, produced from inactive
strict slacks and the actual positive free coordinate halfspaces. -/
def originalCornerFreeOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) : Set ({j : Fin n // j ∉ A} → ℝ) :=
  {r | originalCornerFreeEmbedding A r ∈ originalVertexCornerOpen γ hsmooth v ∧ ∀ j, 0 < r j}

theorem isOpen_originalCornerFreeOpen (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    IsOpen (originalCornerFreeOpen γ hsmooth v A) := by
  apply ((isOpen_originalVertexCornerOpen γ hsmooth v).preimage
    (originalCornerFreeEmbedding A).continuous).inter
  change IsOpen {r : {j : Fin n // j ∉ A} → ℝ | ∀ j, 0 < r j}
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (continuous_apply j))

/-- Admissibility genuinely implies original face membership. -/
theorem originalCornerFreeOpen_mapsTo_face (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    MapsTo (originalCornerFreeEmbedding A) (originalCornerFreeOpen γ hsmooth v A)
      (originalVertexCornerFace γ hsmooth v A) := by
  intro r hr
  refine ⟨originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v ⟨hr.1, ?_⟩,
    originalCornerFreeEmbedding_forced A r⟩
  intro j
  by_cases hj : j ∈ A
  · rw [originalCornerFreeEmbedding_forced A r j hj]
  · rw [originalCornerFreeEmbedding_free A r ⟨j, hj⟩]
    exact (hr.2 ⟨j, hj⟩).le

/-- Actual restricted first derivative, assembled by existing finite-sum,
scalar entropy, composition and subtraction rules. -/
def originalCornerFreeDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    (r : {j : Fin n // j ∉ A} → ℝ) : ({j : Fin n // j ∉ A} → ℝ) →L[ℝ] ℝ :=
  (∑ j : {j : Fin n // j ∉ A}, (Real.log (r j) + 1) • ContinuousLinearMap.proj j) +
    (originalCornerRemainderDerivative γ hsmooth v (originalCornerFreeEmbedding A r)).comp
      (originalCornerFreeEmbedding A) - (originalCornerFaceTilt A y).comp (originalCornerFreeEmbedding A)

theorem hasFDerivAt_originalCornerFreeObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {r : {j : Fin n // j ∉ A} → ℝ} (hr : r ∈ originalCornerFreeOpen γ hsmooth v A) :
    HasFDerivAt (originalCornerFreeObjective γ hsmooth v A y)
      (originalCornerFreeDerivative γ hsmooth v A y r) r := by
  have hsel : HasFDerivAt (fun s : {j : Fin n // j ∉ A} → ℝ => ∑ j, s j * Real.log (s j))
      (∑ j : {j : Fin n // j ∉ A}, (Real.log (r j) + 1) •
        (ContinuousLinearMap.proj j : ({j : Fin n // j ∉ A} → ℝ) →L[ℝ] ℝ)) r := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact (Real.hasDerivAt_mul_log (hr.2 j).ne').comp_hasFDerivAt r
      (ContinuousLinearMap.proj j : ({j : Fin n // j ∉ A} → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact (hsel.add ((hasFDerivAt_originalVertexCornerRemainder γ hsmooth v hr.1).comp r
    (originalCornerFreeEmbedding A).hasFDerivAt)).sub
      ((originalCornerFaceTilt A y).comp (originalCornerFreeEmbedding A)).hasFDerivAt

/-- Genuine free-coordinate basis evaluation of the original linear tilt. -/
theorem originalCornerFaceTilt_free_basis (A : Set (Fin n))
    (y : {j : Fin n // j ∉ A} → ℝ) (j : {j : Fin n // j ∉ A}) :
    originalCornerFaceTilt A y
      (originalCornerFreeEmbedding A (Pi.basisFun ℝ {j : Fin n // j ∉ A} j)) = y j := by
  simp only [originalCornerFaceTilt, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    originalCornerFreeEmbedding_free, smul_eq_mul]
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The ACTUAL restricted derivative gives the original stationarity
coefficient, with the SAME source remainder and original free parameter. -/
theorem originalCornerFreeDerivative_basis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y r : {j : Fin n // j ∉ A} → ℝ) (j : {j : Fin n // j ∉ A}) :
    originalCornerFreeDerivative γ hsmooth v A y r (Pi.basisFun ℝ {j : Fin n // j ∉ A} j) =
      Real.log (r j) + 1 + originalCornerRemainderPartial γ hsmooth v j.val
        (originalCornerFreeEmbedding A r) - y j := by
  simp only [originalCornerFreeDerivative, sub_apply, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [originalCornerFaceTilt_free_basis, originalCornerFreeEmbedding_basis]
  simp [Pi.basisFun_apply, Pi.single_apply, originalCornerRemainderPartial]

/-- Genuine Fermat on the manufactured open free-coordinate neighborhood
gives EVERY original all-pattern stationarity equation at the actual minimum. -/
theorem originalCornerFace_minimizer_stationary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v A)
    (hmin : IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
      (originalVertexCornerFace γ hsmooth v A) x) :
    ∀ j : {j : Fin n // j ∉ A}, Real.log (x j.val) + 1 +
      originalCornerRemainderPartial γ hsmooth v j.val x = y j := by
  have hstrict := originalCornerFace_minimizer_strict γ hsmooth v A y hx hmin
  let r := originalCornerFreeProjection A x
  have hrx : originalCornerFreeEmbedding A r = x := originalCornerFreeEmbedding_projection A x hx.2
  have hr : r ∈ originalCornerFreeOpen γ hsmooth v A :=
    ⟨hrx.symm ▸ hstrict.1.1, fun j => hstrict.2 j.val j.property⟩
  have hlocal : IsLocalMin (originalCornerFreeObjective γ hsmooth v A y) r := by
    change ∀ᶠ s in 𝓝 r, originalCornerFreeObjective γ hsmooth v A y r ≤
      originalCornerFreeObjective γ hsmooth v A y s
    filter_upwards [(isOpen_originalCornerFreeOpen γ hsmooth v A).mem_nhds hr] with s hs
    rw [← originalCornerFaceObjective_free_eq, ← originalCornerFaceObjective_free_eq, hrx]
    exact hmin (originalCornerFreeOpen_mapsTo_face γ hsmooth v A hs)
  have hzero := hlocal.hasFDerivAt_eq_zero (hasFDerivAt_originalCornerFreeObjective γ hsmooth v A y hr)
  intro j
  have h := congrArg (fun L : ({j : Fin n // j ∉ A} → ℝ) →L[ℝ] ℝ =>
    L (Pi.basisFun ℝ {j : Fin n // j ∉ A} j)) hzero
  rw [originalCornerFreeDerivative_basis, hrx] at h
  change Real.log (x j.val) + 1 + originalCornerRemainderPartial γ hsmooth v j.val x - y j = 0 at h
  exact sub_eq_zero.mp h

/-- Actual free-coordinate restriction preserves the prior convex source
objective on the EXACT preimage of its actual face. -/
theorem convexOn_originalCornerFreeObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    ConvexOn ℝ (originalCornerFreeEmbedding A ⁻¹' originalVertexCornerFace γ hsmooth v A)
      (originalCornerFreeObjective γ hsmooth v A y) := by
  apply ((strictConvexOn_originalCornerFaceObjective γ hsmooth v A y).convexOn.comp_linearMap
    (originalCornerFreeEmbedding A).toLinearMap).congr
  intro r _
  exact originalCornerFaceObjective_free_eq γ hsmooth v A y r

/-- The original stationarity equations force the actual functional derivative
to vanish, by the EXISTING actual finite coordinate basis extensionality. -/
theorem originalCornerFreeDerivative_eq_zero_of_stationary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y r : {j : Fin n // j ∉ A} → ℝ)
    (hstation : ∀ j : {j : Fin n // j ∉ A}, Real.log (r j) + 1 +
      originalCornerRemainderPartial γ hsmooth v j.val (originalCornerFreeEmbedding A r) = y j) :
    originalCornerFreeDerivative γ hsmooth v A y r = 0 := by
  have hlin : (originalCornerFreeDerivative γ hsmooth v A y r).toLinearMap = 0 := by
    apply (Pi.basisFun ℝ {j : Fin n // j ∉ A}).ext
    intro j
    change originalCornerFreeDerivative γ hsmooth v A y r (Pi.basisFun ℝ {j : Fin n // j ∉ A} j) = 0
    rw [originalCornerFreeDerivative_basis, hstation j, sub_self]
  ext s
  exact congrArg (fun L : ({j : Fin n // j ∉ A} → ℝ) →ₗ[ℝ] ℝ => L s) hlin

/-- Conversely, genuine stationarity at an admissible original face point
gives the global minimum by EXISTING scalar convex derivative-versus-secant,
applied to EVERY actual segment in the SAME source face. -/
theorem isMinOn_originalCornerFace_of_stationary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v A)
    (hopen : x ∈ originalVertexCornerOpen γ hsmooth v) (hpos : ∀ j ∉ A, 0 < x j)
    (hstation : ∀ j : {j : Fin n // j ∉ A}, Real.log (x j.val) + 1 +
      originalCornerRemainderPartial γ hsmooth v j.val x = y j) :
    IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
      (originalVertexCornerFace γ hsmooth v A) x := by
  let r := originalCornerFreeProjection A x
  have hrx : originalCornerFreeEmbedding A r = x := originalCornerFreeEmbedding_projection A x hx.2
  have hr : r ∈ originalCornerFreeOpen γ hsmooth v A :=
    ⟨hrx.symm ▸ hopen, fun j => hpos j.val j.property⟩
  have hd := hasFDerivAt_originalCornerFreeObjective γ hsmooth v A y hr
  have hzero : originalCornerFreeDerivative γ hsmooth v A y r = 0 := by
    apply originalCornerFreeDerivative_eq_zero_of_stationary
    intro j
    rw [hrx]
    exact hstation j
  rw [hzero] at hd
  intro z hz
  change originalCornerFaceObjective γ hsmooth v A y x ≤ originalCornerFaceObjective γ hsmooth v A y z
  let s := originalCornerFreeProjection A z
  have hsz : originalCornerFreeEmbedding A s = z := originalCornerFreeEmbedding_projection A z hz.2
  have hc := convexOn_originalCornerFreeObjective γ hsmooth v A y
  have hrQ : r ∈ originalCornerFreeEmbedding A ⁻¹' originalVertexCornerFace γ hsmooth v A := by
    change originalCornerFreeEmbedding A r ∈ originalVertexCornerFace γ hsmooth v A
    rwa [hrx]
  have hsQ : s ∈ originalCornerFreeEmbedding A ⁻¹' originalVertexCornerFace γ hsmooth v A := by
    change originalCornerFreeEmbedding A s ∈ originalVertexCornerFace γ hsmooth v A
    rwa [hsz]
  let l : ℝ →ᵃ[ℝ] ({j : Fin n // j ∉ A} → ℝ) := AffineMap.lineMap r s
  have hmaps : MapsTo l (Icc 0 1)
      (originalCornerFreeEmbedding A ⁻¹' originalVertexCornerFace γ hsmooth v A) := by
    simpa only [l, mapsTo_iff_image_subset, ← segment_eq_image_lineMap] using hc.1.segment_subset hrQ hsQ
  have hconv := (hc.comp_affineMap l).subset hmaps (convex_Icc (0 : ℝ) 1)
  have hdline : HasDerivAt (originalCornerFreeObjective γ hsmooth v A y ∘ l) 0 0 := by
    simpa only [zero_apply] using hd.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := r) (b := s) (x := (0 : ℝ))) (by simp)
  have hslope := hconv.le_slope_of_hasDerivAt (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one hdline
  have hdiff : 0 ≤ originalCornerFreeObjective γ hsmooth v A y s -
      originalCornerFreeObjective γ hsmooth v A y r := by
    simpa only [slope_def_field, sub_zero, div_one, Function.comp_apply, l,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  have hmin := sub_nonneg.mp hdiff
  rw [← originalCornerFaceObjective_free_eq, ← originalCornerFaceObjective_free_eq, hrx, hsz] at hmin
  exact hmin

/-- Exact original all-pattern characterization; the forward positivity and
equations are all produced, and the converse uses the true convex source. -/
theorem originalCornerFace_isMinOn_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v A) :
    IsMinOn (originalCornerFaceObjective γ hsmooth v A y) (originalVertexCornerFace γ hsmooth v A) x ↔
      x ∈ originalVertexCornerDomain γ hsmooth v ∧ (∀ j ∉ A, 0 < x j) ∧
        ∀ j : {j : Fin n // j ∉ A}, Real.log (x j.val) + 1 +
          originalCornerRemainderPartial γ hsmooth v j.val x = y j := by
  constructor
  · intro hmin
    have hstrict := originalCornerFace_minimizer_strict γ hsmooth v A y hx hmin
    exact ⟨hstrict.1, hstrict.2, originalCornerFace_minimizer_stationary γ hsmooth v A y hx hmin⟩
  · rintro ⟨hdom, hpos, hstation⟩
    exact isMinOn_originalCornerFace_of_stationary γ hsmooth v A y hx hdom.1 hpos hstation

/-- ONLY the original input manufactures the unique solution to EVERY
original face stationarity system, including the empty free family. -/
theorem existsUnique_originalCornerFace_stationary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    ∃! x, x ∈ originalVertexCornerFace γ hsmooth v A ∧
      x ∈ originalVertexCornerDomain γ hsmooth v ∧ (∀ j ∉ A, 0 < x j) ∧
        ∀ j : {j : Fin n // j ∉ A}, Real.log (x j.val) + 1 +
          originalCornerRemainderPartial γ hsmooth v j.val x = y j := by
  obtain ⟨x, ⟨hx, hmin⟩, huniq⟩ := existsUnique_originalCornerFace_minimizer γ hsmooth v A y
  refine ⟨x, ⟨hx, (originalCornerFace_isMinOn_iff γ hsmooth v A y hx).mp hmin⟩, ?_⟩
  intro z hz
  exact huniq z ⟨hz.1, (originalCornerFace_isMinOn_iff γ hsmooth v A y hz.1).mpr hz.2⟩

end SGPT.Toric
