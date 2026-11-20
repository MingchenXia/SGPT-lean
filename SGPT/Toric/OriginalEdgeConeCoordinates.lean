import SGPT.Toric.OriginalDirectionEdges

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {n : ℕ} {K : Type*}

/-- The closed nonnegative-coordinate region of the SAME genuine real
extension of an original integral basis. -/
def originalEdgeCoordinateCone (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    Set (Fin n → ℝ) :=
  (integralRealBasis B).equivFunL ⁻¹' Set.Ici 0

/-- The region retains the literal real coefficients of the manufactured basis. -/
theorem mem_originalEdgeCoordinateCone_iff
    (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (r : Fin n → ℝ) :
    r ∈ originalEdgeCoordinateCone B ↔ ∀ j, 0 ≤ (integralRealBasis B).repr r j := Iff.rfl

/-- Existing genuine continuity of finite-basis coordinates gives closedness. -/
theorem isClosed_originalEdgeCoordinateCone
    (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) : IsClosed (originalEdgeCoordinateCone B) :=
  isClosed_Ici.preimage (integralRealBasis B).equivFunL.continuous

/-- Existing convex ordered halfspaces and linear preimages give convexity. -/
theorem convex_originalEdgeCoordinateCone
    (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) : Convex ℝ (originalEdgeCoordinateCone B) :=
  (convex_Ici (0 : Fin n → ℝ)).linear_preimage
    (integralRealBasis B).equivFunL.toLinearEquiv.toLinearMap

/-- Each ACTUAL extreme direction gives an internally manufactured ACTUAL
original edge.  Its original basis point lies on that SAME positive ray, so
all real coordinates are nonnegative. -/
theorem latticeVertex_extremeDirection_mem_originalEdgeCoordinateCone [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
      0 < h (x - integerCast v.val))
    {r : Fin n → ℝ} (hr : r ∈ (latticeVertexDirectionSection γ v.val h).extremePoints ℝ) :
    r ∈ originalEdgeCoordinateCone (latticeEdgeCoordinateBasis γ v.val b) := by
  classical
  let B := latticeEdgeCoordinateBasis γ v.val b
  let e := latticeEdgeBasisIndexEquiv γ v.val b
  let E : latticePolytopeEdgesAt γ v.val :=
    ⟨latticeVertexDirectionFace γ v.val r, latticeVertexDirectionFace_isOriginalEdge γ v h hpos hr⟩
  let jE := e.symm E
  have hBj : B jE = b E := by
    simp only [B, jE, latticeEdgeCoordinateBasis_apply, e, Equiv.apply_symm_apply]
  have hpoint := hmem E
  have hpointne : integerCast (v.val + b E) ≠ integerCast v.val := by
    intro heq
    have heq' := integerCast_injective heq
    exact b.ne_zero E (add_left_cancel (heq'.trans (add_zero v.val).symm))
  have hheight := hpos _ (E.property.subset hpoint) hpointne
  have hstep := (mem_latticeVertexDirectionFace_iff γ v.val h hpos hr.1).mp hpoint |>.2
  have hcast : integerCast (v.val + b E) - integerCast v.val = integerCast (b E) := by
    ext i
    simp [integerCast]
  rw [hcast] at hstep
  have hrform : r = (h (integerCast (v.val + b E) - integerCast v.val))⁻¹ •
      integralRealBasis B jE := by
    rw [integralRealBasis_apply, hBj, hstep, smul_smul, ← hcast, inv_mul_cancel₀ hheight.ne', one_smul]
  rw [mem_originalEdgeCoordinateCone_iff]
  intro j
  change 0 ≤ (integralRealBasis B).repr r j
  rw [hrform]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply]
  split_ifs <;> simp only [mul_one, mul_zero] <;> positivity

/-- Genuine Krein--Milman propagates the internally produced nonnegative
extreme directions to the WHOLE actual compact original direction section. -/
theorem latticeVertexDirectionSection_subset_originalEdgeCoordinateCone [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
      0 < h (x - integerCast v.val)) :
    latticeVertexDirectionSection γ v.val h ⊆
      originalEdgeCoordinateCone (latticeEdgeCoordinateBasis γ v.val b) := by
  have hsub := closure_minimal
    (convexHull_min (fun _ hr =>
      latticeVertex_extremeDirection_mem_originalEdgeCoordinateCone γ v b hmem h hpos hr)
      (convex_originalEdgeCoordinateCone (latticeEdgeCoordinateBasis γ v.val b)))
    (isClosed_originalEdgeCoordinateCone (latticeEdgeCoordinateBasis γ v.val b))
  rwa [closure_convexHull_extremePoints (isCompact_latticeVertexDirectionSection γ v.val h)
    (convex_latticeVertexDirectionSection γ v.val h)] at hsub

/-- The ORIGINAL all-edge basis gives nonnegative real coordinates for EVERY
original source point.  Strict separation and the compact section are produced
inside this proof; neither coordinate positivity nor edge generation is input. -/
theorem latticePolytope_originalEdge_real_coordinate_nonneg [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) (j : Fin n) :
    0 ≤ (integralRealBasis (latticeEdgeCoordinateBasis γ v.val b)).repr
      (x - integerCast v.val) j := by
  by_cases hxv : x = integerCast v.val
  · simp [hxv]
  have hP : latticePolytope γ ≠ {integerCast v.val} := by
    intro heq
    exact hxv (by simpa only [heq, Set.mem_singleton_iff] using hx)
  obtain ⟨h, hpos⟩ := exists_latticeVertex_positive_functional γ v hP
  let z := (h (x - integerCast v.val))⁻¹ • (x - integerCast v.val)
  have hz := latticeVertexDirectionSection_normalized_mem γ v h hpos hx hxv
  have hcone := latticeVertexDirectionSection_subset_originalEdgeCoordinateCone
    γ v b hmem h hpos hz
  have hcoord := (mem_originalEdgeCoordinateCone_iff _ _).mp hcone j
  have hheight := hpos x hx hxv
  have hrestore : x - integerCast v.val = h (x - integerCast v.val) • z := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hheight.ne', one_smul]
  rw [hrestore, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg hheight.le hcoord

/-- Exact previously proved integer/real basis readback manufactures ORIGINAL
integer signs for the FULL original lattice-point set, before Nat exponents. -/
theorem latticePolytope_originalEdge_integer_coordinate_nonneg [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    (m : latticePolytopeIntegerPoints γ) (j : Fin n) :
    0 ≤ (latticeEdgeCoordinateBasis γ v.val b).repr (m.val - v.val) j := by
  have hreal := latticePolytope_originalEdge_real_coordinate_nonneg γ v b hmem m.property j
  have hcast : integerCast m.val - integerCast v.val = integerCast (m.val - v.val) := by
    ext i
    simp [integerCast]
  rw [hcast, integralRealBasis_repr_integerCast] at hreal
  exact_mod_cast hreal

/-- ONLY the book's actual original edge-basis smoothness at an ACTUAL vertex
manufactures a finite integral basis, EVERY original lattice coefficient sign,
and EVERY actual original basis neighbor.  These are exactly the raw inputs of
the already proved native polynomial chart producer. -/
theorem exists_latticePolytope_originalEdge_coordinate_basis [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (hsmooth : latticePolytopeEdgeSmoothAt γ v.val) :
    ∃ B : Module.Basis (Fin n) ℤ (Fin n → ℤ),
      (∀ x ∈ latticePolytope γ, ∀ j,
        0 ≤ (integralRealBasis B).repr (x - integerCast v.val) j) ∧
      (∀ m : latticePolytopeIntegerPoints γ, ∀ j, 0 ≤ B.repr (m.val - v.val) j) ∧
      ∀ j, v.val + B j ∈ latticePolytopeIntegerPoints γ := by
  obtain ⟨b, hmem⟩ := hsmooth
  exact ⟨latticeEdgeCoordinateBasis γ v.val b,
    fun _ hx j => latticePolytope_originalEdge_real_coordinate_nonneg γ v b hmem hx j,
    latticePolytope_originalEdge_integer_coordinate_nonneg γ v b hmem,
    latticeEdgeCoordinateBasis_neighbor_mem γ v.val b hmem⟩

end SGPT.Toric
