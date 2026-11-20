import SGPT.Toric.LatticePolytopeSource
import SGPT.Toric.IntegralRealCoordinates
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {n : ℕ} {K : Type*}

/-- An actual nondegenerate segment face at the original vertex.  Neither a ray
nor a desired coordinate cone is part of this definition. -/
def IsOriginalPolytopeEdgeAt (P : Set (Fin n → ℝ)) (v : Fin n → ℝ)
    (E : Set (Fin n → ℝ)) : Prop :=
  ∃ w, w ≠ v ∧ E = segment ℝ v w ∧ IsExtreme ℝ P E

/-- The actual edges of the SAME original finite-generator lattice polytope. -/
def latticePolytopeEdgesAt (γ : K → Fin n → ℤ) (v : Fin n → ℤ) :=
  {E : Set (Fin n → ℝ) // IsOriginalPolytopeEdgeAt (latticePolytope γ) (integerCast v) E}

/-- The book's original edge-basis input, indexed by ALL actual edges.  The
first-point assertion follows below from the actual integral basis readback. -/
def latticePolytopeEdgeSmoothAt (γ : K → Fin n → ℤ) (v : Fin n → ℤ) : Prop :=
  ∃ b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ),
    ∀ E, integerCast (v + b E) ∈ E.val

/-- Original smoothness is required at the actual original vertices only. -/
def latticePolytopeEdgeSmooth (γ : K → Fin n → ℤ) : Prop :=
  ∀ v : latticePolytopeVertices γ, latticePolytopeEdgeSmoothAt γ v.val

/-- The original edge is a genuine face of the original polytope. -/
theorem IsOriginalPolytopeEdgeAt.isExtreme {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E) :
    IsExtreme ℝ P E := h.choose_spec.2.2

/-- Actual face membership is contained in the SAME original source polytope. -/
theorem IsOriginalPolytopeEdgeAt.subset {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E) :
    E ⊆ P := h.isExtreme.1

/-- The given original vertex belongs to its actual edge. -/
theorem IsOriginalPolytopeEdgeAt.vertex_mem {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E) :
    v ∈ E := by
  obtain ⟨w, _, rfl, _⟩ := h
  exact left_mem_segment ℝ v w

/-- Segment geometry gives genuine convexity, without a supplied face certificate. -/
theorem IsOriginalPolytopeEdgeAt.convex {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E) :
    Convex ℝ E := by
  obtain ⟨w, _, rfl, _⟩ := h
  exact convex_segment v w

/-- The actual closed segment is compact in the original real vector space. -/
theorem IsOriginalPolytopeEdgeAt.isCompact {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E) :
    IsCompact E := by
  obtain ⟨w, _, rfl, _⟩ := h
  rw [← convexHull_pair]
  exact ((Set.finite_singleton w).insert v).isCompact_convexHull ℝ

/-- Genuine dimension invariance manufactures the finite edge indexing; no
finite enumeration or assertion about the number of edges is input. -/
def latticeEdgeBasisIndexEquiv (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ)) :
    Fin n ≃ latticePolytopeEdgesAt γ v :=
  (Pi.basisFun ℤ (Fin n)).indexEquiv b

/-- Reindex the SAME original edge vectors by the internally produced bijection. -/
def latticeEdgeCoordinateBasis (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ)) :
    Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
  b.reindex (latticeEdgeBasisIndexEquiv γ v b).symm

/-- Reindexing preserves the literal original lattice vector. -/
theorem latticeEdgeCoordinateBasis_apply (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ)) (j : Fin n) :
    latticeEdgeCoordinateBasis γ v b j = b (latticeEdgeBasisIndexEquiv γ v b j) := by
  simp only [latticeEdgeCoordinateBasis, Module.Basis.reindex_apply, Equiv.symm_symm]

/-- There are no nondegenerate edges in the literal rank-zero ambient space. -/
theorem not_isOriginalPolytopeEdgeAt_zero (P : Set (Fin 0 → ℝ))
    (v : Fin 0 → ℝ) (E : Set (Fin 0 → ℝ)) : ¬ IsOriginalPolytopeEdgeAt P v E := by
  rintro ⟨w, hw, _, _⟩
  exact hw (Subsingleton.elim w v)

/-- Existing segment parametrization and SameRay algebra keep two original
points of the same edge on the same positive direction from the vertex. -/
theorem IsOriginalPolytopeEdgeAt.sameRay_sub {P : Set (Fin n → ℝ)}
    {v : Fin n → ℝ} {E : Set (Fin n → ℝ)} (h : IsOriginalPolytopeEdgeAt P v E)
    {x y : Fin n → ℝ} (hx : x ∈ E) (hy : y ∈ E) :
    SameRay ℝ (x - v) (y - v) := by
  obtain ⟨w, _, rfl, _⟩ := h
  rw [segment_eq_image'] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simpa only [add_sub_cancel_left] using
    ((SameRay.refl (R := ℝ) (w - v)).nonneg_smul_left ha.1).nonneg_smul_right hb.1

/-- Every other actual lattice point on the edge is an integer multiple of
its original basis step, with positive integer coefficient.  Thus the supplied
edge-basis membership is EXACTLY the book's first-lattice-point condition. -/
theorem latticeEdgeBasis_first_lattice_point (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v + b E) ∈ E.val)
    (E : latticePolytopeEdgesAt γ v) (m : Fin n → ℤ)
    (hm : integerCast m ∈ E.val) (hne : m ≠ v) :
    ∃ k : ℤ, 1 ≤ k ∧ m - v = k • b E := by
  let e := latticeEdgeBasisIndexEquiv γ v b
  let B := latticeEdgeCoordinateBasis γ v b
  let j := e.symm E
  have hBj : B j = b E := by
    simp only [B, j, latticeEdgeCoordinateBasis_apply, e, Equiv.apply_symm_apply]
  have hcastsub (a d : Fin n → ℤ) :
      integerCast (a - d) = integerCast a - integerCast d := by
    ext i
    simp [integerCast]
  have hcastadd : integerCast (v + b E) - integerCast v = integerCast (b E) := by
    ext i
    simp [integerCast]
  have hstep : integerCast (b E) ≠ 0 := by
    rw [← hBj, ← integralRealBasis_apply B j]
    exact (integralRealBasis B).ne_zero j
  have hdiff : integerCast m - integerCast v ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => hne (integerCast_injective h))
  have hray := E.property.sameRay_sub hm (hmem E)
  rw [hcastadd] at hray
  obtain ⟨t, ht, hmt⟩ := hray.exists_pos_right hdiff hstep
  have hmt' : integerCast (m - v) = t • integralRealBasis B j := by
    rw [hcastsub, integralRealBasis_apply, hBj]
    exact hmt
  have hcoord : (B.repr (m - v) j : ℝ) = t := by
    rw [← integralRealBasis_repr_integerCast B (m - v) j, hmt']
    simp
  have hkpos : (0 : ℤ) < B.repr (m - v) j := by
    exact_mod_cast (hcoord ▸ ht : 0 < (B.repr (m - v) j : ℝ))
  refine ⟨B.repr (m - v) j, by omega, ?_⟩
  apply integerCast_injective
  rw [hmt', integralRealBasis_apply, hBj]
  ext i
  have hti : t = (B.repr (m - v) j : ℝ) := hcoord.symm
  simp only [integerCast, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [hti]

/-- The original smoothness membership gives actual FULL source lattice-point
membership for the neighbor, without a neighbor-index certificate. -/
theorem latticeEdgeBasis_neighbor_mem (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v + b E) ∈ E.val) (E : latticePolytopeEdgesAt γ v) :
    v + b E ∈ latticePolytopeIntegerPoints γ :=
  E.property.subset (hmem E)

/-- The internally enumerated SAME edge vectors retain actual original
neighbor membership, ready for the full source lattice-point enumeration. -/
theorem latticeEdgeCoordinateBasis_neighbor_mem (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v + b E) ∈ E.val) (j : Fin n) :
    v + latticeEdgeCoordinateBasis γ v b j ∈ latticePolytopeIntegerPoints γ := by
  rw [latticeEdgeCoordinateBasis_apply]
  exact latticeEdgeBasis_neighbor_mem γ v b hmem _

/-- The actual edge type is empty in rank zero. -/
theorem latticePolytopeEdgesAt_zero_isEmpty (γ : K → Fin 0 → ℤ) (v : Fin 0 → ℤ) :
    IsEmpty (latticePolytopeEdgesAt γ v) :=
  ⟨fun E => not_isOriginalPolytopeEdgeAt_zero _ _ _ E.property⟩

/-- The EXISTING empty-basis producer supplies literal rank-zero smoothness. -/
theorem latticePolytopeEdgeSmoothAt_zero (γ : K → Fin 0 → ℤ) (v : Fin 0 → ℤ) :
    latticePolytopeEdgeSmoothAt γ v := by
  let := latticePolytopeEdgesAt_zero_isEmpty γ v
  exact ⟨Module.Basis.empty (Fin 0 → ℤ), fun E => isEmptyElim E⟩

end SGPT.Toric
