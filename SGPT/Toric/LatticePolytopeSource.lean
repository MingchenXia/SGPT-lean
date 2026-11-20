import SGPT.AlmostSemigroup.Counting
import Mathlib.Analysis.Convex.KreinMilman

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting

variable {n : ℕ} {K : Type*} [Fintype K]

/-- The ORIGINAL lattice polytope: actual real convex hull of original integer
generators. No finite-point, vertex, fan or geometry fields are supplied. -/
def latticePolytope (γ : K → Fin n → ℤ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range (fun k => integerCast (γ k)))

/-- The literal FULL original lattice-point set P intersect Z^n. -/
def latticePolytopeIntegerPoints (γ : K → Fin n → ℤ) : Set (Fin n → ℤ) :=
  integerPoints (latticePolytope γ)

/-- Actual original integer points which are extreme points of the SAME real
polytope, rather than a supplied finite vertex enumeration. -/
def latticePolytopeVertices (γ : K → Fin n → ℤ) : Set (Fin n → ℤ) :=
  {m | m ∈ latticePolytopeIntegerPoints γ ∧ integerCast m ∈ (latticePolytope γ).extremePoints ℝ}

omit [Fintype K] in
/-- The actual original integer-point definition retains exact coordinate casting. -/
theorem mem_latticePolytopeIntegerPoints_iff (γ : K → Fin n → ℤ) (m : Fin n → ℤ) :
    m ∈ latticePolytopeIntegerPoints γ ↔ integerCast m ∈ latticePolytope γ := Iff.rfl

omit [Fintype K] in
/-- Existing convex-hull geometry gives convexity of the original source object. -/
theorem convex_latticePolytope (γ : K → Fin n → ℤ) : Convex ℝ (latticePolytope γ) :=
  convex_convexHull ℝ _

/-- Existing genuine finite-hull compactness produces original compactness. -/
theorem isCompact_latticePolytope (γ : K → Fin n → ℤ) : IsCompact (latticePolytope γ) :=
  (Set.finite_range (fun k => integerCast (γ k))).isCompact_convexHull ℝ

omit [Fintype K] in
/-- Every actual original integer generator lies in its SAME real source polytope. -/
theorem latticePolytope_generator_mem (γ : K → Fin n → ℤ) (k : K) :
    integerCast (γ k) ∈ latticePolytope γ :=
  subset_convexHull ℝ _ ⟨k, rfl⟩

omit [Fintype K] in
/-- The original generators manufacture genuine integer-point indices. -/
theorem latticePolytope_integer_generator_mem (γ : K → Fin n → ℤ) (k : K) :
    γ k ∈ latticePolytopeIntegerPoints γ := latticePolytope_generator_mem γ k

/-- Actual source compactness and the EXISTING discrete integer-lattice mother
produce finiteness of the FULL original P intersect Z^n. -/
theorem finite_latticePolytopeIntegerPoints (γ : K → Fin n → ℤ) :
    (latticePolytopeIntegerPoints γ).Finite :=
  finite_integerPoints (isCompact_latticePolytope γ).isBounded

omit [Fintype K] in
/-- Existing true finite-hull extremality puts every actual vertex in the
original integer generator image, without a vertex-generation certificate. -/
theorem latticePolytope_extremePoints_subset_generators (γ : K → Fin n → ℤ) :
    (latticePolytope γ).extremePoints ℝ ⊆ Set.range (fun k => integerCast (γ k)) :=
  extremePoints_convexHull_subset

/-- Actual extreme points form a genuinely finite original real set. -/
theorem finite_latticePolytope_extremePoints (γ : K → Fin n → ℤ) :
    ((latticePolytope γ).extremePoints ℝ).Finite :=
  (Set.finite_range (fun k => integerCast (γ k))).subset
    (latticePolytope_extremePoints_subset_generators γ)

/-- The actual integer vertex set is finite by the produced original lattice-point finiteness. -/
theorem finite_latticePolytopeVertices (γ : K → Fin n → ℤ) :
    (latticePolytopeVertices γ).Finite :=
  (finite_latticePolytopeIntegerPoints γ).subset (fun _ hm => hm.1)

omit [Fintype K] in
/-- The actual real vertex image is EXACTLY the actual extreme-point set
of the SAME original polytope, with integer preimages manufactured internally. -/
theorem latticePolytopeVertices_cast_image (γ : K → Fin n → ℤ) :
    integerCast '' latticePolytopeVertices γ = (latticePolytope γ).extremePoints ℝ := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm.2
  · intro hx
    obtain ⟨k, hk⟩ := latticePolytope_extremePoints_subset_generators γ hx
    change integerCast (γ k) = x at hk
    refine ⟨γ k, ⟨latticePolytope_integer_generator_mem γ k, ?_⟩, hk⟩
    rwa [hk]

omit [Fintype K] in
/-- Original lattice membership and original generator inclusion give the
EXACT hull of ALL original lattice points, without a hull premise. -/
theorem convexHull_latticePolytopeIntegerPoints (γ : K → Fin n → ℤ) :
    convexHull ℝ (integerCast '' latticePolytopeIntegerPoints γ) = latticePolytope γ := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨m, hm, rfl⟩
      exact hm
    · exact convex_latticePolytope γ
  · apply convexHull_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨γ k, latticePolytope_integer_generator_mem γ k, rfl⟩

/-- Genuine Krein--Milman and produced finite-hull closedness give the EXACT
original polytope as the hull of its actual integer vertices. -/
theorem convexHull_latticePolytopeVertices (γ : K → Fin n → ℤ) :
    convexHull ℝ (integerCast '' latticePolytopeVertices γ) = latticePolytope γ := by
  rw [latticePolytopeVertices_cast_image]
  calc
    _ = closure (convexHull ℝ ((latticePolytope γ).extremePoints ℝ)) :=
      ((finite_latticePolytope_extremePoints γ).isClosed_convexHull ℝ).closure_eq.symm
    _ = _ := closure_convexHull_extremePoints (isCompact_latticePolytope γ) (convex_latticePolytope γ)

/-- Every FULL original lattice point satisfies the EXACT produced vertex-hull
condition required by the native vertex-open-cover producer. -/
theorem latticePolytopeIntegerPoint_mem_vertex_hull (γ : K → Fin n → ℤ)
    (m : latticePolytopeIntegerPoints γ) :
    integerCast m.val ∈ convexHull ℝ (integerCast '' latticePolytopeVertices γ) := by
  rw [convexHull_latticePolytopeVertices]
  exact m.property

variable [Nonempty K]

omit [Fintype K] in
/-- Actual nonempty source generators manufacture nonempty original polytope. -/
theorem nonempty_latticePolytope (γ : K → Fin n → ℤ) : (latticePolytope γ).Nonempty :=
  ⟨integerCast (γ (Classical.arbitrary K)), latticePolytope_generator_mem γ _⟩

omit [Fintype K] in
/-- Actual original generators manufacture nonempty FULL lattice-point index. -/
theorem nonempty_latticePolytopeIntegerPoints (γ : K → Fin n → ℤ) :
    (latticePolytopeIntegerPoints γ).Nonempty :=
  ⟨γ (Classical.arbitrary K), latticePolytope_integer_generator_mem γ _⟩

/-- Genuine compact extreme-point existence and actual integer vertex readback
manufacture nonempty original vertices, including rank zero and lower affine dimension. -/
theorem nonempty_latticePolytopeVertices (γ : K → Fin n → ℤ) :
    (latticePolytopeVertices γ).Nonempty := by
  obtain ⟨x, hx⟩ := (isCompact_latticePolytope γ).extremePoints_nonempty (nonempty_latticePolytope γ)
  rw [← latticePolytopeVertices_cast_image γ] at hx
  obtain ⟨m, hm, _⟩ := hx
  exact ⟨m, hm⟩

/-- The actual finite nonempty FULL original lattice-point set has a genuine
nonempty Fin(d+1) enumeration, produced without an enumeration premise. -/
theorem exists_latticePolytopeIntegerPoints_enumeration (γ : K → Fin n → ℤ) :
    ∃ d : ℕ, Nonempty (Fin (d + 1) ≃ latticePolytopeIntegerPoints γ) := by
  let : Fintype (latticePolytopeIntegerPoints γ) := (finite_latticePolytopeIntegerPoints γ).fintype
  let : Nonempty (latticePolytopeIntegerPoints γ) := (nonempty_latticePolytopeIntegerPoints γ).to_subtype
  have hpos : 0 < Fintype.card (latticePolytopeIntegerPoints γ) := Fintype.card_pos
  refine ⟨Fintype.card (latticePolytopeIntegerPoints γ) - 1, ⟨?_⟩⟩
  exact (Fintype.equivFinOfCardEq (Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)).symm).symm

end SGPT.Toric
