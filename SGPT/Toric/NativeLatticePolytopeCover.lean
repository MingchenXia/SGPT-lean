import SGPT.Toric.LatticePolytopeSource
import SGPT.Toric.MonomialVertexCover

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
attribute [local instance] monomialProjectiveTopology

variable {n d : ℕ} {K : Type*} [Fintype K]

/-- The literal FULL original exponent family, from an actual finite enumeration
of the manufactured P intersect Z^n set. No geometry/cover certificate is supplied. -/
def latticePolytopeExponentFamily (γ : K → Fin n → ℤ)
    (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ) : Fin (d + 1) → Fin n → ℤ :=
  fun i => (e i).val

/-- Actual vertices select their OWN original indices inside the FULL lattice-point
family, using the already manufactured original integer membership. -/
def latticePolytopeVertexIndex (γ : K → Fin n → ℤ)
    (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (v : latticePolytopeVertices γ) : Fin (d + 1) :=
  e.symm ⟨v.val, v.property.1⟩

omit [Fintype K] in
/-- The selected exponent is the SAME original integer vertex, before any real readback. -/
theorem latticePolytopeExponentFamily_vertexIndex (γ : K → Fin n → ℤ)
    (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ) (v : latticePolytopeVertices γ) :
    latticePolytopeExponentFamily γ e (latticePolytopeVertexIndex γ e v) = v.val := by
  exact congrArg Subtype.val (e.apply_symm_apply ⟨v.val, v.property.1⟩)

/-- The actual source polytope and its ACTUAL vertices manufacture the EXACT
raw hull condition of the genuine native cover, with no hull assumption. -/
theorem latticePolytopeExponentFamily_vertex_hull (γ : K → Fin n → ℤ)
    (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ) (i : Fin (d + 1)) :
    (fun k => (latticePolytopeExponentFamily γ e i k : ℝ)) ∈
      convexHull ℝ (Set.range (fun v : latticePolytopeVertices γ => fun k =>
        (latticePolytopeExponentFamily γ e (latticePolytopeVertexIndex γ e v) k : ℝ))) := by
  have himage : Set.range (fun v : latticePolytopeVertices γ => fun k =>
      (latticePolytopeExponentFamily γ e (latticePolytopeVertexIndex γ e v) k : ℝ)) =
        integerCast '' latticePolytopeVertices γ := by
    simp_rw [latticePolytopeExponentFamily_vertexIndex]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  rw [himage]
  exact latticePolytopeIntegerPoint_mem_vertex_hull γ (e i)

variable [Nonempty K]

/-- Original finite lattice generators internally manufacture the ACTUAL global
native vertex-open cover for the FULL original lattice-point exponent family. -/
theorem nativeLatticePolytope_vertex_opens_cover (γ : K → Fin n → ℤ)
    (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (p : Projectivization ℂ (Fin (d + 1) → ℂ))
    (hp : p ∈ monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) :
    ∃ v : latticePolytopeVertices γ,
      p ∈ Set.range (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) := by
  let : Fintype (latticePolytopeVertices γ) := (finite_latticePolytopeVertices γ).fintype
  let : Nonempty (latticePolytopeVertices γ) := (nonempty_latticePolytopeVertices γ).to_subtype
  exact monomialProjectiveOrbitClosure_vertex_opens_cover
    (latticePolytopeExponentFamily γ e) (latticePolytopeVertexIndex γ e)
    (latticePolytopeExponentFamily_vertex_hull γ e) p hp

/-- With ONLY the original finite nonempty integer generator family as input,
produce a genuine FULL lattice-point enumeration and its ACTUAL native vertex
cover. No enumeration, finite-point, vertex-hull or cover premise is assumed. -/
theorem exists_nativeLatticePolytope_vertex_cover (γ : K → Fin n → ℤ) :
    ∃ (d : ℕ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ),
      ∀ p : Projectivization ℂ (Fin (d + 1) → ℂ),
        p ∈ monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e) →
          ∃ v : latticePolytopeVertices γ,
            p ∈ Set.range (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) := by
  obtain ⟨d, ⟨e⟩⟩ := exists_latticePolytopeIntegerPoints_enumeration γ
  exact ⟨d, e, nativeLatticePolytope_vertex_opens_cover γ e⟩

end SGPT.Toric
