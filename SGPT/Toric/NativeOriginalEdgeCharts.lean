import SGPT.Toric.OriginalEdgeConeCoordinates
import SGPT.Toric.NativeUnimodularFacetCharts

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators
attribute [local instance] monomialProjectiveTopology

variable {n d : ℕ}

/-- ONLY the book's original edge smoothness at the ACTUAL vertex manufactures
the finite basis, all coefficient signs and neighbor indices, then reuses the
existing genuine native chart on the SAME original projective orbit closure. -/
theorem exists_nativeOriginalEdge_chart {K : Type*} [Fintype K]
    (γ : K → Fin n → ℤ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (v : latticePolytopeVertices γ) (hsmooth : latticePolytopeEdgeSmoothAt γ v.val) :
    ∃ (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (ν : Fin n → Fin (d + 1))
      (ch : OpenPartialHomeomorph
        (monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) (Fin n → ℂ)),
      (∀ j, latticePolytopeExponentFamily γ e (ν j) - v.val = B j) ∧
      ch.target = Set.univ ∧
      ch.source = Subtype.val ⁻¹' Set.range
        (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) ∧
      (∀ z, (ch.symm z).val = monomialVertexPoint B
        (latticePolytopeExponentFamily γ e) (latticePolytopeVertexIndex γ e v) z) ∧
      (∀ z, (ch.symm z).val ∉ Set.range
        (monomialProjectiveOrbit (latticePolytopeExponentFamily γ e)) ↔ ∏ j, z j = 0) ∧
      (∀ p, p ∈ ch.source → ∀ w hw, p.val = Projectivization.mk ℂ w hw →
        w (latticePolytopeVertexIndex γ e v) ≠ 0 ∧ ∀ j, ch p j =
          w (ν j) / w (latticePolytopeVertexIndex γ e v)) := by
  obtain ⟨B, _, hcoeff, hneighbor⟩ := exists_latticePolytope_originalEdge_coordinate_basis γ v hsmooth
  let β := latticePolytopeExponentFamily γ e
  let vi := latticePolytopeVertexIndex γ e v
  have hβv : β vi = v.val := latticePolytopeExponentFamily_vertexIndex γ e v
  let ν : Fin n → Fin (d + 1) := fun j => e.symm ⟨v.val + B j, hneighbor j⟩
  have hβν (j : Fin n) : β (ν j) = v.val + B j :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hν : ∀ j, β (ν j) - β vi = B j := by
    intro j
    rw [hβν, hβv, add_sub_cancel_left]
  have hpos : ∀ i j, 0 ≤ B.repr (β i - β vi) j := by
    intro i j
    have h := hcoeff (e i) j
    change 0 ≤ B.repr (β i - v.val) j at h
    simpa only [hβv] using h
  let ch := monomialOriginalVertexChart B β vi ν hpos hν
  refine ⟨B, ν, ch, ?_, monomialOriginalVertexChart_target B β vi ν hpos hν,
    monomialOriginalVertexChart_source B β vi ν hpos hν,
    monomialOriginalVertexChart_symm_val B β vi ν hpos hν,
    monomialOriginalVertexChart_boundary B β vi ν hpos hν, ?_⟩
  · intro j
    change β (ν j) - v.val = B j
    rw [hβν, add_sub_cancel_left]
  · intro p hp w hw hpw
    exact monomialOriginalVertexChart_ratio B β vi ν hpos hν p hp w hw hpw

/-- Original edge smoothness at ALL actual original vertices manufactures a
covering family of genuine whole-C^n charts.  No normal-fan, sign, neighbor,
native chart, or covering certificate occurs in the input. -/
theorem exists_nativeOriginalEdge_covering_charts {K : Type*} [Fintype K] [Nonempty K]
    (γ : K → Fin n → ℤ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    ∃ charts : latticePolytopeVertices γ → OpenPartialHomeomorph
        (monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) (Fin n → ℂ),
      (∀ v, (charts v).target = Set.univ ∧
        (charts v).source = Subtype.val ⁻¹' Set.range
          (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) ∧
        ∀ z, ((charts v).symm z).val ∉ Set.range
          (monomialProjectiveOrbit (latticePolytopeExponentFamily γ e)) ↔ ∏ j, z j = 0) ∧
      ∀ p, ∃ v, p ∈ (charts v).source := by
  classical
  choose B ν ch hch using fun v => exists_nativeOriginalEdge_chart γ e v (hsmooth v)
  refine ⟨ch, ?_, ?_⟩
  · intro v
    exact ⟨(hch v).2.1, (hch v).2.2.1, (hch v).2.2.2.2.1⟩
  · intro p
    obtain ⟨v, hv⟩ := nativeLatticePolytope_vertex_opens_cover γ e p.val p.property
    refine ⟨v, ?_⟩
    rw [(hch v).2.2.1]
    exact hv

/-- ONLY original finite nonempty lattice generators and the book's ORIGINAL
edge-basis smoothness internally produce the FULL original lattice-point
index and covering native charts, with literal original torus boundary.
This is a geometry producer for the actual monomial closure; source fan/XΣ,
analytic compatibility and the Guillemin reference remain separate. -/
theorem exists_nativeOriginalEdge_geometry {K : Type*} [Fintype K] [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    ∃ (d : ℕ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
      (charts : latticePolytopeVertices γ → OpenPartialHomeomorph
        (monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) (Fin n → ℂ)),
      (∀ v, (charts v).target = Set.univ ∧
        (charts v).source = Subtype.val ⁻¹' Set.range
          (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) ∧
        ∀ z, ((charts v).symm z).val ∉ Set.range
          (monomialProjectiveOrbit (latticePolytopeExponentFamily γ e)) ↔ ∏ j, z j = 0) ∧
      ∀ p, ∃ v, p ∈ (charts v).source := by
  obtain ⟨d, ⟨e⟩⟩ := exists_latticePolytopeIntegerPoints_enumeration γ
  obtain ⟨charts, hcharts⟩ := exists_nativeOriginalEdge_covering_charts γ e hsmooth
  exact ⟨d, e, charts, hcharts⟩

end SGPT.Toric
