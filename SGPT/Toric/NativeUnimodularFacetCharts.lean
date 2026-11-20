import SGPT.Toric.UnimodularFacetNeighbors
import SGPT.Toric.NativeLatticePolytopeCover
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators
attribute [local instance] monomialProjectiveTopology

variable {n d : ℕ}

/-- Actual original-character basis change identifies the SAME original
projective closure before any native chart transport. -/
def monomialOriginalClosureHomeomorph (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) :
    monomialProjectiveOrbitClosure β ≃ₜ
      monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) :=
  Homeomorph.setCongr (by
    have h := monomialProjectiveOrbitClosure_latticeBasisChange (Pi.basisFun ℤ (Fin n)) b β
    simpa only [Pi.basisFun_repr] using h.symm)

/-- This genuine homeomorphism retains the literal underlying original point. -/
theorem monomialOriginalClosureHomeomorph_val (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (p : monomialProjectiveOrbitClosure β) :
    (monomialOriginalClosureHomeomorph b β p).val = p.val := rfl

/-- The inverse retains the SAME point as well. -/
theorem monomialOriginalClosureHomeomorph_symm_val (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ)
    (p : monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j)) :
    ((monomialOriginalClosureHomeomorph b β).symm p).val = p.val := rfl

/-- Existing genuine native vertex chart transported to the SAME original
standard-coordinate orbit closure through a produced equality. -/
def monomialOriginalVertexChart (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    OpenPartialHomeomorph (monomialProjectiveOrbitClosure β) (Fin n → ℂ) :=
  (monomialOriginalClosureHomeomorph b β).transOpenPartialHomeomorph
    (monomialVertexChart b β v ν hpos hν)

/-- The actual original-closure chart has the whole C^n target, including n=0. -/
theorem monomialOriginalVertexChart_target (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (hν : ∀ j, β (ν j) - β v = b j) :
    (monomialOriginalVertexChart b β v ν hpos hν).target = Set.univ := rfl

/-- Its original source is exactly the SAME original vertex-coordinate open. -/
theorem monomialOriginalVertexChart_source (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (hν : ∀ j, β (ν j) - β v = b j) :
    (monomialOriginalVertexChart b β v ν hpos hν).source =
      Subtype.val ⁻¹' Set.range (monomialProjectiveRatioPoint d v) := by
  change (monomialOriginalClosureHomeomorph b β) ⁻¹'
    (monomialVertexChart b β v ν hpos hν).source = _
  rw [monomialVertexChart_source]
  rfl

/-- Whole inverse readback preserves the literal original normalized polynomials. -/
theorem monomialOriginalVertexChart_symm_val (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (hν : ∀ j, β (ν j) - β v = b j)
    (z : Fin n → ℂ) :
    ((monomialOriginalVertexChart b β v ν hpos hν).symm z).val = monomialVertexPoint b β v z := by
  change ((monomialVertexChart b β v ν hpos hν).symm z).val = _
  rw [monomialVertexChart_symm]
  rfl

/-- Exact ORIGINAL orbit-range equality transports the genuine boundary formula. -/
theorem monomialOriginalVertexChart_boundary (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (hν : ∀ j, β (ν j) - β v = b j)
    (z : Fin n → ℂ) :
    ((monomialOriginalVertexChart b β v ν hpos hν).symm z).val ∉
      Set.range (monomialProjectiveOrbit β) ↔ ∏ j, z j = 0 := by
  have hrange : Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) =
      Set.range (monomialProjectiveOrbit β) := by
    simpa only [Pi.basisFun_repr] using
      monomialProjectiveOrbit_range_latticeBasisChange (Pi.basisFun ℤ (Fin n)) b β
  rw [monomialOriginalVertexChart_symm_val, ← hrange]
  rw [monomialVertexPoint_mem_orbit_iff_prod_ne_zero b β v ν hpos hν]
  exact not_not

/-- EVERY original homogeneous representative has the SAME nonzero denominator
and original neighboring-coordinate ratio, after actual closure transport. -/
theorem monomialOriginalVertexChart_ratio (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (β : Fin (d + 1) → Fin n → ℤ) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (hν : ∀ j, β (ν j) - β v = b j)
    (p : monomialProjectiveOrbitClosure β)
    (hp : p ∈ (monomialOriginalVertexChart b β v ν hpos hν).source)
    (w : Fin (d + 1) → ℂ) (hw : w ≠ 0) (hpw : p.val = Projectivization.mk ℂ w hw) :
    w v ≠ 0 ∧ ∀ j, monomialOriginalVertexChart b β v ν hpos hν p j = w (ν j) / w v := by
  exact monomialVertexChart_ratio_readback b β v ν hpos hν
    (monomialOriginalClosureHomeomorph b β p) hp w hw hpw

/-- Original integral facet arithmetic manufactures a genuine chart on the
SAME full-lattice orbit closure. No sign, neighbor or native chart is supplied. -/
theorem exists_nativeUnimodularFacet_chart {K F : Type*} [Fintype K] [Fintype F]
    (γ : K → Fin n → ℤ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ) (v : latticePolytopeVertices γ)
    (σ : Fin n → F) (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hP : latticePolytope γ = integralFacetRegion u a)
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v.val) = 0)
    (hinactive : ∀ ρ, ρ ∉ Set.range σ → 0 < integralFacetValue u a ρ (integerCast v.val)) :
    ∃ (ν : Fin n → Fin (d + 1))
      (ch : OpenPartialHomeomorph
        (monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) (Fin n → ℂ)),
      (∀ j, latticePolytopeExponentFamily γ e (ν j) - v.val = c.symm (Pi.basisFun ℤ (Fin n) j)) ∧
      ch.target = Set.univ ∧
      ch.source = Subtype.val ⁻¹' Set.range
        (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) ∧
      (∀ z, (ch.symm z).val = monomialVertexPoint ((Pi.basisFun ℤ (Fin n)).map c.symm)
        (latticePolytopeExponentFamily γ e) (latticePolytopeVertexIndex γ e v) z) ∧
      (∀ z, (ch.symm z).val ∉ Set.range
        (monomialProjectiveOrbit (latticePolytopeExponentFamily γ e)) ↔ ∏ j, z j = 0) ∧
      (∀ p, p ∈ ch.source → ∀ w hw, p.val = Projectivization.mk ℂ w hw →
        w (latticePolytopeVertexIndex γ e v) ≠ 0 ∧ ∀ j, ch p j =
          w (ν j) / w (latticePolytopeVertexIndex γ e v)) := by
  let b := (Pi.basisFun ℤ (Fin n)).map c.symm
  let β := latticePolytopeExponentFamily γ e
  let vi := latticePolytopeVertexIndex γ e v
  have hβv : β vi = v.val := latticePolytopeExponentFamily_vertexIndex γ e v
  let ν : Fin n → Fin (d + 1) := fun j => e.symm
    ⟨v.val + c.symm (Pi.basisFun ℤ (Fin n) j),
      latticePolytope_unimodular_neighbor_mem γ u a v.val σ c hP hσ hzero hinactive j⟩
  have hβν (j : Fin n) : β (ν j) = v.val + c.symm (Pi.basisFun ℤ (Fin n) j) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hν : ∀ j, β (ν j) - β vi = b j := by
    intro j
    rw [hβν, hβv, add_sub_cancel_left]
    rfl
  have hpos : ∀ i j, 0 ≤ b.repr (β i - β vi) j := by
    intro i j
    have h := latticePolytope_unimodular_coordinate_nonneg γ u a v.val σ c hP hσ hzero (e i) j
    change 0 ≤ c (β i - v.val) j at h
    simpa only [b, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_symm, Pi.basisFun_repr, hβv] using h
  let ch := monomialOriginalVertexChart b β vi ν hpos hν
  refine ⟨ν, ch, ?_, monomialOriginalVertexChart_target b β vi ν hpos hν,
    monomialOriginalVertexChart_source b β vi ν hpos hν,
    monomialOriginalVertexChart_symm_val b β vi ν hpos hν,
    monomialOriginalVertexChart_boundary b β vi ν hpos hν, ?_⟩
  · intro j
    change β (ν j) - v.val = c.symm (Pi.basisFun ℤ (Fin n) j)
    rw [hβν, add_sub_cancel_left]
  · intro p hp w hw hpw
    exact monomialOriginalVertexChart_ratio b β vi ν hpos hν p hp w hw hpw

/-- Actual original source facet data at every actual vertex manufacture a
covering family of native whole-C^n charts on the SAME original closure. -/
theorem exists_nativeUnimodularFacet_covering_charts {K F : Type*}
    [Fintype K] [Nonempty K] [Fintype F]
    (γ : K → Fin n → ℤ) (e : Fin (d + 1) ≃ latticePolytopeIntegerPoints γ)
    (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (σ : latticePolytopeVertices γ → Fin n → F)
    (c : latticePolytopeVertices γ → ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)))
    (hP : latticePolytope γ = integralFacetRegion u a)
    (hσ : ∀ v j, u (σ v j) = (LinearMap.proj j).comp (c v).toLinearMap)
    (hzero : ∀ v j, integralFacetValue u a (σ v j) (integerCast v.val) = 0)
    (hinactive : ∀ v ρ, ρ ∉ Set.range (σ v) → 0 < integralFacetValue u a ρ (integerCast v.val)) :
    ∃ charts : latticePolytopeVertices γ → OpenPartialHomeomorph
        (monomialProjectiveOrbitClosure (latticePolytopeExponentFamily γ e)) (Fin n → ℂ),
      (∀ v, (charts v).target = Set.univ ∧
        (charts v).source = Subtype.val ⁻¹' Set.range
          (monomialProjectiveRatioPoint d (latticePolytopeVertexIndex γ e v)) ∧
        ∀ z, ((charts v).symm z).val ∉ Set.range
          (monomialProjectiveOrbit (latticePolytopeExponentFamily γ e)) ↔ ∏ j, z j = 0) ∧
      ∀ p, ∃ v, p ∈ (charts v).source := by
  classical
  choose ν ch hch using fun v => exists_nativeUnimodularFacet_chart γ e u a v (σ v) (c v)
    hP (hσ v) (hzero v) (hinactive v)
  refine ⟨ch, ?_, ?_⟩
  · intro v
    exact ⟨(hch v).2.1, (hch v).2.2.1, (hch v).2.2.2.2.1⟩
  · intro p
    obtain ⟨v, hv⟩ := nativeLatticePolytope_vertex_opens_cover γ e p.val p.property
    refine ⟨v, ?_⟩
    rw [(hch v).2.2.1]
    exact hv

/-- ONLY original finite lattice generators and original raw unimodular facet
data produce the full lattice enumeration AND actual native covering charts. -/
theorem exists_nativeUnimodularFacet_geometry {K F : Type*}
    [Fintype K] [Nonempty K] [Fintype F]
    (γ : K → Fin n → ℤ) (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (σ : latticePolytopeVertices γ → Fin n → F)
    (c : latticePolytopeVertices γ → ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)))
    (hP : latticePolytope γ = integralFacetRegion u a)
    (hσ : ∀ v j, u (σ v j) = (LinearMap.proj j).comp (c v).toLinearMap)
    (hzero : ∀ v j, integralFacetValue u a (σ v j) (integerCast v.val) = 0)
    (hinactive : ∀ v ρ, ρ ∉ Set.range (σ v) → 0 < integralFacetValue u a ρ (integerCast v.val)) :
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
  obtain ⟨charts, hcharts⟩ := exists_nativeUnimodularFacet_covering_charts γ e u a σ c
    hP hσ hzero hinactive
  exact ⟨d, e, charts, hcharts⟩

end SGPT.Toric
