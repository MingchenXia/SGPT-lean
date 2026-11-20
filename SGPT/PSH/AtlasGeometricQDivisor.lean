import SGPT.PSH.AtlasComponentPrimeTransport

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- A canonical literal ORIGINAL carrier represented by ONE genuine prime on
an internally derived actual component. Witness choices are not index data.
No universal native dictionary, local equation or prime catalog is a field. -/
def AtlasGeometricPrimeCarrier (A : VariableComplexAtlas X)
    [T2Space X] [ParacompactSpace X] :=
  {F : Set X // ∃ a : X,
    letI := A.componentChartedSpace a
    letI := A.componentComplexManifold_of_paracompact a
    ∃ P : GeometricPrimeCarrier (A.pointDimension a) (A.componentOpen a),
      Subtype.val '' P.val = F}

namespace AtlasGeometricPrimeCarrier
variable {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

/-- Exact existing native-to-original geometry, testing EVERY original cut. -/
theorem original_irreducible (P : AtlasGeometricPrimeCarrier A) :
    A.HasIrreducibleAnalyticChartEquations P.val := by
  obtain ⟨a, ha⟩ := P.property
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  obtain ⟨Q, hQ⟩ := ha
  rw [← hQ]
  exact A.geometricPrimeCarrier_componentImage_original_irreducible a Q

theorem nonempty (P : AtlasGeometricPrimeCarrier A) : P.val.Nonempty :=
  P.original_irreducible.2.1

theorem isClosed (P : AtlasGeometricPrimeCarrier A) : IsClosed P.val :=
  P.original_irreducible.1.isClosed A

/-- EVERY point of the SAME literal carrier fixes its entire original component. -/
theorem subset_connectedComponent (P : AtlasGeometricPrimeCarrier A)
    {x : X} (hx : x ∈ P.val) : P.val ⊆ connectedComponent x := by
  obtain ⟨a, ha⟩ := P.property
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  obtain ⟨Q, hQ⟩ := ha
  have hsub : P.val ⊆ connectedComponent a := by
    rw [← hQ]
    rintro y ⟨p, _hp, rfl⟩
    exact p.property
  intro y hy
  have h := hsub hy
  rwa [connectedComponent_eq (hsub hx)] at h

/-- Genuine native codimension and ORIGINAL component dimension constancy
exclude zero-dimensional components at EVERY actual original carrier point. -/
theorem pointDimension_pos (P : AtlasGeometricPrimeCarrier A)
    {x : X} (hx : x ∈ P.val) : 0 < A.pointDimension x := by
  obtain ⟨a, ha⟩ := P.property
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  obtain ⟨Q, hQ⟩ := ha
  have hxa : x ∈ connectedComponent a := by
    rw [← hQ] at hx
    obtain ⟨p, _hp, rfl⟩ := hx
    exact p.property
  have hpos : 0 < A.pointDimension a := by
    have hcodim := Q.subvariety_codimension
    omega
  rw [A.pointDimension_eq_on_connectedComponent a hxa]
  exact hpos

/-- Canonical equality is exactly equality of ORIGINAL carrier sets. -/
theorem ext {P Q : AtlasGeometricPrimeCarrier A} (h : P.val = Q.val) : P = Q :=
  Subtype.ext h

end AtlasGeometricPrimeCarrier

/-- ORIGINAL rational coefficients on actual canonical original carriers,
with precisely the source's locally finite nonzero-carrier convention.
No metric, global denominator, coherent type or prime catalog is a field. -/
structure AtlasEffectiveGeometricQDivisor (A : VariableComplexAtlas X)
    [T2Space X] [ParacompactSpace X] where
  coefficient : AtlasGeometricPrimeCarrier A → ℚ
  coefficient_nonneg : ∀ P, 0 ≤ coefficient P
  locallyFinite : LocallyFinite (fun P => if coefficient P = 0 then ∅ else P.val)

namespace AtlasEffectiveGeometricQDivisor
variable {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

/-- Literal support on the SAME original topology. -/
def support (D : AtlasEffectiveGeometricQDivisor A) : Set X :=
  ⋃ P, if D.coefficient P = 0 then ∅ else P.val

theorem mem_support (D : AtlasEffectiveGeometricQDivisor A) (x : X) :
    x ∈ D.support ↔ ∃ P, 0 < D.coefficient P ∧ x ∈ P.val := by
  classical
  constructor
  · intro hx
    obtain ⟨P, hxP⟩ := mem_iUnion.mp hx
    by_cases hzero : D.coefficient P = 0
    · simp only [hzero, ite_true, mem_empty_iff_false] at hxP
    · exact ⟨P, lt_of_le_of_ne (D.coefficient_nonneg P) (Ne.symm hzero),
        by simpa only [if_neg hzero] using hxP⟩
  · rintro ⟨P, hpos, hxP⟩
    exact mem_iUnion.mpr ⟨P, by simpa only [if_neg (ne_of_gt hpos)] using hxP⟩

theorem support_isClosed (D : AtlasEffectiveGeometricQDivisor A) :
    IsClosed D.support := by
  classical
  exact D.locallyFinite.isClosed_iUnion (fun P => by
    split_ifs
    · exact isClosed_empty
    · exact P.isClosed)

/-- The SAME positive ORIGINAL coefficient subtype retains actual local finiteness. -/
theorem locallyFinite_positive (D : AtlasEffectiveGeometricQDivisor A) :
    LocallyFinite (fun P : {P // 0 < D.coefficient P} => P.val.val) := by
  have h := D.locallyFinite.comp_injective
    (Subtype.val_injective : Function.Injective
      (Subtype.val : {P // 0 < D.coefficient P} → AtlasGeometricPrimeCarrier A))
  have heq : (fun P : {P // 0 < D.coefficient P} =>
      if D.coefficient P.val = 0 then (∅ : Set X) else P.val.val) =
      (fun P : {P // 0 < D.coefficient P} => P.val.val) := by
    funext P
    exact if_neg (ne_of_gt P.property)
  simpa only [Function.comp_def, heq] using h

/-- Literal support excludes EVERY zero-dimensional original component. -/
theorem pointDimension_pos_of_mem_support (D : AtlasEffectiveGeometricQDivisor A)
    {x : X} (hx : x ∈ D.support) : 0 < A.pointDimension x := by
  obtain ⟨P, _hpos, hxP⟩ := (D.mem_support x).mp hx
  exact P.pointDimension_pos hxP

end AtlasEffectiveGeometricQDivisor
end SGPT.PSH.VariableComplexAtlas
