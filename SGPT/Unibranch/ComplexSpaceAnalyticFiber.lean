import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.ComplexSpacePSHMaximum
import SGPT.Unibranch.OriginalAnalyticClosedSubspace

/-! Actual original reduced analytic fibers and ordinary PSH constancy.
Blueprint: complex-space-analytic-fibers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The actual original reduced complex-space object on the literal fiber. -/
def analyticFiber {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (x : X.obj.left) :
    SourceReducedComplexSpace :=
  OriginalAnalyticClosedSubspace.sourceObject Y (f.hom.left.base ⁻¹' {x})
    (isAnalyticSubset_fiber f x)

/-- The full original reduced fiber inclusion, not only its point map. -/
def analyticFiberInclusion {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (x : X.obj.left) : analyticFiber f x ⟶ Y :=
  OriginalAnalyticClosedSubspace.inclusion Y (f.hom.left.base ⁻¹' {x})
    (isAnalyticSubset_fiber f x)

theorem analyticFiberInclusion_range {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (x : X.obj.left) : range (analyticFiberInclusion f x).hom.left.base = f.hom.left.base ⁻¹' {x} :=
  OriginalAnalyticClosedSubspace.inclusion_range Y _ (isAnalyticSubset_fiber f x)

theorem analyticFiberInclusion_isClosedEmbedding {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (x : X.obj.left) : IsClosedEmbedding (analyticFiberInclusion f x).hom.left.base :=
  OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding Y _ (isAnalyticSubset_fiber f x)

/-- A genuine homeomorphism to the SAME literal original point-set fiber. -/
def analyticFiberHomeomorph {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (x : X.obj.left) : (analyticFiber f x).obj.left ≃ₜ (f.hom.left.base ⁻¹' {x}) :=
  (analyticFiberInclusion_isClosedEmbedding f x).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (analyticFiberInclusion_range f x))

theorem analyticFiber_compact_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hp : IsProperMap f.hom.left.base) (x : X.obj.left) : CompactSpace (analyticFiber f x).obj.left := by
  let singularProperFiberCompact : CompactSpace (f.hom.left.base ⁻¹' {x}) :=
    isCompact_iff_compactSpace.mp (hp.isCompact_preimage isCompact_singleton)
  exact (analyticFiberHomeomorph f x).symm.compactSpace

theorem analyticFiber_connected_of_connected_fiber {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (x : X.obj.left) (hconn : IsConnected (f.hom.left.base ⁻¹' {x})) :
    ConnectedSpace (analyticFiber f x).obj.left := by
  let singularActualFiberConnected : ConnectedSpace (f.hom.left.base ⁻¹' {x}) :=
    isConnected_iff_connectedSpace.mp hconn
  exact (analyticFiberHomeomorph f x).symm.surjective.connectedSpace
    (analyticFiberHomeomorph f x).symm.continuous

/-- Original locally ambient PSH is genuinely constant on the literal
connected proper fiber. No PSH or constancy premise on that fiber is input. -/
theorem eq_on_connected_proper_fiber {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hp : IsProperMap f.hom.left.base) (x : X.obj.left)
    (hconn : IsConnected (f.hom.left.base ⁻¹' {x})) {φ : Y.obj.left → EReal}
    (hφ : ∀ y,Y.IsLocallyAmbientPSHAt φ y) {a b : Y.obj.left}
    (ha : f.hom.left.base a = x) (hb : f.hom.left.base b = x) : φ a = φ b := by
  let singularFiberObjectCompact := analyticFiber_compact_of_proper f hp x
  let singularFiberObjectConnected := analyticFiber_connected_of_connected_fiber f x hconn
  obtain ⟨c,-,hc⟩ := eq_const_of_compact_connected_pullback (analyticFiberInclusion f x) hφ
  obtain ⟨a',ha'⟩ : a ∈ range (analyticFiberInclusion f x).hom.left.base := by
    rw [analyticFiberInclusion_range]
    exact ha
  obtain ⟨b',hb'⟩ : b ∈ range (analyticFiberInclusion f x).hom.left.base := by
    rw [analyticFiberInclusion_range]
    exact hb
  have hac := congrFun hc a'
  have hbc := congrFun hc b'
  change φ ((analyticFiberInclusion f x).hom.left.base a') = c at hac
  change φ ((analyticFiberInclusion f x).hom.left.base b') = c at hbc
  rw [ha'] at hac
  rw [hb'] at hbc
  exact hac.trans hbc.symm

end SGPT.Unibranch.SourceReducedComplexSpace
