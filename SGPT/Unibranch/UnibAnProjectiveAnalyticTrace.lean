import SGPT.Unibranch.UnibAnMorphismFunctor
import SGPT.Unibranch.UnibAnSmoothIso
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Foundations.Schemes.NativeProjectiveFano

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Okounkov SGPT.Unibranch SGPT.Foundations.Schemes
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SourceReducedComplexSpace
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal inverse point readback for a smooth-space comparison whose forward
map preserves the same original complex points. -/
theorem smoothIso_inv_point
    {X : Scheme.{0}} {g : X ⟶ Spec (.of ℂ)} {n : ℕ}
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]
    (E : @wholeModel n (SchemeComplexPoint g) (schemeAnalyticPointTopology g)
        (schemeAnalyticTNChartedSpace g n) (schemeAnalyticTN_isComplexManifold g n) ≅
        analytification g)
    (hE : ∀ p : SchemeComplexPoint g,
      pointMap g (E.hom.hom.left.base ⟨p, Set.mem_univ p⟩) = p)
    (x : analytificationLRS g) : (E.inv.hom.left.base x).val = pointMap g x := by
  let y := E.inv.hom.left.base x
  have h := congrArg (fun F : analytification g ⟶ analytification g => F.hom.left.base x)
    E.inv_hom_id
  change E.hom.hom.left.base y = x at h
  exact (hE y.val).symm.trans (congrArg (pointMap g) h)

/-- Zariski-closed subsets have analytic traces on the original projective
analytification, with the literal scheme-point test. The pullback is along the
actual LRS morphism induced by the projective embedding. -/
theorem isAnalyticSubset_projective_algebraicTrace
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    (E : ClosedProjectiveEmbedding f) (Z : Set X) (hZ : IsClosed Z) :
    (analytification f).IsAnalyticSubset ((schemeComplexPointImage f ∘ pointMap f) ⁻¹' Z) := by
  let n := E.ambientDimension
  let g := polynomialProjStructureMap ℂ n
  let P : ClosedProjectiveEmbedding g := ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  let : SmoothOfRelativeDimension n g := inferInstanceAs
    (SmoothOfRelativeDimension n (polynomialProjStructureMap ℂ n))
  let : IsSeparated g := P.isSeparated
  let : QuasiCompact g := P.quasiCompact
  let : LocallyOfFiniteType g := P.locallyOfFiniteType
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n
  let : IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n
  obtain ⟨a, ha⟩ := exists_smoothModel_analytification_iso g n
  let i : analytification f ⟶ analytification g := analytificationMorphism E.map E.over_base
  let π : analytification f ⟶ wholeModel (n := n) (SchemeComplexPoint g) := i ≫ a.inv
  let A := schemeNativeAlgebraicTrace g (E.map '' Z)
  have hA : IsComplexAnalyticSubset (n := n) A :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset g n _ (E.map.isClosedEmbedding.isClosedMap _ hZ)
  let B := (Subtype.val : ↥(Set.univ : Set (SchemeComplexPoint g)) → SchemeComplexPoint g) ⁻¹' A
  have hB : (wholeModel (n := n) (SchemeComplexPoint g)).IsAnalyticSubset B :=
    isAnalyticSubset_preimage_val (isComplexAnalyticSubset_univ (n := n)) hA
  have hread (x : analytificationLRS f) :
      (π.hom.left.base x).val = schemeComplexPointMap f g E.map E.over_base (pointMap f x) := by
    change (a.inv.hom.left.base (i.hom.left.base x)).val = _
    exact (smoothIso_inv_point a ha (i.hom.left.base x)).trans
      (pointMap_analytificationMorphism E.map E.over_base x)
  have heq : π.hom.left.base ⁻¹' B = (schemeComplexPointImage f ∘ pointMap f) ⁻¹' Z := by
    ext x
    change schemeComplexPointImage g (π.hom.left.base x).val ∈ E.map '' Z ↔
      schemeComplexPointImage f (pointMap f x) ∈ Z
    have hs : schemeComplexPointImage g (π.hom.left.base x).val =
        E.map (schemeComplexPointImage f (pointMap f x)) := by
      exact (congrArg (schemeComplexPointImage g) (hread x)).trans
        (Scheme.Hom.comp_apply _ _ _)
    exact (Iff.of_eq (congrArg (fun y => y ∈ E.map '' Z) hs)).trans
      E.map.isClosedEmbedding.injective.mem_set_image
  exact heq ▸ (hB.preimage π)

end

end SGPT.Unibranch.UnibAn
