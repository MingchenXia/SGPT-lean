import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedComponentInverse
import SGPT.Unibranch.ComplexOpenNativeModels
import SGPT.Unibranch.EmbeddedCommonResolutionGeneral
import SGPT.Unibranch.OriginalLocalStrictWindowRegularity

/-! SAME-witness component target immersion retains ENTIRE range and full original triangles.
Blueprint: prime-nov16-analytic-normalization-original-component-good-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentGoodInverse
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
open PrimeNov16AnalyticNormalizationOriginalComponentTargetRange
open PrimeNov16AnalyticNormalizationOriginalClosedComponentInverse
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding
open PrimeNov16AnalyticNormalizationLocalGraph
open SourceReducedComplexSpace

variable {n : ℕ} {B Z : Set (ComplexModel n)} (d : GraphPresentation n B)
  (P : Opens (ComplexModel n))
  (hB : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' B))
  (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
  (hBP : ((Subtype.val : P → ComplexModel n) ⁻¹' B) ⊆ ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
  (hDP : ballDomain (n := n) d.radius ≤ P)
  (g : d.target ⟶ sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ)
  (U : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
  [ParacompactSpace U]
  (hcoord : ∀ t : d.target.obj.left,(g.hom.left.base t).val.val=t.val.val.val)


  (hRange : ∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
    x ∈ U → (x ∈ range g.hom.left.base ↔ x.val.val ∈ B))

include hB hBP hDP hcoord hRange

theorem commonComponent_isIsoOver_original_good
    (G : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace G] (hGU : G ≤ U)
    (hGB : ∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ G → x.val.val ∈ B) :
    IsIsoOver (commonComponent d g U) ((baseInclusion U).hom.left.base ⁻¹' (G : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)) := by
  let j := componentTargetInclusion d P hB hZ hDP g U
  let c := OriginalClosedSubspaceFactorization.inclusion hB hZ hBP
  have hc : IsIsoOver c (G : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left) :=
    @closed_component_isIsoOver n P inferInstance inferInstance inferInstance
      ((Subtype.val : P → ComplexModel n) ⁻¹' B) ((Subtype.val : P → ComplexModel n) ⁻¹' Z)
      hB hZ hBP G (inferInstance : ParacompactSpace G) hGB
  have hj : IsIsoOver j (c.hom.left.base ⁻¹' (G : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)) := by
    apply (isIsoOver_range_of_isOpenImmersion j (componentTargetInclusion_isOpenImmersion d P hB hZ hDP g U)).of_isOpen_subset
      (G.isOpen.preimage c.hom.left.base.hom.continuous)
    intro x hx
    exact (Set.ext_iff.mp (componentTarget_range d P hB hZ hBP hDP g U hcoord hRange) x).mpr (hGU hx)
  have hbig : IsIsoOver (j ≫ c) (G : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left) := hc.comp hj
  have htri := componentTarget_triangle d P hB hZ hBP hDP g U hcoord
  apply OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square (j ≫ c)
    (commonComponent d g U) (𝟙 _) (baseInclusion U) (by infer_instance)
    (baseInclusion_isOpenImmersion U) (by simpa only [Category.id_comp] using htri) _ _ hbig
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨(commonComponent d g U).hom.left.base a,?_⟩
    exact congrArg (fun F => F.hom.left.base a) htri
  · intro _hp
    exact ⟨p,rfl⟩

theorem commonMap_isIsoOver_original_good
    (G : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace G] (hGU : G ≤ U)
    (hGB : ∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ G → x.val.val ∈ B)
    (hH : ∀ b : (commonGraph d g U).target.obj.left,
      ((commonComponent d g U).hom.left.base b).val ∈ G → d.denominator b.val.val.val ≠ 0) :
    IsIsoOver (commonMap d g U) ((baseInclusion U).hom.left.base ⁻¹' (G : Set (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)) := by
  have hc := commonComponent_isIsoOver_original_good d P hB hZ hBP hDP g U hcoord hRange G hGU hGB
  apply hc.comp
  apply (GraphPresentation.map_isIsoOver (commonGraph d g U)).of_isOpen_subset
    (((G.isOpen.preimage (baseInclusion U).hom.left.base.hom.continuous).preimage
      (commonComponent d g U).hom.left.base.hom.continuous))
  exact hH

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentGoodInverse
