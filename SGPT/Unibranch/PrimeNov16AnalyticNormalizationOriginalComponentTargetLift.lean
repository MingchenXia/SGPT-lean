import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion
import SGPT.Unibranch.OriginalClosedSubspaceFactorization

/-! Actual component factors manufacture their exact raw graph target maps.
Blueprint: prime-nov16-analytic-normalization-original-component-target-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
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

abbrev componentTargetInclusion : (commonGraph d g U).target ⟶
    sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' B) hB :=
  targetEmbedding d _ (commonBaseOpen_le d g U) ≫ d.baseInclusion ≫
    nativeOpenMap B (ballDomain (n := n) d.radius) P d.carrier_analytic hB hDP

instance componentTargetInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (componentTargetInclusion d P hB hZ hDP g U).hom.left := by
  exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    ((targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left ≫
      d.baseInclusion.hom.left ≫
      (nativeOpenMap B (ballDomain (n := n) d.radius) P d.carrier_analytic hB hDP).hom.left))

omit [ParacompactSpace U] in
theorem componentTargetInclusion_point (p : (commonGraph d g U).target.obj.left) :
    ((componentTargetInclusion d P hB hZ hDP g U).hom.left.base p).val.val=p.val.val.val := by
  exact congrArg (fun b => b.val.val) (targetEmbedding_point d _ (commonBaseOpen_le d g U) p)

theorem exists_unique_component_target_lift
    (hcoord : ∀ t : d.target.obj.left,(g.hom.left.base t).val.val=t.val.val.val)
    (hRange : ∀ x : (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ U → (x ∈ range g.hom.left.base ↔ x.val.val ∈ B))
    (A : SourceReducedComplexSpace)
    (f : A ⟶ sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' B) hB)
    (σ : A ⟶ restrictedBase U)
    (htri : f ≫ OriginalClosedSubspaceFactorization.inclusion hB hZ hBP=σ ≫ baseInclusion U) :
    ∃! L : A ⟶ (commonGraph d g U).target,
      L ≫ componentTargetInclusion d P hB hZ hDP g U=f := by
  let j := componentTargetInclusion d P hB hZ hDP g U
  have hland : range f.hom.left.base ⊆ range j.hom.left.base := by
    rintro _ ⟨a,rfl⟩
    let x := (OriginalClosedSubspaceFactorization.inclusion hB hZ hBP).hom.left.base (f.hom.left.base a)
    have hx : x ∈ U := by
      have he := congrArg (fun F => F.hom.left.base a) htri
      change x=(σ.hom.left.base a).val at he
      exact he.symm ▸ (σ.hom.left.base a).property
    have hxB : x.val.val ∈ B := (f.hom.left.base a).property
    obtain ⟨b,hb⟩ := (hRange x hx).mpr hxB
    have hbU : g.hom.left.base b ∈ U := hb.symm ▸ hx
    have hbV : b.val ∈ commonBaseOpen d g U :=
      (mem_commonBaseOpen d g U b.val).mpr ⟨b.property,hbU⟩
    let p : (commonGraph d g U).target.obj.left := ⟨b.val,hbV⟩
    refine ⟨p,Subtype.ext (Subtype.ext ?_)⟩
    exact (componentTargetInclusion_point d P hB hZ hDP g U p).trans
      ((hcoord b).symm.trans (congrArg (fun z => z.val.val) hb))
  let L := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left f.hom.left hland
  have hL := LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left f.hom.left hland
  have hs : L ≫ (commonGraph d g U).target.obj.hom=A.obj.hom := by
    rw [← Over.w j.hom,← Category.assoc,hL]
    exact Over.w f.hom
  let F : A ⟶ (commonGraph d g U).target := ObjectProperty.homMk (Over.homMk L hs)
  have hF : F ≫ j=f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hL
  refine ⟨F,hF,?_⟩
  intro K hK
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono j.hom.left).mp
  exact congrArg (fun q => q.hom.left) (hK.trans hF.symm)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentTargetLift
