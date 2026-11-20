import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding
import SGPT.Unibranch.OriginalClosedSubspaceFactorization

/-! Genuine full inverse over an actual open contained in a literal analytic component.
Blueprint: prime-nov16-analytic-normalization-original-closed-component-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedComponentInverse
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding

theorem closed_component_isIsoOver {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {C D : Set M} (hC : IsComplexAnalyticSubset (n := n) C)
    (hD : IsComplexAnalyticSubset (n := n) D) (hCD : C ⊆ D)
    (G : Opens (ofClosedAnalytic D hD).obj.left) [ParacompactSpace G]
    (hG : ∀ x : (ofClosedAnalytic D hD).obj.left,x ∈ G → x.val ∈ C) :
    IsIsoOver (OriginalClosedSubspaceFactorization.inclusion hC hD hCD) G := by
  let X := ofClosedAnalytic D hD
  let Y := ofClosedAnalytic C hC
  let j : Y ⟶ X := OriginalClosedSubspaceFactorization.inclusion hC hD hCD
  have hp : IsProperMap j.hom.left.base := by
    change IsProperMap (Set.inclusion hCD)
    exact (Topology.IsClosedEmbedding.inclusion hCD
      (hC.isClosed.preimage continuous_subtype_val)).isProperMap
  let A := restrictedSource j hp G
  let T := restrictedBase G
  let i : A ⟶ Y := sourceInclusion j hp G
  let k : T ⟶ X := baseInclusion G
  let L : A ⟶ T := restrictedMap j hp G
  have hL : L ≫ k=i ≫ j := restrictedMap_square j hp G
  obtain ⟨R0,hR0,_huniq⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization
    hC hD hCD T k (fun x => hG x.val x.property)
  have hland : range R0.hom.left.base ⊆ range i.hom.left.base := by
    rintro _ ⟨x,rfl⟩
    have he := congrArg (fun F => F.hom.left.base x) hR0
    have hx : j.hom.left.base (R0.hom.left.base x) ∈ G := he.symm ▸ x.property
    exact ⟨⟨R0.hom.left.base x,hx⟩,rfl⟩
  let Rraw := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left R0.hom.left hland
  have hRi := LocallyRingedSpace.IsOpenImmersion.lift_fac i.hom.left R0.hom.left hland
  have hRs : Rraw ≫ A.obj.hom=T.obj.hom := by
    rw [← Over.w i.hom,← Category.assoc,hRi]
    exact Over.w R0.hom
  let R : T ⟶ A := ObjectProperty.homMk (Over.homMk Rraw hRs)
  have hR : R ≫ i=R0 := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hRi
  have hLR : L ≫ R=𝟙 A := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (i.hom.left ≫ j.hom.left)).mp
    have he : (L ≫ R) ≫ (i ≫ j)=𝟙 A ≫ (i ≫ j) := by
      calc
        _=L ≫ ((R ≫ i) ≫ j) := by simp only [Category.assoc]
        _=L ≫ (R0 ≫ j) := congrArg (fun z => L ≫ (z ≫ j)) hR
        _=L ≫ k := congrArg (fun z => L ≫ z) hR0
        _=i ≫ j := hL
        _= _ := (Category.id_comp (i ≫ j)).symm
    exact congrArg (fun F => F.hom.left) he
  have hRL : R ≫ L=𝟙 T := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono k.hom.left).mp
    have he : (R ≫ L) ≫ k=𝟙 T ≫ k := by
      rw [Category.assoc,hL,← Category.assoc,hR,hR0,Category.id_comp]
    exact congrArg (fun F => F.hom.left) he
  let E : A.obj.left ≅ T.obj.left :=
    { hom := L.hom.left
      inv := R.hom.left
      hom_inv_id := congrArg (fun F => F.hom.left) hLR
      inv_hom_id := congrArg (fun F => F.hom.left) hRL }
  have hLI : LocallyRingedSpace.IsOpenImmersion L.hom.left := by
    have : IsIso L.hom.left := E.isIso_hom
    infer_instance
  have hraw : i.hom.left ≫ j.hom.left=L.hom.left ≫ k.hom.left := by
    exact (congrArg (fun F => F.hom.left) hL).symm
  refine ⟨A.obj.left,i.hom.left,sourceInclusion_isOpenImmersion j hp G,Subtype.range_coe,?_,?_⟩
  · rw [hraw]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hLI _ (baseInclusion_isOpenImmersion G)
  · rw [hraw]
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact (L.hom.left.base a).property
    · intro hx
      let x0 : T.obj.left := ⟨x,hx⟩
      refine ⟨R.hom.left.base x0,?_⟩
      have he := congrArg (fun F => F.hom.left.base x0) hRL
      exact congrArg Subtype.val he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedComponentInverse
