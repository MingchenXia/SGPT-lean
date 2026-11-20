import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding

/-! Actual full proper finite normal branch map into the SAME common original base open.
Blueprint: prime-nov16-analytic-normalization-original-branch-restriction.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRestriction
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding

variable {S B X : SourceReducedComplexSpace} (q : S ⟶ B)
  (hq : IsProperMap q.hom.left.base) (g : B ⟶ X)
  (U : Opens X.obj.left) [ParacompactSpace U] [ParacompactSpace (sourceOpen g U)]

def componentMap : restrictedBase (sourceOpen g U) ⟶ X := baseInclusion (sourceOpen g U) ≫ g

omit [ParacompactSpace U] in
private theorem component_lands : range (componentMap g U).hom.left.base ⊆ (U : Set X.obj.left) := by
  rintro _ ⟨b,rfl⟩
  let b0 : sourceOpen g U := b
  exact b0.property

omit [ParacompactSpace U] in
private theorem component_range :
    (Subtype.val : U → X.obj.left) ⁻¹' range (componentMap g U).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
  ext u
  constructor
  · rintro ⟨b,hb⟩
    let b0 : sourceOpen g U := b
    exact ⟨b0.val,hb⟩
  · rintro ⟨b,hb⟩
    have hbU : g.hom.left.base b ∈ U := hb.symm ▸ u.property
    exact ⟨⟨b,hbU⟩,hb⟩

def branchMap : restrictedSource q hq (sourceOpen g U) ⟶ restrictedBase U :=
  restrictedMap q hq (sourceOpen g U) ≫ landingMap (componentMap g U) U (component_lands g U)

private theorem landing_proper (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    IsProperMap (landingMap (componentMap g U) U (component_lands g U)).hom.left.base := by
  apply landingMap_proper
  · exact hg.comp (baseInclusion_isOpenImmersion (sourceOpen g U)).base_open.isEmbedding
  · rw [component_range]
    exact hc

theorem branchMap_proper (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    IsProperMap (branchMap q hq g U).hom.left.base :=
  (landing_proper g U hg hc).comp (restrictedMap_proper q hq (sourceOpen g U))

private theorem finite_fibres_comp {A B C : Type} (f : A → B) (g : B → C)
    (hf : ∀ b,(f ⁻¹' {b}).Finite) (hg : Function.Injective g) (c : C) :
    ((g ∘ f) ⁻¹' {c}).Finite := by
  by_cases he : ∃ b,g b=c
  · obtain ⟨b,hb⟩ := he
    have hs : (g ∘ f) ⁻¹' {c}=f ⁻¹' {b} := by
      ext a
      change g (f a)=c ↔ f a=b
      rw [← hb,hg.eq_iff]
    rw [hs]
    exact hf b
  · have hs : (g ∘ f) ⁻¹' {c}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact he ⟨f a,ha⟩
    rw [hs]
    exact finite_empty

theorem branchMap_fibres_finite
    (hfinite : ∀ b : B.obj.left,(q.hom.left.base ⁻¹' {b}).Finite)
    (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base))
    (x : (restrictedBase U).obj.left) : ((branchMap q hq g U).hom.left.base ⁻¹' {x}).Finite := by
  exact finite_fibres_comp (restrictedMap q hq (sourceOpen g U)).hom.left.base
    (landingMap (componentMap g U) U (component_lands g U)).hom.left.base
    (restrictedMap_fibres_finite q hq (sourceOpen g U) hfinite)
    (landingMap_closed (componentMap g U) U (component_lands g U)
      (hg.comp (baseInclusion_isOpenImmersion (sourceOpen g U)).base_open.isEmbedding)
      (by rw [component_range]; exact hc)).injective x

omit [ParacompactSpace U] in
theorem branchSource_normal
    (hn : ∀ p : S.obj.left,IsDomain (S.obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed (S.obj.left.presheaf.stalk p).carrier)
    (p : (restrictedSource q hq (sourceOpen g U)).obj.left) :
    IsDomain ((restrictedSource q hq (sourceOpen g U)).obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((restrictedSource q hq (sourceOpen g U)).obj.left.presheaf.stalk p).carrier :=
  restrictedSource_normal_stalks q hq (sourceOpen g U) (fun p _ => hn p) p

omit [ParacompactSpace U] in
private theorem restriction_surjective (hs : Function.Surjective q.hom.left.base) :
    Function.Surjective (restrictedMap q hq (sourceOpen g U)).hom.left.base := by
  intro b
  let b0 : sourceOpen g U := b
  obtain ⟨p,hp⟩ := hs b0.val
  have hpU : q.hom.left.base p ∈ sourceOpen g U := hp.symm ▸ b0.property
  let p0 : sourceOpen q (sourceOpen g U) := ⟨p,hpU⟩
  refine ⟨p0,Subtype.ext ?_⟩
  exact (restrictedMap_point q hq (sourceOpen g U) p0).trans hp

theorem branchMap_range (hs : Function.Surjective q.hom.left.base) :
    range (branchMap q hq g U).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
  have hr : range (landingMap (componentMap g U) U (component_lands g U)).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
    rw [← component_range g U]
    have hl : range (componentMap g U).hom.left.base ⊆ range (baseInclusion U).hom.left.base := by
      rintro _ ⟨b,rfl⟩
      let b0 : sourceOpen g U := b
      exact ⟨⟨g.hom.left.base b0.val,b0.property⟩,rfl⟩
    exact LocallyRingedSpace.IsOpenImmersion.lift_range _ _ hl
  change range ((landingMap (componentMap g U) U (component_lands g U)).hom.left.base ∘
    (restrictedMap q hq (sourceOpen g U)).hom.left.base)=_
  rw [Set.range_comp,Set.range_eq_univ.mpr (restriction_surjective q hq g U hs),Set.image_univ,hr]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRestriction
