import SGPT.Unibranch.NativeNov16RawAnalyticMorphismExt

/-! Genuine overlapping actual source charts internally manufacture full lift compatibility.
Blueprint: native-nov16-analytic-cover-lift-gluing.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16AnalyticCoverLiftGluing
open SourceReducedComplexSpace HironakaIntrinsicMorphismGluingAnalytic

theorem exists_unique_lift {ι : Type} {A : LocallyRingedSpace}
    (σA : A ⟶ complexPoint) (T : ι → LocallyRingedSpace) (j : ∀ i,T i ⟶ A)
    [∀ i,LocallyRingedSpace.IsOpenImmersion (j i)]
    (hcover : ∀ x : A,∃ (i : ι) (t : T i),(j i).base t=x)
    (hcharts : ∀ i,hasAnalyticCharts (Over.mk (j i ≫ σA)))
    {X B : SourceReducedComplexSpace} (p : B ⟶ X) (G : Set X.obj.left)
    (hp : IsIsoOver p G) (f : A ⟶ X.obj.left)
    (L : ∀ i,T i ⟶ B.obj.left) (hScalar : ∀ i,L i ≫ B.obj.hom=j i ≫ σA)
    (htri : ∀ i,L i ≫ p.hom.left=j i ≫ f)
    (hd : ∀ i,Dense ((j i ≫ f).base ⁻¹' G)) :
    ∃! F : A ⟶ B.obj.left,F ≫ p.hom.left=f ∧ F ≫ B.obj.hom=σA := by
  have hcompat (i k : ι) : pullback.fst (j i) (j k) ≫ L i=
      pullback.snd (j i) (j k) ≫ L k := by
    let a := pullback.fst (j i) (j k)
    let b := pullback.snd (j i) (j k)
    let σ := a ≫ (j i ≫ σA)
    have hch : hasAnalyticCharts (Over.mk σ) :=
      hasAnalyticCharts_of_openImmersion σ (j i ≫ σA) (hcharts i) a rfl
    have hden : Dense ((a ≫ (j i ≫ f)).base ⁻¹' G) := by
      change Dense (a.base ⁻¹' ((j i ≫ f).base ⁻¹' G))
      exact (hd i).preimage
        (inferInstance : LocallyRingedSpace.IsOpenImmersion a).base_open.isOpenMap
    apply NativeNov16RawAnalyticMorphismExt.hom_ext_of_dense_good σ hch p G hp
      (a ≫ (j i ≫ f)) hden (a ≫ L i) (b ≫ L k)
    · rw [Category.assoc,hScalar i]
    · rw [Category.assoc,hScalar k,← Category.assoc]
      change (pullback.snd (j i) (j k) ≫ j k) ≫ σA=
        pullback.fst (j i) (j k) ≫ (j i ≫ σA)
      rw [← pullback.condition,Category.assoc]
    · rw [Category.assoc,htri i]
    · rw [Category.assoc,htri k,← Category.assoc]
      change (pullback.snd (j i) (j k) ≫ j k) ≫ f=
        pullback.fst (j i) (j k) ≫ (j i ≫ f)
      rw [← pullback.condition,Category.assoc]
  obtain ⟨F,hF,_hFu⟩ := HironakaIntrinsicMorphismGluing.exists_unique_morphism T j hcover L hcompat
  have hFp : F ≫ p.hom.left=f := by
    apply HironakaIntrinsicMorphismGluing.hom_ext T j hcover
    intro i
    rw [← Category.assoc,hF,htri]
  have hFs : F ≫ B.obj.hom=σA := by
    apply HironakaIntrinsicMorphismGluing.hom_ext T j hcover
    intro i
    rw [← Category.assoc,hF,hScalar]
  refine ⟨F,⟨hFp,hFs⟩,?_⟩
  intro K hK
  apply HironakaIntrinsicMorphismGluing.hom_ext T j hcover
  intro i
  apply NativeNov16RawAnalyticMorphismExt.hom_ext_of_dense_good
    (j i ≫ σA) (hcharts i) p G hp (j i ≫ f) (hd i) (j i ≫ K) (j i ≫ F)
  · rw [Category.assoc,hK.2]
  · rw [Category.assoc,hFs]
  · rw [Category.assoc,hK.1]
  · rw [Category.assoc,hFp]

end SGPT.Unibranch.NativeNov16AnalyticCoverLiftGluing
