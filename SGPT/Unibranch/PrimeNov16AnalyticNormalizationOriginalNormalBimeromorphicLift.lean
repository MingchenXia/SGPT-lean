import SGPT.Unibranch.NativeNov16NormalizationExistence
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance
import SGPT.Unibranch.NativeNov16LocalModelMorphismExt

/-! Full global normal-source proper-bimeromorphic lift, with every local object constructed internally.
Blueprint: prime-nov16-analytic-normalization-original-normal-bimeromorphic-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology
open SGPT.Foundations.Analysis.Pending HironakaReducedComplexAnalyticSpaces
open HironakaIntrinsicComplexAnalyticRegularLocus
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalBimeromorphicLift
open SourceReducedComplexSpace NativeNov16LocalModelMorphismExt
open PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting

private theorem glue_actual_lifts {ι : Type} {A : LocallyRingedSpace}
    (σA : A ⟶ complexPoint) (T : ι → LocallyRingedSpace) (j : ∀ i,T i ⟶ A)
    [∀ i,LocallyRingedSpace.IsOpenImmersion (j i)]
    (hcover : ∀ x : A,∃ (i : ι) (t : T i),(j i).base t=x)
    (hcharts : ∀ i,HasLocalModels (T i) (j i ≫ σA))
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
    have hch : HasLocalModels (pullback (j i) (j k)) σ :=
      PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance.hasLocalModels_of_openImmersion σ (j i ≫ σA) (hcharts i) a rfl
    have hden : Dense ((a ≫ (j i ≫ f)).base ⁻¹' G) := by
      change Dense (a.base ⁻¹' ((j i ≫ f).base ⁻¹' G))
      exact (hd i).preimage
        (inferInstance : LocallyRingedSpace.IsOpenImmersion a).base_open.isOpenMap
    apply NativeNov16LocalModelMorphismExt.hom_ext_of_dense_good σ hch p G hp
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
  apply NativeNov16LocalModelMorphismExt.hom_ext_of_dense_good
    (j i ≫ σA) (hcharts i) p G hp (j i ≫ f) (hd i) (j i ≫ K) (j i ≫ F)
  · rw [Category.assoc,hK.2]
  · rw [Category.assoc,hFs]
  · rw [Category.assoc,hK.1]
  · rw [Category.assoc,hFp]

private def baseRange (X : SourceReducedComplexSpace) (i : X.obj.left) : Opens X.obj.left :=
  ⟨range (atPoint X i).into.hom.left.base,(atPoint X i).into_open.base_open.isOpen_range⟩

private instance baseRange_paracompact (X : SourceReducedComplexSpace) (i : X.obj.left) :
    ParacompactSpace (baseRange X i) := by
  let : MetrizableSpace (atPoint X i).base.obj.left := (atPoint X i).base_metrizable
  let e : (atPoint X i).base.obj.left ≃ₜ baseRange X i :=
    (atPoint X i).into_open.base_open.isEmbedding.toHomeomorph
  let : MetrizableSpace (baseRange X i) := e.symm.isEmbedding.metrizableSpace
  let : MetricSpace (baseRange X i) := TopologicalSpace.metrizableSpaceMetric (baseRange X i)
  infer_instance

theorem exists_unique_lift {X Y : SourceReducedComplexSpace}
    (hY : ∀ y : Y.obj.left,IsDomain (Y.obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (Y.obj.left.presheaf.stalk y).carrier)
    (f : Y ⟶ X) (hf : IsProperBimeromorphic f) :
    ∃! L : Y ⟶ NativeNov16NormalizationSpace.source X,
      L ≫ NativeNov16NormalizationSpace.projection X=f := by
  let hp := hf.1
  obtain ⟨Z,_hZa,_hZ,hbad,hgood⟩ := hf.2
  have hdOld : Dense (f.hom.left.base ⁻¹' Zᶜ) := by
    simpa only [Set.preimage_compl] using (interior_eq_empty_iff_dense_compl.mp hbad)
  have hdReg : Dense (f.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
    PrimeNov16AnalyticNormalizationOriginalGoodDensity.dense_preimage_of_actual_good_inverse
      f Zᶜ hgood hdOld _ (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus X)
  let A (i : X.obj.left) := restrictedSource f hp (baseRange X i)
  let j (i : X.obj.left) : A i ⟶ Y := sourceInclusion f hp (baseRange X i)
  let : ∀ i,LocallyRingedSpace.IsOpenImmersion (j i).hom.left := fun i =>
    sourceInclusion_isOpenImmersion f hp (baseRange X i)
  have hnormal (i : X.obj.left) : ∀ y : (A i).obj.left,
      IsDomain ((A i).obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((A i).obj.left.presheaf.stalk y).carrier :=
    restrictedSource_normal_stalks f hp (baseRange X i) (fun y _hy => hY y)
  have hcover : ∀ y : Y.obj.left,∃ (i : X.obj.left) (a : (A i).obj.left),(j i).hom.left.base a=y := by
    intro y
    obtain ⟨i,b,hb⟩ := NativeNov16NormalizationSpace.base_cover X (f.hom.left.base y)
    exact ⟨i,⟨y,⟨b,hb⟩⟩,rfl⟩
  have hlocal (i : X.obj.left) : ∃ L : A i ⟶ NativeNov16NormalizationSpace.source X,
      L ≫ NativeNov16NormalizationSpace.projection X=j i ≫ f := by
    obtain ⟨g,hg,G,hG,hd⟩ := exists_actual_overlap_retargeting f hp Zᶜ hgood hdOld
      (𝟙 X) (atPoint X i).into (baseRange X i) (fun _x hx => hx)
    obtain ⟨l,hl,_hu⟩ := (atPoint X i).good_map_lift (A i) (hnormal i) g G hG hd
    refine ⟨l ≫ NativeNov16NormalizationExistence.chartMorphism X i,?_⟩
    calc
      (l ≫ NativeNov16NormalizationExistence.chartMorphism X i) ≫
          NativeNov16NormalizationSpace.projection X =
          l ≫ (NativeNov16NormalizationExistence.chartMorphism X i ≫
            NativeNov16NormalizationSpace.projection X) := Category.assoc _ _ _
      _ = l ≫ ((atPoint X i).projection ≫ (atPoint X i).into) :=
        congrArg (fun t => l ≫ t) (NativeNov16NormalizationExistence.chart_projection X i)
      _ = (l ≫ (atPoint X i).projection) ≫ (atPoint X i).into := (Category.assoc _ _ _).symm
      _ = g ≫ (atPoint X i).into := congrArg (fun t => t ≫ (atPoint X i).into) hl
      _ = j i ≫ f := by simpa only [Category.comp_id] using hg
  classical
  choose L hL using hlocal
  let T := fun i : X.obj.left => (A i).obj.left
  let u := fun i : X.obj.left => (j i).hom.left
  let : ∀ i,LocallyRingedSpace.IsOpenImmersion (u i) := fun i => inferInstance
  have hmodels (i : X.obj.left) : HasLocalModels (T i) (u i ≫ Y.obj.hom) := by
    rw [Over.w (j i).hom]
    exact of_source (A i)
  have hscalar (i : X.obj.left) :
      (L i).hom.left ≫ (NativeNov16NormalizationSpace.source X).obj.hom = u i ≫ Y.obj.hom :=
    (Over.w (L i).hom).trans (Over.w (j i).hom).symm
  have htri (i : X.obj.left) :
      (L i).hom.left ≫ (NativeNov16NormalizationSpace.projection X).hom.left = u i ≫ f.hom.left :=
    congrArg (fun t => t.hom.left) (hL i)
  have hd (i : X.obj.left) : Dense ((u i ≫ f.hom.left).base ⁻¹' intrinsicRegularLocus X.obj) :=
    hdReg.preimage (inferInstance : LocallyRingedSpace.IsOpenImmersion (u i)).base_open.isOpenMap
  obtain ⟨F,hF,hUnique⟩ := glue_actual_lifts Y.obj.hom T u hcover hmodels
    (NativeNov16NormalizationSpace.projection X) (intrinsicRegularLocus X.obj)
    (NativeNov16NormalizationExistence.isIsoOver_intrinsicRegularLocus X) f.hom.left
    (fun i => (L i).hom.left) hscalar htri hd
  let lift : Y ⟶ NativeNov16NormalizationSpace.source X := ObjectProperty.homMk (Over.homMk F hF.2)
  have hproj : lift ≫ NativeNov16NormalizationSpace.projection X=f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hF.1
  refine ⟨lift,hproj,?_⟩
  intro M hM
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hUnique M.hom.left ⟨congrArg (fun t => t.hom.left) hM,Over.w M.hom⟩
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalBimeromorphicLift
