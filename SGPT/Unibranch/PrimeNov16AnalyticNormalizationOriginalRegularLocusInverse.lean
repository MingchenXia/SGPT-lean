import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntrinsicRegularNormal
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodDensity
import SGPT.Unibranch.ComplexOpenNativeModels

/-! Actual local normalizers are isomorphisms over the ORIGINAL intrinsic regular locus.
Blueprint: prime-nov16-analytic-normalization-original-regular-locus-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
open SGPT.Foundations.Analysis.Pending
open HironakaIntrinsicComplexAnalyticRegularLocus
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRegularLocusInverse
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalIntrinsicRegularNormal

private theorem cancel_full_openImmersion {A B C : SourceReducedComplexSpace}
    (j : B ⟶ C) [LocallyRingedSpace.IsOpenImmersion j.hom.left]
    {f g : A ⟶ B} (h : f ≫ j = g ≫ j) : f=g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono j.hom.left).mp (congrArg (fun t => t.hom.left) h)

theorem atPoint_regular_isIsoOver (X : SourceReducedComplexSpace) (i : X.obj.left) :
    IsIsoOver (atPoint X i).projection
      ((atPoint X i).into.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  let A := atPoint X i
  let U : Opens A.base.obj.left :=
    ⟨A.into.hom.left.base ⁻¹' intrinsicRegularLocus X.obj,
      (isOpen_intrinsicRegularLocus X.obj).preimage A.into.hom.left.base.hom.continuous⟩
  let : MetrizableSpace A.base.obj.left := A.base_metrizable
  let : MetricSpace A.base.obj.left := TopologicalSpace.metrizableSpaceMetric A.base.obj.left
  let : ParacompactSpace U := inferInstance
  let : LocallyRingedSpace.IsOpenImmersion A.into.hom.left := A.into_open
  let T : SourceReducedComplexSpace := @restrictedBase A.base U inferInstance
  let S := restrictedSource A.projection A.proper U
  let j : T ⟶ A.base := baseInclusion U
  let k : S ⟶ A.source := sourceInclusion A.projection A.proper U
  let q : S ⟶ T := restrictedMap A.projection A.proper U
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := by dsimp only [j];infer_instance
  let : LocallyRingedSpace.IsOpenImmersion k.hom.left := by dsimp only [k];infer_instance
  have hqj : q ≫ j = k ≫ A.projection := restrictedMap_square A.projection A.proper U
  have hT : ∀ t : T.obj.left,IsDomain (T.obj.left.presheaf.stalk t).carrier ∧
      IsIntegrallyClosed (T.obj.left.presheaf.stalk t).carrier := by
    intro t
    let F : T ⟶ X := j ≫ A.into
    let : LocallyRingedSpace.IsOpenImmersion F.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (j.hom.left ≫ A.into.hom.left)
      infer_instance
    have ht : F.hom.left.base t ∈ intrinsicRegularLocus X.obj := t.property
    obtain ⟨hd,hn⟩ := normal_stalk_of_intrinsicRegular X (F.hom.left.base t) ht
    let : IsDomain (X.obj.left.presheaf.stalk (F.hom.left.base t)).carrier := hd
    let : IsIntegrallyClosed (X.obj.left.presheaf.stalk (F.hom.left.base t)).carrier := hn
    let E := (asIso (F.hom.left.stalkMap t)).commRingCatIsoToRingEquiv
    exact ⟨Function.Injective.isDomain E.symm E.symm.injective,IsIntegrallyClosed.of_equiv E⟩
  have hjGood := isIsoOver_range_of_isOpenImmersion j
    (show LocallyRingedSpace.IsOpenImmersion j.hom.left from inferInstance)
  have hjDense : Dense (j.hom.left.base ⁻¹' range j.hom.left.base) := by
    have he : j.hom.left.base ⁻¹' range j.hom.left.base = Set.univ :=
      Set.eq_univ_of_forall (fun t => ⟨t,rfl⟩)
    rw [he]
    exact dense_univ
  obtain ⟨a,ha,_hUnique⟩ := A.good_map_lift T hT j (range j.hom.left.base) hjGood hjDense
  have haRange : range a.hom.left.base ⊆ range k.hom.left.base := by
    rintro _ ⟨t,rfl⟩
    have ht := congrArg (fun f : T ⟶ A.base => f.hom.left.base t) ha
    refine ⟨⟨a.hom.left.base t,?_⟩,rfl⟩
    change A.projection.hom.left.base (a.hom.left.base t) ∈ U
    change A.projection.hom.left.base (a.hom.left.base t)=t.val at ht
    rw [ht]
    exact t.property
  let b := LocallyRingedSpace.IsOpenImmersion.lift k.hom.left a.hom.left haRange
  have hbk : b ≫ k.hom.left = a.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ haRange
  have hbσ : b ≫ S.obj.hom = T.obj.hom := by
    rw [← Over.w k.hom,← Category.assoc,hbk]
    exact Over.w a.hom
  let β : T ⟶ S := ObjectProperty.homMk (Over.homMk b hbσ)
  have hβk : β ≫ k=a := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hbk
  have hβq : β ≫ q = 𝟙 T := by
    apply cancel_full_openImmersion j
    rw [Category.assoc,hqj,← Category.assoc,hβk,ha,Category.id_comp]
  have hDense : Dense ((k ≫ A.projection).hom.left.base ⁻¹' A.good) :=
    A.good_source_dense.preimage
      (show LocallyRingedSpace.IsOpenImmersion k.hom.left from inferInstance).base_open.isOpenMap
  have hqβ : q ≫ β = 𝟙 S := by
    apply cancel_full_openImmersion k
    apply NativeNov16NormalizationOverlapUniqueness.hom_ext_of_dense_good
      A.projection A.good A.good_inverse (k ≫ A.projection) hDense
    · calc
        ((q ≫ β) ≫ k) ≫ A.projection = q ≫ ((β ≫ k) ≫ A.projection) := by
          simp only [Category.assoc]
        _ = q ≫ (a ≫ A.projection) := congrArg (fun f => q ≫ (f ≫ A.projection)) hβk
        _ = q ≫ j := congrArg (fun f => q ≫ f) ha
        _ = k ≫ A.projection := hqj
    · simp only [Category.id_comp]
  let E : S.obj.left ≅ T.obj.left :=
    { hom := q.hom.left
      inv := β.hom.left
      hom_inv_id := congrArg (fun f : S ⟶ S => f.hom.left) hqβ
      inv_hom_id := congrArg (fun f : T ⟶ T => f.hom.left) hβq }
  let : IsIso q.hom.left := E.isIso_hom
  have hcomp : LocallyRingedSpace.IsOpenImmersion (k ≫ A.projection).hom.left := by
    rw [← hqj]
    change LocallyRingedSpace.IsOpenImmersion (q.hom.left ≫ j.hom.left)
    infer_instance
  refine ⟨S.obj.left,k.hom.left,inferInstance,?_,hcomp,?_⟩
  · exact (Subtype.range_coe : range (Subtype.val : sourceOpen A.projection U → A.source.obj.left) = _)
  · apply subset_antisymm
    · rintro _ ⟨s,rfl⟩
      exact s.property
    · intro y hy
      refine ⟨β.hom.left.base ⟨y,hy⟩,?_⟩
      have hβp : β ≫ k ≫ A.projection=j := by
        rw [← Category.assoc,hβk,ha]
      exact congrArg (fun f : T ⟶ A.base => f.hom.left.base ⟨y,hy⟩) hβp

theorem atPoint_regular_dense (X : SourceReducedComplexSpace) (i : X.obj.left) :
    Dense ((atPoint X i).projection.hom.left.base ⁻¹'
      ((atPoint X i).into.hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) :=
  PrimeNov16AnalyticNormalizationOriginalGoodDensity.dense_preimage_of_actual_good_inverse
    (atPoint X i).projection (atPoint X i).good (atPoint X i).good_inverse
    (atPoint X i).good_source_dense _
    ((OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus X).preimage
      (atPoint X i).into_open.base_open.isOpenMap)
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRegularLocusInverse
