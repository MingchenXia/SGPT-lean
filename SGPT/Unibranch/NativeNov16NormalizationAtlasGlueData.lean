import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-! Actual local normalizations, full triple rotations and cocycle from only X.
Blueprint: native-nov16-normalization-atlas-glue-data.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16NormalizationAtlasGlueData
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps

variable (X : SourceReducedComplexSpace)

abbrev localObject (i : X.obj.left) : LocallyRingedSpace := (atPoint X i).source.obj.left
abbrev overlapObject (i j : X.obj.left) : LocallyRingedSpace := (overlapSource X i j).obj.left
abbrev inclusion (i j : X.obj.left) : overlapObject X i j ⟶ localObject X i :=
  (overlapInclusion X i j).hom.left
abbrev projection (i : X.obj.left) : localObject X i ⟶ X.obj.left :=
  ((atPoint X i).projection ≫ (atPoint X i).into).hom.left
abbrev transition (i j : X.obj.left) : overlapObject X i j ⟶ overlapObject X j i :=
  (overlapMap X i j).hom.left

instance inclusion_open (i j : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (inclusion X i j) := overlapInclusion_open X i j

theorem overlap_square (i j : X.obj.left) :
    transition X i j ≫ inclusion X j i ≫ projection X j = inclusion X i j ≫ projection X i := by
  exact congrArg (fun f => f.hom.left) (overlapMap_projection X i j)

theorem inclusion_range (i j : X.obj.left) : range (inclusion X i j).base =
    (projection X i).base ⁻¹' range (atPoint X j).into.hom.left.base := by
  ext y
  constructor
  · rintro ⟨s,rfl⟩
    exact s.property
  · intro hy
    exact ⟨⟨y,hy⟩,rfl⟩

/-- Full uniqueness on any actual raw open source of a chosen local normalization. -/
theorem maps_eq_over_original (i : X.obj.left) {A : LocallyRingedSpace}
    (c : A ⟶ localObject X i) [hc : LocallyRingedSpace.IsOpenImmersion c]
    (L K : A ⟶ localObject X i)
    (hL : L ≫ projection X i = c ≫ projection X i)
    (hK : K ≫ projection X i = c ≫ projection X i) : L=K := by
  let σA := c ≫ (atPoint X i).source.obj.hom
  have hA : NativeNov16LocalModelMorphismExt.HasLocalModels A σA :=
    PrimeNov16AnalyticNormalizationOriginalLocalModelInheritance.hasLocalModels_of_openImmersion
      σA (atPoint X i).source.obj.hom
      (NativeNov16LocalModelMorphismExt.of_source (atPoint X i).source) c rfl
  have hScalar (M : A ⟶ localObject X i)
      (hM : M ≫ projection X i = c ≫ projection X i) :
      M ≫ (atPoint X i).source.obj.hom=σA := by
    have hs : projection X i ≫ X.obj.hom = (atPoint X i).source.obj.hom :=
      Over.w ((atPoint X i).projection ≫ (atPoint X i).into).hom
    dsimp only [σA]
    rw [← hs,← Category.assoc,hM,Category.assoc]
  have hBase (M : A ⟶ localObject X i)
      (hM : M ≫ projection X i = c ≫ projection X i) :
      M ≫ (atPoint X i).projection.hom.left = c ≫ (atPoint X i).projection.hom.left := by
    apply (cancel_mono (atPoint X i).into.hom.left).mp
    change M ≫ ((atPoint X i).projection.hom.left ≫ (atPoint X i).into.hom.left) =
      c ≫ ((atPoint X i).projection.hom.left ≫ (atPoint X i).into.hom.left) at hM
    simpa only [Category.assoc] using hM
  have hd : Dense ((c ≫ (atPoint X i).projection.hom.left).base ⁻¹' (atPoint X i).good) :=
    (atPoint X i).good_source_dense.preimage hc.base_open.isOpenMap
  exact NativeNov16LocalModelMorphismExt.hom_ext_of_dense_good σA hA
    (atPoint X i).projection (atPoint X i).good (atPoint X i).good_inverse
    (c ≫ (atPoint X i).projection.hom.left) hd L K
    (hScalar L hL) (hScalar K hK) (hBase L hL) (hBase K hK)

instance inclusion_self_iso (i : X.obj.left) : IsIso (inclusion X i i) := by
  have hs : Function.Surjective (inclusion X i i).base := by
    intro y
    have hy : y ∈ range (inclusion X i i).base := by
      rw [inclusion_range]
      exact ⟨(atPoint X i).projection.hom.left.base y,rfl⟩
    exact hy
  let : Epi (inclusion X i i).base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

theorem transition_self (i : X.obj.left) : transition X i i=𝟙 _ := by
  apply (cancel_mono (inclusion X i i)).mp
  apply maps_eq_over_original X i (inclusion X i i)
    (transition X i i ≫ inclusion X i i) ((𝟙 _) ≫ inclusion X i i)
  · simpa only [Category.assoc] using overlap_square X i i
  · simp only [Category.id_comp]

abbrev tripleObject (i j k : X.obj.left) : LocallyRingedSpace :=
  pullback (inclusion X i j) (inclusion X i k)

def tripleInclusion (i j k : X.obj.left) : tripleObject X i j k ⟶ localObject X i :=
  pullback.fst (inclusion X i j) (inclusion X i k) ≫ inclusion X i j

instance tripleInclusion_open (i j k : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (tripleInclusion X i j k) := by
  dsimp only [tripleInclusion]
  infer_instance

private theorem triple_rotation_range (i j k : X.obj.left) :
    range (pullback.fst (inclusion X i j) (inclusion X i k) ≫
      transition X i j ≫ inclusion X j i).base ⊆ range (inclusion X j k).base := by
  rw [inclusion_range]
  rintro _ ⟨z,rfl⟩
  have he : (pullback.fst (inclusion X i j) (inclusion X i k) ≫
      transition X i j ≫ inclusion X j i) ≫ projection X j =
      (pullback.snd (inclusion X i j) (inclusion X i k) ≫ inclusion X i k) ≫ projection X i := by
    calc
      _ = pullback.fst (inclusion X i j) (inclusion X i k) ≫
          (transition X i j ≫ inclusion X j i ≫ projection X j) := by simp only [Category.assoc]
      _ = pullback.fst (inclusion X i j) (inclusion X i k) ≫
          (inclusion X i j ≫ projection X i) :=
        congrArg (fun a => pullback.fst (inclusion X i j) (inclusion X i k) ≫ a) (overlap_square X i j)
      _ = _ := by rw [← Category.assoc,pullback.condition]
  have hk : (projection X i).base
      ((inclusion X i k).base ((pullback.snd (inclusion X i j) (inclusion X i k)).base z)) ∈
      range (atPoint X k).into.hom.left.base := by
    have hm : (inclusion X i k).base
        ((pullback.snd (inclusion X i j) (inclusion X i k)).base z) ∈
        range (inclusion X i k).base := ⟨_,rfl⟩
    rw [inclusion_range] at hm
    exact hm
  have hp : (projection X j).base
      ((pullback.fst (inclusion X i j) (inclusion X i k) ≫
        transition X i j ≫ inclusion X j i).base z) =
      (projection X i).base
        ((inclusion X i k).base ((pullback.snd (inclusion X i j) (inclusion X i k)).base z)) :=
    congrArg (fun f => f.base z) he
  change (projection X j).base
    ((pullback.fst (inclusion X i j) (inclusion X i k) ≫
      transition X i j ≫ inclusion X j i).base z) ∈ range (atPoint X k).into.hom.left.base
  rw [hp]
  exact hk

def tripleTransition (i j k : X.obj.left) : tripleObject X i j k ⟶ tripleObject X j k i := by
  let a := pullback.fst (inclusion X i j) (inclusion X i k) ≫ transition X i j
  let b := LocallyRingedSpace.IsOpenImmersion.lift (inclusion X j k)
    (a ≫ inclusion X j i) (triple_rotation_range X i j k)
  exact pullback.lift b a (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

theorem tripleTransition_fac (i j k : X.obj.left) :
    tripleTransition X i j k ≫ pullback.snd (inclusion X j k) (inclusion X j i) =
      pullback.fst (inclusion X i j) (inclusion X i k) ≫ transition X i j :=
  pullback.lift_snd _ _ _

theorem tripleTransition_over (i j k : X.obj.left) :
    tripleTransition X i j k ≫ tripleInclusion X j k i ≫ projection X j =
      tripleInclusion X i j k ≫ projection X i := by
  have hc : tripleInclusion X j k i =
      pullback.snd (inclusion X j k) (inclusion X j i) ≫ inclusion X j i := pullback.condition
  calc
    _ = (tripleTransition X i j k ≫ pullback.snd (inclusion X j k) (inclusion X j i)) ≫
        inclusion X j i ≫ projection X j := by rw [hc]; simp only [Category.assoc]
    _ = (pullback.fst (inclusion X i j) (inclusion X i k) ≫ transition X i j) ≫
        inclusion X j i ≫ projection X j :=
      congrArg (fun a => a ≫ inclusion X j i ≫ projection X j) (tripleTransition_fac X i j k)
    _ = _ := by simp only [Category.assoc,overlap_square,tripleInclusion]

theorem tripleTransition_cocycle (i j k : X.obj.left) :
    tripleTransition X i j k ≫ tripleTransition X j k i ≫ tripleTransition X k i j=𝟙 _ := by
  let a := tripleTransition X i j k ≫ tripleTransition X j k i ≫ tripleTransition X k i j
  apply (cancel_mono (tripleInclusion X i j k)).mp
  apply maps_eq_over_original X i (tripleInclusion X i j k)
    (a ≫ tripleInclusion X i j k) ((𝟙 _) ≫ tripleInclusion X i j k)
  · dsimp only [a]
    simp only [Category.assoc,tripleTransition_over]
  · simp only [Category.id_comp]

/-- The actual full gluing datum depends only on the original reduced space. -/
def glueData : LocallyRingedSpace.GlueData where
  J := X.obj.left
  U := localObject X
  V := fun ij => overlapObject X ij.1 ij.2
  f := inclusion X
  f_id _ := inferInstance
  t := transition X
  t_id := transition_self X
  t' := tripleTransition X
  t_fac := tripleTransition_fac X
  cocycle := tripleTransition_cocycle X
  f_open _ _ := inferInstance

end SGPT.Unibranch.NativeNov16NormalizationAtlasGlueData
