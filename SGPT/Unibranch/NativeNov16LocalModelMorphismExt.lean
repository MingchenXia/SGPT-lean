import SGPT.Unibranch.NativeNov16RawAnalyticMorphismExt

/-! Genuine original local models suffice; no global countability on raw triple overlaps.
Blueprint: native-nov16-local-model-morphism-ext.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16LocalModelMorphismExt
open SourceReducedComplexSpace

def HasLocalModels (A : LocallyRingedSpace) (σA : A ⟶ complexPoint) : Prop :=
  ∀ x : A,∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
    IsComplexAnalyticSubset (n := n) C ∧
    ∃ j : (modelOver U C).left ⟶ A,LocallyRingedSpace.IsOpenImmersion j ∧
      j ≫ σA=(modelOver U C).hom ∧ x ∈ range j.base

theorem of_source (A : SourceReducedComplexSpace) : HasLocalModels A.obj.left A.obj.hom :=
  A.property.2.2

theorem of_countable_charts (A : LocallyRingedSpace) (σA : A ⟶ complexPoint)
    (hA : hasAnalyticCharts (Over.mk σA)) : HasLocalModels A σA := hA.2.2

theorem morphism_eq_of_base_eq {A : LocallyRingedSpace} {B : SourceReducedComplexSpace}
    (σA : A ⟶ complexPoint) (hA : HasLocalModels A σA)
    (F G : A ⟶ B.obj.left) (hF : F ≫ B.obj.hom=σA) (hG : G ≫ B.obj.hom=σA)
    (hbase : F.base=G.base) : F=G := by
  classical
  choose n U C hC j hj hs hx using hA
  let T := fun x : A => (modelOver (U x) (C x)).left
  let : ∀ x,LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hc : ∀ x : A,∃ (a : A) (u : T a),(j a).base u=x := by
    intro x
    obtain ⟨u,hu⟩ := hx x
    exact ⟨x,u,hu⟩
  apply HironakaIntrinsicMorphismGluing.hom_ext T j hc F G
  intro x
  apply NativeNov16RawAnalyticMorphismExt.morphism_eq_of_base_eq
    (modelOver (U x) (C x)).hom (hasAnalyticCharts_model (U x) (C x) (hC x))
    (j x ≫ F) (j x ≫ G)
  · rw [Category.assoc,hF]
    exact hs x
  · rw [Category.assoc,hG]
    exact hs x
  · simp only [LocallyRingedSpace.comp_base,hbase]

theorem hom_ext_of_dense_good {A : LocallyRingedSpace} {X B : SourceReducedComplexSpace}
    (σA : A ⟶ complexPoint) (hA : HasLocalModels A σA)
    (p : B ⟶ X) (G : Set X.obj.left) (hp : IsIsoOver p G)
    (f : A ⟶ X.obj.left) (hd : Dense (f.base ⁻¹' G))
    (L K : A ⟶ B.obj.left) (hLpoint : L ≫ B.obj.hom=σA) (hKpoint : K ≫ B.obj.hom=σA)
    (hL : L ≫ p.hom.left=f) (hK : K ≫ p.hom.left=f) : L=K := by
  apply morphism_eq_of_base_eq σA hA L K hLpoint hKpoint
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  suffices he : (fun x => L.base x)=(fun x => K.base x) by exact congrFun he
  apply HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense hp
    L.base.hom.continuous K.base.hom.continuous
  · intro x
    change (L ≫ p.hom.left).base x=(K ≫ p.hom.left).base x
    exact congrArg (fun t : A ⟶ X.obj.left => t.base x) (hL.trans hK.symm)
  · exact hd
  · intro x hx
    change (L ≫ p.hom.left).base x ∈ G
    rw [hL]
    exact hx

end SGPT.Unibranch.NativeNov16LocalModelMorphismExt
