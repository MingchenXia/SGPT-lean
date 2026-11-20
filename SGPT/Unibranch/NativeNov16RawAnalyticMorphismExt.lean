import SGPT.Unibranch.NativeNov16NormalizationOverlapUniqueness

/-! Entire raw actual analytic source morphisms, including genuine native pullback overlaps.
Blueprint: native-nov16-raw-analytic-morphism-ext.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaIntrinsicMorphismGluingAnalytic
namespace SGPT.Unibranch.NativeNov16RawAnalyticMorphismExt
open SourceReducedComplexSpace

private theorem exists_local_morphism_eq {A : LocallyRingedSpace} {B : SourceReducedComplexSpace}
    (σA : A ⟶ complexPoint) (hA : hasAnalyticCharts (Over.mk σA))
    (F G : A ⟶ B.obj.left) (hScalarF : F ≫ B.obj.hom=σA) (hScalarG : G ≫ B.obj.hom=σA)
    (hbase : F.base = G.base) (x : A) :
    ∃ (P : LocallyRingedSpace) (j : P ⟶ A),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      j ≫ F = j ≫ G := by
  obtain ⟨d, U, C, hC, i, hi, hip, c, hcx⟩ := hA.2.2 x
  obtain ⟨e, V, D, _hD, k, hk, hkp, hFx⟩ := B.property.2.2 (F.base x)
  let S := (modelOver U C).left
  let i₀ : S ⟶ A := i
  let k₀ : (modelOver V D).left ⟶ B.obj.left := k
  let : LocallyRingedSpace.IsOpenImmersion i₀ := hi
  let : LocallyRingedSpace.IsOpenImmersion k₀ := hk
  have hip₀ : i₀ ≫ σA = subspacePointMap (n := d) C := hip
  have hkp₀ : k₀ ≫ B.obj.hom = subspacePointMap (n := e) D := hkp
  let Q : Opens S.toTopCat :=
    ⟨(i₀ ≫ F).base ⁻¹' range k₀.base,
      hk.base_open.isOpen_range.preimage (i₀ ≫ F).base.hom.continuous⟩
  let P := S.restrict Q.isOpenEmbedding
  let p : P ⟶ S := S.ofRestrict Q.isOpenEmbedding
  let hp : LocallyRingedSpace.IsOpenImmersion p := by
    dsimp only [p, P]
    infer_instance
  let j : P ⟶ A := p ≫ i₀
  have hcQ : c ∈ Q := by
    change F.base (i₀.base c) ∈ range k₀.base
    have hcx0 : i₀.base c=x := hcx
    rw [hcx0]
    exact hFx
  have hF : range (j ≫ F).base ⊆ range k₀.base := by
    rintro _ ⟨u, rfl⟩
    exact u.property
  have hG : range (j ≫ G).base ⊆ range k₀.base := by
    rintro _ ⟨u, rfl⟩
    change G.base (i₀.base u.val) ∈ range k₀.base
    rw [← hbase]
    exact u.property
  let L := LocallyRingedSpace.IsOpenImmersion.lift k₀ (j ≫ F) hF
  let R := LocallyRingedSpace.IsOpenImmersion.lift k₀ (j ≫ G) hG
  have hL : L ≫ k₀ = j ≫ F :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac k₀ _ hF
  have hR : R ≫ k₀ = j ≫ G :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac k₀ _ hG
  have hP : hasAnalyticCharts (Over.mk (j ≫ σA)) := by
    have hP₀ := @hasAnalyticCharts_of_openImmersion P S
      (p ≫ subspacePointMap (n := d) C) (subspacePointMap (n := d) C)
      (hasAnalyticCharts_model U C hC) p hp rfl
    change hasAnalyticCharts (Over.mk ((p ≫ i₀) ≫ σA))
    rw [Category.assoc, hip₀]
    exact hP₀
  have hLp : L ≫ subspacePointMap (n := e) D = j ≫ σA := by
    rw [← hkp₀, ← Category.assoc, hL, Category.assoc, hScalarF]
  have hRp : R ≫ subspacePointMap (n := e) D = j ≫ σA := by
    rw [← hkp₀, ← Category.assoc, hR, Category.assoc, hScalarG]
  have hLRbase : L.base = R.base := by
    ext u
    apply hk.base_open.injective
    calc
      k₀.base (L.base u) = (j ≫ F).base u :=
        congrArg (fun f => f.base u) hL
      _ = (j ≫ G).base u := by
        simp only [LocallyRingedSpace.comp_base, hbase]
      _ = k₀.base (R.base u) := (congrArg (fun f => f.base u) hR).symm
  have hLR : L = R :=
    HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq
      (j ≫ σA) hP L R hLp hRp hLRbase
  refine ⟨P, j, inferInstance, ?_, ?_⟩
  · exact ⟨⟨c, hcQ⟩, hcx⟩
  · exact hL.symm.trans ((congrArg (fun f => f ≫ k₀) hLR).trans hR)

theorem morphism_eq_of_base_eq {A : LocallyRingedSpace} {B : SourceReducedComplexSpace}
    (σA : A ⟶ complexPoint) (hA : hasAnalyticCharts (Over.mk σA))
    (F G : A ⟶ B.obj.left) (hF : F ≫ B.obj.hom=σA) (hG : G ≫ B.obj.hom=σA)
    (hbase : F.base=G.base) : F=G := by
  classical
  choose P j hj hx heq using fun x => exists_local_morphism_eq σA hA F G hF hG hbase x
  let : ∀ x,LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hc : ∀ x : A,∃ (a : A) (u : P a),(j a).base u=x := by
    intro x
    obtain ⟨u,hu⟩ := hx x
    exact ⟨x,u,hu⟩
  exact HironakaIntrinsicMorphismGluing.hom_ext P j hc F G heq

theorem hom_ext_of_dense_good {A : LocallyRingedSpace} {X B : SourceReducedComplexSpace}
    (σA : A ⟶ complexPoint) (hA : hasAnalyticCharts (Over.mk σA))
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

end SGPT.Unibranch.NativeNov16RawAnalyticMorphismExt
