import SGPT.Unibranch.HironakaG11LiftUniqueness
import SGPT.Unibranch.SourceMorphismExt

/-! Genuine full overlap uniqueness, inverse and cocycle from actual dense-good triangles.
Blueprint: native-nov16-normalization-overlap-uniqueness.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.NativeNov16NormalizationOverlapUniqueness
open SourceReducedComplexSpace

theorem hom_ext_of_dense_good {X A B : SourceReducedComplexSpace}
    (p : B ⟶ X) (G : Set X.obj.left) (hp : IsIsoOver p G)
    (f : A ⟶ X) (hd : Dense (f.hom.left.base ⁻¹' G))
    (L K : A ⟶ B) (hL : L ≫ p=f) (hK : K ≫ p=f) : L=K := by
  apply morphism_eq_of_base_eq L K
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  suffices he : (fun x => L.hom.left.base x)=(fun x => K.hom.left.base x) by
    exact congrFun he
  apply HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense hp
    L.hom.left.base.hom.continuous K.hom.left.base.hom.continuous
  · intro x
    change (L ≫ p).hom.left.base x=(K ≫ p).hom.left.base x
    exact congrArg (fun t : A ⟶ X => t.hom.left.base x) (hL.trans hK.symm)
  · exact hd
  · intro x hx
    change (L ≫ p).hom.left.base x ∈ G
    rw [hL]
    exact hx

def isoOfMutualLifts {X A B : SourceReducedComplexSpace}
    (p : A ⟶ X) (q : B ⟶ X) (G : Set X.obj.left)
    (hp : IsIsoOver p G) (hq : IsIsoOver q G)
    (hdp : Dense (p.hom.left.base ⁻¹' G)) (hdq : Dense (q.hom.left.base ⁻¹' G))
    (L : A ⟶ B) (K : B ⟶ A) (hL : L ≫ q=p) (hK : K ≫ p=q) : A ≅ B := by
  refine ⟨L,K,?_,?_⟩
  · apply hom_ext_of_dense_good p G hp p hdp (L ≫ K) (𝟙 A)
    · rw [Category.assoc,hK,hL]
    · exact Category.id_comp p
  · apply hom_ext_of_dense_good q G hq q hdq (K ≫ L) (𝟙 B)
    · rw [Category.assoc,hL,hK]
    · exact Category.id_comp q

theorem isoOfMutualLifts_hom {X A B : SourceReducedComplexSpace}
    (p : A ⟶ X) (q : B ⟶ X) (G : Set X.obj.left)
    (hp : IsIsoOver p G) (hq : IsIsoOver q G)
    (hdp : Dense (p.hom.left.base ⁻¹' G)) (hdq : Dense (q.hom.left.base ⁻¹' G))
    (L : A ⟶ B) (K : B ⟶ A) (hL : L ≫ q=p) (hK : K ≫ p=q) :
    (isoOfMutualLifts p q G hp hq hdp hdq L K hL hK).hom=L := rfl

theorem cocycle_of_triangles {X A B C : SourceReducedComplexSpace}
    (p : C ⟶ X) (G : Set X.obj.left) (hp : IsIsoOver p G)
    (q : B ⟶ X) (f : A ⟶ X) (hd : Dense (f.hom.left.base ⁻¹' G))
    (L : A ⟶ B) (M : B ⟶ C) (N : A ⟶ C)
    (hL : L ≫ q=f) (hM : M ≫ p=q) (hN : N ≫ p=f) : L ≫ M=N := by
  apply hom_ext_of_dense_good p G hp f hd (L ≫ M) N _ hN
  rw [Category.assoc,hM,hL]

end SGPT.Unibranch.NativeNov16NormalizationOverlapUniqueness
