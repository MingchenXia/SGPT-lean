import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceResidue

/-! Full actual morphisms on original model opens internally preserve residue values.
Blueprint: native-nov16-original-pullback-values.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16OriginalPullbackValues
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspaceResidue
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

local instance stalkLocal (C : Set M) (x : C) :
    IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  actualSubspaceStalk_isLocalRing (n := n) C x

private theorem point_base (C : Set M) (x : C) :
    (subspacePointMap (n := n) C).base x=(0 : ComplexModel 0) := rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_stalk_const (C : Set M) (D : Set N)
    (W : Opens (actualSubspaceLocallyRingedSpace (n := n) C).toTopCat)
    (f : (actualSubspaceLocallyRingedSpace (n := n) C).restrict W.isOpenEmbedding ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hpoint : f ≫ subspacePointMap (n := m) D=
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict W.isOpenEmbedding ≫
        subspacePointMap (n := n) C) (x : W) (c : ℂ) :
    ((actualSubspaceLocallyRingedSpace (n := n) C).restrictStalkIso W.isOpenEmbedding x).hom
      (f.stalkMap x (actualSubspaceStalkConst (n := m) D (f.base x) c))=
        actualSubspaceStalkConst (n := n) C x.val c := by
  let A := actualSubspaceLocallyRingedSpace (n := n) C
  let e := A.ofRestrict W.isOpenEmbedding
  let E := A.restrictStalkIso W.isOpenEmbedding x
  have h := LocallyRingedSpace.stalkMap_congr_hom
    (f ≫ subspacePointMap (n := m) D) (e ≫ subspacePointMap (n := n) C) hpoint x
  have hs : (subspacePointMap (n := m) D).stalkMap (f.base x) ≫ f.stalkMap x=
      (subspacePointMap (n := n) C).stalkMap x.val ≫ e.stalkMap x := by
    calc
      _=(f ≫ subspacePointMap (n := m) D).stalkMap x :=
        (LocallyRingedSpace.stalkMap_comp f (subspacePointMap (n := m) D) x).symm
      _=(e ≫ subspacePointMap (n := n) C).stalkMap x := by
        simpa [LocallyRingedSpace.comp_base,TopCat.comp_app,point_base,e,A] using h
      _= _ := LocallyRingedSpace.stalkMap_comp e (subspacePointMap (n := n) C) x
  have hc := ConcreteCategory.congr_hom hs (actualComplexPointStalkEquiv.symm c)
  simp only [ConcreteCategory.comp_apply] at hc
  have hc' : f.stalkMap x (actualSubspaceStalkConst (n := m) D (f.base x) c)=
      e.stalkMap x (actualSubspaceStalkConst (n := n) C x.val c) :=
    (congrArg (f.stalkMap x) (actualSubspacePointMap_stalk_const D (f.base x) c).symm).trans
      (hc.trans (congrArg (e.stalkMap x) (actualSubspacePointMap_stalk_const C x.val c)))
  change E.hom (f.stalkMap x (actualSubspaceStalkConst (n := m) D (f.base x) c))=_
  rw [hc',← A.restrictStalkIso_inv_eq_ofRestrict]
  exact E.commRingCatIsoToRingEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
theorem restricted_stalk_value (C : Set M) (D : Set N)
    (W : Opens (actualSubspaceLocallyRingedSpace (n := n) C).toTopCat)
    (f : (actualSubspaceLocallyRingedSpace (n := n) C).restrict W.isOpenEmbedding ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hpoint : f ≫ subspacePointMap (n := m) D=
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict W.isOpenEmbedding ≫
        subspacePointMap (n := n) C) (x : W)
    (a : ((actualSubspaceSheaf (n := m) D).presheaf.stalk (f.base x)).carrier) :
    actualSubspaceStalkEval (n := n) C x.val
      (((actualSubspaceLocallyRingedSpace (n := n) C).restrictStalkIso W.isOpenEmbedding x).hom
        (f.stalkMap x a))=actualSubspaceStalkEval (n := m) D (f.base x) a := by
  let E := ((actualSubspaceLocallyRingedSpace (n := n) C).restrictStalkIso
    W.isOpenEmbedding x).commRingCatIsoToRingEquiv
  have : IsLocalHom E.toRingHom :=
    isLocalHom_of_leftInverse E.symm.toRingHom E.left_inv
  let ψ := E.toRingHom.comp (f.stalkMap x).hom
  have : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  let c := actualSubspaceStalkEval (n := m) D (f.base x) a
  have hz : a-actualSubspaceStalkConst (n := m) D (f.base x) c ∈
      IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := m) D).presheaf.stalk (f.base x)).carrier := by
    rw [← actualSubspaceStalkEval_ker,RingHom.mem_ker,map_sub,actualSubspaceStalkEval_const]
    exact sub_self c
  have hm := map_nonunit ψ _ hz
  change ψ _ ∈ IsLocalRing.maximalIdeal
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x.val).carrier at hm
  rw [← actualSubspaceStalkEval_ker,RingHom.mem_ker] at hm
  have hc := restricted_stalk_const C D W f hpoint x c
  change ψ (actualSubspaceStalkConst (n := m) D (f.base x) c)=
    actualSubspaceStalkConst (n := n) C x.val c at hc
  simp only [map_sub] at hm
  exact (sub_eq_zero.mp hm).trans
    ((congrArg (actualSubspaceStalkEval (n := n) C x.val) hc).trans
      (actualSubspaceStalkEval_const C x.val c))

set_option backward.isDefEq.respectTransparency.types false in
theorem pullTop_value (C : Set M) (D : Set N)
    (W : Opens (actualSubspaceLocallyRingedSpace (n := n) C).toTopCat)
    (f : (actualSubspaceLocallyRingedSpace (n := n) C).restrict W.isOpenEmbedding ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hpoint : f ≫ subspacePointMap (n := m) D=
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict W.isOpenEmbedding ≫
        subspacePointMap (n := n) C) (x : W)
    (s : ((actualSubspaceSheaf (n := m) D).presheaf.obj (op ⊤)).carrier) :
    actualSubspaceStalkEval (n := n) C x.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W x.val x.property
        (openTopEquiv (actualSubspaceLocallyRingedSpace (n := n) C) W (pullTopRingHom f s)))=
      actualSubspaceStalkEval (n := m) D (f.base x)
        ((actualSubspaceSheaf (n := m) D).presheaf.germ ⊤ (f.base x) (by trivial) s) := by
  let A := actualSubspaceLocallyRingedSpace (n := n) C
  let E := A.restrictStalkIso W.isOpenEmbedding x
  calc
    _=actualSubspaceStalkEval (n := n) C x.val
        (E.hom ((A.restrict W.isOpenEmbedding).presheaf.germ ⊤ x (by trivial)
          (pullTopRingHom f s))) :=
      congrArg (actualSubspaceStalkEval (n := n) C x.val)
        (openTopEquiv_germ A W (pullTopRingHom f s) x)
    _=actualSubspaceStalkEval (n := n) C x.val
        (E.hom (f.stalkMap x ((actualSubspaceSheaf (n := m) D).presheaf.germ
          ⊤ (f.base x) (by trivial) s))) :=
      congrArg (fun t => actualSubspaceStalkEval (n := n) C x.val (E.hom t))
        (pullTop_germ f s x)
    _= _ := restricted_stalk_value C D W f hpoint x _

end SGPT.Unibranch.NativeNov16OriginalPullbackValues
