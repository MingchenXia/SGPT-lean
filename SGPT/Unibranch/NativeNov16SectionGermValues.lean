import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceLocalFunctions

/-! Actual section values determine the SAME original locally holomorphic function germ.
Blueprint: native-nov16-section-germ-values.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.NativeNov16SectionGermValues
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
open HironakaActualAnalyticSubspaceLocalFunctions HironakaHolomorphicJetRankLoci
open HironakaSmoothCentreRealDomainActualSheafStalk
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationGraphStalkChart

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem holomorphic_sub (x : M) (F G : M → ℂ)
    (hF : HolomorphicAt n F x) (hG : HolomorphicAt n G x) :
    HolomorphicAt n (fun y => F y-G y) x := by
  filter_upwards [hF,hG] with y hyF hyG
  exact hyF.sub hyG

private theorem originalFunctionImage_sub (C : Set M) (p : C) (F G : M → ℂ)
    (hF : HolomorphicAt n F p.val) (hG : HolomorphicAt n G p.val) :
    originalFunctionImage C p (fun y => F y-G y) (holomorphic_sub p.val F G hF hG)=
      originalFunctionImage C p F hF-originalFunctionImage C p G hG := by
  unfold originalFunctionImage
  rw [← map_sub]
  apply congrArg (intrinsicGermMap C p)
  simp only [chartTranslatedGerm,translatedGerm]
  exact HolGerm.mk_sub _ _ _ _

theorem germ_eq_original_function_of_values
    (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    (F : M → ℂ)
    (hs : ∀ (y : C) (hy : y ∈ W),actualSubspaceStalkEval (n := n) C y
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W y hy s)=F y.val)
    (x : C) (hx : x ∈ W) (hF : HolomorphicAt n F x.val) :
    (actualSubspaceSheaf (n := n) C).presheaf.germ W x hx s=
      originalFunctionImage C x F hF := by
  obtain ⟨O,hxO,t,hOW,ht⟩ := actualSubspaceSection_local_ambient C W s x hx
  let G := sectionExtension O t
  have hG : HolomorphicAt n G x.val := sectionExtension_holomorphicAt O t x.val hxO
  have hValues (y : M) (hy : y ∈ O) (hyC : y ∈ C) : G y=F y := by
    let q : C := ⟨y,hyC⟩
    change sectionExtension O t y=F y
    rw [sectionExtension_apply O t y hy]
    exact (actualSubspaceStalkEval_inclusion_germ C O t q hy).symm.trans
      ((congrArg (actualSubspaceStalkEval (n := n) C q) (ht q hy)).symm.trans (hs q (hOW q hy)))
  have hVan : (vanishingIdeal (n := n) C).mem x.val (fun y => G y-F y) := by
    refine ⟨holomorphic_sub x.val G F hG hF,?_⟩
    filter_upwards [O.isOpen.mem_nhds hxO] with y hy hyC
    exact sub_eq_zero.mpr (hValues y hy hyC)
  have hZero := (original_function_image_zero_iff C hC x (fun y => G y-F y)
    (holomorphic_sub x.val G F hG hF)).mpr hVan
  rw [originalFunctionImage_sub C x G F hG hF] at hZero
  have hr := actualOriginalFunctionGerm_eq_section O x.val hxO t G hG
    (Eventually.of_forall fun _ => rfl)
  have hi : originalFunctionImage C x G hG=
      (actualSubspaceInclusion (n := n) C).stalkMap x (actualOriginalFunctionGerm x.val G hG) :=
    intrinsicGermMap_original_function C x G hG
  exact ((ht x hxO).trans ((congrArg ((actualSubspaceInclusion (n := n) C).stalkMap x) hr.symm).trans
    hi.symm)).trans (sub_eq_zero.mp hZero)

end SGPT.Unibranch.NativeNov16SectionGermValues
