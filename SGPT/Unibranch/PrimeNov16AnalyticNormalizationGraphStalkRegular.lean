import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphSheafCancellation

/-! The actual holomorphic denominator section is regular in EVERY full stalk.
Blueprint: prime-nov16-analytic-normalization-graph-stalk-regular.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceResidue
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceLocalFunctions
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkRegular
open PrimeNov16AnalyticNormalizationDenominatorGraph

def ambientDenominatorSection {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (hH : DifferentiableOn ℂ H U) :
    actualComplexSection (n := n+k) (⊤ : Opens (wideDomain k U)) := by
  have hs : ContDiffOn ℂ ∞ (fun z => H (baseProjection n k z)) (wideDomain k U) :=
    (contDiffOn_of_differentiableOn_complex hH U.isOpen).comp
      (baseProjection n k).contDiff.contDiffOn (fun _ hz => hz)
  have hm : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ℂ) ∞
      (fun z : wideDomain k U => H (baseProjection n k z.val)) :=
    hs.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  exact ⟨fun z => H (baseProjection n k z.val.val),hm.comp contMDiff_subtype_val⟩

def denominatorSection {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) :
    ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.obj (op ⊤)).carrier :=
  (actualSubspaceInclusion (n := n+k) (graphClosure U C H G)).toHom.c.app (op ⊤)
    (ambientDenominatorSection U H hH)

theorem denominatorSection_value {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (p : graphClosure U C H G) :
    actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) p
      ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.germ
        ⊤ p (by trivial) (denominatorSection U C H G hH)) =
      H (baseProjection n k p.val.val) := by
  have he := AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply
    (actualSubspaceInclusion (n := n+k) (graphClosure U C H G))
    ⊤ p (by trivial) (ambientDenominatorSection U H hH)
  calc
    _ = actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) p
      ((actualSubspaceInclusion (n := n+k) (graphClosure U C H G)).stalkMap p
        ((actualComplexStructureSheaf (n := n+k) (wideDomain k U)).presheaf.germ
          ⊤ p.val (by trivial) (ambientDenominatorSection U H hH))) :=
        congrArg (actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) p) he.symm
    _ = _ := actualSubspaceStalkEval_inclusion_germ _ ⊤ (ambientDenominatorSection U H hH) p (by trivial)

def denominatorStalk {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (p : graphClosure U C H G) :
    ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier :=
  (actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.germ
    ⊤ p (by trivial) (denominatorSection U C H G hH)

theorem denominatorStalk_mul_eq_zero {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (p : graphClosure U C H G)
    (r : ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier)
    (hr : denominatorStalk U C H G hH p * r = 0) : r = 0 := by
  let F := (actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf
  obtain ⟨W,hpW,s,hs⟩ := F.exists_germ_eq r
  let iTop : W ⟶ (⊤ : Opens (TopCat.of (graphClosure U C H G))) := homOfLE le_top
  let dW := F.map iTop.op (denominatorSection U C H G hH)
  have hg : F.germ W p hpW (dW*s) = F.germ W p hpW 0 := by
    rw [map_mul,map_zero]
    change F.germ W p hpW (F.map iTop.op (denominatorSection U C H G hH)) * _ = 0
    rw [F.germ_res_apply,hs]
    exact hr
  obtain ⟨Q,hpQ,iW,iW',heq⟩ := F.germ_eq p hpW hpW (dW*s) 0 hg
  let sQ := F.map iW.op s
  have hsQ : sQ = 0 := by
    apply PrimeNov16AnalyticNormalizationGraphSheafCancellation.actual_section_zero_of_denominator_mul_zero
      U C H G Q sQ
    intro z
    have he := congrArg (fun t => actualSubspaceStalkEval (n := n+k) (graphClosure U C H G)
      z.val (F.germ Q z.val z.property t)) heq
    rw [map_zero,map_zero,map_zero] at he
    rw [F.germ_res_apply,map_mul,map_mul] at he
    have hd : actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) z.val
        (F.germ W z.val ((leOfHom iW) z.property) dW) =
        H (baseProjection n k z.val.val.val) := by
      rw [F.germ_res_apply]
      exact denominatorSection_value U C H G hH z.val
    rw [hd] at he
    change H _ * actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) z.val
      (F.germ Q z.val z.property (F.map iW.op s)) = 0
    rw [F.germ_res_apply]
    exact he
  calc
    r = F.germ W p hpW s := hs.symm
    _ = F.germ Q p hpQ sQ := (F.germ_res_apply iW p hpQ s).symm
    _ = 0 := by rw [hsQ,map_zero]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkRegular
