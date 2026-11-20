import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDensity
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceLocalFunctions

/-! Actual whole quotient-sheaf sections and denominator cancellation.
Blueprint: prime-nov16-analytic-normalization-graph-sheaf-cancellation.tex. -/
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
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphSheafCancellation
open PrimeNov16AnalyticNormalizationDenominatorGraph

theorem actual_section_values_continuous {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier) :
    Continuous (fun z : W => actualSubspaceStalkEval (n := n) C z.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W z.val z.property s)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨O,hzO,t,_hOW,ht⟩ := actualSubspaceSection_local_ambient C W s z.val z.property
  have hc : Continuous (fun y : W => y.val.val) := continuous_subtype_val.comp continuous_subtype_val
  have hf : ContinuousAt (fun y : W => sectionExtension O t y.val.val) z :=
    (sectionExtension_holomorphicAt O t z.val.val hzO).continuousAt.comp
      (f := fun y : W => y.val.val) (x := z) hc.continuousAt
  apply hf.congr
  filter_upwards [hc.continuousAt.preimage_mem_nhds (O.isOpen.mem_nhds hzO)] with y hy
  rw [sectionExtension_apply O t y.val.val hy]
  exact (actualSubspaceStalkEval_inclusion_germ C O t y.val hy).symm.trans
    (congrArg (actualSubspaceStalkEval (n := n) C y.val) (ht y.val hy).symm)

/-- The ENTIRE original quotient-sheaf section vanishes, not only its values
on the good locus and not merely a supplied polynomial representative. -/
theorem actual_section_zero_of_denominator_mul_zero {n k : ℕ}
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (W : Opens (TopCat.of (graphClosure U C H G)))
    (s : ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.obj (op W)).carrier)
    (hs : ∀ z : W,H (baseProjection n k z.val.val.val) *
      actualSubspaceStalkEval (n := n+k) (graphClosure U C H G) z.val
        ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.germ
          W z.val z.property s) = 0) : s = 0 := by
  apply actualSubspaceSection_eq_zero_of_eval
  intro z hz
  exact PrimeNov16AnalyticNormalizationGraphDensity.continuous_zero_of_denominator_mul_zero
    U C H G W _ (actual_section_values_continuous (n := n+k) _ W s) hs ⟨z,hz⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphSheafCancellation
