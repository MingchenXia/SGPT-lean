import SGPT.PSH.SourceIGoodBackground
import SGPT.Toric.ProjectiveLineLogSingularity
import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- WHOLE original generic analytic example uses genuine global QPSH, with
positive admissible mass internally produced rather than assumed. -/
theorem sourceAnalytic_iGood (omega : KahlerBackground n M) (u : M → EReal)
    (hu : (ofFixedModel n M).IsQPSH u)
    (hA : FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) u) :
    sourceIGood (n := n) u := by
  apply (sourceIGood_iff_native _).mpr
  obtain ⟨θ,hθ⟩ := hu
  exact AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type omega
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential hA

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric
open Set Filter
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- Actual universal native chart germs of the literal original projective
logarithmic potential have honest positive-rational singleton presentations. -/
theorem projectiveLogSingularity_hasAnalyticType :
    HasManifoldAnalyticSingularityType (n := 1) projectiveLogSingularity := by
  intro e z hz
  obtain ⟨b,hb⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  let f : Fin 1 → ComplexModel 1 → ℂ := fun _ y => if b then 1 else y 0
  have hf : HolomorphicGeneratorsAt f z := by
    refine ⟨univ,isOpen_univ,mem_univ _,?_⟩
    intro j
    cases b <;> dsimp [f] <;> fun_prop
  have hsingle (y : ComplexModel 1) :
      generatorLog f y = if b then 0 else logNormSq (y 0) := by
    rw [generatorLog_eq_log_sum]
    cases b <;> simp [f,logNormSq]
  have hB : BoundedRealGermAt (fun y => -projectiveFSPotential y) z :=
    boundedRealGermAt_of_continuousAt
      contDiff_projectiveFSPotential.continuous.neg.continuousAt
  refine ⟨(1 : ℚ),1,f,by norm_num,hf,(fun y => -projectiveFSPotential y),hB,?_⟩
  apply Eventually.of_forall
  intro y
  simp only [Rat.cast_one,EReal.coe_one,one_mul]
  change projectiveLogSingularity (e.val.symm y) =
    generatorLog f y + ((-projectiveFSPotential y : ℝ) : EReal)
  rw [hb,hsingle]
  have h := congrArg (fun v : EReal => v + ((-projectiveFSPotential y : ℝ) : EReal))
    (projectiveLogSingularity_corrected_chart b y)
  simpa only [add_assoc,← EReal.coe_add,add_neg_cancel,EReal.coe_zero,add_zero] using h

/-- The additional printed projective-line particular of the whole original
analytic I-good example: GLOBAL goodness, with no original FS mass premise. -/
theorem projectiveLogSingularity_iGood : sourceIGood (n := 1) projectiveLogSingularity := by
  apply (sourceIGood_iff_native _).mpr
  exact AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type
    projectiveNativeFSBackground
    (isThetaPshPotential_projectiveNativeFS_of_source
      isThetaPSH_projectiveLogSingularity).quasiPshPotential
    projectiveLogSingularity_hasAnalyticType

end SGPT.Toric
