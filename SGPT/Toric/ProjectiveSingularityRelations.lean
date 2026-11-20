import SGPT.PSH.SourceFullMassIGood
import SGPT.PSH.GlobalPComparison
import SGPT.PSH.VariableLelong
import SGPT.Okounkov.CoordinateResidual
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability

set_option autoImplicit false

/-! # The original projective P/I/singularity-type example

This proves all clauses of SGPT `ex:Pequivnotequivex` on the same quotient
projective line, with its original two-chart atlas and literal potentials.
The independently defined squared-log source Lelong reader is one at the
logarithmic pole; the native log-norm reader is two.
-/

noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology ENNReal NNReal Classical ContDiff

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

private theorem finiteChart_origin : projectiveModelChart false projectiveOrigin = 0 := by
  apply (projectiveModelChart false).right_inv
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

private theorem origin_mem_finiteChart :
    projectiveOrigin ∈ (projectiveModelChart false).source := by
  apply (projectiveModelChart false).map_target
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

private theorem coordinate_logSingularity_lelong :
    lelongNumber (n := 1)
      (chartFunction projectiveLogSingularity (projectiveNativeChart false)) 0 = 2 := by
  have hfun : (fun z : ComplexModel 1 =>
      chartFunction projectiveLogSingularity (projectiveNativeChart false) z +
        (projectiveFSPotential z : EReal)) = (fun z => logNormSq (z 0)) := by
    funext z
    exact projectiveLogSingularity_corrected_chart false z
  have hlog : lelongNumber (n := 1) (fun z : ComplexModel 1 => logNormSq (z 0)) 0 = 2 := by
    simpa using SGPT.Okounkov.lelongNumber_scaled_logNormSq_eq
      (0 : Fin 1) (x := (0 : ComplexModel 1)) (by simp) (c := (1 : ℝ≥0)) (by norm_num)
  have hcorrect := LelongChartReaderInvariance.lelongNumber_add_continuous_eq (n := 1)
    (u := chartFunction projectiveLogSingularity (projectiveNativeChart false))
    (x := (0 : ComplexModel 1)) contDiff_projectiveFSPotential.continuous.continuousAt
  rw [hfun, hlog] at hcorrect
  exact hcorrect.symm

/-- The native log-norm reader of the literal squared-log pole is two. -/
theorem lelongNumber_projectiveLogSingularity_origin :
    lelongNumber (n := 1) projectiveLogSingularity projectiveOrigin = 2 := by
  have h := LelongChartReaderInvariance.lelongNumber_chartFunction_eq
    (u := projectiveLogSingularity) (projectiveNativeChart false) origin_mem_finiteChart
  rw [projectiveNativeChart_val, finiteChart_origin] at h
  exact h.symm.trans coordinate_logSingularity_lelong

/-- The original independent squared-log source reader at the same pole is one. -/
theorem sourceLelong_projectiveLogSingularity_origin :
    projectiveLineAtlas.sourceLelong projectiveLogSingularity projectiveOrigin = 1 := by
  rw [projectiveLineAtlas.sourceLelong_eq_chart projectiveLogSingularity projectiveOrigin
    false origin_mem_finiteChart]
  change SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := 1)
    (chartFunction projectiveLogSingularity (projectiveNativeChart false))
    (projectiveModelChart false projectiveOrigin) = 1
  rw [finiteChart_origin]
  have h := SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (n := 1) (by norm_num)
    (chartFunction projectiveLogSingularity (projectiveNativeChart false)) (0 : ComplexModel 1)
  rw [coordinate_logSingularity_lelong] at h
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  simpa using h.symm


private theorem sourceZero_thetaPSH :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (0 : P1 → EReal) := by
  simpa only [sourceSingularityEnvelope_projectiveLogLog_eq_zero] using
    isThetaPSH_sourceSingularityEnvelope_logLog

private theorem sourceOrder_of_native {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsQPSH u) (hv : projectiveLineAtlas.IsQPSH v)
    (h : IEnvelope.IOrderOnManifold (n := 1) u v) :
    sourceIOrder projectiveLineAtlas u v := by
  refine ⟨hu, hv, ?_⟩
  intro c hc i
  exact h c hc (projectiveNativeChart i)

private theorem nativeOrder_of_source {u v : P1 → EReal}
    (h : sourceIOrder projectiveLineAtlas u v) :
    IEnvelope.IOrderOnManifold (n := 1) u v := by
  intro c hc e
  obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  have he : e = projectiveNativeChart i := Subtype.ext hi
  subst e
  exact h.2.2 c hc i

/-- The same literal log-log potential has the global source P type of zero. -/
theorem sourcePEquivalent_projectiveLogLog_zero :
    GlobalPComparison.sourcePEquivalent (n := 1) projectiveLogLogPotential 0 := by
  have hmass : DiagonalMass.HasPositivePotentialMass projectiveNativeFSBackground.form
      projectiveLogLogPotential isThetaPshPotential_projectiveLogLogPotential := by
    change 0 < projectiveLogLogNonPluripolarMeasure univ
    rw [projectiveLogLogNonPluripolarMeasure_univ]
    exact zero_lt_one
  have h := GlobalPComparison.sourcePEquivalent_singularityEnvelope
    projectiveNativeFSBackground projectiveNativeFSBackground.form
    isThetaPshPotential_projectiveLogLogPotential hmass
  simpa only [projectiveLogLog_nativeEnvelope_eq_zero] using h

/-- All genuine native chart multiplier ideals agree with those of zero. -/
theorem iEquivalentOnManifold_projectiveLogLog_zero :
    IEnvelope.IEquivalentOnManifold (n := 1) projectiveLogLogPotential 0 :=
  GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    sourcePEquivalent_projectiveLogLog_zero

/-- The original two-chart I-equivalence retains both genuine QPSH domains. -/
theorem sourceIEquivalent_projectiveLogLog_zero :
    sourceIEquivalent projectiveLineAtlas projectiveLogLogPotential 0 := by
  have hφ : projectiveLineAtlas.IsQPSH projectiveLogLogPotential :=
    ⟨projectiveFSForm, isThetaPSH_projectiveLogLogPotential⟩
  have h0 : projectiveLineAtlas.IsQPSH (0 : P1 → EReal) :=
    ⟨projectiveFSForm, sourceZero_thetaPSH⟩
  exact ⟨sourceOrder_of_native hφ h0 iEquivalentOnManifold_projectiveLogLog_zero.1,
    sourceOrder_of_native h0 hφ iEquivalentOnManifold_projectiveLogLog_zero.2⟩

/-- Its finite-constant singularity type nevertheless differs from zero. -/
theorem not_singularityEquiv_projectiveLogLog_zero :
    ¬ SingularityEquiv projectiveLogLogPotential (0 : P1 → EReal) := by
  simpa only [sourceSingularityEnvelope_projectiveLogLog_eq_zero] using
    not_singularityEquiv_projectiveLogLog_envelope


private theorem nativeZero_lelong (p : P1) :
    lelongNumber (n := 1) (0 : P1 → EReal) p = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_not_gt
  intro hp
  have hbot := eq_bot_of_lelongNumber_pos (by norm_num : 0 < 1)
    (PluripolarCapacityDichotomy.isThetaPshPotential_zero projectiveNativeFSBackground).1 hp
  exact EReal.zero_ne_bot hbot

/-- The literal logarithmic pole fails actual all-chart I-equivalence with zero. -/
theorem not_iEquivalentOnManifold_projectiveLogSingularity_zero :
    ¬ IEnvelope.IEquivalentOnManifold (n := 1) projectiveLogSingularity 0 := by
  intro h
  have hunit0 := SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt
    (PluripolarCapacityDichotomy.isThetaPshPotential_zero projectiveNativeFSBackground).1
    (c := 2) (by norm_num) (x := projectiveOrigin) (by
      change lelongNumber (n := 1) (0 : P1 → EReal) projectiveOrigin < _
      rw [nativeZero_lelong]
      norm_num)
  have hunit : (HolomorphicIdealSheaves.multiplierIdeal (n := 1) 2
      projectiveLogSingularity).mem projectiveOrigin (fun _ => (1 : ℂ)) := by
    exact PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
      h.2 (by norm_num : (0 : ℝ) < 2) projectiveOrigin (fun _ => (1 : ℂ)) hunit0
  have hbound := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal
    (by norm_num : 0 < 1) hunit
  rw [lelongNumber_projectiveLogSingularity_origin] at hbound
  rw [finrank_real_of_complex] at hbound
  norm_num [ComplexModel] at hbound

/-- Explicit exhaustion of the genuine native atlas rules out the original Bool I-type. -/
theorem not_sourceIEquivalent_projectiveLogSingularity_zero :
    ¬ sourceIEquivalent projectiveLineAtlas projectiveLogSingularity 0 := by
  intro h
  exact not_iEquivalentOnManifold_projectiveLogSingularity_zero
    ⟨nativeOrder_of_source h.1, nativeOrder_of_source h.2⟩

/-- The original global P-type of the literal logarithmic pole differs from zero. -/
theorem not_sourcePEquivalent_projectiveLogSingularity_zero :
    ¬ GlobalPComparison.sourcePEquivalent (n := 1) projectiveLogSingularity 0 := by
  intro h
  exact not_iEquivalentOnManifold_projectiveLogSingularity_zero
    (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent h)


/-- The entire literal logarithmic pole is below the log-log global source P-type. -/
theorem sourcePOrder_projectiveLogSingularity_logLog :
    GlobalPComparison.sourcePOrder (n := 1) projectiveLogSingularity
      projectiveLogLogPotential := by
  apply SingularGlobalPOrder.sourcePOrder_of_moreSingularOn projectiveNativeFSBackground
    projectiveNativeFSBackground.form projectiveNativeFSBackground.form
    (isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveLogSingularity)
    isThetaPshPotential_projectiveLogLogPotential
  exact ⟨-2, fun p _ => projectiveLogSingularity_le_logLog_add_neg_two p⟩

/-- The comparison consequently holds for actual multiplier germs in every native chart. -/
theorem iOrderOnManifold_projectiveLogSingularity_logLog :
    IEnvelope.IOrderOnManifold (n := 1) projectiveLogSingularity projectiveLogLogPotential :=
  GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
    sourcePOrder_projectiveLogSingularity_logLog

/-- The original two-chart I-order retains the two original genuine QPSH domains. -/
theorem sourceIOrder_projectiveLogSingularity_logLog :
    sourceIOrder projectiveLineAtlas projectiveLogSingularity projectiveLogLogPotential :=
  sourceOrder_of_native ⟨projectiveFSForm, isThetaPSH_projectiveLogSingularity⟩
    ⟨projectiveFSForm, isThetaPSH_projectiveLogLogPotential⟩
    iOrderOnManifold_projectiveLogSingularity_logLog

/-- Every clause of original `ex:Pequivnotequivex`, for the literal original
potentials and Bool atlas. Global P and actual source I are used throughout. -/
theorem original_projective_singularity_relation_example :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogLogPotential ∧
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogSingularity ∧
    sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential = 0 ∧
    GlobalPComparison.sourcePEquivalent (n := 1) projectiveLogLogPotential 0 ∧
    sourceIEquivalent projectiveLineAtlas projectiveLogLogPotential 0 ∧
    ¬ SingularityEquiv projectiveLogLogPotential (0 : P1 → EReal) ∧
    projectiveLineAtlas.sourceLelong projectiveLogSingularity projectiveOrigin = 1 ∧
    ¬ sourceIEquivalent projectiveLineAtlas projectiveLogSingularity 0 ∧
    ¬ GlobalPComparison.sourcePEquivalent (n := 1) projectiveLogSingularity 0 ∧
    GlobalPComparison.sourcePOrder (n := 1) projectiveLogSingularity
      projectiveLogLogPotential ∧
    sourceIOrder projectiveLineAtlas projectiveLogSingularity projectiveLogLogPotential :=
  ⟨isThetaPSH_projectiveLogLogPotential, isThetaPSH_projectiveLogSingularity,
    sourceSingularityEnvelope_projectiveLogLog_eq_zero,
    sourcePEquivalent_projectiveLogLog_zero, sourceIEquivalent_projectiveLogLog_zero,
    not_singularityEquiv_projectiveLogLog_zero, sourceLelong_projectiveLogSingularity_origin,
    not_sourceIEquivalent_projectiveLogSingularity_zero,
    not_sourcePEquivalent_projectiveLogSingularity_zero,
    sourcePOrder_projectiveLogSingularity_logLog, sourceIOrder_projectiveLogSingularity_logLog⟩

end SGPT.Toric
