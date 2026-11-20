import SGPT.BBJ.CantorEnvelopeConsequences
import SGPT.BBJ.CantorPoleSequence
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

/-! The same concrete Cantor objects discharge the two complete original examples. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ

open Set MeasureTheory SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal Classical

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "ω" => projectiveNativeFSBackground.form
local notation "Θ" => projectiveNativeFSBackground.form + projectiveNativeFSBackground.form

/-- The independent source squared-log point reader is zero as well. -/
theorem squaredLogLelongNumber_cantorLogPotential (p : P1) :
    SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := 1)
      cantorLogPotential p = 0 := by
  have h := SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (n := 1) (by norm_num) cantorLogPotential p
  rw [lelongNumber_cantorLogPotential] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- Whole original `ex:BBJ`, for the same concrete polar set, measure and potential. -/
theorem original_cantor_BBJ_example :
    projectiveCantorSet.Nonempty ∧
    IsCompact projectiveCantorSet ∧
    Perfect projectiveCantorSet ∧
    IsTotallyDisconnected projectiveCantorSet ∧
    ManifoldLocallyPluripolar (n := 1) projectiveCantorSet ∧
    IsProbabilityMeasure projectiveCantorProbability ∧
    (∀ p : P1, projectiveCantorProbability {p} = 0) ∧
    projectiveCantorProbability.support = projectiveCantorSet ∧
    projectiveLineAtlas.IsThetaPSH projectiveFSForm cantorLogPotential ∧
    IsThetaPshPotential (ω).val cantorLogPotential ∧
    (∀ p : P1, cantorLogPotential p = ⊥ ↔ p ∈ projectiveCantorSet) ∧
    PositiveProductCurrents.IsPositive cantorNativeProductCurrent ∧
    cantorNativeTrace = projectiveCantorProbability ∧
    (∀ (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h),
      cantorNativeProductCurrent (CurrentTraceMeasure.smulTest h hh
        (PositiveProductCurrents.kahlerTest projectiveNativeFSBackground 0)) =
          ∫ p, h p ∂projectiveCantorProbability) ∧
    (∀ p : P1, NonKahlerLocus.lelongNumber (n := 1) cantorLogPotential p = 0) ∧
    (∀ p : P1, SquaredLogLelongSourceNormalization.squaredLogLelongNumber
      (n := 1) cantorLogPotential p = 0) ∧
    DiagonalMass.diagonalPotentialMeasure ω cantorLogPotential
      isThetaPshPotential_cantorLogPotential = 0 ∧
    DiagonalMass.diagonalPotentialMass ω cantorLogPotential
      isThetaPshPotential_cantorLogPotential = 0 ∧
    IEnvelope.IEquivalentOnManifold (n := 1) cantorLogPotential (fun _ : P1 => 0) ∧
    SGPT.PSH.VariableComplexAtlas.sourceIEquivalent projectiveLineAtlas
      cantorLogPotential (fun _ : P1 => 0) ∧
    ¬ SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := 1)
      cantorLogPotential (fun _ : P1 => 0) := by
  refine ⟨projectiveCantorSet_nonempty, isCompact_projectiveCantorSet,
    perfect_projectiveCantorSet, isTotallyDisconnected_projectiveCantorSet,
    manifoldLocallyPluripolar_projectiveCantorSet, by infer_instance,
    projectiveCantorProbability_singleton, projectiveCantorProbability_support,
    isThetaPSH_cantorLogPotential, isThetaPshPotential_cantorLogPotential,
    cantorLogPotential_eq_bot_iff, cantorNativeProductCurrent_positive,
    cantorNativeTrace_eq_projectiveCantorProbability, ?_,
    lelongNumber_cantorLogPotential, squaredLogLelongNumber_cantorLogPotential,
    diagonalPotentialMeasure_cantorLogPotential_eq_zero,
    diagonalPotentialMass_cantorLogPotential_eq_zero,
    iEquivalentOnManifold_cantorLogPotential_zero,
    sourceIEquivalent_cantorLogPotential_zero,
    not_sourcePEquivalent_cantorLogPotential_zero⟩
  intro h hh
  rw [cantorNativeProductCurrent_smulTest h hh]
  exact (integral_map continuous_projectiveCantorCode.measurable.aemeasurable
    (CurrentTraceMeasure.chartSmooth_continuous hh).aestronglyMeasurable).symm

/-- Whole original `ex:Igood:L228`, for that same actual Cantor potential. -/
theorem original_cantor_not_iGood_example :
    ¬ IGood (n := 1) cantorLogPotential ∧
    ¬ SGPT.PSH.VariableComplexAtlas.sourceIGood (n := 1) cantorLogPotential ∧
    SGPT.PSH.VariableComplexAtlas.sourceIEnvelope
      (projectiveFSForm.add projectiveFSForm) cantorLogPotential = 0 ∧
    IEnvelope.iSingularityEnvelope (Θ).val cantorLogPotential = 0 ∧
    DiagonalMass.diagonalPotentialMass ω (fun _ : P1 => 0)
      isThetaPshPotential_projectiveZero = 1 ∧
    DiagonalMass.diagonalPotentialMass Θ cantorLogPotential
      isThetaPshPotential_cantorLogPotential_double = 1 ∧
    DiagonalMass.diagonalPotentialMass Θ (fun _ : P1 => 0)
      isThetaPshPotential_projectiveZero_double = 2 ∧
    DiagonalMass.diagonalPotentialMass Θ cantorLogPotential
      isThetaPshPotential_cantorLogPotential_double =
        DiagonalMass.diagonalPotentialMass ω (fun _ : P1 => 0)
          isThetaPshPotential_projectiveZero ∧
    DiagonalMass.diagonalPotentialMass Θ cantorLogPotential
      isThetaPshPotential_cantorLogPotential_double <
        DiagonalMass.diagonalPotentialMass Θ (fun _ : P1 => 0)
          isThetaPshPotential_projectiveZero_double := by
  refine ⟨not_iGood_cantorLogPotential, not_sourceIGood_cantorLogPotential,
    sourceIEnvelope_cantorLogPotential_double_eq_zero,
    iSingularityEnvelope_cantorLogPotential_double_eq_zero,
    diagonalPotentialMass_projectiveZero,
    diagonalPotentialMass_cantorLogPotential_double,
    diagonalPotentialMass_projectiveZero_double, ?_, ?_⟩
  · rw [diagonalPotentialMass_cantorLogPotential_double,
      diagonalPotentialMass_projectiveZero]
  · rw [diagonalPotentialMass_cantorLogPotential_double,
      diagonalPotentialMass_projectiveZero_double]
    norm_num

end SGPT.BBJ
