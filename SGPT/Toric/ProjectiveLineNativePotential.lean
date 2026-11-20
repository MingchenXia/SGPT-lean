import SGPT.Toric.ProjectiveLineNativeManifold
import SGPT.Toric.ProjectiveLogLog
import SGPT.Toric.RelativeThetaCriterion
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The universal original source condition manufactures the genuine native potential record. -/
theorem isThetaPshPotential_projectiveNativeFS_of_source {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    IsThetaPshPotential projectiveNativeFSBackground.form.val u := by
  constructor
  · intro e z hz
    obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
    refine ⟨e.val.target, projectiveFSPotential, hz, ?_, ?_⟩
    · exact ⟨e.val.open_target, Subset.rfl,
        contDiff_projectiveFSPotential.contDiffOn, fun _ _ => rfl⟩
    · change PlurisubharmonicOn
        (fun y => u (e.val.symm y) + (projectiveFSPotential y : EReal)) e.val.target
      rw [hi]
      exact hu.preferred_chart_corrected i
        contDiff_projectiveFSPotential.contDiffOn (fun _ _ => rfl)
  · intro x O hO hxO
    obtain ⟨y, hy, hfin⟩ := hu.locallyNondegenerate x (mem_univ x) O hO hxO
    exact ⟨y, hy.2, hfin⟩

/-- The unchanged actual original log-log potential enters the native source domain. -/
theorem isThetaPshPotential_projectiveLogLogPotential :
    IsThetaPshPotential projectiveNativeFSBackground.form.val projectiveLogLogPotential :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveLogLogPotential

/-- The actual Borel sigma algebra of the unchanged original quotient topology. -/
instance projectiveNativeMeasurableSpace : MeasurableSpace P1 := borel P1

instance projectiveNativeBorelSpace : BorelSpace P1 := ⟨rfl⟩

/-- The genuine native diagonal NP measure, not a radial measure definition. -/
def projectiveLogLogNonPluripolarMeasure : Measure P1 :=
  SGPT.Foundations.Analysis.Pending.DiagonalMass.diagonalPotentialMeasure
    projectiveNativeFSBackground.form projectiveLogLogPotential
    isThetaPshPotential_projectiveLogLogPotential

/-- Actual compact Kahler finiteness is produced by the complete native theorem. -/
instance projectiveLogLogNonPluripolarMeasureFinite :
    IsFiniteMeasure projectiveLogLogNonPluripolarMeasure :=
  SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    projectiveNativeFSBackground projectiveNativeFSBackground.form
    isThetaPshPotential_projectiveLogLogPotential

/-- The genuine actual NP measure does not charge the original potential's pole locus. -/
theorem projectiveLogLogNonPluripolarMeasure_pole_null :
    projectiveLogLogNonPluripolarMeasure {p | projectiveLogLogPotential p = ⊥} = 0 := by
  simpa only [projectiveLogLogNonPluripolarMeasure,
    SGPT.Foundations.Analysis.Pending.DiagonalMass.diagonalPotentialMeasure] using
    SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin 1 => projectiveNativeFSBackground.form)
      (u := fun _ => projectiveLogLogPotential)
      (fun _ => isThetaPshPotential_projectiveLogLogPotential.1)
      isThetaPshPotential_projectiveLogLogPotential

/-- The produced original origin pole is genuinely null for the native NP measure. -/
theorem projectiveLogLogNonPluripolarMeasure_origin :
    projectiveLogLogNonPluripolarMeasure {projectiveOrigin} = 0 := by
  apply measure_mono_null _ projectiveLogLogNonPluripolarMeasure_pole_null
  intro p hp
  have h : p = projectiveOrigin := mem_singleton_iff.mp hp
  subst p
  exact projectiveLogLogPotential_origin

/-- The opposite genuine original source potential detects the infinity singleton. -/
theorem projectiveLogLogNonPluripolarMeasure_infinity :
    projectiveLogLogNonPluripolarMeasure {projectiveInfinity} = 0 := by
  have hop := isThetaPshPotential_projectiveNativeFS_of_source
    isThetaPSH_projectiveOppositeLogSingularity
  have hnull : projectiveLogLogNonPluripolarMeasure
      {p | projectiveOppositeLogSingularity p = ⊥} = 0 := by
    simpa only [projectiveLogLogNonPluripolarMeasure,
      SGPT.Foundations.Analysis.Pending.DiagonalMass.diagonalPotentialMeasure] using
      SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (θ := fun _ : Fin 1 => projectiveNativeFSBackground.form)
        (u := fun _ => projectiveLogLogPotential)
        (fun _ => isThetaPshPotential_projectiveLogLogPotential.1) hop
  apply measure_mono_null _ hnull
  intro p hp
  have h : p = projectiveInfinity := mem_singleton_iff.mp hp
  subst p
  exact projectiveOppositeLogSingularity_infinity

/-- The actual two-point boundary is null; no total NP mass is asserted. -/
theorem projectiveLogLogNonPluripolarMeasure_boundary :
    projectiveLogLogNonPluripolarMeasure projectiveToricBoundary = 0 := by
  have heq : projectiveToricBoundary = {projectiveOrigin} ∪ {projectiveInfinity} := by
    ext p
    simp [projectiveToricBoundary, or_comm]
  rw [heq]
  apply le_antisymm _ zero_le
  calc
    projectiveLogLogNonPluripolarMeasure ({projectiveOrigin} ∪ {projectiveInfinity}) ≤
        projectiveLogLogNonPluripolarMeasure {projectiveOrigin} +
          projectiveLogLogNonPluripolarMeasure {projectiveInfinity} := measure_union_le _ _
    _ = 0 := by rw [projectiveLogLogNonPluripolarMeasure_origin,
      projectiveLogLogNonPluripolarMeasure_infinity, add_zero]

end SGPT.Toric
