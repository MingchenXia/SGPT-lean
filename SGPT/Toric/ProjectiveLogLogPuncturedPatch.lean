import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open scoped Topology ContDiff

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The genuine open nonzero coordinate domain. -/
def projectiveLogLogPuncturedDomain : TopologicalSpace.Opens (ComplexModel 1) :=
  ⟨complexTorus 1, isOpen_complexTorus 1⟩

/-- Literal actual real profile after the original smooth FS correction. -/
def projectiveLogLogCorrectedProfile (z : ComplexModel 1) : ℝ :=
  logLogProfile (Real.log (‖z 0‖ ^ 2))

theorem continuousOn_projectiveLogLogCorrectedProfile :
    ContinuousOn projectiveLogLogCorrectedProfile projectiveLogLogPuncturedDomain := by
  have hnorm : Continuous (fun z : ComplexModel 1 => ‖z 0‖ ^ 2) := by
    simpa only [projectiveModelEquiv_symm_apply, ← Complex.sq_norm] using
      contDiff_projectiveModel_normSq.continuous
  have hlog : ContinuousOn (fun z : ComplexModel 1 => Real.log (‖z 0‖ ^ 2))
      projectiveLogLogPuncturedDomain :=
    hnorm.continuousOn.log (fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hz 0)))
  exact (continuousOn_univ.mp (convexOn_logLogProfile.continuousOn isOpen_univ)).comp_continuousOn hlog

theorem plurisubharmonicOn_projectiveLogLogCorrectedProfile :
    PlurisubharmonicOn (fun z => (projectiveLogLogCorrectedProfile z : EReal))
      projectiveLogLogPuncturedDomain := by
  have hp := plurisubharmonicOn_tropicalPullback_of_convexOn
    logLogEuclideanProfile_mem_realGrowthClass.1
  have heq : tropicalPullback (fun x => (logLogEuclideanProfile x : EReal)) =
      (fun z => (projectiveLogLogCorrectedProfile z : EReal)) := by
    funext z
    change (logLogProfile (tropicalization z 0) : EReal) = _
    rw [tropicalization_apply_eq_log_norm_sq]
    rfl
  rw [heq] at hp
  exact hp

theorem isLocallyBoundedPshOn_projectiveLogLogCorrectedProfile :
    IsLocallyBoundedPshOn projectiveLogLogPuncturedDomain projectiveLogLogCorrectedProfile :=
  LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
    plurisubharmonicOn_projectiveLogLogCorrectedProfile
    continuousOn_projectiveLogLogCorrectedProfile

/-- A real original preferred-chart patch, not an assumed local BT model. -/
def projectiveLogLogPuncturedPatch :
    Patch (fun _ : Fin 1 => projectiveNativeFSBackground.form)
      (fun _ => projectiveLogLogPotential) where
  chart := projectiveNativeChart false
  domain := projectiveLogLogPuncturedDomain
  domain_le_target := by
    intro z _
    change z ∈ (projectiveModelChart false).target
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  potential := fun _ => projectiveFSPotential
  localPotential := fun _ => ⟨projectiveLogLogPuncturedDomain.isOpen, by
    intro z _
    change z ∈ (projectiveModelChart false).target
    simp [projectiveModelChart, projectiveQuotientScalarChart_target],
    contDiff_projectiveFSPotential.contDiffOn, fun _ _ => rfl⟩
  plurisubharmonic := by
    intro _
    change PlurisubharmonicOn
      (fun z => projectiveLogLogPotential ((projectiveModelChart false).symm z) +
        (projectiveFSPotential z : EReal)) projectiveLogLogPuncturedDomain
    have hp := isThetaPSH_projectiveLogLogPotential.preferred_chart_corrected false
      contDiff_projectiveFSPotential.contDiffOn (fun _ _ => rfl)
    change PlurisubharmonicOn
      (fun z : ComplexModel 1 => projectiveLogLogPotential
        ((projectiveModelChart false).symm z) + (projectiveFSPotential z : EReal))
      (projectiveModelChart false).target at hp
    exact hp.mono (by
      intro z _
      simp [projectiveModelChart, projectiveQuotientScalarChart_target])

theorem projectiveLogLogPuncturedPatch_corrected (i : Fin 1) {z : ComplexModel 1}
    (hz : z ∈ projectiveLogLogPuncturedDomain) :
    projectiveLogLogPuncturedPatch.corrected i z = (projectiveLogLogCorrectedProfile z : EReal) := by
  change projectiveLogLogPotential ((projectiveModelChart false).symm z) +
    (projectiveFSPotential z : EReal) = _
  rw [projectiveLogLogPotential_finite (hz 0), projectiveFSPotential_eq, ← Complex.sq_norm,
    ← EReal.coe_add]
  congr 1
  exact sub_add_cancel _ _

theorem projectiveLogLogPuncturedPatch_source :
    (projectiveLogLogPuncturedPatch.source : Set P1) = projectiveToricBoundaryᶜ := by
  ext p
  constructor
  · intro hp
    change p ∈ (projectiveModelChart false).source ∧
      projectiveModelChart false p ∈ complexTorus 1 at hp
    have h := (projectiveToricBoundary_chart_off_iff false _).mpr hp.2
    rwa [(projectiveModelChart false).left_inv hp.1] at h
  · intro hp
    exact ⟨projectiveToricBoundary_compl_subset_finite_source hp,
      projectiveFiniteCoordinate_mem_torus_of_off_boundary hp⟩

/-- Actual NP truncation agrees with genuine BT on this punctured real patch. -/
theorem projectiveLogLogNonPluripolarMeasure_restrict_punctured :
    projectiveLogLogNonPluripolarMeasure.restrict projectiveToricBoundaryᶜ =
      projectiveLogLogPuncturedPatch.pushMeasure
        (canonicalMixedBedfordTaylorMeasure projectiveLogLogPuncturedDomain
          (fun _ : Fin 1 => projectiveLogLogCorrectedProfile)
          (fun _ => isLocallyBoundedPshOn_projectiveLogLogCorrectedProfile)) := by
  rw [← projectiveLogLogPuncturedPatch_source]
  change (GlobalNonPluripolar.globalMixedMeasure
    (fun _ : Fin 1 => projectiveNativeFSBackground.form)
    (fun _ => projectiveLogLogPotential)
    (fun _ => isThetaPshPotential_projectiveLogLogPotential.1)).restrict _ = _
  rw [GlobalNonPluripolar.globalMixedMeasure_restrict_patch]
  unfold GlobalNonPluripolar.patchMeasure
  apply congrArg projectiveLogLogPuncturedPatch.pushMeasure
  exact MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (fun _ => isLocallyBoundedPshOn_projectiveLogLogCorrectedProfile)
    projectiveLogLogPuncturedPatch.plurisubharmonic
    (fun i z hz => projectiveLogLogPuncturedPatch_corrected i hz)

end SGPT.Toric
