import SGPT.Toric.ProjectiveLogLogBedfordTaylor
import SGPT.Toric.LogLogModelEnvelope

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ENNReal

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "D" => projectiveLogLogPuncturedDomain

/-- The actual original global NP measure equals the genuinely calibrated radial patch transport. -/
theorem projectiveLogLogNonPluripolarMeasure_eq_push_radial :
    projectiveLogLogNonPluripolarMeasure =
      projectiveLogLogPuncturedPatch.pushMeasure
        (Measure.map projectiveModelEquiv logLogRadialMeasure) := by
  have ha : ∀ᵐ p ∂projectiveLogLogNonPluripolarMeasure,
      p ∈ projectiveToricBoundaryᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using
      projectiveLogLogNonPluripolarMeasure_boundary
  have he := Measure.restrict_eq_self_of_ae_mem ha
  calc
    projectiveLogLogNonPluripolarMeasure =
        projectiveLogLogNonPluripolarMeasure.restrict projectiveToricBoundaryᶜ := he.symm
    _ = projectiveLogLogPuncturedPatch.pushMeasure logLogCanonicalBTMeasure :=
      projectiveLogLogNonPluripolarMeasure_restrict_punctured
    _ = _ := congrArg projectiveLogLogPuncturedPatch.pushMeasure
      logLogCanonicalBT_eq_map_radial

/-- The total mass is computed from the original NP construction, including its corner atom. -/
theorem projectiveLogLogNonPluripolarMeasure_univ :
    projectiveLogLogNonPluripolarMeasure univ = 1 := by
  let ν := Measure.map projectiveModelEquiv logLogRadialMeasure
  have hν0 : ν (D : Set (ComplexModel 1))ᶜ = 0 := by
    change (Measure.map projectiveModelEquiv logLogRadialMeasure) _ = 0
    rw [← logLogCanonicalBT_eq_map_radial]
    exact canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hνr : ν.restrict D = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν0)
  have hν1 : ν univ = 1 := by
    change (Measure.map projectiveModelEquiv logLogRadialMeasure) univ = 1
    rw [Measure.map_apply projectiveModelEquiv.continuous.measurable
      MeasurableSet.univ, preimage_univ, logLogRadialMeasure_univ]
  calc
    projectiveLogLogNonPluripolarMeasure univ = ν D := by
      rw [projectiveLogLogNonPluripolarMeasure_eq_push_radial,
        projectiveLogLogPuncturedPatch.pushMeasure_apply]
      simp only [preimage_univ, inter_univ]
      rfl
    _ = (ν.restrict D) univ := (Measure.restrict_apply_univ _).symm
    _ = ν univ := by rw [hνr]
    _ = 1 := hν1

/-- The true projective image of the finite-coordinate corner circle. -/
def projectiveLogLogCornerCircle : Set P1 :=
  (projectiveModelChart false).symm ''
    {z : ComplexModel 1 | ‖z 0‖ = Real.exp (-logLogLambda / 2)}

/-- The positive slope jump remains a literal circle mass of the original NP measure. -/
theorem projectiveLogLogNonPluripolarMeasure_cornerCircle :
    projectiveLogLogNonPluripolarMeasure projectiveLogLogCornerCircle =
      ENNReal.ofReal (1 - logLogLambda⁻¹) := by
  let C : Set (ComplexModel 1) :=
    {z | ‖z 0‖ = Real.exp (-logLogLambda / 2)}
  have hCT : ∀ z : ComplexModel 1, z ∈ (projectiveModelChart false).target := by
    intro z
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  have hCD : C ⊆ D := by
    intro z hz
    change ∀ i : Fin 1, z i ≠ 0
    intro i
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
    intro hzero
    have hn : ‖z 0‖ = Real.exp (-logLogLambda / 2) := hz
    rw [hzero, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn.symm
  have hpre : (D : Set (ComplexModel 1)) ∩
      (projectiveModelChart false).symm ⁻¹' projectiveLogLogCornerCircle = C := by
    ext z
    constructor
    · rintro ⟨_, w, hw, he⟩
      have hwz : w = z :=
        (projectiveModelChart false).symm.injOn (hCT w) (hCT z) he
      rwa [← hwz]
    · intro hz
      exact ⟨hCD hz, z, hz, rfl⟩
  have hC : MeasurableSet C := by
    have hc : Continuous (fun z : ComplexModel 1 => ‖z 0‖) := by fun_prop
    exact (isClosed_eq hc continuous_const).measurableSet
  have hm : projectiveModelEquiv ⁻¹' C =
      {z : ℂ | ‖z‖ = Real.exp (-logLogLambda / 2)} := by
    ext z
    simp only [mem_preimage, C, mem_ofPred_eq, projectiveModelEquiv_apply_zero]
  rw [projectiveLogLogNonPluripolarMeasure_eq_push_radial,
    projectiveLogLogPuncturedPatch.pushMeasure_apply]
  change (Measure.map projectiveModelEquiv logLogRadialMeasure)
    ((D : Set (ComplexModel 1)) ∩
      (projectiveModelChart false).symm ⁻¹' projectiveLogLogCornerCircle) = _
  rw [hpre, Measure.map_apply projectiveModelEquiv.continuous.measurable hC,
    hm, logLogRadialMeasure_cornerCircle]

/-- The original log-log example's actual source class, NP mass, model envelope and type change. -/
theorem original_projectiveLogLog_nonpluripolar_mass_and_envelope :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogLogPotential ∧
    projectiveLogLogNonPluripolarMeasure univ = 1 ∧
    sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential = 0 ∧
    ¬ SingularityEquiv projectiveLogLogPotential
      (sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential) :=
  ⟨isThetaPSH_projectiveLogLogPotential,
    projectiveLogLogNonPluripolarMeasure_univ,
    sourceSingularityEnvelope_projectiveLogLog_eq_zero,
    not_singularityEquiv_projectiveLogLog_envelope⟩

end SGPT.Toric
