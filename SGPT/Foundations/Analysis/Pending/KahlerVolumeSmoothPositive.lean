import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent

set_option autoImplicit false

/-!
# Actual Kahler volume has a smooth strictly positive chart density

An independent actual chart-map adaptation of the smooth mixed-density
formula. The actual smooth top power and Hermitian positivity produce the
density, and almost-everywhere measurable inverse/forward chart composition
produces the existing smooth-positive-volume predicate, including dimension zero.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
  IntegrationCurrent SmoothMixedMeasureDensity ProductTestForms TopDegreeDensity
  ChartwiseGlobalL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual zero-potential Kahler measure satisfies the existing smooth-positive-volume predicate. -/
theorem isSmoothPositiveVolume_kahlerVolume (omega : KahlerBackground n M) :
    IsSmoothPositiveVolume (n := n) (kahlerVolume omega) := by
  intro e
  let ρ : ComplexModel n → ℝ := fun z => topDensity ((formPow omega.form.val n).coeff e z)
  have hρ : ContDiffOn ℝ ∞ ρ e.val.target :=
    (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ (topBasis n)).contDiff.comp_contDiffOn
      ((formPow omega.form.val n).smooth e)
  have hpos : ∀ z ∈ e.val.target, 0 < ρ z :=
    fun _ hz => topDensity_formPow_pos omega.isKahler.1 hz
  have hdensity : chartDensity (fun _ => omega.form) e = fun z => ENNReal.ofReal (ρ z) := by
    funext z
    simp only [chartDensity, ρ, formPow_coeff, formPower_eq_wedgeProd, topDensity_wedgeProd]
  have h0 : IsThetaPshPotential omega.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  let ν := (volume.restrict e.val.target).withDensity (chartDensity (fun _ => omega.form) e)
  have hac : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hν : (kahlerVolume omega).restrict e.val.source = Measure.map e.val.symm ν := by
    rw [← himage, kahlerVolume, diagonalPotentialMeasure]
    exact restrict_image_eq_map (fun _ => h0.1) e e.val.open_target.measurableSet (Subset.refl _)
  have hinv : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hac
  have hforward : AEMeasurable e.val (Measure.map e.val.symm ν) := by
    rw [← hν]
    exact e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  refine ⟨ρ, hρ, hpos, ?_⟩
  rw [hν, hforward.map_map_of_aemeasurable hinv]
  have hid : (e.val ∘ e.val.symm) =ᵐ[ν] id :=
    hac.ae_le ((ae_restrict_mem e.val.open_target.measurableSet).mono fun z hz => e.val.right_inv hz)
  rw [Measure.map_congr hid, Measure.map_id]
  change (volume.restrict e.val.target).withDensity (chartDensity (fun _ => omega.form) e) = _
  rw [hdensity]

end

end SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
