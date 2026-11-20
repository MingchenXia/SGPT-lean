import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

/-!
# AuxiliaryProbabilityVolume

The normalized Kähler volume `ωⁿ / ∫ ωⁿ` as a smooth positive probability measure.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.PositiveClasses IntegrationCurrent ChartwiseGlobalL1
open scoped Topology ContDiff ENNReal

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X]

omit [IsComplexManifold n X] [BorelSpace X] in
/-- Natural positive scalar multiplication preserves actual smooth chart
volume densities, proved from map/restriction and with-density identities. -/
theorem smoothPositiveVolume_smul {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {c : ℝ} (hc : 0 < c) :
    IsSmoothPositiveVolume (n := n) (ENNReal.ofReal c • μ) := by
  intro e
  obtain ⟨ρ, hρ, hpos, hmap⟩ := hμ e
  refine ⟨fun z => c * ρ z, contDiffOn_const.mul hρ,
    fun z hz => mul_pos hc (hpos z hz), ?_⟩
  rw [Measure.restrict_smul, Measure.map_smul, hmap]
  have hd : (fun z => ENNReal.ofReal (c * ρ z)) =
      ENNReal.ofReal c • (fun z => ENNReal.ofReal (ρ z)) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hc.le]
  rw [hd, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

variable [CompactSpace X] [Nonempty X]

/-- Actual original Kähler volume has positive finite real total mass. -/
theorem kahlerVolume_real_mass_pos (omega : KahlerBackground n X) :
    0 < (kahlerVolume omega).real univ :=
  ENNReal.toReal_pos
    (KahlerLaplacianStokes.kahlerVolume_pos_of_isOpen omega isOpen_univ univ_nonempty).ne'
    (measure_ne_top _ _)

/-- Constructed auxiliary volume, separate from the original general BM μ. -/
def sourceAuxiliaryProbabilityVolume (omega : KahlerBackground n X) : Measure X :=
  ENNReal.ofReal ((kahlerVolume omega).real univ)⁻¹ • kahlerVolume omega

/-- Probability follows from the actual finite positive mass; no probability
or normalization-equality certificate is supplied. -/
instance sourceAuxiliaryProbabilityVolume_isProbability (omega : KahlerBackground n X) :
    IsProbabilityMeasure (sourceAuxiliaryProbabilityVolume omega) := by
  refine ⟨?_⟩
  have hm := kahlerVolume_real_mass_pos omega
  rw [sourceAuxiliaryProbabilityVolume, Measure.smul_apply, smul_eq_mul,
    ← ENNReal.ofReal_toReal (measure_ne_top (kahlerVolume omega) univ),
    ← ENNReal.ofReal_mul (inv_pos.mpr hm).le]
  change ENNReal.ofReal (((kahlerVolume omega).real univ)⁻¹ * (kahlerVolume omega).real univ) = 1
  rw [inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one]

/-- The actual constructed probability volume retains smooth strict positivity
in every ORIGINAL chart, including complex dimension zero. -/
theorem sourceAuxiliaryProbabilityVolume_smoothPositive (omega : KahlerBackground n X) :
    IsSmoothPositiveVolume (n := n) (sourceAuxiliaryProbabilityVolume omega) :=
  smoothPositiveVolume_smul (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
    (inv_pos.mpr (kahlerVolume_real_mass_pos omega))

end SGPT.Bergman.PolynomialH0Growth
