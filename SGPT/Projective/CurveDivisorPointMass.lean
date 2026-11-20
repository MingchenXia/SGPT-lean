import SGPT.Projective.DivisorNormalShuffleCalibration
import SGPT.Projective.ComplexNormalWedge

/-! The actual normalized full original curve divisor current has its
actual regular zero multiplicity as point mass.
Blueprint: curve-divisor-point-mass.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open DivisorRegularLocus DivisorIntegrationCurrent
open StronglyPositiveForms ConstantFormProducts TopDegreeDensity CanonicalCurrentFrame
open SGPT.Projective.NumEq.CompleteIntersections
open _root_.SGPT.Foundations.Analysis.LocalCurrents

private theorem curveComplement : 2 * 0 = Module.finrank ℝ (ComplexModel (0 + 1)) - 2 := by
  rw [SGPT.Foundations.Analysis.FirstPass.complexModel_real_finrank]

/-- Exact original canonical shuffle at a genuine regular curve zero. -/
theorem curve_divisorShuffleDensity_at_regular {Ω : Opens (ComplexModel 1)}
    (g : ComplexModel 1 → ℂ) (x : ComplexModel 1) (P : RegularPresentation g x)
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel 1) - 2)) :
    divisorShuffleDensity g
      (currentPairingBasis (canonicalBasis 1) (degreeTwo (Nat.succ_pos 0))) η x =
      (P.m : ℝ) * (castForm curveComplement.symm (η x)) ![] := by
  let ℓ := fderiv ℂ P.h x
  have hℓ : ℓ ≠ 0 := P.dh_ne x P.mem
  have hβ : ∀ u v : ComplexModel 1,
      ((P.m : ℝ) • ComplexNormalForm.normalForm ℓ) ![u, v] = divisorDensity g u v x := by
    intro u v
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ComplexNormalForm.normalForm_pair, divisorDensity,
      indicator_of_mem P.mem_regularLocus, P.divisorMult_eq, P.transverseForm_eq]
    rfl
  rw [divisorShuffleDensity_eq_topDensity_standard g η x
    ((P.m : ℝ) • ComplexNormalForm.normalForm ℓ) hβ curveComplement,
    wedgeTo_smul_left, topDensity_smul]
  congr 1
  let D : ComplexModel 0 →L[ℂ] ComplexModel 1 := 0
  have hD : ℓ.comp D = 0 := by simp [D]
  have harea := ComplexNormalWedge.normal_wedge_area ℓ hℓ D hD
    (castForm curveComplement.symm (η x))
  rw [LinearMap.normDet_of_subsingleton, one_mul] at harea
  refine harea.trans ?_
  change (castForm curveComplement.symm (η x)) _ = _
  congr 1
  funext i
  exact False.elim (by have := i.isLt; omega)

/-- The full actual current, not merely its support, counts an isolated regular zero. -/
theorem curve_divisorCurrent_point_mass {Ω : Opens (ComplexModel 1)}
    {g : ComplexModel 1 → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (x : ComplexModel 1) (_hx : x ∈ Ω) (P : RegularPresentation g x)
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel 1) - 2))
    (hzero : ∀ z ∈ tsupport (η : ComplexModel 1 →
      RealForm 1 (Module.finrank ℝ (ComplexModel 1) - 2)), g z = 0 → z = x) :
    wedgePairing (currentPairingBasis (canonicalBasis 1) (degreeTwo (Nat.succ_pos 0)))
      (divisorCurrent hg hg0) η =
        (P.m : ℝ) * (castForm curveComplement.symm (η x)) ![] := by
  rw [divisorCurrent_wedgePairing_eq_integral]
  let F := divisorShuffleDensity g
    (currentPairingBasis (canonicalBasis 1) (degreeTwo (Nat.succ_pos 0))) η
  have hoff : ∀ z ∉ ({x} : Set (ComplexModel 1)), F z = 0 := by
    intro z hz
    by_cases hs : z ∈ tsupport (η : ComplexModel 1 →
      RealForm 1 (Module.finrank ℝ (ComplexModel 1) - 2))
    · by_cases hr : z ∈ regularLocus g
      · exact False.elim (hz (Set.mem_singleton_iff.mpr
          (hzero z hs (eq_zero_of_mem_regularLocus hr))))
      · exact divisorShuffleDensity_eq_zero_off_regular g _ η z (fun h => hr h.1)
    · have hη : η z = 0 := image_eq_zero_of_notMem_tsupport hs
      simp [F, divisorShuffleDensity, hη]
  have hsingle : ∫ z in ({x} : Set (ComplexModel 1)), F z ∂(μHE[0] : Measure (ComplexModel 1)) =
      ∫ z, F z ∂(μHE[0] : Measure (ComplexModel 1)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hoff
  change ∫ z, F z ∂(μHE[0] : Measure (ComplexModel 1)) = _
  rw [← hsingle, integral_singleton]
  simp only [MeasureTheory.Measure.euclideanHausdorffMeasure_zero,
    MeasureTheory.Measure.hausdorffMeasure_zero_singleton, measureReal_def,
    ENNReal.toReal_one, one_smul]
  exact curve_divisorShuffleDensity_at_regular g x P η

end SGPT.Projective.NumEq.AlgebraicCurveDegree
