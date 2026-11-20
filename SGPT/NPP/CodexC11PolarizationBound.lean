import SGPT.Okounkov.TranscendentalWNRegStatement
import SGPT.Foundations.Analysis.TestLeviPairing

/-! A direct polarized scalar test bound from the source regularity input.
No measurable Hessian or metric-Laplacian representative is asserted here.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11PolarizationBound.lean` (module `C11PolarizationBound`), with module and namespace renamed.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWNReg

namespace SGPT.NPP.Codex.C11PolarizationBound

variable {n : ℕ}

/-- On a fixed compact chart set and in a fixed direction, the source test
bound has a nonnegative constant independent of the test function. -/
theorem exists_directional_levi_test_bound
    {g : ComplexModel n → ℝ} {U K : Set (ComplexModel n)}
    (h : HasLocallyBoundedComplexHessianOn g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v : ComplexModel n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : ComplexModel n → ℝ,
      ContDiff ℝ ∞ φ → tsupport φ ⊆ K →
      |∫ z, g z * leviForm φ z v| ≤ A * ∫ z, |φ z| := by
  obtain ⟨C, hC⟩ := h K hK hKU
  refine ⟨max 0 (C * ‖v‖ ^ 2), le_max_left _ _, ?_⟩
  intro φ hφ hφK
  exact (hC φ hφ hφK v).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (integral_nonneg fun _ => abs_nonneg _))

/-- The same directional bound in the open-domain test-function interface,
with the actual restricted chart Lebesgue measure on the right. -/
theorem exists_directional_open_test_bound
    {g : ComplexModel n → ℝ} {U K : Set (ComplexModel n)}
    (h : HasLocallyBoundedComplexHessianOn g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (Ω : Opens (ComplexModel n))
    (hΩK : (Ω : Set (ComplexModel n)) ⊆ K) (v : ComplexModel n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : 𝓓(Ω, ℝ), (∀ z, 0 ≤ φ z) →
      |∫ z, g z * leviForm φ z v| ≤
        A * ∫ z : Ω, φ z ∂(volume.comap Subtype.val) := by
  obtain ⟨A, hA, hbound⟩ := exists_directional_levi_test_bound h hK hKU v
  refine ⟨A, hA, ?_⟩
  intro φ hφ
  have htest := hbound φ φ.contDiff (φ.tsupport_subset.trans hΩK)
  have hread : (∫ z : Ω, φ z ∂(volume.comap Subtype.val)) = ∫ z, |φ z| := by
    calc
      _ = ∫ z in (Ω : Set (ComplexModel n)), φ z :=
        integral_subtype_comap Ω.isOpen.measurableSet (fun z => φ z)
      _ = ∫ z, φ z := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
        image_eq_zero_of_notMem_tsupport (fun ht => hz (φ.tsupport_subset ht)))
      _ = ∫ z, |φ z| := by congr 1; funext z; exact (abs_of_nonneg (hφ z)).symm
  rw [hread]
  exact htest

/-- The exact existing distributional Levi operator satisfies that open-domain
bound, provided its original coefficient is locally integrable on the domain. -/
theorem exists_distributional_levi_test_bound
    {g : ComplexModel n → ℝ} {U K : Set (ComplexModel n)}
    (h : HasLocallyBoundedComplexHessianOn g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (Ω : Opens (ComplexModel n))
    (hΩK : (Ω : Set (ComplexModel n)) ⊆ K)
    (hg : LocallyIntegrableOn g Ω volume) (v : ComplexModel n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : 𝓓(Ω, ℝ), (∀ z, 0 ≤ φ z) →
      |distributionalLeviCLM v (regularDistribution volume g hg) φ| ≤
        A * ∫ z : Ω, φ z ∂(volume.comap Subtype.val) := by
  obtain ⟨A, hA, hbound⟩ := exists_directional_open_test_bound h hK hKU Ω hΩK v
  refine ⟨A, hA, ?_⟩
  intro φ hφ
  rw [distributionalLeviCLM_regularDistribution_apply]
  exact hbound φ hφ

/-- Every compact chart subset has one constant controlling differences of
directional Levi distributions, as required by polarization. -/
theorem exists_polarized_levi_test_bound
    {g : ComplexModel n → ℝ} {U K : Set (ComplexModel n)}
    (h : HasLocallyBoundedComplexHessianOn g U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ K →
      ∀ v w : ComplexModel n,
      |(∫ z, g z * leviForm φ z (v + w)) -
        (∫ z, g z * leviForm φ z (v - w))| ≤
          (C * ‖v + w‖ ^ 2 + C * ‖v - w‖ ^ 2) * ∫ z, |φ z| := by
  obtain ⟨C, hC⟩ := h K hK hKU
  refine ⟨C, ?_⟩
  intro φ hφ hφK v w
  calc
    |(∫ z, g z * leviForm φ z (v + w)) -
        (∫ z, g z * leviForm φ z (v - w))| ≤
        |∫ z, g z * leviForm φ z (v + w)| +
          |∫ z, g z * leviForm φ z (v - w)| := abs_sub _ _
    _ ≤ (C * ‖v + w‖ ^ 2) * (∫ z, |φ z|) +
        (C * ‖v - w‖ ^ 2) * (∫ z, |φ z|) :=
      add_le_add (hC φ hφ hφK (v + w)) (hC φ hφ hφK (v - w))
    _ = _ := by ring

end SGPT.NPP.Codex.C11PolarizationBound
