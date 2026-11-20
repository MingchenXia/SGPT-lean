import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.FirstPass.CurrentPairing

/-! The actual full normalized divisor-current pairing as the SAME
Hausdorff-area integral. Blueprint: `divisor-current-shuffle-area.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending DivisorIntegrationCurrent
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Literal original normalized signed shuffle density, retaining the
original divisor density and arbitrary actual complementary test form. -/
def divisorShuffleDensity {n q : ℕ} {Ω : Opens (ComplexModel n)}
    (g : ComplexModel n → ℂ) (v : Fin 2 ⊕ Fin q → ComplexModel n)
    (η : TestForm Ω q) (x : ComplexModel n) : ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q),
    ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
      (η x (fun j => v (s.out (Sum.inr j))) *
        divisorDensity g (v (s.out (Sum.inl 0))) (v (s.out (Sum.inl 1))) x)

/-- Full native local current action is exactly the original Hausdorff
integral of its SAME signed complementary shuffle density. -/
theorem divisorCurrent_wedgePairing_eq_integral {n q : ℕ} {Ω : Opens (ComplexModel n)}
    {g : ComplexModel n → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (v : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm Ω q) :
    wedgePairing v (divisorCurrent hg hg0) η =
      ∫ x, divisorShuffleDensity g v η x ∂(μHE[2 * n - 2] : Measure (ComplexModel n)) := by
  have hpair (s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q)) :
      (fun i : Fin 2 => v (s.out (Sum.inl i))) =
        ![v (s.out (Sum.inl 0)), v (s.out (Sum.inl 1))] := by
    funext i
    fin_cases i <;> rfl
  have hi (s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q)) :
      Integrable (fun x => ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
        (η x (fun j => v (s.out (Sum.inr j))) *
          divisorDensity g (v (s.out (Sum.inl 0))) (v (s.out (Sum.inl 1))) x))
        (μHE[2 * n - 2] : Measure (ComplexModel n)) :=
    (integrable_testFunction_mul (locallyIntegrableOn_divisorDensity hg hg0
      (v (s.out (Sum.inl 0))) (v (s.out (Sum.inl 1))))
      (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η)).const_mul _
  rw [wedgePairing_apply]
  simp only [Units.smul_def, zsmul_eq_mul]
  calc
    _ = ∑ s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q),
        ∫ x, ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (η x (fun j => v (s.out (Sum.inr j))) *
            divisorDensity g (v (s.out (Sum.inl 0))) (v (s.out (Sum.inl 1))) x)
          ∂(μHE[2 * n - 2] : Measure (ComplexModel n)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hpair s, divisorCurrent_apply, integral_const_mul]
      rfl
    _ = _ := by
      rw [← integral_finsetSum Finset.univ (fun s _ => hi s)]
      rfl

/-- The unchanged signed density is supported on the actual original
regular zero locus inside the original test domain. -/
theorem divisorShuffleDensity_eq_zero_off_regular {n q : ℕ} {Ω : Opens (ComplexModel n)}
    (g : ComplexModel n → ℂ) (v : Fin 2 ⊕ Fin q → ComplexModel n)
    (η : TestForm Ω q) (x : ComplexModel n)
    (hx : x ∉ DivisorRegularLocus.regularLocus g ∩ (Ω : Set (ComplexModel n))) :
    divisorShuffleDensity g v η x = 0 := by
  classical
  by_cases hxR : x ∈ DivisorRegularLocus.regularLocus g
  · have hxΩ : x ∉ (Ω : Set (ComplexModel n)) := fun h => hx ⟨hxR, h⟩
    have hη : η x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hxΩ (η.tsupport_subset h))
    simp [divisorShuffleDensity, hη]
  · simp [divisorShuffleDensity, divisorDensity, indicator_of_notMem hxR]

/-- The actual full current pairing integrates over its actual original
regular zero locus, not an arbitrary measure or parameter replacement. -/
theorem divisorCurrent_wedgePairing_eq_setIntegral_regular {n q : ℕ}
    {Ω : Opens (ComplexModel n)} {g : ComplexModel n → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (v : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm Ω q) :
    wedgePairing v (divisorCurrent hg hg0) η =
      ∫ x in DivisorRegularLocus.regularLocus g ∩ (Ω : Set (ComplexModel n)),
        divisorShuffleDensity g v η x ∂(μHE[2 * n - 2] : Measure (ComplexModel n)) := by
  rw [divisorCurrent_wedgePairing_eq_integral]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => divisorShuffleDensity_eq_zero_off_regular g v η x hx)).symm

end SGPT.Projective.NumEq.CompleteIntersections
