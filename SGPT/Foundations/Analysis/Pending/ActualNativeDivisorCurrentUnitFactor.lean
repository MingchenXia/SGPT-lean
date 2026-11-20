import SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentPower

set_option autoImplicit false

/-!
# Full geometric divisor currents after a genuine holomorphic unit factor

Both regular-presentation transports are constructed on the actual domain.
The intrinsic multiplicities and transverse forms recover the geometric
density, and all compact test pairings recover the entire native current.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentUnitFactor

open DivisorRegularLocus DivisorIntegrationCurrent

variable {n : ℕ} {Ω : Opens (EuclideanSpace ℂ (Fin n))}
  {g u : EuclideanSpace ℂ (Fin n) → ℂ} {x : EuclideanSpace ℂ (Fin n)}

private def mul_unit_presentation (P : RegularPresentation g x) (hx : x ∈ Ω)
    (hu : DifferentiableOn ℂ u Ω) (hunit : ∀ y ∈ Ω, u y ≠ 0) :
    RegularPresentation (fun y => g y * u y) x where
  U := P.U ∩ Ω
  isOpen := P.isOpen.inter Ω.isOpen
  mem := ⟨P.mem, hx⟩
  m := P.m
  m_pos := P.m_pos
  h := P.h
  v := fun y => P.v y * u y
  h_diff := P.h_diff.mono inter_subset_left
  v_diff := (P.v_diff.mono inter_subset_left).mul (hu.mono inter_subset_right)
  h_zero := P.h_zero
  dh_ne := fun y hy => P.dh_ne y hy.1
  v_ne := fun y hy => mul_ne_zero (P.v_ne y hy.1) (hunit y hy.2)
  eq := fun y hy => by rw [P.eq y hy.1, mul_assoc]

private def remove_unit_presentation
    (P : RegularPresentation (fun y => g y * u y) x) (hx : x ∈ Ω)
    (hu : DifferentiableOn ℂ u Ω) (hunit : ∀ y ∈ Ω, u y ≠ 0) :
    RegularPresentation g x where
  U := P.U ∩ Ω
  isOpen := P.isOpen.inter Ω.isOpen
  mem := ⟨P.mem, hx⟩
  m := P.m
  m_pos := P.m_pos
  h := P.h
  v := fun y => P.v y * (u y)⁻¹
  h_diff := P.h_diff.mono inter_subset_left
  v_diff := (P.v_diff.mono inter_subset_left).mul
    ((hu.mono inter_subset_right).inv (fun y hy => hunit y hy.2))
  h_zero := P.h_zero
  dh_ne := fun y hy => P.dh_ne y hy.1
  v_ne := fun y hy => mul_ne_zero (P.v_ne y hy.1) (inv_ne_zero (hunit y hy.2))
  eq := fun y hy => by
    calc
      g y = (g y * u y) * (u y)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (hunit y hy.2), mul_one]
      _ = P.h y ^ P.m * (P.v y * (u y)⁻¹) := by rw [P.eq y hy.1, mul_assoc]

private theorem divisorDensity_mul_unit_eq
    (hu : DifferentiableOn ℂ u Ω) (hunit : ∀ y ∈ Ω, u y ≠ 0)
    (hx : x ∈ Ω) (v w : EuclideanSpace ℂ (Fin n)) :
    divisorDensity (fun y => g y * u y) v w x = divisorDensity g v w x := by
  classical
  by_cases hreg : x ∈ regularLocus g
  · obtain ⟨P⟩ := hreg
    let Q := mul_unit_presentation P hx hu hunit
    simp only [divisorDensity, indicator_of_mem P.mem_regularLocus,
      indicator_of_mem Q.mem_regularLocus]
    rw [Q.divisorMult_eq, P.divisorMult_eq, Q.transverseForm_eq, P.transverseForm_eq]
    rfl
  · have hnot : x ∉ regularLocus (fun y => g y * u y) := by
      intro h
      obtain ⟨P⟩ := h
      exact hreg (remove_unit_presentation P hx hu hunit).mem_regularLocus
    simp only [divisorDensity, indicator_of_notMem hreg, indicator_of_notMem hnot]

private theorem divisorCurrent_mul_unit_eq
    (hg : DifferentiableOn ℂ g Ω) (hu : DifferentiableOn ℂ u Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (hunit : ∀ y ∈ Ω, u y ≠ 0)
    (hgu : DifferentiableOn ℂ (fun y => g y * u y) Ω)
    (hgu0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z * u z ≠ 0) :
    divisorCurrent hgu hgu0 = divisorCurrent hg hg0 := by
  ext v : 1
  ext φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, divisorCurrent_apply, divisorCurrent_apply]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change φ y * divisorDensity (fun y => g y * u y) (v 0) (v 1) y =
    φ y * divisorDensity g (v 0) (v 1) y
  by_cases hy : y ∈ Ω
  · rw [divisorDensity_mul_unit_eq hu hunit hy]
  · have hφ : φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (φ.tsupport_subset h))
    simp only [hφ, zero_mul]

/-- A genuine holomorphic unit leaves the full power current unchanged.
The product's holomorphicity, nonzero germs and geometric current identity
are all internally constructed from the natural original inputs. -/
theorem exists_divisorCurrent_pow_mul_unit
    (hg : DifferentiableOn ℂ g Ω) (hu : DifferentiableOn ℂ u Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) (hunit : ∀ y ∈ Ω, u y ≠ 0) (a : ℕ) :
    ∃ (hprod : DifferentiableOn ℂ (fun y => g y ^ a * u y) Ω)
      (hprod0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ^ a * u z ≠ 0),
      divisorCurrent hprod hprod0 = (a : ℝ) • divisorCurrent hg hg0 := by
  obtain ⟨hga, hga0, hpow⟩ := ActualNativeDivisorCurrentPower.exists_divisorCurrent_pow hg hg0 a
  have hprod : DifferentiableOn ℂ (fun y => g y ^ a * u y) Ω := hga.mul hu
  have hprod0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ^ a * u z ≠ 0 := by
    intro y hy
    exact ((hga0 y hy).and_eventually (Ω.isOpen.mem_nhds hy)).mono
      (fun z hz => mul_ne_zero hz.1 (hunit z hz.2))
  refine ⟨hprod, hprod0, ?_⟩
  exact (divisorCurrent_mul_unit_eq hga hu hga0 hunit hprod hprod0).trans hpow

end SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentUnitFactor
