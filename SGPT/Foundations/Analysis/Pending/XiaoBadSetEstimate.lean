import SGPT.Foundations.Analysis.Pending.AubinYauMatrixBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

/-!
# Xiao's normalized bad-set estimate and Hermitian trace domination

Source: Xiao, arXiv:1308.2878v2, proof of Theorem 1.2 (published Theorem 1.4),
`references/xiao15-weak-morse/source/tran_morse_aif.tex`, equations `e integral`,
`xe ineq form`, and `alpha ineq`. The bad-set bound isolates the actual measure
argument giving the factor four. It does not assume a bigness criterion.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.XiaoBadSetEstimate

/-- Every positive Hermitian matrix is bounded by its relative trace. -/
theorem quad_le_trace_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (B *ᵥ x)).re ≤
      (A⁻¹ * B).trace.re * (star x ⬝ᵥ (A *ᵥ x)).re := by
  classical
  obtain ⟨lam, hlam, -, htr, -, hquad, -⟩ :=
    AubinYauMatrixBounds.exists_frame hA hB
  apply hquad _ ?_ x
  intro k
  rw [htr, Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact Finset.single_le_sum (fun j _ => (hlam j).le) (Finset.mem_univ k)

/-- A relative trace bound supplies a genuine lower quadratic-form bound. -/
theorem quad_div_le_of_trace_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {T : ℝ} (hT : 0 < T)
    (htrace : (A⁻¹ * B).trace.re ≤ T) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (B *ᵥ x)).re / T ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
  rw [div_le_iff₀ hT]
  have hnonneg : 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
    exact (Complex.nonneg_iff.mp (hA.posSemidef.dotProduct_mulVec_nonneg x)).1
  exact (quad_le_trace_mul hA hB x).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right htrace hnonneg)

/-- The measure estimate producing Xiao's factor four, with actual integrals. -/
theorem integral_ge_of_bad_set {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {c N M : ℝ}
    (hc : 0 ≤ c) (hN : 0 < N) (hM : 0 < M)
    (hint : ∫ x, g x ∂μ = M)
    (hgood : ∀ x, g x < 2 * M → c / (2 * N * M) ≤ f x) :
    c / (4 * N * M) ≤ ∫ x, f x ∂μ := by
  let E : Set X := {x | 2 * M ≤ g x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hgm
  have hmarkov : 2 * M * μ.real E ≤ M := by
    simpa only [E, hint] using
      mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hg0) hg (2 * M)
  have hbad : μ.real E ≤ 1 / 2 := by nlinarith
  have hcomp : 1 / 2 ≤ μ.real Eᶜ := by
    have hsum := measureReal_add_measureReal_compl (μ := μ) hE
    rw [probReal_univ] at hsum
    linarith
  have hfactor : 0 ≤ c / (2 * N * M) := by positivity
  have hrestricted : c / (2 * N * M) * μ.real Eᶜ ≤ ∫ x in Eᶜ, f x ∂μ := by
    calc
      c / (2 * N * M) * μ.real Eᶜ = ∫ _ in Eᶜ, c / (2 * N * M) ∂μ := by
        simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      _ ≤ _ := integral_mono_ae (integrable_const _) hf.integrableOn <|
        (ae_restrict_mem hE.compl).mono fun x hx => hgood x (lt_of_not_ge hx)
  calc
    c / (4 * N * M) = c / (2 * N * M) * (1 / 2) := by ring
    _ ≤ c / (2 * N * M) * μ.real Eᶜ :=
      mul_le_mul_of_nonneg_left hcomp hfactor
    _ ≤ ∫ x in Eᶜ, f x ∂μ := hrestricted
    _ ≤ ∫ x, f x ∂μ := setIntegral_le_integral hf (ae_of_all μ hf0)

end SGPT.Foundations.Analysis.Pending.XiaoBadSetEstimate
