import SGPT.Okounkov.TranscendentalSkodaSurjective
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Skoda curvature with an additional smooth psh weight

The kernel-bundle Hörmander estimate accepts a general smooth weight, but
the existing Skoda division theorem specializes it to `p log |G|²`.  This
file proves the curvature and data bounds for the additional smooth psh
weight `ψ`, with the same constants and the same actual Skoda lifting.
It is a preliminary to weighted division, not the division theorem itself:
the weighted integral estimates and the singular-psh limiting argument
remain to be established.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter
open scoped Topology ComplexConjugate ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Okounkov.TranscendentalSkoda

variable {n R : ℕ}

/-- Adding a smooth psh weight can only increase the vector Levi form. -/
theorem vectorLevi_le_add_smooth_psh {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ ψ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D)
    (hψ : ContDiffOn ℝ ∞ ψ D)
    (hpsh : PlurisubharmonicOn (fun z => (ψ z : EReal)) D)
    {z : ComplexModel n} (hz : z ∈ D) (α : Fin R → Fin n → ℂ) :
    vectorLevi Φ z α ≤ vectorLevi (fun y => Φ y + ψ y) z α := by
  have hΦ₂ : ContDiffAt ℝ 2 Φ z :=
    (hΦ.contDiffAt (hD.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hψ₂ : ContDiffAt ℝ 2 ψ z :=
    (hψ.contDiffAt (hD.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq : vectorLevi (fun y => Φ y + ψ y) z α =
      vectorLevi Φ z α + vectorLevi ψ z α := by
    unfold vectorLevi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact leviForm_add hΦ₂ hψ₂ _
  have hnonneg : 0 ≤ vectorLevi ψ z α := by
    unfold vectorLevi
    apply Finset.sum_nonneg
    intro i _
    exact leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := ⟨D, hD⟩)
      hψ hpsh hz _
  rw [heq]
  linarith

/-- The Skoda curvature inequality survives an arbitrary smooth psh weight. -/
theorem skoda_curvature_add_smooth_psh {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hn : 0 < n) {G : Fin R → ComplexModel n → ℂ}
    (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {p : ℝ} (hp : (n : ℝ) < p)
    {ψ : ComplexModel n → ℝ} (hψ : ContDiffOn ℝ ∞ ψ D)
    (hpsh : PlurisubharmonicOn (fun z => (ψ z : EReal)) D)
    {z : ComplexModel n} (hz : z ∈ D) {α : Fin R → Fin n → ℂ}
    (hα : InKernel G z α) :
    ((p - n) / (2 * n)) * secondFundamental G z α ≤
      vectorLevi (fun y => p * Real.log (generatorNormSq G y) + ψ y) z α -
        (1 + (p - n) / (2 * n)) * secondFundamental G z α := by
  have hbase := skodaWeight_curvature hD hn hG hpos hp hz hα
  have hadd := vectorLevi_le_add_smooth_psh hD
    (contDiffOn_skodaWeight hD hG hpos p) hψ hpsh hz α
  linarith

/-- The same extra weight preserves the pointwise right-hand side needed for
the kernel-bundle Hörmander estimate. -/
theorem skodaForm_twisted_bound_add_smooth_psh {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hn : 0 < n) {G : Fin R → ComplexModel n → ℂ}
    (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z)
    {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f D)
    {p : ℝ} (hp : (n : ℝ) < p)
    {ψ : ComplexModel n → ℝ} (hψ : ContDiffOn ℝ ∞ ψ D)
    (hpsh : PlurisubharmonicOn (fun z => (ψ z : EReal)) D)
    {z : ComplexModel n} (hz : z ∈ D) {α : Fin R → Fin n → ℂ}
    (hα : InKernel G z α) :
    ‖∑ i, ∑ j, conj (α i j) * skodaForm G f i j z‖ ^ 2 ≤
      ‖f z‖ ^ 2 / ((p - n) / (2 * n) * generatorNormSq G z) *
        (vectorLevi (fun y => p * Real.log (generatorNormSq G y) + ψ y) z α -
          (1 + (p - n) / (2 * n)) * secondFundamental G z α) := by
  have hbase := skodaForm_twisted_bound hD hn hG hpos hf hp hz hα
  have hadd := vectorLevi_le_add_smooth_psh hD
    (contDiffOn_skodaWeight hD hG hpos p) hψ hpsh hz α
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < (p - n) / (2 * n) := div_pos (by linarith) (by positivity)
  have hcoeff : 0 ≤ ‖f z‖ ^ 2 / ((p - n) / (2 * n) * generatorNormSq G z) :=
    div_nonneg (sq_nonneg _) (mul_nonneg ht.le (hpos z hz).le)
  exact hbase.trans (mul_le_mul_of_nonneg_left (by linarith) hcoeff)

/-- The numerator used in the Hörmander bound has the desired extra
`exp(-ψ)` factor, with no change to its division constant. -/
theorem skoda_g_mul_exp_add {S t p a ψ : ℝ} (hS : 0 < S) :
    a / (t * S) * Real.exp (-(p * Real.log S + ψ)) =
      (a * S ^ (-(p + 1)) / t) * Real.exp (-ψ) := by
  rw [show -(p * Real.log S + ψ) = -(p * Real.log S) + -ψ by ring, Real.exp_add]
  rw [← mul_assoc, skoda_g_mul_exp hS]

/-- Nonnegative cutoff shifts preserve the same weighted majorant. -/
theorem skoda_g_mul_exp_add_shift_le {S t p a ψ lam : ℝ}
    (hS : 0 < S) (ht : 0 < t) (ha : 0 ≤ a) (hlam : 0 ≤ lam) :
    a / (t * S) * Real.exp (-(p * Real.log S + ψ + lam)) ≤
      (a * S ^ (-(p + 1)) / t) * Real.exp (-ψ) := by
  calc
    _ ≤ a / (t * S) * Real.exp (-(p * Real.log S + ψ)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ha (mul_nonneg ht.le hS.le))
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := skoda_g_mul_exp_add hS

end SGPT.NAPotential.GAGAMult
