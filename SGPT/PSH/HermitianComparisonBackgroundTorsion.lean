import SGPT.PSH.HermitianComparisonLowerTrace

/-!
# Uniform local torsion budgets for the actual Hermitian expansion

The complete ordinary BT term is removed before estimating. The remaining
terms are bounded by strict-set masses of lower ordinary traces, with one
constant chosen from the compact geometry before every potential.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonBackgroundTorsion

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.PSH.HermitianComparisonOneFactor SGPT.PSH.HermitianComparisonCutoff
  SGPT.PSH.HermitianComparisonDensity SGPT.PSH.HermitianComparisonTorsion
  SGPT.PSH.HermitianComparisonLowerTrace
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U : Opens (ComplexModel n)}

def derivativeWeight {ι : Type*} [Fintype ι] (D : ι → Residual n U)
    (φ : 𝓓(U, ℝ)) (f : ComplexModel n → ℝ) : ℝ :=
  ∑ i, ddcWedgePairing (by omega : 0 + (D i).degree = (D i).degree)
    (D i).positive (D i).form scalarUnit φ f

def properCorrectedTraceBudget (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (A : Set (ComplexModel n)) : ℝ := by
  classical
  exact ∑ s : Finset (Fin p) with s.card < p,
    ((backgroundResidual p T hT hTc v hv hσ s).positive.traceMeasure A).toReal

/-- Genuine torsion control uniform in every bounded potential. The
ordinary BT summand with all factors selected contributes exactly zero;
only strictly lower selected-factor traces occur in the budget. -/
theorem exists_background_derivative_setMass_bound
    (p : ℕ) {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T : LocalProductCurrent n U (1 + p))
      (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
      (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
      (φ : 𝓓(U, ℝ)), tsupport φ ⊆ K → (∀ x, |φ x| ≤ 1) →
      ∀ (A : Set (ComplexModel n)), MeasurableSet A → ∀ δ : ℝ, 0 ≤ δ →
      ∀ (f : ComplexModel n → ℝ), Measurable f →
        (∀ x ∈ U, |f x| ≤ δ) → (∀ x ∈ U, x ∉ A → f x = 0) →
        |derivativeWeight (backgroundResidual p T hT hTc v hv hσ) φ f| ≤
          B * δ * properCorrectedTraceBudget p T hT hTc v hv hσ (A ∩ K) := by
  classical
  let α : (s : Finset (Fin p)) → ComplexModel n → RealForm n (2 * (p - s.card)) :=
    fun s x => wedgeProd (p - s.card) (fun _ => σ x)
  have hα : ∀ s, ContDiffOn ℝ ∞ (α s) U := fun s =>
    contDiffOn_wedgeProd (p - s.card) (fun _ => σ) (fun _ => hσ)
  choose C hC hbound using fun s : Finset (Fin p) =>
    exists_ddcWedgePairing_setMass_bound (by omega : 0 + (p - s.card) = p - s.card)
      (hα s) hK hKU (scalarUnit (n := n))
  let B : ℝ := ∑ s : Finset (Fin p), C s
  have hB : 0 ≤ B := Finset.sum_nonneg (fun s _ => hC s)
  refine ⟨B, hB, ?_⟩
  intro T hT hTc v hv φ hφK hφ A hA δ hδ f hf hfb hfzero
  let D := backgroundResidual p T hT hTc v hv hσ
  let F : Finset (Fin p) → ℝ := fun s =>
    ddcWedgePairing (by omega : 0 + (D s).degree = (D s).degree)
      (D s).positive (D s).form scalarUnit φ f
  have hsum : derivativeWeight D φ f = ∑ s : Finset (Fin p) with s.card < p, F s := by
    apply (Finset.sum_subset (Finset.filter_subset (fun s : Finset (Fin p) => s.card < p)
      Finset.univ) ?_).symm
    intro s _ hnot
    have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
    have hfull : s.card = p := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      omega
    exact ddcWedgePairing_backgroundResidual_full p T hT hTc v hv hσ s hfull φ f
  have hterm : ∀ s : Finset (Fin p), |F s| ≤ B * δ *
      ((D s).positive.traceMeasure (A ∩ K)).toReal := by
    intro s
    have h := hbound s (D s).current (D s).positive φ hφK hφ A hA δ hδ f hf hfb hfzero
    change |F s| ≤ C s * δ * ((D s).positive.traceMeasure (A ∩ K)).toReal at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun t _ => hC t) (Finset.mem_univ s)) hδ)
      ENNReal.toReal_nonneg)
  rw [hsum]
  calc
    _ ≤ ∑ s : Finset (Fin p) with s.card < p,
        B * δ * ((D s).positive.traceMeasure (A ∩ K)).toReal :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hterm s)
    _ = B * δ * properCorrectedTraceBudget p T hT hTc v hv hσ (A ∩ K) := by
      exact (Finset.mul_sum _ _ _).symm

end SGPT.PSH.HermitianComparisonBackgroundTorsion
