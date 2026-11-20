import SGPT.Foundations.Analysis.Pending.CompactCollarCutoff
import SGPT.Foundations.Analysis.Pending.CurveWeightedClosedForms

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.CurveCollarBackground

open FirstPass FirstPass.PositiveClasses ManifoldTubePositivity
open CurveWeightedClosedForms CompactCollarCutoff

noncomputable section

/-- Actual inverse-chart continuity transports a zero neighborhood to a zero
germ; only target coefficients are asserted. -/
theorem ddcClosedForm_coeff_eq_zero_of_locally_zero {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ρ : M → ℝ} (hρ : ChartSmooth (n := n) ρ) {N : Set M} (hN : IsOpen N)
    (hzero : ∀ x ∈ N, ρ x = 0) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) (hzN : e.val.symm z ∈ N) :
    (ddcClosedForm ρ hρ).val.coeff e z = 0 := by
  rw [ddcClosedForm_coeff]
  have heq : (fun w => ρ (e.val.symm w)) =ᶠ[𝓝 z] fun _ => 0 := by
    have hmem := (e.val.continuousAt_symm hz) (hN.mem_nhds hzN)
    filter_upwards [hmem] with w hw
    exact hzero _ hw
  rw [smoothDDC_congr heq, smoothDDC_zero]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M]

/-- Actual closed curve background with scalar weight `D*C*(-ρ)`. -/
def curveCollarBackground (ω : KahlerBackground 1 M) (D C : ℝ)
    (ρ : M → ℝ) (hρ : ChartSmooth (n := 1) ρ) : ClosedRealOneOneForm 1 M :=
  curveWeightedClosedForm (fun x => D * C * (-ρ x))
    (fun e => contDiffOn_const.mul (hρ e).neg) ω.form

@[simp] theorem curveCollarBackground_coeff (ω : KahlerBackground 1 M) (D C : ℝ)
    (ρ : M → ℝ) (hρ : ChartSmooth (n := 1) ρ) (e : ComplexChart 1 M)
    (z : ComplexModel 1) :
    (curveCollarBackground ω D C ρ hρ).val.coeff e z =
      (D * C * (-ρ (e.val.symm z))) • ω.form.val.coeff e z := rfl

/-- Both cutoffs and the curvature buffer are produced from actual compact
collars; no curvature or semipositivity certificate is an input. -/
theorem exists_curveCollarBackground [CompactSpace M] (ω : KahlerBackground 1 M)
    {K V₁ V₂ : Set M} (hK : IsCompact K) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hKV₁ : K ⊆ V₁) (hV₁V₂ : closure V₁ ⊆ V₂) (D : ℝ) (hD : 0 ≤ D) :
    ∃ (ρin ρout : M → ℝ) (hin : ChartSmooth (n := 1) ρin)
      (hout : ChartSmooth (n := 1) ρout) (C : ℝ),
      0 < C ∧ (∀ x, -1 ≤ ρin x) ∧ (∀ x, ρin x ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ρin x = 0) ∧
      (∀ x ∉ V₁, ρin x = -1) ∧
      (∀ x, -1 ≤ ρout x) ∧ (∀ x, ρout x ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ closure V₁ ⊆ N ∧ ∀ x ∈ N, ρout x = 0) ∧
      (∀ x ∉ V₂, ρout x = -1) ∧
      (curveCollarBackground ω D C ρin hin).val.IsSemipositive ∧
      (curveCollarBackground ω D C ρin hin + D • ddcClosedForm ρout hout).val.IsSemipositive := by
  obtain ⟨ρin, hin, hinlow, hinup, hinN, hinoff⟩ :=
    exists_chartSmooth_collar (n := 1) hK hV₁ hKV₁
  obtain ⟨ρout, hout, houtlow, houtup, houtN, houtoff, C, hC, hbound⟩ :=
    exists_chartSmooth_collar_ddc_lower ω isClosed_closure.isCompact hV₂ hV₁V₂
  have hκ : (curveCollarBackground ω D C ρin hin).val.IsSemipositive :=
    curveWeightedClosedForm_isSemipositive _
      (fun x => mul_nonneg (mul_nonneg hD hC.le) (neg_nonneg.mpr (hinup x)))
      ω.isSemipositive
  refine ⟨ρin, ρout, hin, hout, C, hC, hinlow, hinup, hinN, hinoff,
    houtlow, houtup, houtN, houtoff, hκ, ?_⟩
  intro e z hz v
  by_cases hy : e.val.symm z ∈ V₁
  · obtain ⟨N, hN, hV₁N, hzero⟩ := houtN
    have hddc := ddcClosedForm_coeff_eq_zero_of_locally_zero hout hN hzero e hz
      (hV₁N (subset_closure hy))
    simpa only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      hddc, smul_zero, add_zero] using hκ e z hz v
  · have hpos := mul_nonneg hD (hbound e z hz v)
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply] at hpos ⊢
    rw [curveCollarBackground_coeff, hinoff _ hy]
    simp only [neg_neg, mul_one, ContinuousAlternatingMap.smul_apply]
    simp only [smul_eq_mul] at hpos ⊢
    nlinarith

end

end SGPT.Foundations.Analysis.Pending.CurveCollarBackground
