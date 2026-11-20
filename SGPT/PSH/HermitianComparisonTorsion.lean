import SGPT.PSH.HermitianComparisonMollifier

/-!
# Uniform genuine Borel bounds for the nonclosed smooth residual

The bound is chosen from the residual form and the compact coordinate set
before any Bedford--Taylor factor. It controls the actual Hessian-density
extension on bounded Borel weights, so strict-set indicators and positive
parts are covered without an assumed derivative measure.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonTorsion

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.PSH.HermitianComparisonDensity SGPT.PSH.HermitianComparisonOneFactor
  SGPT.PSH.HermitianComparisonCutoff
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n r k m : ℕ} {U : Opens (ComplexModel n)}

/-- The actual Borel extension of `ddᶜ(R∧α)` has uniform local order zero.
The constant depends on the smooth form, compact set and complementary
form, and is chosen BEFORE every positive current and Borel weight. -/
theorem exists_ddcWedgePairing_compact_bound (h' : r + k = m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (γ : formSpan n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : LocalProductCurrent n U (m + 1))
      (hR : IsPositive R) (φ : 𝓓(U, ℝ)), tsupport φ ⊆ K →
      ∀ (f : ComplexModel n → ℝ), Measurable f → IsLocallyBoundedOn f U →
        |ddcWedgePairing h' hR α γ φ f| ≤
          C * ∫ x, |φ x * f x| ∂hR.traceMeasure := by
  classical
  let I := Fin (Module.finrank ℝ (formSpan n k)) × Fin (n * 2) × Fin (n * 2)
  let g : I → ComplexModel n → ℝ := fun i =>
    hessFun i.2.1 i.2.2 (formCoeff α i.1)
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) U := fun i =>
    contDiffOn_hessFun (contDiffOn_formCoeff hα i.1) i.2.1 i.2.2
  choose B₀ hB₀ using fun i : I =>
    hK.exists_bound_of_continuousOn ((hg i).continuousOn.mono hKU)
  let B : I → ℝ := fun i => max (B₀ i) 0
  have hB : ∀ i, 0 ≤ B i := fun i => le_max_right _ _
  have hgb : ∀ i x, x ∈ K → |g i x| ≤ B i := by
    intro i x hx
    have hb : |g i x| ≤ B₀ i := by simpa only [Real.norm_eq_abs] using hB₀ i x hx
    exact hb.trans (le_max_left _ _)
  let β : I → formSpan n (m + 1) := fun i =>
    wedgeLM m (isOneOne_coeffForm i.2.1 i.2.2)
      (wedgeSpan n h' γ (formBasis n k i.1))
  choose D hD hD₁ hD₂ using fun i : I => exists_orderUnit (β i).2
  let C : ℝ := (1 / (4 * Real.pi)) * ∑ i, B i * D i
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hB i) (hD i))
  refine ⟨C, hC, ?_⟩
  intro R hR φ hφK f hf hfb
  obtain ⟨M, hM⟩ := hfb (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  have hφf : Integrable (fun x => φ x * f x) hR.traceMeasure :=
    hR.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
      hf.aestronglyMeasurable ⟨M, hM⟩
  have hterm : ∀ i : I,
      |∫ x, f x * (φ x * ((U : Set (ComplexModel n)).indicator (g i) x *
          hR.density (β i) x)) ∂hR.traceMeasure| ≤
        (B i * D i) * ∫ x, |φ x * f x| ∂hR.traceMeasure := by
    intro i
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hφf.abs.const_mul _)
    filter_upwards [abs_density_le_of_orderUnit hR (β i) (hD₁ i) (hD₂ i)] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem (hKU hxK)]
      simp only [Real.norm_eq_abs, abs_mul]
      have hb := mul_le_mul (hgb i x hxK) hx (abs_nonneg _) (hB i)
      have hb' := mul_le_mul_of_nonneg_left hb
        (mul_nonneg (abs_nonneg (φ x)) (abs_nonneg (f x)))
      nlinarith only [hb']
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hxK (hφK hs))
      simp only [hφ, zero_mul, mul_zero, norm_zero, abs_zero, le_refl]
  change |∑ i : I, (-(1 / (4 * Real.pi))) *
      ∫ x, f x * (φ x * ((U : Set (ComplexModel n)).indicator (g i) x *
        hR.density (β i) x)) ∂hR.traceMeasure| ≤ _
  calc
    _ ≤ ∑ i : I, (1 / (4 * Real.pi)) *
        ((B i * D i) * ∫ x, |φ x * f x| ∂hR.traceMeasure) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi))]
      exact mul_le_mul_of_nonneg_left (hterm i) (by positivity)
    _ = C * ∫ x, |φ x * f x| ∂hR.traceMeasure := by
      simp only [C, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A constant residual contributes no torsion, including at arbitrary
bounded Borel weights. This removes the full-degree ordinary BT term from
the background expansion before estimating lower traces. -/
theorem ddcWedgePairing_const (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R)
    (α : RealForm n (2 * k)) (γ : formSpan n r) (φ : 𝓓(U, ℝ))
    (f : ComplexModel n → ℝ) :
    ddcWedgePairing h' hR (fun _ => α) γ φ f = 0 := by
  unfold ddcWedgePairing
  apply Finset.sum_eq_zero
  intro i _
  have he : hessFun i.2.1 i.2.2 (formCoeff (fun _ : ComplexModel n => α) i.1) =
      fun _ => (0 : ℝ) := by
    have hcoeff : formCoeff (fun _ : ComplexModel n => α) i.1 =
        fun _ => (coeffCLM n k i.1) α := rfl
    rw [hcoeff]
    funext z
    change (fderiv ℝ (fun x : ComplexModel n =>
      fderiv ℝ (fun _ : ComplexModel n => (coeffCLM n k i.1) α) x
        (realBasis n i.2.2)) z) (realBasis n i.2.1) = 0
    simp only [fderiv_const_apply, zero_apply]
  change (-(1 / (4 * Real.pi))) * ∫ x, f x * (φ x *
    ((U : Set (ComplexModel n)).indicator
      (hessFun i.2.1 i.2.2 (formCoeff (fun _ : ComplexModel n => α) i.1)) x *
        hR.density _ x)) ∂hR.traceMeasure = 0
  simp only [he, indicator_zero, zero_mul, mul_zero, integral_zero]

/-- A single geometry constant bounds every actual finite residual sum.
It is selected before the positive closed factors, and thus before all
bounded potential inputs in a Hermitian background expansion. -/
theorem exists_finite_ddcWedgePairing_compact_bound {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (α : ∀ i, ComplexModel n → RealForm n (2 * k i))
    (hα : ∀ i, ContDiffOn ℝ ∞ (α i) U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ∀ i, LocalProductCurrent n U (k i + 1))
      (hR : ∀ i, IsPositive (R i)) (φ : 𝓓(U, ℝ)), tsupport φ ⊆ K →
      ∀ (f : ComplexModel n → ℝ), Measurable f → IsLocallyBoundedOn f U →
        |∑ i, ddcWedgePairing (by omega : 0 + k i = k i) (hR i)
          (α i) SGPT.PSH.HermitianComparisonCutoff.scalarUnit φ f| ≤
          C * ∑ i, ∫ x, |φ x * f x| ∂(hR i).traceMeasure := by
  classical
  choose C hC hbound using fun i => exists_ddcWedgePairing_compact_bound
    (by omega : 0 + k i = k i) (hα i) hK hKU
      SGPT.PSH.HermitianComparisonCutoff.scalarUnit
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro R hR φ hφK f hf hfb
  calc
    _ ≤ ∑ i, C i * ∫ x, |φ x * f x| ∂(hR i).traceMeasure :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => hbound i (R i) (hR i) φ hφK f hf hfb)
    _ ≤ ∑ i, (∑ j, C j) * ∫ x, |φ x * f x| ∂(hR i).traceMeasure := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
        (integral_nonneg fun _ => abs_nonneg _)
    _ = (∑ j, C j) * ∑ i, ∫ x, |φ x * f x| ∂(hR i).traceMeasure :=
      (Finset.mul_sum _ _ _).symm

/-- Uniform local torsion control by the trace mass of the actual comparison
set. The weight vanishes off that set and is bounded there by the gap `δ`.
The constant is chosen before the current, set, weight and gap. -/
theorem exists_ddcWedgePairing_setMass_bound (h' : r + k = m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (γ : formSpan n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : LocalProductCurrent n U (m + 1))
      (hR : IsPositive R) (φ : 𝓓(U, ℝ)), tsupport φ ⊆ K → (∀ x, |φ x| ≤ 1) →
      ∀ (A : Set (ComplexModel n)), MeasurableSet A → ∀ δ : ℝ, 0 ≤ δ →
      ∀ (f : ComplexModel n → ℝ), Measurable f →
        (∀ x ∈ U, |f x| ≤ δ) → (∀ x ∈ U, x ∉ A → f x = 0) →
        |ddcWedgePairing h' hR α γ φ f| ≤
          C * δ * (hR.traceMeasure (A ∩ K)).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_ddcWedgePairing_compact_bound h' hα hK hKU γ
  refine ⟨C, hC, ?_⟩
  intro R hR φ hφK hφ A hA δ hδ f hf hfb hfzero
  have hflb : IsLocallyBoundedOn f U := fun L _ hLU =>
    ⟨δ, fun x hx => hfb x (hLU hx)⟩
  have hφf : Integrable (fun x => φ x * f x) hR.traceMeasure :=
    hR.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
      hf.aestronglyMeasurable ⟨δ, fun x hx => hfb x (φ.tsupport_subset hx)⟩
  have hAK := hA.inter hK.measurableSet
  have hfin : hR.traceMeasure (A ∩ K) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt (hR.traceMeasure_lt_top hK hKU)
  have hmajor : Integrable ((A ∩ K).indicator (fun _ => δ)) hR.traceMeasure :=
    (integrable_indicator_iff hAK).mpr (integrableOn_const hfin.ne)
  have hpoint : ∀ x, |φ x * f x| ≤ (A ∩ K).indicator (fun _ => δ) x := by
    intro x
    by_cases hxK : x ∈ K
    · by_cases hxA : x ∈ A
      · rw [indicator_of_mem (show x ∈ A ∩ K from ⟨hxA, hxK⟩), abs_mul]
        exact (mul_le_mul (hφ x) (hfb x (hKU hxK)) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul δ)
      · rw [hfzero x (hKU hxK) hxA, mul_zero, abs_zero,
          indicator_of_notMem (fun h => hxA h.1)]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hxK (hφK hs))
      rw [hφx, zero_mul, abs_zero, indicator_of_notMem (fun h => hxK h.2)]
  have hi : (∫ x, |φ x * f x| ∂hR.traceMeasure) ≤
      δ * (hR.traceMeasure (A ∩ K)).toReal := by
    have hle := integral_mono hφf.abs hmajor hpoint
    rw [integral_indicator_const δ hAK, smul_eq_mul, measureReal_def] at hle
    simpa only [mul_comm] using hle
  calc
    _ ≤ C * ∫ x, |φ x * f x| ∂hR.traceMeasure := hbound R hR φ hφK f hf hflb
    _ ≤ C * (δ * (hR.traceMeasure (A ∩ K)).toReal) := mul_le_mul_of_nonneg_left hi hC
    _ = C * δ * (hR.traceMeasure (A ∩ K)).toReal := (mul_assoc _ _ _).symm

/-- The full ordinary Bedford--Taylor term has a constant degree-zero
residual, so it contributes exactly zero to the unlocalized torsion.
Every surviving subset therefore has strictly fewer selected BT factors. -/
theorem ddcWedgePairing_backgroundResidual_full (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) (hcard : s.card = p)
    (φ : 𝓓(U, ℝ)) (f : ComplexModel n → ℝ) :
    ddcWedgePairing (by omega : 0 + (backgroundResidual p T hT hTc v hv hσ s).degree =
      (backgroundResidual p T hT hTc v hv hσ s).degree)
      (backgroundResidual p T hT hTc v hv hσ s).positive
      (backgroundResidual p T hT hTc v hv hσ s).form scalarUnit φ f = 0 := by
  have hc : ∀ z w : ComplexModel n,
      (backgroundResidual p T hT hTc v hv hσ s).form z =
        (backgroundResidual p T hT hTc v hv hσ s).form w := by
    intro z w
    change wedgeProd (p - s.card) (fun _ => σ z) =
      wedgeProd (p - s.card) (fun _ => σ w)
    rw [hcard, Nat.sub_self]
    rfl
  have he : (backgroundResidual p T hT hTc v hv hσ s).form =
      fun _ => (backgroundResidual p T hT hTc v hv hσ s).form 0 :=
    funext fun z => hc z 0
  rw [he]
  exact ddcWedgePairing_const _ _ _ _ _ _

end SGPT.PSH.HermitianComparisonTorsion
