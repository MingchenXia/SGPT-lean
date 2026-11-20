import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingEnergyTail
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-!
# Actual uniform E1 energy truncation tails

Xia SGPT PDF0127--0128, estimate (3.46). Genuine model-type truncations,
actual ordered energy comparison and the produced fixed self-gap excess
bound give a common vanishing tail. No energy-error monotonicity or uniform
convergence certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyUniformTruncationTail

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses DiagonalMass GlobalNonPluripolar
open RelativeEnergyIntegrability FiniteEnergyCharacterization
open SingularModelEnergyTruncation SingularModelIncreasingEnergyTail
open SingularModelFiniteEnergyOrderedComparison
open MongeAmpereEnergyDecreasing

noncomputable section

private theorem canonicalGap_max_eq_positivePart {p v : EReal}
    (hpt : p ≠ ⊤) (hvt : v ≠ ⊤) (hvp : v ≤ p) {C : ℝ} (hC : 0 ≤ C) :
    canonicalERealDiffToReal (max v (p - (C : EReal))) v =
      max ((canonicalERealAbsDiff p v).toReal - C) 0 := by
  cases p using EReal.rec with
  | top => exact (hpt rfl).elim
  | bot =>
    have hvb : v = ⊥ := bot_unique hvp
    subst v
    simp [hC]
  | coe p =>
    cases v using EReal.rec with
    | top => exact (hvt rfl).elim
    | bot =>
      simp only [← EReal.coe_sub, max_eq_right bot_le,
        canonicalERealAbsDiff_bot_right (EReal.coe_ne_bot _), ENNReal.toReal_top,
        zero_sub, max_eq_right (neg_nonpos.mpr hC)]
      simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal, -EReal.coe_sub]
    | coe v =>
      have hvpR : v ≤ p := EReal.coe_le_coe_iff.mp hvp
      rw [canonicalERealAbsDiff_coe_coe, ENNReal.toReal_ofReal (abs_nonneg _),
        abs_of_nonneg (sub_nonneg.mpr hvpR), ← EReal.coe_sub]
      by_cases hvc : v ≤ p - C
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hvc),
          canonicalERealDiffToReal_coe_coe, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr (le_of_not_ge hvc)),
          canonicalERealDiffToReal_coe_coe, max_eq_right (by linarith)]
        ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
private theorem integrable_referenceAbsGap
    (hu : RelativeFiniteEnergy θ φ u hφ) :
    Integrable (fun x => (canonicalERealAbsDiff (φ x) (u x)).toReal)
      (diagonalPotentialMeasure θ u hu.1.plurisubharmonic) := by
  have hpm := hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum := hu.1.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hfin := ((relativeFiniteEnergy_iff θ φ u hφ hu.1.plurisubharmonic).mp hu).2
  exact integrable_toReal_of_lintegral_ne_top (hpm.canonicalERealAbsDiff hum).aemeasurable hfin.ne

/-- Actual ordered finite energies have a truncation error bounded by the
integrable self-gap tail of one fixed smaller finite-energy potential. -/
theorem energy_truncation_error_le_fixed_self_tail (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (huv : u ≤ v) (j : ℕ) :
    0 ≤ (energy θ φ hφ (truncation φ v j)).toReal - (energy θ φ hφ v).toReal ∧
    (energy θ φ hφ (truncation φ v j)).toReal - (energy θ φ hφ v).toReal ≤
      (2 : ℝ) ^ (n + 1) * ∫ x,
        {x | (j : ℝ) / 2 < (canonicalERealAbsDiff (φ x) (u x)).toReal}.indicator
          (fun x => (canonicalERealAbsDiff (φ x) (u x)).toReal) x
        ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic := by
  have hT := relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  have hTE1 : RelativeFiniteEnergyPreceq θ φ (truncation φ v j) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hT
  have hvT : v ≤ truncation φ v j := fun x => le_max_left _ _
  refine ⟨sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono
    omega (preceq_of_relativeFiniteEnergy hv) hTE1 hvT), ?_⟩
  have he := energy_sub_le_integral_smaller_diagonal_of_preceq omega hTE1
    (preceq_of_relativeFiniteEnergy hv) hvT
  have hC : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hgvm :=
    (hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.canonicalERealAbsDiff
      hv.1.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).ennreal_toReal
  have hgum :=
    (hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.canonicalERealAbsDiff
      hu.1.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).ennreal_toReal
  let g := fun x => (canonicalERealAbsDiff (φ x) (v x)).toReal
  let f := fun x => (canonicalERealAbsDiff (φ x) (u x)).toReal
  let A := {x | (j : ℝ) / 2 < f x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hgum
  have hposInt : Integrable (fun x => max (g x - (j : ℝ)) 0)
      (diagonalPotentialMeasure θ v hv.1.plurisubharmonic) :=
    (integrable_referenceAbsGap hv).mono_nonneg
      ((hgvm.sub measurable_const).max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun x => le_max_right _ _) (ae_of_all _ fun x =>
        max_le (sub_le_self _ hC) ENNReal.toReal_nonneg)
  have htailInt := (integrable_referenceAbsGap hu).indicator hA
  have htailNN : ∀ x, 0 ≤ A.indicator f x := fun x =>
    indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x
  have hI := lintegral_referenceGap_excess_le_fixed_tail omega hu.1
    hv.1.plurisubharmonic huv hv.1.le_reference hC
  have hInd : (fun x => ENNReal.ofReal (A.indicator f x)) =
      A.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, ENNReal.ofReal_zero]
  have hreal : (∫ x, max (g x - (j : ℝ)) 0
      ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic) ≤
      (2 : ℝ) ^ (n + 1) * ∫ x, A.indicator f x
        ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (pow_nonneg (by norm_num) _) (integral_nonneg htailNN))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hposInt
        (ae_of_all _ fun x => le_max_right _ _),
      ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal htailInt (ae_of_all _ htailNN), hInd]
    exact hI
  calc
    _ ≤ ∫ x, canonicalERealDiffToReal (truncation φ v j x) (v x)
      ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := he
    _ = ∫ x, max (g x - (j : ℝ)) 0
      ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := integral_congr_ae
        (ae_of_all _ fun x => canonicalGap_max_eq_positivePart
          (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
          (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
          (hv.1.le_reference x) hC)
    _ ≤ _ := hreal

/-- For every fixed lower index, genuine increasing E1 potentials have
actual energy truncation errors tending uniformly to zero in the entire tail. -/
theorem uniform_energy_truncation_error_of_monotone (omega : KahlerBackground n M)
    {uj : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergy θ φ (uj j) hφ)
    (hm : ∀ x, Monotone fun j => uj j x) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ C : ℕ, N ≤ C → ∀ j : ℕ, i ≤ j →
      |(energy θ φ hφ (truncation φ (uj j) C)).toReal -
        (energy θ φ hφ (uj j)).toReal| < ε := by
  let f := fun x => (canonicalERealAbsDiff (φ x) (uj i x)).toReal
  let A := fun C : ℕ => {x | (C : ℝ) / 2 < f x}
  let μ := diagonalPotentialMeasure θ (uj i) (hu i).1.plurisubharmonic
  have hfm : Measurable f :=
    (hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.canonicalERealAbsDiff
      (hu i).1.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).ennreal_toReal
  have hAm (C : ℕ) : MeasurableSet (A C) := measurableSet_lt measurable_const hfm
  have hf : Integrable f μ := integrable_referenceAbsGap (hu i)
  have htail : Tendsto (fun C : ℕ => ∫ x, (A C).indicator f x ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun C : ℕ => ∫ x, (A C).indicator f x ∂μ)
        atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
        (fun C => (hf.indicator (hAm C)).aestronglyMeasurable) hf.norm
        (fun C => ae_of_all _ fun x => norm_indicator_le_norm_self _ _) ?_
      apply ae_of_all
      intro x
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * f x)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with C hNC
      have hCR : (N : ℝ) ≤ C := by exact_mod_cast hNC
      have hx : x ∉ A C := by
        change ¬ (C : ℝ) / 2 < f x
        linarith
      exact (indicator_of_notMem hx f).symm
    simpa only [integral_zero] using h
  have hscaled : Tendsto
      (fun C : ℕ => (2 : ℝ) ^ (n + 1) * ∫ x, (A C).indicator f x ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul htail
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscaled.eventually_lt_const hε)
  refine ⟨N, fun C hNC j hij => ?_⟩
  have hb := energy_truncation_error_le_fixed_self_tail omega (hu i) (hu j)
    (fun x => hm x hij) C
  rw [abs_of_nonneg hb.1]
  exact hb.2.trans_lt (hN C hNC)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyUniformTruncationTail
