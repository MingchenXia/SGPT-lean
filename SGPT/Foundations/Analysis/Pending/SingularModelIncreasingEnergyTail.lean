import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyOrderedComparison
import Mathlib.MeasureTheory.Integral.Layercake

set_option autoImplicit false

/-!
# Actual fixed self-gap control of increasing energy truncation tails

Xia SGPT PDF0128, the genuine uniform-in-a-tail estimate (3.46).
Actual full-mass distribution comparison and layer cake produce the fixed
lower-endpoint tail bound. General E1 continuity is a separate consumer.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingEnergyTail

open FirstPass FirstPass.PositiveClasses DiagonalMass RelativeEnergy
open RelativeEnergyIntegrability RelativePreceqClasses

noncomputable section

private theorem lintegral_excess_le_tail {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hcomp : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ K * ν {x | t ≤ 2 * g x})
    {C : ℝ} (hC : 0 ≤ C) :
    (∫⁻ x, ENNReal.ofReal (max (f x - C) 0) ∂μ) ≤
      K * (2 * ∫⁻ x, {x | C / 2 < g x}.indicator (fun x => ENNReal.ofReal (g x)) x ∂ν) := by
  have hfC : Measurable (fun x => max (f x - C) 0) := (hf.sub measurable_const).max measurable_const
  have hgC : Measurable (fun x => max (2 * g x - C) 0) :=
    ((hg.const_mul 2).sub measurable_const).max measurable_const
  rw [lintegral_eq_lintegral_meas_lt μ
    (ae_of_all μ fun x => le_max_right (f x - C) (0 : ℝ)) hfC.aemeasurable]
  calc
    (∫⁻ t in Ioi 0, μ {x | t < max (f x - C) 0}) ≤
        ∫⁻ t in Ioi 0, K * ν {x | t ≤ max (2 * g x - C) 0} := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have hS : {x | t < max (f x - C) 0} = {x | C + t < f x} := by
        ext x
        simp only [mem_ofPred_eq, lt_max_iff]
        constructor
        · rintro (h | h) <;> linarith
        · intro h; left; linarith
      have hT : {x | t ≤ max (2 * g x - C) 0} = {x | C + t ≤ 2 * g x} := by
        ext x
        simp only [mem_ofPred_eq, le_max_iff]
        constructor
        · rintro (h | h) <;> linarith
        · intro h; left; linarith
      rw [hS, hT]
      exact hcomp (C + t) (by linarith)
    _ = K * ∫⁻ x, ENNReal.ofReal (max (2 * g x - C) 0) ∂ν := by
      rw [lintegral_const_mul' _ _ hK]
      rw [← lintegral_eq_lintegral_meas_le ν
        (ae_of_all ν fun x => le_max_right (2 * g x - C) (0 : ℝ))
        hgC.aemeasurable]
    _ ≤ K * ∫⁻ x, 2 * {x | C / 2 < g x}.indicator
        (fun x => ENNReal.ofReal (g x)) x ∂ν := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (max (2 * g x - C) 0) ≤
        2 * {x | C / 2 < g x}.indicator (fun x => ENNReal.ofReal (g x)) x
      by_cases hx : C / 2 < g x
      · rw [indicator_of_mem (s := {x | C / 2 < g x}) hx, ← ENNReal.ofReal_ofNat (n := 2),
          ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (max_le (by linarith) (by linarith))
      · rw [indicator_of_notMem (s := {x | C / 2 < g x}) hx, mul_zero]
        have h : 2 * g x - C ≤ 0 := by linarith
        simp only [max_eq_right h, ENNReal.ofReal_zero]
        exact le_rfl
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

private theorem real_referenceGap_of_finite_order {a b : EReal}
    (hat : a ≠ ⊤) (hbt : b ≠ ⊤) (hab : a ≠ ⊥) (hbb : b ≠ ⊥) (hba : b ≤ a) :
    (canonicalERealAbsDiff a b).toReal = a.toReal - b.toReal := by
  have hR := EReal.toReal_le_toReal hba hbb hat
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hbt hbb]
  simp only [canonicalERealAbsDiff_coe_coe, EReal.toReal_coe,
    abs_of_nonneg (sub_nonneg.mpr hR)]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hR)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual relative fundamental distribution estimate also holds in
dimension zero, by the genuine null-pole and empty-tuple producers. -/
theorem diagonalPotentialMeasure_superlevel_le_all_dim
    (omega : KahlerBackground n M) (hu : RelativeFullMass θ φ u hφ)
    (hv : IsThetaPshPotential θ.val v) (huv : u ≤ v) (hvφ : v ≤ φ)
    {t : ℝ} (ht : 0 < t) :
    diagonalPotentialMeasure θ v hv {x | t < (canonicalERealAbsDiff (φ x) (v x)).toReal} ≤
      2 ^ n * diagonalPotentialMeasure θ u hu.plurisubharmonic
        {x | t ≤ 2 * (canonicalERealAbsDiff (φ x) (u x)).toReal} := by
  by_cases hn : 0 < n
  · exact RelativeFullMassEnergyUpwardClosure.diagonalPotentialMeasure_superlevel_le hn
      omega hu hv huv hvφ ht
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have heq : diagonalPotentialMeasure θ v hv = diagonalPotentialMeasure θ u hu.plurisubharmonic :=
    GlobalDiagonalScaling.globalMixedMeasure_congr rfl (by funext i; exact Fin.elim0 i) _ _
  rw [heq, pow_zero, one_mul]
  have hae : ∀ᵐ x ∂diagonalPotentialMeasure θ u hu.plurisubharmonic, u x ≠ ⊥ :=
    ae_iff.mpr (by simpa only [not_not] using
      FiniteEnergyCharacterization.diagonalPotentialMeasure_pole_null θ hu.plurisubharmonic)
  apply measure_mono_ae
  filter_upwards [hae] with x hub
  intro hx
  have hvb : v x ≠ ⊥ := ne_bot_of_le_ne_bot hub (huv x)
  have hpb : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hvb (hvφ x)
  have hut := hu.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x
  have hvt := hv.1.quasiPlurisubharmonic.ne_top x
  have hpt := hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x
  have huvR := EReal.toReal_le_toReal (huv x) hub hvt
  have hvφR := EReal.toReal_le_toReal (hvφ x) hvb hpt
  change t < (canonicalERealAbsDiff (φ x) (v x)).toReal at hx
  change t ≤ 2 * (canonicalERealAbsDiff (φ x) (u x)).toReal
  rw [real_referenceGap_of_finite_order hpt hvt hpb hvb (hvφ x)] at hx
  rw [real_referenceGap_of_finite_order hpt hut hpb hub ((huv x).trans (hvφ x))]
  linarith

/-- Actual full-mass comparison and layer cake bound the larger potential's
self-gap excess by one fixed lower-endpoint self-gap tail. -/
theorem lintegral_referenceGap_excess_le_fixed_tail
    (omega : KahlerBackground n M) (hu : RelativeFullMass θ φ u hφ)
    (hv : IsThetaPshPotential θ.val v) (huv : u ≤ v) (hvφ : v ≤ φ)
    {C : ℝ} (hC : 0 ≤ C) :
    (∫⁻ x, ENNReal.ofReal (max ((canonicalERealAbsDiff (φ x) (v x)).toReal - C) 0)
      ∂diagonalPotentialMeasure θ v hv) ≤
      2 ^ (n + 1) * ∫⁻ x,
        {x | C / 2 < (canonicalERealAbsDiff (φ x) (u x)).toReal}.indicator
          (fun x => ENNReal.ofReal (canonicalERealAbsDiff (φ x) (u x)).toReal) x
        ∂diagonalPotentialMeasure θ u hu.plurisubharmonic := by
  have hpm := hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum := hu.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hf := (hpm.canonicalERealAbsDiff hvm).ennreal_toReal
  have hg := (hpm.canonicalERealAbsDiff hum).ennreal_toReal
  have h := lintegral_excess_le_tail hf hg
    (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    (fun t ht => diagonalPotentialMeasure_superlevel_le_all_dim omega hu hv huv hvφ ht) hC
  simpa only [pow_succ, mul_assoc] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingEnergyTail
