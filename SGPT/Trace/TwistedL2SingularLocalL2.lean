import SGPT.Trace.TwistedL2SingularCompact

/-!
# Local square integrability from the singular weighted estimate

On a compact set, a quasi-psh weight is bounded above. Thus a finite weighted
`L²` error, a bounded smooth datum, and an upper bound for `a + b` imply local
unweighted square integrability of the holomorphic correction. This is the
local step needed to apply analytic removability on an exhaustion sublevel.
The estimates are proved from the stated weighted bound and local hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- The weighted correction bound implies unweighted local `L²` on each
compact set whose non-pole part belongs to the region of the weighted bound. -/
theorem locally_sq_integrable_of_weighted_difference
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G S : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {U K : Set X} (hK : IsCompact K)
    (hKU : K \ {x | ψ x = ⊥} ⊆ U)
    (hI : ∫⁻ x in U, ENNReal.ofReal
      (‖G x - S x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ < ⊤) :
    ∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ < ⊤ := by
  have hloc : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isSmoothPositiveVolume hμ
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  obtain ⟨CG, hCG⟩ := hK.exists_bound_of_continuousOn
    ((continuous_norm_of_isSmoothSectionOn L hG).continuousOn.mono (subset_univ K))
  obtain ⟨Mψ, hMψ⟩ := exists_le_coe_of_isCompact hqpsh hK
  set A : Set X := {x | ψ x = ⊥}
  set f : X → ℝ := fun x => ‖G x - S x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)
  set κ : ℝ := 2 * (M * Real.exp Mψ)
  have hKA : MeasurableSet (K \ A) := hK.isClosed.measurableSet.diff hcl.measurableSet
  have hpt : ∀ x ∈ K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ≤
      ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) := by
    intro x hx
    have hab : 0 < a x + b x := add_pos (ha0 x) (hb0 x)
    have hM0 : 0 ≤ M := hab.le.trans (hM x)
    have hψbot : ψ x ≠ ⊥ := hx.2
    have hφle : (ψ x).toReal ≤ Mψ := by
      have h := hMψ x hx.1
      rw [← EReal.coe_toReal (htop x) hψbot] at h
      exact_mod_cast h
    have hf0 : 0 ≤ f x := by dsimp [f]; positivity
    have hκ0 : 0 ≤ κ := by dsimp [κ]; positivity
    rw [← ENNReal.ofReal_mul hκ0,
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hκ0 hf0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hG' : ‖G x‖ ≤ CG :=
      (Real.norm_eq_abs _ ▸ (le_abs_self _)).trans (hCG x hx.1)
    have hexp : Real.exp ((ψ x).toReal) ≤ Real.exp Mψ := Real.exp_le_exp.mpr hφle
    have hGS : ‖G x - S x‖ ^ 2 =
        (a x + b x) * Real.exp ((ψ x).toReal) * f x := by
      dsimp [f]
      field_simp
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hnorm : ‖S x‖ ≤ ‖G x‖ + ‖G x - S x‖ := by
      calc ‖S x‖ = ‖G x - (G x - S x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hsq : ‖S x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖G x - S x‖ ^ 2 := by
      nlinarith [norm_nonneg (S x), norm_nonneg (G x), norm_nonneg (G x - S x),
        sq_nonneg (‖G x‖ - ‖G x - S x‖)]
    have hGS' : ‖G x - S x‖ ^ 2 ≤ M * Real.exp Mψ * f x := by
      rw [hGS]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hM x) hexp (Real.exp_pos _).le hM0) hf0
    have hG2 : ‖G x‖ ^ 2 ≤ CG ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG' 2
    dsimp [κ]
    nlinarith
  calc ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ
      ≤ ∫⁻ x in K \ A,
          ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) ∂μ :=
          setLIntegral_mono' hKA hpt
    _ = ENNReal.ofReal (2 * CG ^ 2) * μ (K \ A) +
          ENNReal.ofReal κ * ∫⁻ x in K \ A, ENNReal.ofReal (f x) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := by
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((measure_mono sdiff_subset).trans_lt hKμ), ENNReal.mul_lt_top
          ENNReal.ofReal_lt_top ?_⟩
      exact (lintegral_mono_set hKU).trans_lt hI


/-- A single finite weighted-error bound gives a uniform unweighted `L²`
bound on a fixed compact set, independently of the section. -/
theorem exists_uniform_local_sq_bound_of_weighted_difference
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {U K : Set X} (hK : IsCompact K) (hKU : K \ {x | ψ x = ⊥} ⊆ U)
    {I : ℝ≥0∞} (hI : I < ⊤) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ S : (x : X) → L.Fiber x,
      (∫⁻ x in U, ENNReal.ofReal
        (‖G x - S x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I →
      (∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ) ≤ B := by
  have hloc : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isSmoothPositiveVolume hμ
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  obtain ⟨CG, hCG⟩ := hK.exists_bound_of_continuousOn
    ((continuous_norm_of_isSmoothSectionOn L hG).continuousOn.mono (subset_univ K))
  obtain ⟨Mψ, hMψ⟩ := exists_le_coe_of_isCompact hqpsh hK
  set A : Set X := {x | ψ x = ⊥}
  set κ : ℝ := 2 * (M * Real.exp Mψ)
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * CG ^ 2) * μ K + ENNReal.ofReal κ * I
  refine ⟨B, ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKμ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI⟩, ?_⟩
  intro S hS
  set f : X → ℝ := fun x => ‖G x - S x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)
  have hKA : MeasurableSet (K \ A) := hK.isClosed.measurableSet.diff hcl.measurableSet
  have hpt : ∀ x ∈ K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ≤
      ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) := by
    intro x hx
    have hab : 0 < a x + b x := add_pos (ha0 x) (hb0 x)
    have hM0 : 0 ≤ M := hab.le.trans (hM x)
    have hψbot : ψ x ≠ ⊥ := hx.2
    have hφle : (ψ x).toReal ≤ Mψ := by
      have h := hMψ x hx.1
      rw [← EReal.coe_toReal (htop x) hψbot] at h
      exact_mod_cast h
    have hf0 : 0 ≤ f x := by dsimp [f]; positivity
    have hκ0 : 0 ≤ κ := by dsimp [κ]; positivity
    rw [← ENNReal.ofReal_mul hκ0,
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hκ0 hf0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hG' : ‖G x‖ ≤ CG :=
      (Real.norm_eq_abs _ ▸ (le_abs_self _)).trans (hCG x hx.1)
    have hexp : Real.exp ((ψ x).toReal) ≤ Real.exp Mψ := Real.exp_le_exp.mpr hφle
    have hGS : ‖G x - S x‖ ^ 2 =
        (a x + b x) * Real.exp ((ψ x).toReal) * f x := by
      dsimp [f]
      field_simp
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hnorm : ‖S x‖ ≤ ‖G x‖ + ‖G x - S x‖ := by
      calc ‖S x‖ = ‖G x - (G x - S x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hsq : ‖S x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖G x - S x‖ ^ 2 := by
      nlinarith [norm_nonneg (S x), norm_nonneg (G x), norm_nonneg (G x - S x),
        sq_nonneg (‖G x‖ - ‖G x - S x‖)]
    have hGS' : ‖G x - S x‖ ^ 2 ≤ M * Real.exp Mψ * f x := by
      rw [hGS]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hM x) hexp (Real.exp_pos _).le hM0) hf0
    have hG2 : ‖G x‖ ^ 2 ≤ CG ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG' 2
    dsimp [κ]
    nlinarith
  calc ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ
      ≤ ∫⁻ x in K \ A,
          ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) ∂μ :=
          setLIntegral_mono' hKA hpt
    _ = ENNReal.ofReal (2 * CG ^ 2) * μ (K \ A) +
          ENNReal.ofReal κ * ∫⁻ x in K \ A, ENNReal.ofReal (f x) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ B := by
      dsimp only [B]
      apply add_le_add
      · have hμKA : μ (K \ A) ≤ μ K := measure_mono sdiff_subset
        gcongr
      · gcongr
        exact (lintegral_mono_set hKU).trans hS

end SGPT.Trace.TwistedL2
