import SGPT.Okounkov.TranscendentalExtensionStatement
import SGPT.Okounkov.TranscendentalExtensionThetaOn
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Elementary pieces for the extension of Kähler currents

Package EXT (blueprint `tok:ct-extension`). Bookkeeping lemmas used in the assembly of DRWNXZ
Theorem 6.1:

* multiples of a Kähler form as backgrounds: monotonicity and additivity of `θ`-psh in the
  coefficient (`thetaOn_mono_smul`, `thetaOn_add_smul`, `isThetaPshPotential_mono_smul`);
* the Kähler margin: on a compact manifold `θ + dd^c φ ≥ ω'` for a Kähler form `ω'` gives
  `φ ∈ PSH(X, (1 - δ) θ)` for some `δ ∈ (0, 1)` when `θ` is Kähler
  (`exists_margin_of_isKahlerCurrentPotential`; FPT: `ω|_Y + dd^c φ ≥ δ ω|_Y`);
* Hölder continuity implies continuity (`IsChartHolderWith.continuous`), and a function whose
  exponential is continuous is continuous (`continuous_of_continuous_expPotential`);
* positive multiples (`isThetaPshPotential_const_mul`, `continuous_const_mul_ereal`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

section Forms

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem isSemipositive_smul {a : ClosedRealOneOneForm n M} (ha : a.val.IsSemipositive)
    {c : ℝ} (hc : 0 ≤ c) : (c • a).val.IsSemipositive := by
  intro e z hz v
  have h := ha e z hz v
  simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h ⊢
  exact mul_nonneg hc h

/-- `θ`-psh for `a ω` implies `θ`-psh for `b ω` when `a ≤ b`. -/
theorem thetaOn_mono_smul (ω : KahlerBackground n M) {a b : ℝ} (hab : a ≤ b) {u : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn (a • ω.form).val u Ω) :
    ThetaPlurisubharmonicOn (b • ω.form).val u Ω := by
  have h := thetaOn_add_semipositive hu (isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr hab))
  rwa [← add_smul, add_sub_cancel] at h

theorem isThetaPshPotential_mono_smul (ω : KahlerBackground n M) {a b : ℝ} (hab : a ≤ b)
    {u : M → EReal} (hu : IsThetaPshPotential (a • ω.form).val u) :
    IsThetaPshPotential (b • ω.form).val u := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu
    (isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr hab))
  rwa [← add_smul, add_sub_cancel] at h

/-- `θ`-psh for `a ω` plus `θ`-psh for `b ω` is `θ`-psh for `(a + b) ω`. -/
theorem thetaOn_add_smul (ω : KahlerBackground n M) {a b : ℝ} {u v : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn (a • ω.form).val u Ω)
    (hv : ThetaPlurisubharmonicOn (b • ω.form).val v Ω) :
    ThetaPlurisubharmonicOn ((a + b) • ω.form).val (fun x => u x + v x) Ω := by
  have h := thetaOn_add hu hv
  rwa [← add_smul] at h

/-- `θ`-psh for the form `ω` itself is `θ`-psh for `1 • ω`. -/
theorem isThetaPshPotential_one_smul_iff (θ : ClosedRealOneOneForm n M) {u : M → EReal} :
    IsThetaPshPotential ((1 : ℝ) • θ).val u ↔ IsThetaPshPotential θ.val u := by
  rw [one_smul]

/-- A positive multiple of a `θ`-psh potential. -/
theorem isThetaPshPotential_const_mul {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c) :
    IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x) :=
  RestrictedApproximantComparison.isThetaPshPotential_smul hu hc

/-- **The Kähler margin.** On a compact manifold, if `θ + dd^c φ` dominates a Kähler form, where
`θ` is itself a Kähler form, then `φ ∈ PSH(X, (1 - δ) θ)` for some `δ ∈ (0, 1)`, i.e.
`θ + dd^c φ ≥ δ θ`. -/
theorem exists_margin_of_isKahlerCurrentPotential [CompactSpace M] (ω : KahlerBackground n M)
    {φ : M → EReal} (hφ : IsKahlerCurrentPotential ω.form φ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ IsThetaPshPotential ((1 - δ) • ω.form).val φ := by
  obtain ⟨κ, hκ⟩ := hφ
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω.form)
  -- `κ ≥ A⁻¹ ω`
  set δ : ℝ := min (A⁻¹) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (inv_pos.mpr hA) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδpos, hδ1, ?_⟩
  -- `(ω - κ) + (κ - δ ω) = (1 - δ) ω`, and `κ - δ ω ≥ 0`
  have hpos : (κ.form - δ • ω.form).val.IsSemipositive := by
    intro e z hz v
    have h1 := hsemi e z hz v
    have h2 := ω.isSemipositive e z hz v
    have h3 := κ.isSemipositive e z hz v
    rw [sub_eq_add_neg]
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    -- `A κ ≥ ω` and `δ ≤ A⁻¹`
    have hAk : ω.form.val.coeff e z ![v, Complex.I • v] ≤
        A * κ.form.val.coeff e z ![v, Complex.I • v] := by linarith
    have hδA : δ * A ≤ 1 := by
      calc δ * A ≤ A⁻¹ * A := mul_le_mul_of_nonneg_right (min_le_left _ _) hA.le
        _ = 1 := inv_mul_cancel₀ hA.ne'
    nlinarith [mul_le_mul_of_nonneg_left hAk hδpos.le]
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ hpos
  have heq : (ω.form - κ.form) + (κ.form - δ • ω.form) = (1 - δ) • ω.form := by
    rw [sub_smul, one_smul]; abel
  rwa [heq] at h

end Forms

section Continuity

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]

/-- Hölder continuity in the charts implies continuity. -/
theorem IsChartHolderWith.continuous {α : ℝ} (hα : 0 < α) {f : M → ℝ}
    (hf : IsChartHolderWith (k := k) α f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨V, hV, -, C, hC, hHol⟩ :=
    hf (chartAt (ComplexModel k) x) (chart_mem_atlas _ x) x (mem_chart_source _ x)
  have hcont : ContinuousAt (chartAt (ComplexModel k) x) x :=
    (chartAt (ComplexModel k) x).continuousAt (mem_chart_source _ x)
  have hlim : Tendsto (fun a => C * ‖chartAt (ComplexModel k) x a -
      chartAt (ComplexModel k) x x‖ ^ α) (𝓝 x) (𝓝 0) := by
    have h0 : Tendsto (fun a => ‖chartAt (ComplexModel k) x a -
        chartAt (ComplexModel k) x x‖) (𝓝 x) (𝓝 0) := by
      have := (hcont.sub (continuousAt_const (y := chartAt (ComplexModel k) x x))).norm
      simpa using this.tendsto
    have h1 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h0
    rw [Real.zero_rpow hα.ne'] at h1
    simpa using h1.const_mul C
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hV] with a ha
  rw [Real.norm_eq_abs]
  exact hHol a ha x (mem_of_mem_nhds hV)

end Continuity

/-- A function with values `≠ ⊤` whose exponential is continuous is continuous. -/
theorem continuous_of_continuous_expPotential {M : Type*} [TopologicalSpace M] {u : M → EReal}
    (htop : ∀ x, u x ≠ ⊤) (hu : Continuous (expPotential u)) : Continuous u := by
  have heq : u = fun x => ENNReal.log (ENNReal.ofReal (expPotential u x)) := by
    funext x
    rw [expPotential, ENNReal.ofReal_toReal (exp_ne_top' (htop x)), EReal.log_exp]
  rw [heq]
  exact ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp hu)
where
  exp_ne_top' {a : EReal} (ha : a ≠ ⊤) : EReal.exp a ≠ ⊤ :=
    fun h => ha (EReal.exp_eq_top_iff.mp h)

/-- Multiplication by a positive real is continuous on `EReal`. -/
theorem continuous_const_mul_ereal {s : ℝ} (hs : 0 < s) :
    Continuous fun x : EReal => (s : EReal) * x := by
  rw [continuous_iff_continuousAt]
  intro x
  have h := EReal.continuousAt_mul (p := ((s : EReal), x))
    (Or.inl (show (s : EReal) ≠ 0 from by exact_mod_cast hs.ne'))
    (Or.inl (show (s : EReal) ≠ 0 from by exact_mod_cast hs.ne'))
    (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))
  exact h.comp (continuousAt_const.prodMk continuousAt_id)

end SGPT.Okounkov.TranscendentalExtension
