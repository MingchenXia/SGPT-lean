import SGPT.PSH.GlobalL2PoleFunction
import SGPT.PSH.GlobalL2LocalSingular
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Weights with a logarithmic pole for the point extension

Blueprint `claude-global-l2b.tex`, node `claude-global-l2b:pole-weight`.

For `φ ∈ PSH(X, θ - δω)` and a pole function `ψ ∈ PSH(X, Bω)` with `ψ ≤ 0`, finite off a point
`x`, the weight `φ' = φ + ψ/k` (`poleWeight`) lies in `PSH(X, θ - (δ/2)ω)` as soon as
`2B ≤ kδ` (`isThetaPshPotential_poleWeight`).  Comparison of the densities
`e^{-kφ'} = e^{-kφ} e^{-ψ}` (`multiplierWeight_poleWeight_coe`): `e^{-kφ} ≤ e^{-kφ'}`,
`e^{-kφ'} ≤ e^{-kφ} e^{-t}` where `ψ ≥ t`, and `e^{-kφ'} = ∞` where `ψ = -∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-! ### Multiplier weights -/

/-- `e^{-c(x + t)} = e^{-cx} e^{-ct}` for `x < ⊤`, `c > 0`. -/
theorem multiplierWeight_add_coe {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) (t : ℝ) :
    multiplierWeight c (x + (t : EReal)) =
      multiplierWeight c x * ENNReal.ofReal (Real.exp (-(c * t))) := by
  induction x using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot hc, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
  | top => exact absurd rfl hx

/-- The weight `φ + ψ / k`. -/
def poleWeight {X : Type*} (φ ψ : X → EReal) (k : ℕ) (y : X) : EReal :=
  φ y + ((1 / (k : ℝ) : ℝ) : EReal) * ψ y

theorem coe_mul_nonpos {c : ℝ} (hc : 0 ≤ c) {e : EReal} (he : e ≤ 0) : (c : EReal) * e ≤ 0 := by
  induction e using EReal.rec with
  | bot =>
      rcases hc.lt_or_eq with h | h
      · rw [EReal.coe_mul_bot_of_pos h]; exact bot_le
      · rw [← h, EReal.coe_zero, zero_mul]
  | coe s =>
      rw [← EReal.coe_mul]
      exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hc (EReal.coe_nonpos.mp he))
  | top => exact absurd he (by simp)

variable {X : Type*} {φ ψ : X → EReal} {k : ℕ}

theorem poleWeight_le (hψ : ∀ y, ψ y ≤ 0) (y : X) : poleWeight φ ψ k y ≤ φ y := by
  have h := coe_mul_nonpos (c := 1 / (k : ℝ)) (by positivity) (hψ y)
  calc poleWeight φ ψ k y ≤ φ y + 0 := add_le_add le_rfl h
    _ = φ y := add_zero _

/-- `e^{-kφ} ≤ e^{-kφ'}`. -/
theorem multiplierWeight_le_poleWeight (hψ : ∀ y, ψ y ≤ 0) (y : X) :
    multiplierWeight (k : ℝ) (φ y) ≤ multiplierWeight (k : ℝ) (poleWeight φ ψ k y) :=
  multiplierWeight_antitone (Nat.cast_nonneg k) (poleWeight_le hψ y)

/-- Where `ψ` is finite, `e^{-kφ'} = e^{-kφ} e^{-ψ}`. -/
theorem multiplierWeight_poleWeight_coe (hk : 0 < k) {y : X} (hφ : φ y ≠ ⊤) {s : ℝ}
    (hs : ψ y = (s : EReal)) :
    multiplierWeight (k : ℝ) (poleWeight φ ψ k y) =
      multiplierWeight (k : ℝ) (φ y) * ENNReal.ofReal (Real.exp (-s)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [poleWeight, hs, ← EReal.coe_mul, multiplierWeight_add_coe hk' hφ]
  congr 3
  field_simp

/-- Where `ψ = -∞`, `e^{-kφ'} = ∞`. -/
theorem multiplierWeight_poleWeight_bot (hk : 0 < k) {y : X} (hs : ψ y = ⊥) :
    multiplierWeight (k : ℝ) (poleWeight φ ψ k y) = ⊤ := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [poleWeight, hs, EReal.coe_mul_bot_of_pos (by positivity), EReal.add_bot,
    multiplierWeight_bot hk']

/-- Where `ψ ≥ t`, `e^{-kφ'} ≤ e^{-kφ} e^{-t}`. -/
theorem multiplierWeight_poleWeight_le (hk : 0 < k) {y : X} (hφ : φ y ≠ ⊤) {t : ℝ}
    (ht : (t : EReal) ≤ ψ y) (hψ : ψ y ≤ 0) :
    multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ≤
      multiplierWeight (k : ℝ) (φ y) * ENNReal.ofReal (Real.exp (-t)) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ψ y = (s : EReal) := by
    induction h : ψ y using EReal.rec with
    | bot => rw [h] at ht; exact absurd ht (by simp)
    | coe s => exact ⟨s, rfl⟩
    | top => rw [h] at hψ; exact absurd hψ (by simp)
  rw [multiplierWeight_poleWeight_coe hk hφ hs]
  rw [hs] at ht
  exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (neg_le_neg (EReal.coe_le_coe_iff.mp ht)))) zero_le

/-! ### The weight is `(θ - δ/2 ω)`-psh -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`φ + ψ/k ∈ PSH(X, θ - (δ/2) ω)`** for `φ ∈ PSH(X, θ - δω)`, `ψ ∈ PSH(X, Bω)`, `ψ ≤ 0`,
`ψ > -∞` off `x`, in positive dimension, when `2B ≤ kδ`. -/
theorem isThetaPshPotential_poleWeight (hn : 0 < n) (ωb : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {δ B : ℝ} {φ ψ : M → EReal} {k : ℕ}
    (hk : 0 < k) (hkB : 2 * B ≤ k * δ)
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hψ : ThetaPlurisubharmonic (B • ωb.form).val ψ) {x : M} (hψx : ∀ y, y ≠ x → ψ y ≠ ⊥) :
    IsThetaPshPotential (θ - (δ / 2) • ωb.form).val (poleWeight φ ψ k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
    (c := 1 / (k : ℝ)) (by positivity) hψ
  have h2 := FirstPass.LocalPotentials.thetaPlurisubharmonic_add hφ.1 h1
  have hsemi : ((δ / 2 - B / k) • ωb.form).val.IsSemipositive := by
    refine Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive ?_
    rw [sub_nonneg, div_le_iff₀ hk']
    linarith
  have h3 := Pending.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive h2 hsemi
  have hform : θ - δ • ωb.form + (1 / (k : ℝ)) • (B • ωb.form) +
      (δ / 2 - B / k) • ωb.form = θ - (δ / 2) • ωb.form := by
    rw [smul_smul]
    have : (1 / (k : ℝ)) * B = B / k := by ring
    rw [this]
    module
  rw [hform] at h3
  refine ⟨h3, fun y U hU hyU => ?_⟩
  -- a point of `U` other than `x`, then a point where `φ` is finite
  obtain ⟨y₀, hy₀U, hy₀x⟩ : ∃ y₀ ∈ U, y₀ ≠ x := by
    by_cases hy : y = x
    · exact exists_ne_mem_of_isOpen hn hU (hy ▸ hyU)
    · exact ⟨y, hyU, hy⟩
  obtain ⟨y₁, hy₁, hy₁φ⟩ := hφ.2 y₀ (U ∩ {x}ᶜ) (hU.inter isOpen_compl_singleton) ⟨hy₀U, hy₀x⟩
  refine ⟨y₁, hy₁.1, ?_⟩
  have hψ1 : ψ y₁ ≠ ⊥ := hψx y₁ hy₁.2
  have hmul : ((1 / (k : ℝ) : ℝ) : EReal) * ψ y₁ ≠ ⊥ := by
    induction h : ψ y₁ using EReal.rec with
    | bot => exact absurd h hψ1
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
  rw [poleWeight]
  exact fun h => (EReal.add_eq_bot_iff.mp h).elim hy₁φ hmul

end SGPT.PSH.GlobalL2
