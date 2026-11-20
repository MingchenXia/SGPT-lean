import SGPT.PSH.GlobalL2SectionsPosMass

/-!
# The Bergman sequence and the lower bound of `prop:Bergman_approx`

Blueprint `claude-global-l2:bergman-lower`, `claude-global-l2b.tex`, node
`claude-global-l2b:bergman-seq`.  Source `prop:Bergman_approx` (`chapter_pshfunctions.tex`
1944--1961), `eq:Bergman_seq_def`:

`φ_k = (1/k) log sup { |s|²_{h^k ⊗ h_T} : s ∈ H⁰(X, L^k ⊗ T), ∫_X |s|²_{h^k ⊗ h_T} e^{-kφ} ω^n ≤ 1 }`.

* `bergmanSeq ωb L T φ k`: this function (`ω^n` is `kahlerVolume ωb`, the non-pluripolar measure
  of `ω` with the zero potential; `log 0 = -∞`).
* `bergmanSeq_lower`: if `θ = c₁(L, h)` and `θ_φ` is a Kähler current, there are `k₀` and `C > 0`
  with `φ_k ≥ φ - (log C)/k` for all `k ≥ k₀` (the book's proof: the point extension of
  `thm:OT_ext` for `Y = {x}`, here `globalPointExtension`).  Consequently `φ ⪯ φ_k`
  (`bergmanSeq_preceq`), the first inequality of `prop:Bergman_approx`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- **The Bergman sequence** (source `eq:Bergman_seq_def`):
`φ_k(x) = (1/k) log sup {|s(x)|² : s ∈ H⁰(X, L^k ⊗ T), ∫ |s|² e^{-kφ} ω^n ≤ 1}`. -/
def bergmanSeq [CompactSpace X] (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (φ : X → EReal) (k : ℕ) (x : X) : EReal :=
  ((1 / (k : ℝ) : ℝ) : EReal) * ENNReal.log (⨆ s : twistedSections L T k,
    ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤ 1),
      ENNReal.ofReal (‖s x‖ ^ 2))

/-- A Kähler current dominates a multiple of any Kähler form. -/
theorem exists_isThetaPshPotential_sub_smul_of_kahlerCurrent [CompactSpace X]
    (ωb : KahlerBackground n X) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ δ : ℝ, 0 < δ ∧ IsThetaPshPotential (θ - δ • ωb.form).val φ := by
  obtain ⟨ω', hω'⟩ := hφ
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω' (-ωb.form)
  refine ⟨1 / A, by positivity, ?_⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hω'
    (KahlerDomination.isSemipositive_smul hsemi (by positivity : (0 : ℝ) ≤ 1 / A))
  have hform : θ - ω'.form + (1 / A) • (-ωb.form + A • ω'.form) = θ - (1 / A) • ωb.form := by
    rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hA.ne', one_smul]
    module
  rwa [hform] at h

/-- **The lower bound of `prop:Bergman_approx`**: `φ_k ≥ φ - (log C)/k` for `k ≥ k₀`. -/
theorem bergmanSeq_lower [CompactSpace X] (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ (k₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℕ, k₀ ≤ k → ∀ x : X,
      φ x - ((Real.log C / k : ℝ) : EReal) ≤ bergmanSeq ωb L T φ k x := by
  obtain ⟨δ, hδ, hφδ⟩ := exists_isThetaPshPotential_sub_smul_of_kahlerCurrent ωb hφ
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  obtain ⟨k₀, C, hC, hext⟩ := globalPointExtension (n := n) (X := X) ‹CompactSpace X› ωb
    (IntegrationCurrent.kahlerVolume ωb) hμ L T hL hT θ hθ δ hδ
  refine ⟨max k₀ 1, C, hC, fun k hk x => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  by_cases hx : φ x = ⊥
  · rw [hx, EReal.bot_sub]; exact bot_le
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = (r : EReal) :=
    ⟨(φ x).toReal, (EReal.coe_toReal (hφδ.1.quasiPlurisubharmonic.ne_top x) hx).symm⟩
  -- a unit vector at `x`
  set e := prefFrame (twistedPower L T k) x
  have he : 0 < ‖e.val.symm x 1‖ :=
    frameNorm_pos (twistedPower L T k).Fiber e.val (mem_prefFrame _ x)
  set v : (twistedPower L T k).Fiber x := ((‖e.val.symm x 1‖⁻¹ : ℝ) : ℂ) • e.val.symm x 1
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he),
      inv_mul_cancel₀ he.ne']
  obtain ⟨s, hsx, hsint⟩ := hext k (le_of_max_le_left hk) φ hφδ x hx v
  set M : ℝ := C * Real.exp (-((k : ℝ) * r)) with hM
  have hM0 : 0 < M := by positivity
  have hsint' : ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
      ∂(IntegrationCurrent.kahlerVolume ωb) ≤ ENNReal.ofReal M := by
    refine hsint.trans (le_of_eq ?_)
    rw [hv, hr, multiplierWeight_coe, one_pow, ENNReal.ofReal_one, one_mul,
      ← ENNReal.ofReal_mul hC.le]
  -- the normalized section
  set c : ℝ := Real.sqrt M⁻¹ with hc
  have hc2 : c ^ 2 = M⁻¹ := Real.sq_sqrt (by positivity)
  set s' : twistedSections L T k := ((c : ℝ) : ℂ) • s with hs'
  have hs'y : ∀ y, ‖s' y‖ ^ 2 = M⁻¹ * ‖s y‖ ^ 2 := by
    intro y
    rw [hs', ContMDiffSection.coe_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, hc2]
  have hnorm : ∫⁻ y, ENNReal.ofReal (‖s' y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
      ∂(IntegrationCurrent.kahlerVolume ωb) ≤ 1 := by
    calc ∫⁻ y, ENNReal.ofReal (‖s' y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
          ∂(IntegrationCurrent.kahlerVolume ωb)
        = ∫⁻ y, ENNReal.ofReal M⁻¹ * (ENNReal.ofReal (‖s y‖ ^ 2) *
            multiplierWeight (k : ℝ) (φ y)) ∂(IntegrationCurrent.kahlerVolume ωb) := by
          refine lintegral_congr fun y => ?_
          rw [hs'y, ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ = ENNReal.ofReal M⁻¹ * ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) *
            multiplierWeight (k : ℝ) (φ y) ∂(IntegrationCurrent.kahlerVolume ωb) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M⁻¹ * ENNReal.ofReal M := mul_le_mul_of_nonneg_left hsint' zero_le
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hM0.ne', ENNReal.ofReal_one]
  have hval : ENNReal.ofReal (‖s' x‖ ^ 2) = ENNReal.ofReal M⁻¹ := by
    rw [hs'y, hsx, hv, one_pow, mul_one]
  have hsup : ENNReal.ofReal M⁻¹ ≤ ⨆ s : twistedSections L T k,
      ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
          ∂(IntegrationCurrent.kahlerVolume ωb) ≤ 1), ENNReal.ofReal (‖s x‖ ^ 2) := by
    rw [← hval]
    exact le_iSup₂ (f := fun (s : twistedSections L T k) (_ : ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) *
      multiplierWeight (k : ℝ) (φ y) ∂(IntegrationCurrent.kahlerVolume ωb) ≤ 1) =>
        ENNReal.ofReal (‖s x‖ ^ 2)) s' hnorm
  have hlog := ENNReal.log_monotone hsup
  rw [ENNReal.log_ofReal_of_pos (by positivity)] at hlog
  have hlogM : Real.log M⁻¹ = (k : ℝ) * r - Real.log C := by
    rw [Real.log_inv, hM, Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  rw [hlogM] at hlog
  have h := coe_mul_le_coe_mul (c := 1 / (k : ℝ)) (by positivity) hlog
  rw [hr, ← EReal.coe_sub]
  unfold bergmanSeq
  refine le_trans (le_of_eq ?_) h
  congr 1
  field_simp

/-- **`φ ⪯ φ_k`** for `k ≥ k₀` (first inequality of `prop:Bergman_approx`). -/
theorem bergmanSeq_preceq [CompactSpace X] (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ c : ℝ, ∀ x : X, φ x ≤ bergmanSeq ωb L T φ k x + (c : EReal) := by
  obtain ⟨k₀, C, hC, h⟩ := bergmanSeq_lower ωb L T hL hT θ hθ hφ
  refine ⟨k₀, fun k hk => ⟨Real.log C / k, fun x => ?_⟩⟩
  have h1 := h k hk x
  have h2 := add_le_add h1 (le_refl ((Real.log C / k : ℝ) : EReal))
  rwa [EReal.sub_add_cancel] at h2

end SGPT.PSH.GlobalL2
