import SGPT.Trace.TwistedL2SingularLimitConstruction

/-!
# Weakly pseudoconvex singular twisted L² estimate

Sublevel exhaustion and Montel--Fatou construction prove the weakly
pseudoconvex estimate conditional on `TwistedL2CorrectionStatement`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

variable (n X) in
/-- The weakly pseudoconvex estimate follows from the main twisted estimate. -/
theorem weaklyPseudoconvexTwistedL2CorrectionStatement_of_main
    (hmain : TwistedL2CorrectionStatement n X) :
    WeaklyPseudoconvexTwistedL2CorrectionStatement n X := by
  intro omega Ψ hΨ hΨpsh hΨc μ hμ L hL ψ hψ a b ha hb hbounds hcurv G hG D Dω hD hDω hint
  obtain ⟨hqpsh, htop, hcl, hAn, hsm⟩ := hψ
  obtain ⟨m, M, hm, hmM⟩ := hbounds
  have ha0 : ∀ x, 0 < a x := fun x => hm.trans_le (hmM x).1
  have hb0 : ∀ x, 0 < b x := fun x => hm.trans_le (hmM x).2.2.1
  have hsum : ∀ x, a x + b x ≤ 2 * M := fun x => by
    have := hmM x
    linarith [this.2.1, this.2.2.2]
  set I := ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ with hIdef
  by_cases hI : I = ⊤
  · exact ⟨fun _ => 0, isHolomorphicSectionOn_zero L univ, by rw [hI]; exact le_top⟩
  have hIlt : I < ⊤ := lt_top_iff_ne_top.mpr hI
  let V : ℕ → Set X := fun j => {x | Ψ x < (j : ℝ)}
  let A : Set X := {x | ψ x = ⊥}
  let U : ℕ → Set X := fun j => V j \ A
  have hΨcont : Continuous Ψ := continuous_of_chartSmooth' hΨ
  have hVo : ∀ j, IsOpen (V j) := fun j => isOpen_lt hΨcont continuous_const
  have hVm : Monotone V := by
    intro i j hij x hx
    change Ψ x < (j : ℝ)
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact lt_of_lt_of_le hx hcast
  have hcover : ∀ x : X, ∃ j, x ∈ V j := fun x => exists_nat_gt (Ψ x)
  have hUo : ∀ j, IsOpen (U j) := fun j => (hVo j).sdiff hcl
  have hUeq : ∀ j, U j = {x | Ψ x < (j : ℝ) ∧ ψ x ≠ ⊥} := fun j => rfl
  let φ : X → ℝ := fun x => (ψ x).toReal
  let Dσ : X → ℝ := fun x => 2 * max (Dω x) 0
  have hmw : ∀ x ∉ A, ∀ t : ℝ,
      ENNReal.ofReal (t * Real.exp (-φ x)) = ENNReal.ofReal t * multiplierWeight 1 (ψ x) :=
    fun x hx t => ofReal_mul_exp_neg_toReal t hx (htop x)
  have hexists : ∀ j, ∃ T : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber T (U j) ∧
      (∫⁻ x in U j, ENNReal.ofReal
        (‖G x - T x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I := by
    intro j
    obtain ⟨r, hrK, hrhalf, hrcut⟩ := exists_complete_metric_sublevel omega hΨ hΨpsh hΨc
      ⟨hqpsh, htop, hcl, hAn, hsm⟩ (j : ℝ)
    rw [← hUeq j] at hrK hrcut
    have hsmU : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) φ (U j) := fun c =>
      (hsm c).mono fun z hz => ⟨hz.1, hz.2.2⟩
    have hDσ : ∀ (c : ComplexChart n X) (e : AtlasFrame L),
        ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U j → ∀ v : ComplexModel n,
          ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
            Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v := by
      intro c e z hz hzU v
      have h1 := hDω c e z hz hzU.2 v
      have hk := kahlerQuad_nonneg omega c hz.1 v
      have h2 := hrhalf c z hz.1 hzU.1 hzU.2 v
      have h3 : Dω (c.val.symm z) * kahlerQuad omega c z v ≤
          max (Dω (c.val.symm z)) 0 * kahlerQuad omega c z v :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hk
      have h4 : max (Dω (c.val.symm z)) 0 * kahlerQuad omega c z v ≤
          Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v := by
        dsimp [Dσ]
        nlinarith [le_max_right (Dω (c.val.symm z)) 0]
      linarith
    have hintσ : ∫⁻ x in U j, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ < ⊤ := by
      calc ∫⁻ x in U j, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ
          ≤ ∫⁻ x in U j, 2 * (ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x)) ∂μ := by
            refine setLIntegral_mono' (hUo j).measurableSet fun x hx => ?_
            have hmax : ENNReal.ofReal (2 * max (Dω x) 0) = 2 * ENNReal.ofReal (Dω x) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
              congr 1
              rcases le_total (Dω x) 0 with h | h
              · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
              · rw [max_eq_left h]
            rw [hmw x hx.2, show Dσ x = 2 * max (Dω x) 0 from rfl, hmax, mul_assoc]
        _ ≤ ∫⁻ x in {x | Ψ x ≤ (j : ℝ)},
            2 * (ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x)) ∂μ :=
          lintegral_mono_set fun x hx => (show Ψ x ≤ (j : ℝ) from (show Ψ x < (j : ℝ) from hx.1).le)
        _ = 2 * ∫⁻ x in {x | Ψ x ≤ (j : ℝ)},
            ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x) ∂μ :=
          lintegral_const_mul' _ _ (by norm_num)
        _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (hint _ (hΨc (j : ℝ)))
    obtain ⟨T, hThol, hTest⟩ := hmain omega (U j) (hUo j) r hrK hrcut μ hμ L hL φ a b hsmU
      (chartSmoothOn_of_chartSmooth ha (U j)) (chartSmoothOn_of_chartSmooth hb (U j))
      ⟨m, M, hm, fun x _ => hmM x⟩
      (fun c e ρ hρ z hz hzU v hv => hcurv c e ρ hρ z hz hzU.2 v hv)
      G (IsSmoothSectionOn.mono' L hG (subset_univ (U j))) D Dσ
      (fun c e ρ hρ z hz hzU v => hD c e ρ hρ z hz hzU.2 v) hDσ hintσ
    refine ⟨T, hThol, hTest.trans ?_⟩
    rw [hIdef]
    refine (setLIntegral_congr_fun (hUo j).measurableSet fun x hx => hmw x hx.2 (D x)).trans_le ?_
    exact setLIntegral_le_lintegral _ _
  choose T hT hTest using hexists
  exact exists_singular_weighted_limit_section_of_punctured_sections hμ L hqpsh htop hcl hAn
    ha hb ha0 hb0 hsum hG hVo hVm hcover hIlt T hT hTest

end SGPT.Trace.TwistedL2
