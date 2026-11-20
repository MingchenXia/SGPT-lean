import SGPT.Trace.OptimalExtensionGainMass
import SGPT.Trace.OptimalExtensionCurvature
import SGPT.Trace.TwistedL2YDensity
import SGPT.Trace.TwistedL2SingularWeaklyPseudoconvex

/-!
# The actual global twisted correction for locally positive optimal weights

The completed unconditional manifold estimate is applied on genuine compact
exhaustion sublevels, where positive lower bounds are produced. Optimal twists
may approach zero at the original parameter-disc boundary.
Blueprint: work/sgpt-resume-20261114/bert-e2-exhaustion/blueprint/bert-e2-exhaustion.tex.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalTwistedExhaustion
open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth SGPT.Trace.TwistedL2
open HermitianHolomorphicLineBundle

/-- Common positive lower bounds are produced from actual positive
continuous functions and an actual compact set, including the empty case. -/
theorem exists_common_positive_lower_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {a b : Y → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ y, 0 < a y) (hb0 : ∀ y, 0 < b y) :
    ∃ m : ℝ, 0 < m ∧ ∀ y ∈ K, m ≤ a y ∧ m ≤ b y := by
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (ha.inf hb).continuousOn
    refine ⟨min (a y) (b y), lt_min (ha0 y) (hb0 y), fun z hz =>
      ⟨(hmin hz).trans (min_le_left _ _), (hmin hz).trans (min_le_right _ _)⟩⟩
  · refine ⟨1, one_pos, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- The actual global singular twisted correction estimate needs only
pointwise positive smooth twists and a finite common upper bound, rather
than an assumed positive infimum at the parameter-disc boundary. -/
theorem global_correction_of_locally_positive_twists :
  ∀ (omega : KahlerBackground n X) (Ψ : X → ℝ), ChartSmooth (n := n) Ψ →
    (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun y => Ψ (c.val.symm y)) z v) →
    (∀ t : ℝ, IsCompact {x | Ψ x ≤ t}) →
  ∀ μ : Measure X, IsSmoothPositiveVolume (n := n) μ →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
  ∀ ψ : X → EReal, IsAdmissibleSingularWeight (n := n) ψ →
  ∀ a b : X → ℝ, ChartSmooth (n := n) a → ChartSmooth (n := n) b →
    (∀ x, 0 < a x) → (∀ x, 0 < b x) → (∃ M : ℝ, ∀ x, a x + b x ≤ M) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => a (c.val.symm y)) (fun y => b (c.val.symm y))
          (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
  ∀ G : (x : X) → L.Fiber x, IsSmoothSectionOn L G univ →
  ∀ D Domega : X → ℝ,
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => a (c.val.symm y))
            (fun y => b (c.val.symm y)) (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L),
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          Domega (c.val.symm z) * kahlerQuad omega c z v) →
    (∀ K : Set X, IsCompact K →
      ∫⁻ x in K, ENNReal.ofReal (Domega x) * multiplierWeight 1 (ψ x) ∂μ < ⊤) →
  ∃ S : (x : X) → L.Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
    ∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) * multiplierWeight 1 (ψ x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ
 := by
  intro omega Ψ hΨ hΨpsh hΨc μ hμ L hL ψ hψ a b ha hb ha0 hb0 hsum hcurv G hG D Dω hD hDω hint
  obtain ⟨hqpsh, htop, hcl, hAn, hsm⟩ := hψ
  obtain ⟨M, hsum⟩ := hsum
  have hmain : TwistedL2CorrectionStatement n X := twistedL2CorrectionStatement_manifold n X
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
    obtain ⟨m, hm, hlow⟩ := exists_common_positive_lower_bound (hΨc (j : ℝ))
      (continuous_of_chartSmooth' ha) (continuous_of_chartSmooth' hb) ha0 hb0
    obtain ⟨T, hThol, hTest⟩ := hmain omega (U j) (hUo j) r hrK hrcut μ hμ L hL φ a b hsmU
      (chartSmoothOn_of_chartSmooth ha (U j)) (chartSmoothOn_of_chartSmooth hb (U j))
      ⟨m, M, hm, fun x hx => by
        have hxK : x ∈ {x | Ψ x ≤ (j : ℝ)} := (show Ψ x < (j : ℝ) from hx.1).le
        have hxl := hlow x hxK
        have hxU := hsum x
        have hxa := ha0 x
        have hxb := hb0 x
        exact ⟨hxl.1, by linarith, hxl.2, by linarith⟩⟩
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


open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass

theorem mass_annularDensity_le_total {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {t : ℝ} (ht : 0 ≤ t) : mass (annularDensity ε δ) t ≤ windowMass ε + δ := by
  apply ge_of_tendsto (tendsto_mass_annularDensity hε δ)
  filter_upwards [eventually_ge_atTop t] with r hr
  exact mass_mono (contDiff_annularDensity ε δ).continuous
    (fun q _ => annularDensity_pos ε hδ q) ht hr

theorem actual_optimal_twist_sum_bound {ε δ R t : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : 0 < t) (htR : t ≤ R) :
    twist (annularDensity ε δ) t + (correction (annularDensity ε δ) t)⁻¹ ≤
      (windowMass ε + δ) / (δ * Real.exp (-R)) := by
  have hp : ∀ r ∈ Ici (0 : ℝ), 0 < annularDensity ε δ r := fun r _ => annularDensity_pos ε hδ r
  have ha := (antitone_annularDensity hε hδ.le).antitoneOn (Ici 0)
  rw [twist_add_reciprocal_correction (contDiff_annularDensity ε δ).continuous hp ha ht
    ((contDiff_annularDensity ε δ).differentiable (by simp) t)]
  have hC : 0 < windowMass ε + δ := add_pos (windowMass_pos hε) hδ
  have hl : δ * Real.exp (-R) ≤ annularDensity ε δ t := by
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg htR)) hδ.le
    dsimp only [annularDensity]
    linarith [annularWindow_nonneg ε t]
  exact (div_le_div_of_nonneg_right (mass_annularDensity_le_total hε hδ ht.le)
    (annularDensity_pos ε hδ t).le).trans
      (div_le_div_of_nonneg_left hC.le (mul_pos hδ (Real.exp_pos _)) hl)

omit [MeasurableSpace X] [BorelSpace X] in
/-- The native optimal twist hypotheses are produced from the actual
annular integral weights and the original smooth positive bounded logarithmic
truncation. Their infima may be zero at the original disc boundary. -/
theorem actual_native_optimal_twist_data {ε δ R : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {T : X → ℝ} (hT : ChartSmooth (n := n) T) (hT0 : ∀ x, 0 < T x) (hTR : ∀ x, T x ≤ R) :
    ChartSmooth (n := n) (fun x => twist (annularDensity ε δ) (T x)) ∧
    ChartSmooth (n := n) (fun x => (correction (annularDensity ε δ) (T x))⁻¹) ∧
    (∀ x, 0 < twist (annularDensity ε δ) (T x)) ∧
    (∀ x, 0 < (correction (annularDensity ε δ) (T x))⁻¹) ∧
    ∃ M : ℝ, ∀ x, twist (annularDensity ε δ) (T x) +
      (correction (annularDensity ε δ) (T x))⁻¹ ≤ M := by
  have hp : ∀ r ∈ Ici (0 : ℝ), 0 < annularDensity ε δ r := fun r _ => annularDensity_pos ε hδ r
  have ha := (antitone_annularDensity hε hδ.le).antitoneOn (Ici 0)
  refine ⟨?_, ?_, fun x => twist_pos (contDiff_annularDensity ε δ).continuous hp (hT0 x),
    fun x => inv_pos.mpr (correction_pos (contDiff_annularDensity ε δ).continuous hp ha (hT0 x)
      ((contDiff_annularDensity ε δ).differentiable (by simp) _)),
    (windowMass ε + δ) / (δ * Real.exp (-R)), fun x => actual_optimal_twist_sum_bound hε hδ (hT0 x) (hTR x)⟩
  · intro c z hz
    have hs := contDiffAt_twist (contDiff_annularDensity ε δ) hp (hT0 (c.val.symm z))
    exact (hs.comp z ((hT c).contDiffAt (c.val.open_target.mem_nhds hz))).contDiffWithinAt
  · intro c z hz
    have hs := SGPT.Trace.OptimalExtensionCurvature.contDiffAt_inverse_correction
      (contDiff_annularDensity ε δ) hp ha (hT0 (c.val.symm z))
    exact (hs.comp z ((hT c).contDiffAt (c.val.open_target.mem_nhds hz))).contDiffWithinAt


end SGPT.Trace.OptimalTwistedExhaustion
