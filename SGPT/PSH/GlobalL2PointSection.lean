import SGPT.PSH.GlobalL2PointChart
import SGPT.PSH.GlobalL2PointWeights
import SGPT.Foundations.Analysis.Pending.PointPoleExtension

/-!
# The section through a point, for one point

Blueprint `claude-global-l2b.tex`, node `claude-global-l2b:point-section`.

Cover data `D` (`claude-global-l2:cover`), a power `k` with `D.GoodPower k`, `φ` and the pole
weight `φ' = φ + ψ/k`, both in `PSH(X, θ - δω)`; a point `x` with `p = z_a(x)` in chart `a`;
a holomorphic `F₀` on `ball p (4ε) ⊆ B(z_a, R_a/2)` with `F₀(p) = 1` and
`∫ |F₀|² e^{-Φ_a} ≤ C_OT e^{-Φ_a(p)}`; a cut-off `χ`, `1` near `x`, locally constant off a
compact `K` in the annulus `ε ≤ |z_a - p|`, with `|∂̄χ|² ≤ M_χ` in all charts; a pole `ψ ≤ 0`,
`= (n+1) log |z_a - p|²` on `ball p ε`, `≥ (n+1) log ε²` on the annulus.

`exists_section_through_point`: there is `σ ∈ H⁰(X, L^k ⊗ T)` with `σ(x) = v` and
`∫ |σ|² e^{-kφ} dμ ≤ c_D(M_χ, e_ε) C_OT |v|² e^{-kφ(x)}`, the constant `pointConst` depending only
on the cover data, `M_χ` and `e_ε = ε^{-2(n+1)}`.

Proof: correct `χ F` (`F = v_a F₀ ∘ z_a · E_a`) with the weight `e^{-kφ'}`
(`GluingSystem.exists_correction`); the correction `χF - σ` is holomorphic near `x` and
`|χF - σ|² |z - p|^{-2(n+1)}` is integrable there, so it vanishes at `x`
(`PointPole.eq_zero_of_lintegral_pole_bounded`); the `L²` bound is the gluing bound of the
correction plus the bound for `χ F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace CoverData

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- The constant of `exists_section_through_point`; it depends only on the cover data, on the
cut-off bound `Mχ` and on `e = ε^{-2(n+1)}`. -/
def pointConst (Mχ : ℝ) (e : ℝ≥0∞) : ℝ≥0∞ :=
  2 * (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ ^ 2 *
    ((D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ *
      (8 * ((D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
        ENNReal.ofReal (2 / D.lam)))) + 2 * ENNReal.ofReal (2 / D.lam)) *
      ((D.m : ℝ≥0∞) * ENNReal.ofReal Mχ * ENNReal.ofReal D.Aμ * e) + 1) * ENNReal.ofReal D.Aμ

theorem pointConst_ne_top (Mχ : ℝ) {e : ℝ≥0∞} (he : e ≠ ⊤) : D.pointConst Mχ e ≠ ⊤ := by
  unfold pointConst
  have h1 : (D.m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : ENNReal.ofReal D.Aμ ≠ ⊤ := ENNReal.ofReal_ne_top
  have h3 : ENNReal.ofReal (2 / D.lam) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h4 : ENNReal.ofReal Mχ ≠ ⊤ := ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top _ h2
  apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h1)
    (ENNReal.pow_ne_top h2))
  refine ENNReal.add_ne_top.mpr ⟨?_, by norm_num⟩
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) ?_)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h4) h2) he)
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num)
    (ENNReal.mul_ne_top h1 (ENNReal.mul_ne_top h2 (ENNReal.mul_ne_top h2 h3))),
    ENNReal.mul_ne_top (by norm_num) h3⟩

open Classical in
/-- The local section `c₀ F₀ ∘ z_a · E_a` on `z_a⁻¹ Ω`, zero elsewhere. -/
def chartSection (k : ℕ) (a : Fin D.m) (Ω : Set (ComplexModel n)) (c₀ : ℂ)
    (F₀ : ComplexModel n → ℂ) (y : X) : (twistedPower L T k).Fiber y :=
  if y ∈ (D.chartA a).val.source ∧ (D.chartA a).val y ∈ Ω then
    (c₀ * F₀ ((D.chartA a).val y)) • (D.frameE k a).val.symm y 1 else 0

theorem chartSection_of_mem {k : ℕ} {a : Fin D.m} {Ω : Set (ComplexModel n)} {c₀ : ℂ}
    {F₀ : ComplexModel n → ℂ} {y : X} (hy : y ∈ (D.chartA a).val.source)
    (hyΩ : (D.chartA a).val y ∈ Ω) :
    D.chartSection k a Ω c₀ F₀ y = (c₀ * F₀ ((D.chartA a).val y)) • (D.frameE k a).val.symm y 1 :=
  by rw [chartSection, if_pos ⟨hy, hyΩ⟩]

theorem chartSection_of_not_mem {k : ℕ} {a : Fin D.m} {Ω : Set (ComplexModel n)} {c₀ : ℂ}
    {F₀ : ComplexModel n → ℂ} {y : X}
    (hy : y ∉ (D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' Ω) :
    D.chartSection k a Ω c₀ F₀ y = 0 := by
  unfold chartSection; exact if_neg hy

theorem coef_chartSection {k : ℕ} {a : Fin D.m} {Ω : Set (ComplexModel n)}
    (hΩR : Ω ⊆ ball (ctr (n := n) (D.pt a)) (D.R a)) {c₀ : ℂ} {F₀ : ComplexModel n → ℂ} {y : X}
    (hy : y ∈ (D.chartA a).val.source) (hyΩ : (D.chartA a).val y ∈ Ω) :
    (D.frameE k a).val.continuousLinearMapAt ℂ y (D.chartSection k a Ω c₀ F₀ y) =
      c₀ * F₀ ((D.chartA a).val y) := by
  rw [D.chartSection_of_mem hy hyΩ, map_smul,
    trivialization_coef_frame _ (D.mem_frameE_baseSet hy (hΩR hyΩ)), smul_eq_mul, mul_one]

/-- The chart section is holomorphic on `z_a⁻¹ Ω`. -/
theorem chartSection_holomorphic {k : ℕ} {a : Fin D.m} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hΩR : Ω ⊆ ball (ctr (n := n) (D.pt a)) (D.R a)) (c₀ : ℂ)
    {F₀ : ComplexModel n → ℂ} (hF₀ : DifferentiableOn ℂ F₀ Ω) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber
      (D.chartSection k a Ω c₀ F₀) ((D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' Ω) := by
  intro y hy
  have hUo : IsOpen ((D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' Ω) :=
    (D.chartA a).val.isOpen_inter_preimage hΩ
  have hE : y ∈ (D.frameE k a).val.baseSet := D.mem_frameE_baseSet hy.1 (hΩR hy.2)
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n))
    (D.frameE k a).val _ hE]
  have hev : (fun y' => ((D.frameE k a).val ⟨y', D.chartSection k a Ω c₀ F₀ y'⟩).2) =ᶠ[𝓝 y]
      fun y' => c₀ * F₀ ((D.chartA a).val y') := by
    filter_upwards [hUo.mem_nhds hy] with y' hy'
    have hEy : y' ∈ (D.frameE k a).val.baseSet := D.mem_frameE_baseSet hy'.1 (hΩR hy'.2)
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hEy]
    exact D.coef_chartSection hΩR hy'.1 hy'.2
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hsC : ContDiffAt ℂ ∞ (fun z => c₀ * F₀ z) ((D.chartA a).val y) :=
    contDiffAt_of_differentiableOn_complex ((differentiableOn_const c₀).mul hF₀) hΩ hy.2
  exact (hsC.contMDiffAt.comp y (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (D.chartA a).property) hy.1)).mdifferentiableAt (by simp)

section Point

variable (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
  {k : ℕ} (hk : D.GoodPower k) {φ ψ : X → EReal}
  (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
  (hφ' : IsThetaPshPotential (θ - δ • ωb.form).val (poleWeight φ ψ k))

include hL hT hk hφ hφ' in
/-- **The section through a point** (one point; all constants explicit). -/
theorem exists_section_through_point (hn : 0 < n) (a : Fin D.m) {x : X}
    (hxa : x ∈ (D.chartA a).val.source) {ε : ℝ} (hε : 0 < ε)
    (hΩR : ball ((D.chartA a).val x) (4 * ε) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2))
    (hψ0 : ∀ y, ψ y ≤ 0)
    (hψpole : ∀ y ∈ (D.chartA a).val.source, (D.chartA a).val y ∈ ball ((D.chartA a).val x) ε →
      ψ y = (((n : ℝ) + 1 : ℝ) : EReal) * logNormSq ((D.chartA a).val y - (D.chartA a).val x))
    (hψlow : ∀ y, (y ∈ (D.chartA a).val.source → ε ≤ ‖(D.chartA a).val y - (D.chartA a).val x‖) →
      ((((n : ℝ) + 1) * Real.log (ε ^ 2) : ℝ) : EReal) ≤ ψ y)
    {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hχ0 : ∀ y, 0 ≤ χ y) (hχ1 : ∀ y, χ y ≤ 1)
    (hχU : tsupport χ ⊆ (D.chartA a).val.source ∩
      (D.chartA a).val ⁻¹' ball ((D.chartA a).val x) (4 * ε))
    (hχone : ∀ y ∈ (D.chartA a).val.source,
      (D.chartA a).val y ∈ ball ((D.chartA a).val x) ε → χ y = 1)
    {K : Set X} (hK : IsCompact K)
    (hKU : K ⊆ (D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' ball ((D.chartA a).val x) (4 * ε))
    (hKann : ∀ y ∈ K, ε ≤ ‖(D.chartA a).val y - (D.chartA a).val x‖)
    (hconst : ∀ y ∈ ((D.chartA a).val.source ∩
      (D.chartA a).val ⁻¹' ball ((D.chartA a).val x) (4 * ε)) \ K, ∀ᶠ y' in 𝓝 y, χ y' = χ y)
    {Mχ : ℝ} (hMχ0 : 0 ≤ Mχ) (hMχ : ∀ l, ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ Mχ)
    {F₀ : ComplexModel n → ℂ} (hF₀ : DifferentiableOn ℂ F₀ (ball ((D.chartA a).val x) (4 * ε)))
    (hF₀p : F₀ ((D.chartA a).val x) = 1) {C_OT : ℝ}
    (hF₀int : ∫⁻ z in ball ((D.chartA a).val x) (4 * ε),
        ENNReal.ofReal (‖F₀ z‖ ^ 2) * (D.toGluingSystem hL hT hk hφ).W a z ≤
      ENNReal.ofReal C_OT * (D.toGluingSystem hL hT hk hφ).W a ((D.chartA a).val x))
    (hφx : φ x ≠ ⊥) (v : (twistedPower L T k).Fiber x) :
    ∃ σ : twistedSections L T k, σ x = v ∧
      ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
        D.pointConst Mχ (ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2))))) *
          ENNReal.ofReal C_OT * (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)) := by
  classical
  set G := D.toGluingSystem hL hT hk hφ with hG
  set G' := D.toGluingSystem hL hT hk hφ' with hG'
  set c := D.chartA a with hc
  set p := c.val x with hp
  set Ω := ball p (4 * ε) with hΩ
  set U := c.val.source ∩ c.val ⁻¹' Ω with hU
  have hUo : IsOpen U := c.val.isOpen_inter_preimage isOpen_ball
  have hΩR' : Ω ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    hΩR.trans (ball_subset_ball (by linarith [D.R_pos a]))
  have hk0 : 0 < k := hk.1
  have hφtop : ∀ y, φ y ≠ ⊤ := fun y => hφ.1.quasiPlurisubharmonic.ne_top y
  set c₀ : ℂ := G.coef a x v with hc₀
  set F := D.chartSection k a Ω c₀ F₀ with hFdef
  have hFhol := D.chartSection_holomorphic (k := k) (a := a) isOpen_ball hΩR' c₀ hF₀
  have hpΩ : p ∈ Ω := mem_ball_self (by positivity)
  have hpR : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := hΩR' hpΩ
  -- the coefficient of `F`
  have hcoefF : ∀ z ∈ Ω, G.locCoef a F z = c₀ * F₀ z := by
    intro z hz
    have hzt : z ∈ c.val.target := D.ball_subset_target a (hΩR' hz)
    have h1 : c.val.symm z ∈ c.val.source := c.val.map_target hzt
    have h2 : c.val (c.val.symm z) ∈ Ω := by rw [c.val.right_inv hzt]; exact hz
    show (D.frameE k a).val.continuousLinearMapAt ℂ (c.val.symm z) (F (c.val.symm z)) = _
    rw [D.coef_chartSection hΩR' h1 h2, c.val.right_inv hzt]
  -- `∫_U |F|² e^{-kφ} ≤ A C_OT |v|² e^{-kφ(x)}`
  have hI₀ : ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) =
      ENNReal.ofReal (‖c₀‖ ^ 2) * G.W a p :=
    G.density_eq a x v hxa hpR
  have hFU : ∫⁻ y in U, G.D F y ∂μ ≤
      G.A * (ENNReal.ofReal C_OT * (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x))) := by
    have hcont : ContinuousOn (G.locCoef a F) Ω :=
      (((differentiableOn_const c₀).mul hF₀).continuousOn).congr fun z hz => hcoefF z hz
    refine (G.lintegral_open_le a F isOpen_ball hΩR' hcont).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ∫⁻ z in Ω, ENNReal.ofReal (‖G.locCoef a F z‖ ^ 2) * G.W a z
        = ∫⁻ z in Ω, ENNReal.ofReal (‖c₀‖ ^ 2) * (ENNReal.ofReal (‖F₀ z‖ ^ 2) * G.W a z) := by
          refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
          rw [hcoefF z hz, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
      _ = ENNReal.ofReal (‖c₀‖ ^ 2) * ∫⁻ z in Ω, ENNReal.ofReal (‖F₀ z‖ ^ 2) * G.W a z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (‖c₀‖ ^ 2) * (ENNReal.ofReal C_OT * G.W a p) :=
          mul_le_mul_of_nonneg_left hF₀int zero_le
      _ = _ := by rw [hI₀]; ring
  -- the datum `χ F`
  set v₀ : (y : X) → (twistedPower L T k).Fiber y := fun y => ((χ y : ℝ) : ℂ) • F y with hv₀
  have hKU' : K ⊆ U := hKU
  have hconst' : ∀ y ∈ U \ K, ∀ᶠ y' in 𝓝 y, χ y' = χ y := hconst
  have hv' : G'.IsSmooth v₀ := by
    intro l z hz
    exact (D.datum_spec hL hT hk hφ' hUo hFhol hχ hχU hKU' hconst' l (hMχ l) hz).1.contDiffWithinAt
  -- the energy of the datum
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2)))) with he
  have hKw : ∫⁻ y in K, G'.D F y ∂μ ≤ e * ∫⁻ y in U, G.D F y ∂μ := by
    calc ∫⁻ y in K, G'.D F y ∂μ ≤ ∫⁻ y in K, G.D F y * e ∂μ := by
          refine setLIntegral_mono' hK.isClosed.measurableSet fun y hy => ?_
          show ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ≤
            ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) * e
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact multiplierWeight_poleWeight_le hk0 (hφtop y)
            (hψlow y fun _ => hKann y hy) (hψ0 y)
      _ = (∫⁻ y in K, G.D F y ∂μ) * e := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (∫⁻ y in U, G.D F y ∂μ) * e := mul_le_mul_of_nonneg_right (lintegral_mono_set hKU') zero_le
      _ = _ := mul_comm _ _
  have hN : G'.totalEnergy v₀ ≤ (D.m : ℝ≥0∞) * ENNReal.ofReal Mχ * ENNReal.ofReal D.Aμ * e *
      ∫⁻ y in U, G.D F y ∂μ := by
    calc G'.totalEnergy v₀ = ∑ l, G'.energy l v₀ := rfl
      _ ≤ ∑ _l : Fin D.m, ENNReal.ofReal Mχ * (ENNReal.ofReal D.Aμ * (e * ∫⁻ y in U, G.D F y ∂μ)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          refine (D.energy_datum_le hL hT hk hφ' hUo hFhol hχ hχU hKU' hconst' hK l hMχ0
            (hMχ l)).trans ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKw zero_le) zero_le
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hmwx : multiplierWeight (k : ℝ) (φ x) ≠ ⊤ := by
    obtain ⟨s, hs⟩ : ∃ s : ℝ, φ x = (s : EReal) :=
      ⟨(φ x).toReal, (EReal.coe_toReal (hφtop x) hφx).symm⟩
    rw [hs, multiplierWeight_coe]; exact ENNReal.ofReal_ne_top
  set I₀ := ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) with hI₀def
  have hI₀top : I₀ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmwx
  set Y := ∫⁻ y in U, G.D F y ∂μ with hYdef
  have hUfin : Y ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top G.A_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI₀top)) hFU
  set mMAe : ℝ≥0∞ := (D.m : ℝ≥0∞) * ENNReal.ofReal Mχ * ENNReal.ofReal D.Aμ * e with hmMAe
  have hE' : G'.totalEnergy v₀ ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hUfin) hN
  -- the correction
  obtain ⟨S, hSloc, hSint⟩ := G'.exists_correction (D.kappa_le hL hT hk hφ') hv' hE'
  obtain ⟨σ, hσ⟩ := D.exists_section_of_local hL hT hk hφ' S hSloc
  set u : (y : X) → (twistedPower L T k).Fiber y := fun y => v₀ y - S y with hu
  set Z := ∫⁻ y, G'.D u y ∂μ with hZdef
  have hZ : Z ≤ (D.m : ℝ≥0∞) * (G'.A * G'.K₀ v₀) := by
    have := hSint
    rw [Fintype.card_fin] at this
    exact this
  have hZfin : Z ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top G'.A_ne_top (G'.K₀_ne_top hE'))) hZ
  -- the local coefficients of `S` and `σ`
  have hSloc' : ∀ i, ∃ si : ComplexModel n → ℂ,
      DifferentiableOn ℂ si (ball (ctr (n := n) (D.pt i)) (D.R i / 2)) ∧
      ∀ y ∈ (D.chartA i).val.source, (D.chartA i).val y ∈ ball (ctr (n := n) (D.pt i)) (D.R i / 2) →
        S y = si ((D.chartA i).val y) • (D.frameE k i).val.symm y 1 := by
    intro i
    obtain ⟨si, hsi, hSsi⟩ := hSloc i
    exact ⟨si, hsi, fun y hy hyr => hSsi y ⟨hy, hyr⟩⟩
  have hσcoef : ∀ i, ContinuousOn (G.locCoef i (fun y => σ y)) (ball (G.center i) (G.r i)) := by
    intro i
    obtain ⟨si, hsi, hSsi⟩ := hSloc' i
    refine hsi.continuousOn.congr fun z hz => ?_
    have hzR : z ∈ ball (ctr (n := n) (D.pt i)) (D.R i) :=
      ball_subset_ball (by linarith [D.R_pos i]) hz
    have hzt : z ∈ (D.chartA i).val.target := D.ball_subset_target i hzR
    have hs1 : (D.chartA i).val.symm z ∈ (D.chartA i).val.source := (D.chartA i).val.map_target hzt
    show (D.frameE k i).val.continuousLinearMapAt ℂ ((D.chartA i).val.symm z)
      (σ ((D.chartA i).val.symm z)) = si z
    rw [hσ, hSsi _ hs1 (by rw [(D.chartA i).val.right_inv hzt]; exact hz), map_smul,
      trivialization_coef_frame _ (D.mem_frameE_baseSet hs1
        (by rw [(D.chartA i).val.right_inv hzt]; exact hzR)),
      (D.chartA i).val.right_inv hzt, smul_eq_mul, mul_one]
  -- vanishing of the correction at `x`
  obtain ⟨s, hs, hSs⟩ := hSloc' a
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, -, hWge⟩ := G.W_locally_ge (i := a) hpR
  set ε' := min ε ρ₀ with hε'
  have hε'0 : 0 < ε' := lt_min hε hρ₀
  set Ω₁ := ball p ε' with hΩ₁
  have hΩ₁ε : Ω₁ ⊆ ball p ε := ball_subset_ball (min_le_left _ _)
  have hΩ₁Ω : Ω₁ ⊆ Ω := hΩ₁ε.trans (ball_subset_ball (by linarith))
  have hΩ₁r : Ω₁ ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2) := hΩ₁Ω.trans hΩR
  set uc : ComplexModel n → ℂ := fun z => c₀ * F₀ z - s z with huc
  have huc_holo : DifferentiableOn ℂ uc Ω₁ :=
    (((differentiableOn_const c₀).mul hF₀).mono hΩ₁Ω).sub (hs.mono hΩ₁r)
  have hcoefu : ∀ y ∈ c.val.source, c.val y ∈ Ω₁ → G.coef a y (u y) = uc (c.val y) := by
    intro y hy hyΩ
    have hyr := hΩ₁r hyΩ
    have hyR : c.val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
      ball_subset_ball (by linarith [D.R_pos a]) hyr
    have hχy : χ y = 1 := hχone y hy (hΩ₁ε hyΩ)
    show (D.frameE k a).val.continuousLinearMapAt ℂ y (((χ y : ℝ) : ℂ) • F y - S y) = _
    rw [map_sub, map_smul, D.coef_chartSection hΩR' hy (hΩ₁Ω hyΩ), hSs y hy hyr, map_smul,
      trivialization_coef_frame _ (D.mem_frameE_baseSet hy hyR), hχy]
    simp [huc, hc]
  have hb : ∀ η : ℝ, 0 < η → ∫⁻ z in Ω₁, ENNReal.ofReal (δ₀ * ‖uc z‖ ^ 2) *
      ENNReal.ofReal (((‖z - p‖ ^ 2 + η ^ 2) ^ (n + 1))⁻¹) ≤ G'.A * Z := by
    intro η hη
    set h : ComplexModel n → ℝ≥0∞ := fun z => ENNReal.ofReal (δ₀ * ‖uc z‖ ^ 2) *
      ENNReal.ofReal (((‖z - p‖ ^ 2 + η ^ 2) ^ (n + 1))⁻¹) with hh
    have hΩ₁R : Ω₁ ⊆ ball (G'.center a) (G'.R a) := hΩ₁Ω.trans hΩR'
    have hmeas : AEMeasurable (Ω₁.indicator h) (volume.restrict (ball (G'.center a) (G'.R a))) := by
      refine (aemeasurable_indicator_iff measurableSet_ball).mpr ?_
      rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hΩ₁R]
      have h1 : ContinuousOn (fun z => δ₀ * ‖uc z‖ ^ 2) Ω₁ :=
        continuousOn_const.mul (huc_holo.continuousOn.norm.pow 2)
      have h2 : Measurable (fun z : ComplexModel n => ((‖z - p‖ ^ 2 + η ^ 2) ^ (n + 1))⁻¹) := by
        have : Continuous (fun z : ComplexModel n => (‖z - p‖ ^ 2 + η ^ 2) ^ (n + 1)) := by
          fun_prop
        exact this.measurable.inv
      exact (ENNReal.measurable_ofReal.comp_aemeasurable
        (h1.aestronglyMeasurable measurableSet_ball).aemeasurable).mul
        (ENNReal.measurable_ofReal.comp h2).aemeasurable
    calc ∫⁻ z in Ω₁, h z = ∫⁻ z in ball (G'.center a) (G'.R a), Ω₁.indicator h z := by
          rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
            inter_eq_left.mpr hΩ₁R]
      _ ≤ G'.A * ∫⁻ y in G'.region a, Ω₁.indicator h (G'.chart a y) ∂μ :=
          G'.lintegral_ball_le_region a _ hmeas
      _ ≤ G'.A * ∫⁻ y in G'.region a, G'.D u y ∂μ := by
          refine mul_le_mul_of_nonneg_left (setLIntegral_mono' (G'.isOpen_region a).measurableSet
            fun y hy => ?_) zero_le
          have hy1 : y ∈ c.val.source := hy.1
          have hy2 : c.val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := hy.2
          show Ω₁.indicator h (c.val y) ≤ ENNReal.ofReal (‖u y‖ ^ 2) *
            multiplierWeight (k : ℝ) (poleWeight φ ψ k y)
          by_cases hyΩ : c.val y ∈ Ω₁
          · rw [indicator_of_mem hyΩ]
            have hdens : ENNReal.ofReal (‖u y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) =
                ENNReal.ofReal (‖uc (c.val y)‖ ^ 2) * G.W a (c.val y) := by
              rw [← hcoefu y hy1 hyΩ]; exact G.density_eq a y (u y) hy1 hy2
            have hW : ENNReal.ofReal δ₀ ≤ G.W a (c.val y) :=
              hWge (c.val y) (ball_subset_ball (min_le_right _ _) hyΩ)
            have hpole := hψpole y hy1 (hΩ₁ε hyΩ)
            by_cases hyp : c.val y = p
            · have hbot : ψ y = ⊥ := by
                rw [hpole, hyp, sub_self, logNormSq_zero, EReal.coe_mul_bot_of_pos (by positivity)]
              rw [multiplierWeight_poleWeight_bot hk0 hbot]
              by_cases hu0 : ‖u y‖ = 0
              · have : uc (c.val y) = 0 := by
                  rw [← hcoefu y hy1 hyΩ, norm_eq_zero.mp hu0, map_zero]
                simp [hh, this]
              · rw [ENNReal.mul_top (by
                  rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)]
                exact le_top
            · set t := ‖c.val y - p‖ ^ 2 with ht
              have htpos : 0 < t := by
                have := norm_pos_iff.mpr (sub_ne_zero.mpr hyp); positivity
              have hψy : ψ y = ((((n : ℝ) + 1) * Real.log t : ℝ) : EReal) := by
                rw [hpole, logNormSq_of_ne_zero (sub_ne_zero.mpr hyp), ← EReal.coe_mul]
              rw [multiplierWeight_poleWeight_coe hk0 (hφtop y) hψy, ← mul_assoc, hdens]
              have hexp : Real.exp (-(((n : ℝ) + 1) * Real.log t)) = (t ^ (n + 1))⁻¹ := by
                rw [Real.exp_neg, show ((n : ℝ) + 1) * Real.log t = Real.log (t ^ (n + 1)) by
                  rw [Real.log_pow t (n + 1)]; push_cast; ring, Real.exp_log (by positivity)]
              rw [hexp]
              have hinv : ((t + η ^ 2) ^ (n + 1))⁻¹ ≤ (t ^ (n + 1))⁻¹ :=
                inv_anti₀ (by positivity) (pow_le_pow_left₀ htpos.le (by nlinarith) _)
              show ENNReal.ofReal (δ₀ * ‖uc (c.val y)‖ ^ 2) *
                  ENNReal.ofReal (((‖c.val y - p‖ ^ 2 + η ^ 2) ^ (n + 1))⁻¹) ≤ _
              rw [← ht, ENNReal.ofReal_mul hδ₀.le, mul_comm (ENNReal.ofReal δ₀)]
              gcongr
          · rw [indicator_of_notMem hyΩ]; exact zero_le
      _ ≤ G'.A * Z := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
  have huc0 : uc p = 0 :=
    Pending.PointPole.eq_zero_of_lintegral_pole_bounded hn isOpen_ball (mem_ball_self hε'0)
      huc_holo hδ₀ (ENNReal.mul_ne_top G'.A_ne_top hZfin) hb
  have hσx : σ x = v := by
    rw [hσ x, hSs x hxa (hΩR hpΩ)]
    have hsp : s p = c₀ := by
      have h0 := huc0
      simp only [huc, hF₀p, mul_one, sub_eq_zero] at h0
      exact h0.symm
    rw [← hp, hsp]
    exact (G.eq_coef_smul_frame a x v hxa hpR).symm
  refine ⟨σ, hσx, ?_⟩
  -- the `L²` bound
  have hχF : ∀ y, G.D v₀ y ≤ U.indicator (G.D F) y := by
    intro y
    by_cases hyU : y ∈ U
    · rw [indicator_of_mem hyU]
      show ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤
        ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 y), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (hχ0 y) (hχ1 y))
    · rw [indicator_of_notMem hyU]
      have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hyU (hχU h))
      show ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤ 0
      simp [h0]
  set X₂ := ∫⁻ y, G.D v₀ y ∂μ with hX₂def
  have hX₂ : X₂ ≤ Y := by
    rw [hX₂def, hYdef, ← lintegral_indicator hUo.measurableSet]; exact lintegral_mono hχF
  set X₁ := ∫⁻ y, G.D (fun y => v₀ y - σ y) y ∂μ with hX₁def
  have hX₁ : X₁ ≤ Z := by
    refine lintegral_mono fun y => ?_
    show ENNReal.ofReal (‖v₀ y - σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤
      ENNReal.ofReal (‖v₀ y - S y‖ ^ 2) * multiplierWeight (k : ℝ) (poleWeight φ ψ k y)
    rw [hσ y]
    exact mul_le_mul_of_nonneg_left (multiplierWeight_le_poleWeight hψ0 y) zero_le
  have hv₀c : ∀ i, ContinuousOn (G.locCoef i v₀) (ball (G.center i) (G.r i)) := fun i =>
    (hv' i).continuousOn.mono (ball_subset_ball (G.r_lt_R i).le)
  have hsplit : ∫⁻ y, G.D (fun y => σ y) y ∂μ ≤
      (D.m : ℝ≥0∞) * G.A * (2 * G.A * X₁ + 2 * G.A * X₂) := by
    refine (G.lintegral_le_sum_small _).trans ?_
    calc ∑ i, ∫⁻ y in G.small i, G.D (fun y => σ y) y ∂μ
        ≤ ∑ _i : Fin D.m, G.A * (2 * G.A * X₁ + 2 * G.A * X₂) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (G.lintegral_small_le i _ (hσcoef i)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
            ball_subset_ball (G.r_lt_R i).le
          have hWm : AEMeasurable (G.W i) (volume.restrict (ball (G.center i) (G.r i))) :=
            (G.aemeasurable_W i).mono_measure (Measure.restrict_mono hrR le_rfl)
          have hm2 : AEMeasurable (fun z => 2 * (ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) *
              G.W i z)) (volume.restrict (ball (G.center i) (G.r i))) :=
            ((ENNReal.measurable_ofReal.comp_aemeasurable
              (((hv₀c i).aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const
                2)).mul hWm).const_mul _
          have hdc : ContinuousOn (G.locCoef i (fun y => v₀ y - σ y)) (ball (G.center i) (G.r i)) := by
            rw [G.locCoef_sub]; exact (hv₀c i).sub (hσcoef i)
          calc ∫⁻ z in ball (G.center i) (G.r i),
                ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) * G.W i z
              ≤ ∫⁻ z in ball (G.center i) (G.r i),
                  (2 * (ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) * G.W i z) +
                    2 * (ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) * G.W i z)) := by
                refine lintegral_mono fun z => ?_
                have h1 := norm_sq_le_two_mul (G.locCoef i v₀ z) (G.locCoef i (fun y => σ y) z)
                have e1 : G.locCoef i (fun y => v₀ y - σ y) z =
                    G.locCoef i v₀ z - G.locCoef i (fun y => σ y) z := by rw [G.locCoef_sub]
                rw [← e1] at h1
                have h2 : ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) ≤
                    2 * ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) +
                      2 * ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) := by
                  have h3 := ENNReal.ofReal_le_ofReal h1
                  rw [ENNReal.ofReal_add (by positivity) (by positivity),
                    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
                    ENNReal.ofReal_ofNat] at h3
                  exact h3
                calc ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) * G.W i z
                    ≤ (2 * ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) +
                      2 * ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2)) * G.W i z :=
                      mul_le_mul_of_nonneg_right h2 zero_le
                  _ = _ := by ring
            _ = 2 * (∫⁻ z in ball (G.center i) (G.r i),
                  ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) * G.W i z) +
                  2 * ∫⁻ z in ball (G.center i) (G.r i),
                    ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) * G.W i z := by
                rw [lintegral_add_right' _ hm2, lintegral_const_mul' _ _ (by norm_num),
                  lintegral_const_mul' _ _ (by norm_num)]
            _ ≤ 2 * (G.A * ∫⁻ y in G.small i, G.D (fun y => v₀ y - σ y) y ∂μ) +
                  2 * (G.A * ∫⁻ y in G.small i, G.D v₀ y ∂μ) := by
                gcongr
                · exact G.lintegral_ball_r_le_small i _ hdc
                · exact G.lintegral_ball_r_le_small i _ (hv₀c i)
            _ ≤ 2 * (G.A * X₁) + 2 * (G.A * X₂) := by
                gcongr
                · exact setLIntegral_le_lintegral _ _
                · exact setLIntegral_le_lintegral _ _
            _ = 2 * G.A * X₁ + 2 * G.A * X₂ := by ring
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hK₀ : G'.K₀ v₀ ≤ (8 * ((D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
      ENNReal.ofReal (2 / D.lam)))) + 2 * ENNReal.ofReal (2 / D.lam)) * (mMAe * Y) := by
    have hcD : G'.cDiff = (D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
        ENNReal.ofReal (2 / D.lam))) := by
      simp only [GluingSystem.cDiff, Fintype.card_fin]; rfl
    have hl : G'.lam = D.lam := rfl
    rw [GluingSystem.K₀, hcD, hl, add_mul, mul_assoc 8, mul_assoc 2]
    gcongr
  have hA : G.A = ENNReal.ofReal D.Aμ := rfl
  have hA' : G'.A = ENNReal.ofReal D.Aμ := rfl
  rw [hA, hA'] at *
  calc ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ
      = ∫⁻ y, G.D (fun y => σ y) y ∂μ := rfl
    _ ≤ (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ * (2 * ENNReal.ofReal D.Aμ * X₁ +
          2 * ENNReal.ofReal D.Aμ * X₂) := hsplit
    _ ≤ (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ * (2 * ENNReal.ofReal D.Aμ * ((D.m : ℝ≥0∞) *
          (ENNReal.ofReal D.Aμ * ((8 * ((D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
            ENNReal.ofReal (2 / D.lam)))) + 2 * ENNReal.ofReal (2 / D.lam)) * (mMAe * Y)))) +
          2 * ENNReal.ofReal D.Aμ * Y) := by
        gcongr
        exact hX₁.trans (hZ.trans (mul_le_mul_of_nonneg_left (mul_le_mul' le_rfl hK₀) zero_le))
    _ = (2 * (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ ^ 2 *
          ((D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ *
            (8 * ((D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
              ENNReal.ofReal (2 / D.lam)))) + 2 * ENNReal.ofReal (2 / D.lam)) * mMAe + 1)) * Y := by
        ring
    _ ≤ (2 * (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ ^ 2 *
          ((D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ *
            (8 * ((D.m : ℝ≥0∞) * (ENNReal.ofReal D.Aμ * (ENNReal.ofReal D.Aμ *
              ENNReal.ofReal (2 / D.lam)))) + 2 * ENNReal.ofReal (2 / D.lam)) * mMAe + 1)) *
          (ENNReal.ofReal D.Aμ * (ENNReal.ofReal C_OT * I₀)) := by
        gcongr
        exact hFU
    _ = _ := by rw [pointConst, hmMAe]; ring

end Point

end CoverData

end SGPT.PSH.GlobalL2
