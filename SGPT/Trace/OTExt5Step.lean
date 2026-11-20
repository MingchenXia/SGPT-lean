import SGPT.Trace.OTExt5Vanish

/-!
# Steps 2--3 of FPT `thm:compact-submanifold-extension` for a fixed `ε`

Blueprint `claude-ot-ext5.tex`, node `claude-ot-ext5:step`.  Xia, *Foundations of pluripotential
theory*, q07, proof of `thm:compact-submanifold-extension`, Steps 2--4 for a fixed cut-off width
`ε ∈ (0, e^{-4})`.

`exists_section_eps`: for a gentle `Φ ∈ PSH(X, θ_V - N₀ ω)` (`N₀ = 1 + b_K/π + (q + 2) b`) and a
smooth section `G` with `|∂̄G|² ≤ D_G ω`, `D_G = 0` on `W`, the compact twisted `L²` estimate
(`compactTwistedL2CorrectionStatement_manifold`) for `ψ = Φ + q log R`, the twist `(a_ε, b_ε)` and the
datum `∂̄G_ε`, `G_ε = ρ(R/ε) G`, gives `s_ε ∈ H⁰(X, V)` with `s_ε = G` on `W` (Step 3:
`eq_zero_of_lintegral_logPole`) and

`∫_X |s_ε|² e^{-Φ} ≤ 2·20·(32 B² I_ε + (2/π) J_ε) + 2 ∫_{R < ε} |G|² e^{-Φ}`,

`I_ε = ∫_{ε/2 ≤ R ≤ ε} |G|² e^{-Φ} R^{-q}`, `J_ε = ∫_{R < ε} D_G e^{-Φ} R^{-q}` (Step 4: the
correction `u_ε = G_ε - s_ε` satisfies `∫ |u_ε|² e^{-Φ} ≤ 20 ∫ |u_ε|² e^{-Φ}R^{-q}/(a_ε + b_ε)`,
since `(a_ε + b_ε) R^q ≤ 5 R^q (log R)² ≤ 20`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

/-! ### Scalar bounds -/

theorem log_add_lt_neg_three' {ε r : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hr : 0 ≤ r)
    (hr4 : r < Real.exp (-4)) : Real.log (ε + r) < -3 := by
  rw [Real.log_lt_iff_lt_exp (by linarith)]
  have he : Real.exp (-3) = Real.exp (-4) * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hp := Real.exp_pos (-4)
  rw [he]; nlinarith

theorem sq_mul_rpow_log_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {q : ℕ} (hq : 0 < q) :
    r ^ q * Real.log r ^ 2 ≤ 4 := by
  have h := Real.abs_log_mul_self_rpow_lt r (1 / 2) hr hr1 (by norm_num)
  have hs : (r ^ (1 / 2 : ℝ)) ^ 2 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have h1 : Real.log r ^ 2 * r < 4 := by
    have : (Real.log r * r ^ (1 / 2 : ℝ)) ^ 2 < 2 ^ 2 := by
      have h' : |Real.log r * r ^ (1 / 2 : ℝ)| < 2 := by simpa using h
      rw [← sq_abs]
      exact pow_lt_pow_left₀ h' (abs_nonneg _) (by norm_num)
    rw [mul_pow, hs] at this; linarith
  have hrq : r ^ q ≤ r := by
    calc r ^ q ≤ r ^ 1 := pow_le_pow_of_le_one hr.le hr1 hq
      _ = r := pow_one r
  have : r ^ q * Real.log r ^ 2 ≤ r * Real.log r ^ 2 :=
    mul_le_mul_of_nonneg_right hrq (sq_nonneg _)
  linarith

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The twist functions -/

section Twist

variable {ε : ℝ} {R : X → ℝ}

theorem log_twist_lt (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR0 : ∀ x, 0 ≤ R x)
    (hR4 : ∀ x, R x < Real.exp (-4)) (x : X) : Real.log (ε + R x) < -3 :=
  log_add_lt_neg_three' hε hε4 (hR0 x) (hR4 x)

theorem twistA_pos (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR0 : ∀ x, 0 ≤ R x)
    (hR4 : ∀ x, R x < Real.exp (-4)) (x : X) : 0 < twistA ε R x := by
  have ht := log_twist_lt hε hε4 hR0 hR4 x
  have := neg_le_twistMu hε.le (t := Real.log (ε + R x)) (by linarith)
  unfold twistA; linarith

theorem twistBX_pos (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR0 : ∀ x, 0 ≤ R x)
    (hR4 : ∀ x, R x < Real.exp (-4)) (x : X) : 0 < twistBX ε R x := by
  have ht := log_twist_lt hε hε4 hR0 hR4 x
  unfold twistBX twistB; nlinarith

theorem twist_sum_le_log_eps (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR0 : ∀ x, 0 ≤ R x)
    (hR4 : ∀ x, R x < Real.exp (-4)) (x : X) :
    twistA ε R x + twistBX ε R x ≤ 5 * Real.log ε ^ 2 := by
  have ht := log_twist_lt hε hε4 hR0 hR4 x
  have hε1 : ε ≤ 1 := by
    have : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have h1 := twistMu_add_twistB_le hε1 ht.le
  have h2 : Real.log ε ≤ Real.log (ε + R x) := Real.log_le_log hε (by linarith [hR0 x])
  unfold twistA twistBX; nlinarith

theorem twist_sum_mul_pow_le (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR4 : ∀ x, R x < Real.exp (-4))
    {q : ℕ} (hq : 0 < q) {x : X} (hx : 0 < R x) :
    (twistA ε R x + twistBX ε R x) * R x ^ q ≤ 20 := by
  obtain ⟨-, -, h3, h4⟩ := twist_sum_le_five_sq hε hε4 hx (hR4 x)
  have hR1 : R x ≤ 1 := by
    have : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith [hR4 x]
  have h5 := sq_mul_rpow_log_le hx hR1 hq
  have hpow : 0 ≤ R x ^ q := pow_nonneg hx.le q
  unfold twistA twistBX
  nlinarith

theorem chartSmooth_twistA (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) (hR : ChartSmooth (n := n) R)
    (hR0 : ∀ x, 0 ≤ R x) (hR4 : ∀ x, R x < Real.exp (-4)) : ChartSmooth (n := n) (twistA ε R) := by
  intro c z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have ht := log_twist_lt hε hε4 hR0 hR4 (c.val.symm z)
  have hRz : ContDiffAt ℝ ∞ (fun y => R (c.val.symm y)) z :=
    (hR c).contDiffAt (c.val.open_target.mem_nhds hz)
  have hl : ContDiffAt ℝ ∞ (fun y => Real.log (ε + R (c.val.symm y))) z :=
    (contDiffAt_const.add hRz).log (by linarith [hR0 (c.val.symm z)])
  exact (contDiffAt_twistMu ε (by linarith)).comp z hl

theorem chartSmooth_twistBX (hε : 0 < ε) (hR : ChartSmooth (n := n) R) (hR0 : ∀ x, 0 ≤ R x) :
    ChartSmooth (n := n) (twistBX ε R) := by
  intro c z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have hRz : ContDiffAt ℝ ∞ (fun y => R (c.val.symm y)) z :=
    (hR c).contDiffAt (c.val.open_target.mem_nhds hz)
  have hl : ContDiffAt ℝ ∞ (fun y => Real.log (ε + R (c.val.symm y))) z :=
    (contDiffAt_const.add hRz).log (by linarith [hR0 (c.val.symm z)])
  exact (contDiffAt_const.sub hl).pow 2

end Twist

/-! ### Sections -/

section Sections

variable (V : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- A section holomorphic on `X` is an element of `H⁰(X, V)`. -/
theorem exists_holomorphicSections {S : (x : X) → V.Fiber x}
    (hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber S univ) :
    ∃ σ : HolomorphicSections (n := n) V.Fiber, ∀ x, σ x = S x := by
  refine ⟨⟨S, fun x => ?_⟩, fun x => rfl⟩
  set e := trivializationAt ℂ V.Fiber x
  have hE : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V.Fiber x
  rw [Trivialization.contMDiffAt_section_iff e hE]
  set c := complexChartAt (n := n) x
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  have hgd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn e c isOpen_univ hS
  set O := c.val.target ∩ c.val.symm ⁻¹' (univ ∩ e.baseSet)
  have hOo : IsOpen O := c.val.isOpen_inter_preimage_symm (isOpen_univ.inter e.open_baseSet)
  have hxO : c.val x ∈ O := ⟨c.val.map_source hxc, by simp [c.val.left_inv hxc, hE]⟩
  have hev : (fun y => (e ⟨y, S y⟩).2) =ᶠ[𝓝 x]
      fun y => (fun z => e.continuousLinearMapAt ℂ (c.val.symm z) (S (c.val.symm z))) (c.val y) := by
    filter_upwards [c.val.open_source.mem_nhds hxc, e.open_baseSet.mem_nhds hE] with y hy hyE
    show (e ⟨y, S y⟩).2 =
      e.continuousLinearMapAt ℂ (c.val.symm (c.val y)) (S (c.val.symm (c.val y)))
    rw [c.val.left_inv hy, Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hyE]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have hsC := contDiffAt_of_differentiableOn_complex hgd hOo hxO
  exact hsC.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.property) hxc)

/-- A holomorphic section is smooth in every chart and frame. -/
theorem isSmoothSectionOn_of_holomorphic {S : (x : X) → V.Fiber x}
    (hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber S univ) :
    IsSmoothSectionOn V S univ := by
  intro c e
  have := e.property
  have hgd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn e.val c isOpen_univ hS
  have hO : c.val.target ∩ c.val.symm ⁻¹' (univ ∩ e.val.baseSet) =
      chartFrameDomain V c e ∩ c.val.symm ⁻¹' univ := by
    ext z; simp [chartFrameDomain]
  rw [hO] at hgd
  refine (contDiffOn_real_of_differentiableOn_complex hgd ?_).congr fun z hz => ?_
  · rw [preimage_univ, inter_univ]; exact isOpen_chartFrameDomain V c e
  · exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz.1.2 _).symm

theorem frameCoeff_sub_apply (e : AtlasFrame V) {x : X} (hx : x ∈ e.val.baseSet)
    (a b : V.Fiber x) : (e.val ⟨x, a - b⟩).2 = (e.val ⟨x, a⟩).2 - (e.val ⟨x, b⟩).2 := by
  have := e.property
  change e.val.linearEquivAt ℂ x hx (a - b) =
    e.val.linearEquivAt ℂ x hx a - e.val.linearEquivAt ℂ x hx b
  rw [map_sub]

theorem isSmoothSectionOn_sub {G S : (x : X) → V.Fiber x} (hG : IsSmoothSectionOn V G univ)
    (hS : IsSmoothSectionOn V S univ) : IsSmoothSectionOn V (fun x => G x - S x) univ := by
  intro c e
  refine ((hG c e).sub (hS c e)).congr fun z hz => ?_
  exact frameCoeff_sub_apply V e hz.1.2 _ _

end Sections

/-! ### The weight `e^{-ψ}` against `e^{-Φ} R^{-q}` -/

section Weight

variable {Φ : X → EReal} {q : ℕ} {R : X → ℝ}

/-- For `F ≥ 0` vanishing on `{R = 0}`: `F e^{-ψ} = F R^{-q} e^{-Φ}`. -/
theorem ofReal_mul_mw_poleWeight (hΦ : ∀ x, Φ x ≠ ⊤) (hR0 : ∀ x, 0 ≤ R x) {F : X → ℝ} (x : X)
    (hF : R x = 0 → F x = 0) :
    ENNReal.ofReal (F x) * multiplierWeight 1 (poleWeight Φ q R x) =
      ENNReal.ofReal (F x * (R x ^ q)⁻¹) * multiplierWeight 1 (Φ x) := by
  rcases (hR0 x).lt_or_eq with hx | hx
  · rw [multiplierWeight_poleWeight hΦ q hx, mul_comm (multiplierWeight 1 (Φ x)), ← mul_assoc,
      ← ENNReal.ofReal_mul' (inv_nonneg.mpr (pow_nonneg hx.le q))]
  · rw [hF hx.symm, zero_mul, ENNReal.ofReal_zero, zero_mul, zero_mul]

/-- `e^{-ψ} = e^{-Φ} e^{-q log R}` everywhere. -/
theorem mw_poleWeight_eq (hΦ : ∀ x, Φ x ≠ ⊤) (x : X) :
    multiplierWeight 1 (poleWeight Φ q R x) =
      multiplierWeight 1 (Φ x) * multiplierWeight (q : ℝ) (logPole R x) := by
  rw [poleWeight, multiplierWeight_one_add (hΦ x) (coe_mul_logPole_ne_top q R x),
    multiplierWeight_one_coe_mul]

end Weight

/-! ### Steps 2--4 for a fixed `ε` -/

section Eps

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- The real indicator bound used for the densities: for `α, β ≥ 0`,
`(2 α 1_{shell} |G|² + 2 ρ(R/ε)² β D_G) R^{-q} ≤ 2α 1_{shell} |G|² R^{-q} + 2β 1_{R<ε} D_G R^{-q}`. -/
theorem density_mul_le {ε : ℝ} (hε : 0 < ε) {R : X → ℝ} {q : ℕ} {g Dg : X → ℝ}
    (hDg0 : ∀ x, 0 ≤ Dg x) {α β : ℝ} (hβ : 0 ≤ β) {x : X}
    (hx : 0 < R x) :
    (2 * ((shell ε R).indicator (fun _ => α) x * g x) + 2 * (cutR ε R x ^ 2 * (β * Dg x))) *
        (R x ^ q)⁻¹ ≤
      2 * α * (shell ε R).indicator (fun x => g x * (R x ^ q)⁻¹) x +
        2 * β * {x | R x < ε}.indicator (fun x => Dg x * (R x ^ q)⁻¹) x := by
  have hr : 0 ≤ (R x ^ q)⁻¹ := inv_nonneg.mpr (pow_nonneg hx.le q)
  have hcut := cutR_sq_le_indicator hε R x
  have h1 : (shell ε R).indicator (fun _ => α) x * g x * (R x ^ q)⁻¹ =
      α * (shell ε R).indicator (fun x => g x * (R x ^ q)⁻¹) x := by
    by_cases hs : x ∈ shell ε R
    · rw [indicator_of_mem hs, indicator_of_mem hs]; ring
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]; ring
  have h2 : cutR ε R x ^ 2 * (β * Dg x) * (R x ^ q)⁻¹ ≤
      β * {x | R x < ε}.indicator (fun x => Dg x * (R x ^ q)⁻¹) x := by
    by_cases ht : x ∈ {x | R x < ε}
    · rw [indicator_of_mem ht] at hcut ⊢
      have : 0 ≤ β * Dg x * (R x ^ q)⁻¹ := by have := hDg0 x; positivity
      nlinarith
    · rw [indicator_of_notMem ht] at hcut ⊢
      have h0 : cutR ε R x ^ 2 = 0 := le_antisymm hcut (sq_nonneg _)
      rw [h0]; simp
  nlinarith

theorem ofReal_indicator_mul {s : Set X} {f : X → ℝ} {w : X → ℝ≥0∞} (x : X) :
    ENNReal.ofReal (s.indicator f x) * w x = s.indicator (fun x => ENNReal.ofReal (f x) * w x) x := by
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero, zero_mul]

/-- **Steps 2--4 of FPT `thm:compact-submanifold-extension` for a fixed `ε`.** -/
theorem exists_section_eps (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (hWc : IsClosed W) (hmn : m < n)
    {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) {b : ℝ} (hb0 : 0 ≤ b)
    (hbR : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
      ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi +
          b * kahlerQuad ωb c z v)
    {bK : ℝ} (hbK0 : 0 ≤ bK)
    (hRic : ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ),
      IsChartDensity (IntegrationCurrent.kahlerVolume ωb) c ρ →
      ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        leviForm (fun y => Real.log (ρ y)) z v ≤ bK * kahlerQuad ωb c z v)
    {Bρ : ℝ} (hBρ : ∀ t, |deriv TwistedL2.cutoffProfile t| ≤ Bρ)
    {MR : ℝ} (hMR0 : 0 ≤ MR)
    (hMR : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      holDerivSq (fun y => R (c.val.symm y)) z v ≤ MR * kahlerQuad ωb c z v)
    {V : HermitianHolomorphicLineBundle.{0, 0} n X} (hV : IsSourceSmoothHermitianMetric V)
    {θV : ClosedRealOneOneForm n X} (hθV : SGPT.PSH.GlobalL2.IsOwnFirstChernForm V θV)
    {Φ : X → EReal}
    (hΦ : IsThetaPshPotential
      (θV - (1 + bK / Real.pi + (((n - m : ℕ) : ℝ) + 2) * b) • ωb.form).val Φ)
    {c₀ : ℚ} {𝔞 : HolomorphicIdealSheaves.GermIdeal n X}
    (hgen : ActualOriginalSquaredDensityGentle.HasGentleAnalyticSingularitiesOfType (n := n) Φ c₀ 𝔞)
    {M : ℝ} (hΦM : ∀ x, Φ x ≤ M)
    {G : (x : X) → V.Fiber x} (hG : IsSmoothSectionOn V G univ) {Dg : X → ℝ}
    (hDg0 : ∀ x, 0 ≤ Dg x) (hDgW : ∀ x ∈ W, Dg x = 0)
    (hDg : ∀ (c : ComplexChart n X) (e : AtlasFrame V), ∀ z ∈ chartFrameDomain V c e,
      ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff V c e G) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
          Dg (c.val.symm z) * kahlerQuad ωb c z v)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4))
    (hI : ∫⁻ x in shell ε R, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ (n - m))⁻¹) *
      multiplierWeight 1 (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb) ≠ ⊤)
    (hJ : ∫⁻ x in {x | R x < ε}, ENNReal.ofReal (Dg x * (R x ^ (n - m))⁻¹) *
      multiplierWeight 1 (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb) ≠ ⊤) :
    ∃ s : HolomorphicSections (n := n) V.Fiber, (∀ y ∈ W, s y = G y) ∧
      ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight 1 (Φ x)
          ∂(IntegrationCurrent.kahlerVolume ωb) ≤
        2 * (ENNReal.ofReal 20 * (ENNReal.ofReal (32 * Bρ ^ 2) *
          (∫⁻ x in shell ε R, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ (n - m))⁻¹) *
            multiplierWeight 1 (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb)) +
          ENNReal.ofReal (2 / Real.pi) *
          (∫⁻ x in {x | R x < ε}, ENNReal.ofReal (Dg x * (R x ^ (n - m))⁻¹) *
            multiplierWeight 1 (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb)))) +
        2 * ∫⁻ x in {x | R x < ε}, ENNReal.ofReal (‖G x‖ ^ 2) * multiplierWeight 1 (Φ x)
          ∂(IntegrationCurrent.kahlerVolume ωb) := by
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  set q := n - m with hqdef
  have hq : 0 < q := Nat.sub_pos_of_lt hmn
  have hΦt : ∀ x, Φ x ≠ ⊤ := hΦ.1.quasiPlurisubharmonic.ne_top
  have hΦm : Measurable Φ := hΦ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hwm : Measurable fun x => multiplierWeight 1 (Φ x) :=
    (multiplierWeight_antitone zero_le_one).measurable.comp hΦm
  set N₀ : ℝ := 1 + bK / Real.pi + (((n - m : ℕ) : ℝ) + 2) * b with hN₀
  have hN₀0 : 0 ≤ N₀ := by
    have : 0 ≤ bK / Real.pi := div_nonneg hbK0 Real.pi_pos.le
    have : 0 ≤ (((n - m : ℕ) : ℝ) + 2) * b := mul_nonneg (by positivity) hb0
    linarith
  have hΦθ : IsThetaPshPotential θV.val Φ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hΦ
      (KahlerDomination.isSemipositive_smul ωb.isSemipositive hN₀0)
    rwa [sub_add_cancel] at h
  set ψ := poleWeight Φ q R with hψdef
  have hψ : IsAdmissibleSingularWeight (n := n) ψ :=
    isAdmissibleSingularWeight_poleWeight ωb hWc hR hΦθ hgen hq
  have hRc : Continuous R := hR.continuous
  have hRm : Measurable fun x => (R x ^ q)⁻¹ := ((hRc.pow q).measurable).inv
  have hGc : Continuous fun x => ‖G x‖ := continuous_norm_of_isSmoothSectionOn V hG
  have hshm : MeasurableSet (shell ε R) :=
    ((isClosed_le continuous_const hRc).inter (isClosed_le hRc continuous_const)).measurableSet
  have hltm : MeasurableSet {x | R x < ε} := (isOpen_lt hRc continuous_const).measurableSet
  -- the two integrands
  set fI : X → ℝ≥0∞ := (shell ε R).indicator
    (fun x => ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ q)⁻¹) * multiplierWeight 1 (Φ x)) with hfI
  set fJ : X → ℝ≥0∞ := {x | R x < ε}.indicator
    (fun x => ENNReal.ofReal (Dg x * (R x ^ q)⁻¹) * multiplierWeight 1 (Φ x)) with hfJ
  have hfIm : Measurable fI := (((ENNReal.measurable_ofReal.comp
    (((hGc.pow 2).measurable).mul hRm)).mul hwm)).indicator hshm
  have hIeq : ∫⁻ x, fI x ∂μ = ∫⁻ x in shell ε R, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ q)⁻¹) *
      multiplierWeight 1 (Φ x) ∂μ := lintegral_indicator hshm _
  have hJeq : ∫⁻ x, fJ x ∂μ = ∫⁻ x in {x | R x < ε}, ENNReal.ofReal (Dg x * (R x ^ q)⁻¹) *
      multiplierWeight 1 (Φ x) ∂μ := lintegral_indicator hltm _
  -- the weight bound for a density
  have hwt : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → ∀ x,
      ENNReal.ofReal (2 * ((shell ε R).indicator (fun _ => α) x * ‖G x‖ ^ 2) +
        2 * (cutR ε R x ^ 2 * (β * Dg x))) * multiplierWeight 1 (ψ x) ≤
      ENNReal.ofReal (2 * α) * fI x + ENNReal.ofReal (2 * β) * fJ x := by
    intro α β hα hβ x
    have hF0 : R x = 0 → 2 * ((shell ε R).indicator (fun _ => α) x * ‖G x‖ ^ 2) +
        2 * (cutR ε R x ^ 2 * (β * Dg x)) = 0 := by
      intro hx0
      have hxs : x ∉ shell ε R := fun h => by have := h.1; rw [hx0] at this; linarith
      rw [indicator_of_notMem hxs, hDgW x ((hR.eq_zero_iff x).mp hx0)]
      ring
    have hrw := ofReal_mul_mw_poleWeight (q := q) (F := fun y => 2 * ((shell ε R).indicator
      (fun _ => α) y * ‖G y‖ ^ 2) + 2 * (cutR ε R y ^ 2 * (β * Dg y))) hΦt hR.nonneg x hF0
    try simp only at hrw
    rw [hψdef, hrw]
    rcases (hR.nonneg x).lt_or_eq with hx | hx
    · have hle := density_mul_le hε (q := q) (g := fun x => ‖G x‖ ^ 2) hDg0 (α := α) hβ hx
      have hI0 : 0 ≤ (shell ε R).indicator (fun x => ‖G x‖ ^ 2 * (R x ^ q)⁻¹) x :=
        indicator_nonneg (fun y _ => mul_nonneg (sq_nonneg _)
          (inv_nonneg.mpr (pow_nonneg (hR.nonneg y) q))) x
      have hJ0 : 0 ≤ {x | R x < ε}.indicator (fun x => Dg x * (R x ^ q)⁻¹) x :=
        indicator_nonneg (fun y _ => mul_nonneg (hDg0 y)
          (inv_nonneg.mpr (pow_nonneg (hR.nonneg y) q))) x
      calc ENNReal.ofReal ((2 * ((shell ε R).indicator (fun _ => α) x * ‖G x‖ ^ 2) +
            2 * (cutR ε R x ^ 2 * (β * Dg x))) * (R x ^ q)⁻¹) * multiplierWeight 1 (Φ x)
          ≤ ENNReal.ofReal (2 * α * (shell ε R).indicator (fun x => ‖G x‖ ^ 2 * (R x ^ q)⁻¹) x +
              2 * β * {x | R x < ε}.indicator (fun x => Dg x * (R x ^ q)⁻¹) x) *
              multiplierWeight 1 (Φ x) := by gcongr
        _ = ENNReal.ofReal (2 * α) * fI x + ENNReal.ofReal (2 * β) * fJ x := by
          have e1 : ENNReal.ofReal ((shell ε R).indicator (fun x => ‖G x‖ ^ 2 * (R x ^ q)⁻¹) x) *
              multiplierWeight 1 (Φ x) = fI x :=
            ofReal_indicator_mul (w := fun x => multiplierWeight 1 (Φ x)) x
          have e2 : ENNReal.ofReal ({x | R x < ε}.indicator (fun x => Dg x * (R x ^ q)⁻¹) x) *
              multiplierWeight 1 (Φ x) = fJ x :=
            ofReal_indicator_mul (w := fun x => multiplierWeight 1 (Φ x)) x
          rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul,
            ENNReal.ofReal_mul (p := 2 * α) (by positivity),
            ENNReal.ofReal_mul (p := 2 * β) (by positivity), mul_assoc, mul_assoc, e1, e2]
    · rw [← hx, zero_pow hq.ne', inv_zero, mul_zero, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  have hfin : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      ∫⁻ x, ENNReal.ofReal (2 * ((shell ε R).indicator (fun _ => α) x * ‖G x‖ ^ 2) +
        2 * (cutR ε R x ^ 2 * (β * Dg x))) * multiplierWeight 1 (ψ x) ∂μ ≤
      ENNReal.ofReal (2 * α) * ∫⁻ x, fI x ∂μ + ENNReal.ofReal (2 * β) * ∫⁻ x, fJ x ∂μ := by
    intro α β hα hβ
    refine (lintegral_mono fun x => hwt α β hα hβ x).trans (le_of_eq ?_)
    rw [lintegral_add_left (hfIm.const_mul _), lintegral_const_mul _ hfIm,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hIJ : ∀ α β : ℝ, ENNReal.ofReal (2 * α) * ∫⁻ x, fI x ∂μ +
      ENNReal.ofReal (2 * β) * ∫⁻ x, fJ x ∂μ < ⊤ := by
    intro α β
    rw [hIeq, hJeq]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hI), ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hJ)⟩
  have hRpos : ∀ x, ψ x ≠ ⊥ → 0 < R x := by
    intro x hx
    rw [hψdef, ne_eq, poleWeight_eq_bot_iff hq, not_or] at hx
    exact hR.pos_of_notMem fun h => hx.2 ((hR.pole.eq_bot_iff _).mpr h)
  -- the curvature
  have hcurv : ∀ (c : ComplexChart n X) (e : AtlasFrame V) (ρ : ComplexModel n → ℝ),
      IsChartDensity μ c ρ → ∀ z ∈ chartFrameDomain V c e, ψ (c.val.symm z) ≠ ⊥ →
      ∀ v : ComplexModel n, Real.pi * kahlerQuad ωb c z v + ε / R (c.val.symm z) *
          holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v ≤
        twistedCurvature (fun y => twistA ε R (c.val.symm y)) (fun y => twistBX ε R (c.val.symm y))
          (localWeight V c e ρ fun x => (ψ x).toReal) z v :=
    fun c e ρ hρ z hz hψz v =>
      twistedCurvature_poleWeight_ge ωb hR hb0 hbR hRic hV hθV hq hΦ hgen hε hε4 c e ρ hρ hz hψz v
  have hpos : ∀ (c : ComplexChart n X) (e : AtlasFrame V) (ρ : ComplexModel n → ℝ),
      IsChartDensity μ c ρ → ∀ z ∈ chartFrameDomain V c e, ψ (c.val.symm z) ≠ ⊥ →
      ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => twistA ε R (c.val.symm y))
          (fun y => twistBX ε R (c.val.symm y)) (localWeight V c e ρ fun x => (ψ x).toReal) z v := by
    intro c e ρ hρ z hz hψz v hv
    have h := hcurv c e ρ hρ z hz hψz v
    have hq' := kahlerQuad_pos ωb c hz.1 hv
    have : 0 ≤ ε / R (c.val.symm z) * holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v :=
      mul_nonneg (div_nonneg hε.le (hRpos _ hψz).le) (holDerivSq_nonneg _ _ _)
    nlinarith [Real.pi_pos]
  -- the densities
  set α₁ : ℝ := 16 * Bρ ^ 2 with hα₁
  set β₁ : ℝ := 1 / Real.pi with hβ₁
  set α₂ : ℝ := (Bρ * (2 / ε)) ^ 2 * MR with hα₂
  have hα₁0 : 0 ≤ α₁ := by positivity
  have hβ₁0 : 0 ≤ β₁ := by positivity
  have hα₂0 : 0 ≤ α₂ := by positivity
  set D : X → ℝ := fun x => 2 * ((shell ε R).indicator (fun _ => α₁) x * ‖G x‖ ^ 2) +
    2 * (cutR ε R x ^ 2 * (β₁ * Dg x)) with hDdef
  set Dω : X → ℝ := fun x => 2 * ((shell ε R).indicator (fun _ => α₂) x * ‖G x‖ ^ 2) +
    2 * (cutR ε R x ^ 2 * (1 * Dg x)) with hDωdef
  have hD : ∀ (c : ComplexChart n X) (e : AtlasFrame V) (ρ : ComplexModel n → ℝ),
      IsChartDensity μ c ρ → ∀ z ∈ chartFrameDomain V c e, ψ (c.val.symm z) ≠ ⊥ →
      ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff V c e (cutSec V ε R G)) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => twistA ε R (c.val.symm y))
            (fun y => twistBX ε R (c.val.symm y)) (localWeight V c e ρ fun x => (ψ x).toReal) z v := by
    intro c e ρ hρ z hz hψz v
    set H := twistedCurvature (fun y => twistA ε R (c.val.symm y))
      (fun y => twistBX ε R (c.val.symm y)) (localWeight V c e ρ fun x => (ψ x).toReal) z v
    have hc := hcurv c e ρ hρ z hz hψz v
    have hRz := hRpos _ hψz
    have hkq := kahlerQuad_nonneg ωb c hz.1 v
    have hds := holDerivSq_nonneg (fun y => Real.log (ε + R (c.val.symm y))) z v
    have hH1 : ε / R (c.val.symm z) *
        holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v ≤ H := by
      have : 0 ≤ Real.pi * kahlerQuad ωb c z v := by positivity
      linarith
    have hH2 : Real.pi * kahlerQuad ωb c z v ≤ H := by
      have : 0 ≤ ε / R (c.val.symm z) * holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v :=
        mul_nonneg (div_nonneg hε.le hRz.le) hds
      linarith
    have h1 := dbar_cutSec_le V ωb (ε := ε) hR.smooth hG hDg c e hz v
    have h2 := holDerivSq_cutR_le_twisted hε hBρ hR.smooth hR.nonneg c hz.1 hRz v hH1
    have hDgz := hDg0 (c.val.symm z)
    have h3 : Dg (c.val.symm z) * kahlerQuad ωb c z v ≤ β₁ * Dg (c.val.symm z) * H := by
      have : kahlerQuad ωb c z v ≤ H / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]; linarith
      calc Dg (c.val.symm z) * kahlerQuad ωb c z v ≤ Dg (c.val.symm z) * (H / Real.pi) :=
            mul_le_mul_of_nonneg_left this hDgz
        _ = β₁ * Dg (c.val.symm z) * H := by rw [hβ₁]; ring
    have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖G (c.val.symm z)‖)
    have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (cutR ε R (c.val.symm z)))
    have e1 : D (c.val.symm z) * H = 2 * ((shell ε R).indicator (fun _ => 16 * Bρ ^ 2)
        (c.val.symm z) * H * ‖G (c.val.symm z)‖ ^ 2) +
        2 * (cutR ε R (c.val.symm z) ^ 2 * (β₁ * Dg (c.val.symm z) * H)) := by
      simp only [hDdef]; ring
    rw [e1]
    linarith
  have hDω : ∀ (c : ComplexChart n X) (e : AtlasFrame V), ∀ z ∈ chartFrameDomain V c e,
      ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff V c e (cutSec V ε R G)) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
          Dω (c.val.symm z) * kahlerQuad ωb c z v := by
    intro c e z hz _ v
    have h1 := dbar_cutSec_le V ωb (ε := ε) hR.smooth hG hDg c e hz v
    have h2 := holDerivSq_cutR_le hε hBρ hR.smooth c hz.1 v
    have h3 := hMR c z hz.1 v
    have hi0 : 0 ≤ (shell ε R).indicator (fun _ => (Bρ * (2 / ε)) ^ 2) (c.val.symm z) :=
      indicator_nonneg (fun _ _ => sq_nonneg _) _
    have hind : (shell ε R).indicator (fun _ => (Bρ * (2 / ε)) ^ 2) (c.val.symm z) * MR =
        (shell ε R).indicator (fun _ => α₂) (c.val.symm z) := by
      by_cases hs : c.val.symm z ∈ shell ε R
      · rw [indicator_of_mem hs, indicator_of_mem hs]
      · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]
    have h4 : holDerivSq (fun y => cutR ε R (c.val.symm y)) z v ≤
        (shell ε R).indicator (fun _ => α₂) (c.val.symm z) * kahlerQuad ωb c z v := by
      calc holDerivSq (fun y => cutR ε R (c.val.symm y)) z v
          ≤ (shell ε R).indicator (fun _ => (Bρ * (2 / ε)) ^ 2) (c.val.symm z) *
              holDerivSq (fun y => R (c.val.symm y)) z v := h2
        _ ≤ (shell ε R).indicator (fun _ => (Bρ * (2 / ε)) ^ 2) (c.val.symm z) *
              (MR * kahlerQuad ωb c z v) := mul_le_mul_of_nonneg_left h3 hi0
        _ = _ := by rw [← hind]; ring
    have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖G (c.val.symm z)‖)
    have e1 : Dω (c.val.symm z) * kahlerQuad ωb c z v =
        2 * ((shell ε R).indicator (fun _ => α₂) (c.val.symm z) * kahlerQuad ωb c z v *
          ‖G (c.val.symm z)‖ ^ 2) +
        2 * (cutR ε R (c.val.symm z) ^ 2 * (Dg (c.val.symm z) * kahlerQuad ωb c z v)) := by
      simp only [hDωdef]; ring
    rw [e1]
    linarith
  have hDint : ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ < ⊤ :=
    (hfin α₁ β₁ hα₁0 hβ₁0).trans_lt (hIJ α₁ β₁)
  have hDωint : ∫⁻ x, ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x) ∂μ < ⊤ :=
    (hfin α₂ 1 hα₂0 zero_le_one).trans_lt (hIJ α₂ 1)
  -- the twisted `L²` estimate
  obtain ⟨S, hShol, hSint⟩ := compactTwistedL2CorrectionStatement_manifold (n := n) (X := X)
    inferInstance ωb μ hμ V hV ψ hψ (twistA ε R) (twistBX ε R)
    (chartSmooth_twistA hε hε4 hR.smooth hR.nonneg hR.lt_exp)
    (chartSmooth_twistBX hε hR.smooth hR.nonneg) (twistA_pos hε hε4 hR.nonneg hR.lt_exp)
    (twistBX_pos hε hε4 hR.nonneg hR.lt_exp) hpos (cutSec V ε R G)
    (isSmoothSectionOn_cutSec V hR.smooth hG) D Dω hD hDω hDωint
  obtain ⟨σ, hσ⟩ := exists_holomorphicSections V hShol
  set u : (x : X) → V.Fiber x := fun x => cutSec V ε R G x - S x with hudef
  have hus : IsSmoothSectionOn V u univ := isSmoothSectionOn_sub V
    (isSmoothSectionOn_cutSec V hR.smooth hG) (isSmoothSectionOn_of_holomorphic V hShol)
  have huc : Continuous fun x => ‖u x‖ := continuous_norm_of_isSmoothSectionOn V hus
  have hSfin : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 / (twistA ε R x + twistBX ε R x)) *
      multiplierWeight 1 (ψ x) ∂μ < ⊤ := hSint.trans_lt hDint
  have hab : ∀ x, 0 < twistA ε R x + twistBX ε R x := fun x =>
    add_pos (twistA_pos hε hε4 hR.nonneg hR.lt_exp x) (twistBX_pos hε hε4 hR.nonneg hR.lt_exp x)
  -- Step 3: the critical integral of `u_ε` is finite, so `u_ε = 0` on `W`
  have hcrit : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) *
      multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.ofReal_ne_top (r := 5 * Real.log ε ^ 2 * Real.exp M)) hSfin.ne) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [mw_poleWeight_eq hΦt x]
    have hw : ENNReal.ofReal (Real.exp (-M)) ≤ multiplierWeight 1 (Φ x) := by
      have := multiplierWeight_antitone zero_le_one (hΦM x)
      rwa [multiplierWeight_coe, one_mul] at this
    have hA := hab x
    have hle := twist_sum_le_log_eps hε hε4 hR.nonneg hR.lt_exp x
    set A := twistA ε R x + twistBX ε R x
    have hreal : ‖u x‖ ^ 2 ≤ 5 * Real.log ε ^ 2 * Real.exp M * (‖u x‖ ^ 2 / A) *
        Real.exp (-M) := by
      have e : 5 * Real.log ε ^ 2 * Real.exp M * (‖u x‖ ^ 2 / A) * Real.exp (-M) =
          5 * Real.log ε ^ 2 * (‖u x‖ ^ 2 / A) * (Real.exp M * Real.exp (-M)) := by ring
      rw [e, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_div_assoc',
        le_div_iff₀ hA]
      nlinarith [sq_nonneg ‖u x‖]
    calc ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x)
        ≤ ENNReal.ofReal (5 * Real.log ε ^ 2 * Real.exp M * (‖u x‖ ^ 2 / A) * Real.exp (-M)) *
            multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x) := by gcongr
      _ = ENNReal.ofReal (5 * Real.log ε ^ 2 * Real.exp M) * (ENNReal.ofReal (‖u x‖ ^ 2 / A) *
            (ENNReal.ofReal (Real.exp (-M)) * multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (5 * Real.log ε ^ 2 * Real.exp M) * (ENNReal.ofReal (‖u x‖ ^ 2 / A) *
            (multiplierWeight 1 (Φ x) * multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x))) := by
          gcongr
  have hu0 : ∀ y ∈ W, u y = 0 := by
    intro y hy
    have h := eq_zero_of_lintegral_logPole hμ hWreg hmn hR (huc.pow 2) hcrit hy
    have h2 : ‖u y‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hcut1 : ∀ y ∈ W, cutSec V ε R G y = G y := by
    intro y hy
    have hc1 : cutR ε R y = 1 := cutR_eq_one hε (by rw [(hR.eq_zero_iff y).mpr hy]; linarith)
    simp [cutSec, hc1]
  refine ⟨σ, fun y hy => ?_, ?_⟩
  · rw [hσ y, ← hcut1 y hy]
    exact (sub_eq_zero.mp (hu0 y hy)).symm
  -- Step 4: the norm bound
  have hσu : ∀ x, ‖σ x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * ‖cutSec V ε R G x‖ ^ 2 := by
    intro x
    have h : σ x = cutSec V ε R G x - u x := by rw [hσ x, hudef]; exact (sub_sub_cancel _ _).symm
    rw [h]
    have := norm_sub_le (cutSec V ε R G x) (u x)
    nlinarith [norm_nonneg (cutSec V ε R G x), norm_nonneg (u x),
      norm_nonneg (cutSec V ε R G x - u x), sq_nonneg (‖cutSec V ε R G x‖ - ‖u x‖)]
  have hcutG : ∀ x, ‖cutSec V ε R G x‖ ^ 2 ≤ {x | R x < ε}.indicator (fun x => ‖G x‖ ^ 2) x := by
    intro x
    have hc := cutR_sq_le_indicator hε R x
    rw [cutSec, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    by_cases ht : x ∈ {x | R x < ε}
    · rw [indicator_of_mem ht] at hc ⊢
      nlinarith [sq_nonneg ‖G x‖]
    · rw [indicator_of_notMem ht] at hc ⊢
      have : cutR ε R x ^ 2 = 0 := le_antisymm hc (sq_nonneg _)
      rw [this, zero_mul]
  set gG : X → ℝ≥0∞ := {x | R x < ε}.indicator
    (fun x => ENNReal.ofReal (‖G x‖ ^ 2) * multiplierWeight 1 (Φ x)) with hgG
  have hgGm : Measurable gG :=
    ((ENNReal.measurable_ofReal.comp (hGc.pow 2).measurable).mul hwm).indicator hltm
  have hpt : ∀ x, ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight 1 (Φ x) ≤
      2 * (ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x)) + 2 * gG x := by
    intro x
    have h1 : ‖σ x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 +
        2 * {x | R x < ε}.indicator (fun x => ‖G x‖ ^ 2) x := by
      have := hcutG x; have := hσu x; linarith
    have hg0 : 0 ≤ {x | R x < ε}.indicator (fun x => ‖G x‖ ^ 2) x :=
      indicator_nonneg (fun _ _ => sq_nonneg _) _
    calc ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight 1 (Φ x)
        ≤ ENNReal.ofReal (2 * ‖u x‖ ^ 2 + 2 * {x | R x < ε}.indicator (fun x => ‖G x‖ ^ 2) x) *
            multiplierWeight 1 (Φ x) := by gcongr
      _ = 2 * (ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x)) + 2 * gG x := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_assoc, mul_assoc, hgG,
            ofReal_indicator_mul (w := fun x => multiplierWeight 1 (Φ x))]
  have hu20 : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ ≤
      ENNReal.ofReal 20 * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 / (twistA ε R x + twistBX ε R x)) *
        multiplierWeight 1 (ψ x) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hxW : x ∈ W
    · rw [hu0 x hxW, norm_zero]; simp
    · have hx := hR.pos_of_notMem hxW
      rw [hψdef, multiplierWeight_poleWeight hΦt q hx]
      have hA := hab x
      have hle := twist_sum_mul_pow_le hε hε4 hR.lt_exp hq hx
      set A := twistA ε R x + twistBX ε R x
      have hRq : 0 < R x ^ q := pow_pos hx q
      have hreal : ‖u x‖ ^ 2 ≤ 20 * (‖u x‖ ^ 2 / A) * (R x ^ q)⁻¹ := by
        have h1 : 1 ≤ 20 / (A * R x ^ q) := by
          rw [le_div_iff₀ (mul_pos hA hRq)]; linarith
        have h2 : 20 * (‖u x‖ ^ 2 / A) * (R x ^ q)⁻¹ = ‖u x‖ ^ 2 * (20 / (A * R x ^ q)) := by
          field_simp
        rw [h2]
        exact le_mul_of_one_le_right (sq_nonneg _) h1
      calc ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x)
          ≤ ENNReal.ofReal (20 * (‖u x‖ ^ 2 / A) * (R x ^ q)⁻¹) * multiplierWeight 1 (Φ x) := by
            gcongr
        _ = ENNReal.ofReal 20 * (ENNReal.ofReal (‖u x‖ ^ 2 / A) *
              (multiplierWeight 1 (Φ x) * ENNReal.ofReal (R x ^ q)⁻¹)) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
            ring
  have hfinD := hfin α₁ β₁ hα₁0 hβ₁0
  rw [hIeq, hJeq] at hfinD
  have e2 : ENNReal.ofReal (2 * α₁) = ENNReal.ofReal (32 * Bρ ^ 2) := by rw [hα₁]; ring_nf
  have e3 : ENNReal.ofReal (2 * β₁) = ENNReal.ofReal (2 / Real.pi) := by rw [hβ₁]; ring_nf
  rw [e2, e3] at hfinD
  calc ∫⁻ x, ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ
      ≤ ∫⁻ x, (2 * (ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x)) + 2 * gG x) ∂μ :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ +
          2 * ∫⁻ x, gG x ∂μ := by
        rw [lintegral_add_right _ (hgGm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ _ := by
        rw [hgG, lintegral_indicator hltm]
        gcongr
        refine hu20.trans ?_
        gcongr
        exact hSint.trans hfinD



end Eps

end SGPT.Trace.OTExt5
