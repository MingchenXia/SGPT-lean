import SGPT.PSH.SiuL2System

/-!
# The gluing system on `X × Δ` for a weight `mΦ + Ψ` with `Ψ ∈ PSH(X × Δ, p₁^*(s θ_G))`

Blueprint `claude-siu-gen.tex`, node `claude-siu-gen:system`.

This generalizes `SGPT.PSH.SiuL2.SiuCover.toSystem`, whose singular weight is
`mΦ + ψ_X(x) + ψ_Δ(t)` with `ψ_X ∈ PSH(X, s θ_G)` and `ψ_Δ` psh on `Δ`, to the singular weight
`mΦ + Ψ` with an arbitrary `Ψ ∈ PSH(X × Δ, p₁^*(s θ_G))` (a quasi-psh function on the product whose
negativity is controlled by `s θ_G` in the `X`-directions only).  The extra generality is needed
for Siu's argument on `X × Δ`: the weight with an isolated logarithmic pole at a point
`(x₀, t₀)` (`max((n+3) log|z - z₀|², (n+3) log|t - t₀|²)`) is not of the form `ψ_X + ψ_Δ`.

The local weights are

`Ψ_a = m(ρ_L + Φ) + (s ρ_G + Ψ) + [(K - s) ρ_G - λ|z - z_a|²]`

in the product chart of index `a` (`psiGen`); the only change with respect to `psiP` is that
`s ρ_G + Ψ` is psh as a function on the product chart (`psiGen_psh`), by the same local-potential
argument as for `Φ`.  Everything else (charts, frames, partition of unity, measure, local solver,
contraction factor) is that of `toSystem`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.NAPotential.NAGaga

/-! ### Extended-real bookkeeping -/

theorem ereal_three {m : ℝ} (hm : 0 < m) {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (ρ₁ ρ₂ g Q : ℝ) :
    (m : EReal) * ((ρ₁ : EReal) + a) + ((ρ₂ : EReal) + b) + (g : EReal) + (Q : EReal) =
      ((m : EReal) * a + b) + ((m * ρ₁ + ρ₂ + g + Q : ℝ) : EReal) := by
  induction a using EReal.rec with
  | top => exact absurd rfl ha
  | bot =>
      rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hm]
      simp
  | coe a =>
    induction b using EReal.rec with
    | top => exact absurd rfl hb
    | bot => simp
    | coe b =>
      simp only [← EReal.coe_add, ← EReal.coe_mul]
      congr 1
      ring

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SiuCover

variable {μ : Measure X} {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ L G)

/-! ### The local weights -/

/-- The local potential `s ρ_G ∘ p₁` of `p₁^*(s θ_G)` in the product chart. -/
def ρGP (s : ℝ) (a : Fin D.m) (w : ComplexModel (n + 1)) : ℝ :=
  s * D.ρG a (coordinateMap Prod.fst (D.chartP a) (D.chartX a) w)

/-- The psh part `Ψ_a = m(ρ_L + Φ) + (s ρ_G + Ψ) + g_a` of the local weight. -/
def psiGen (s : ℝ) (K m : ℕ) (Φ Ψ : X × unitDisc → EReal) (a : Fin D.m)
    (w : ComplexModel (n + 1)) : EReal :=
  ((m : ℝ) : EReal) * ((D.ρLP a w : EReal) + Φ ((D.chartP a).val.symm w)) +
    ((D.ρGP s a w : EReal) + Ψ ((D.chartP a).val.symm w)) + (D.gW s K a (projX n w) : EReal)

theorem psiGen_psh (hL : IsSourceSmoothHermitianMetric L) (hG : IsSourceSmoothHermitianMetric G)
    {θ θG : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ)
    (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    {Ψ : X × unitDisc → EReal}
    (hΨ : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
        (s • θG)).val Ψ) (a : Fin D.m) :
    PlurisubharmonicOn (D.psiGen s K m Φ Ψ a) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) := by
  have hDo := isOpen_prodDom (ctr (n := n) (D.pt a)) (D.R a) 1
  have hpX : DifferentiableOn ℂ (projX n) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    (projX n).differentiable.differentiableOn
  -- (1) the `Φ` part
  have hpot := (LocalPotentialPullback.isSmoothLocalPotential_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (D.chartP a)
    (D.isSmoothLocalPotential_ρL hL hθ a)).mono hDo (D.prodDom_subset_potentialDomain a)
  have h1 : PlurisubharmonicOn (fun w => (D.ρLP a w : EReal) + Φ ((D.chartP a).val.symm w))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    plurisubharmonicOn_add_localPotential hΦ (D.chartP a) hpot
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1' := h1.const_mul hm'
  -- (2) the `Ψ` part
  have hpotG := (LocalPotentialPullback.isSmoothLocalPotential_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (D.chartP a)
    (D.isSmoothLocalPotential_sρG hG hθG s a)).mono hDo (D.prodDom_subset_potentialDomain a)
  have h2 : PlurisubharmonicOn (fun w => (D.ρGP s a w : EReal) + Ψ ((D.chartP a).val.symm w))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    plurisubharmonicOn_add_localPotential' hΨ (D.chartP a) hpotG
  -- (3) the smooth part
  have h4X : PlurisubharmonicOn (fun z => (D.gW s K a z : EReal))
      (ball (ctr (n := n) (D.pt a)) (D.R a)) :=
    plurisubharmonicOn_of_contDiffOn_levi_nonneg isOpen_ball
      (((contDiffOn_const.mul (D.contDiffOn_ρG hG a)).sub
        (contDiff_const.mul ((contDiff_norm_sq ℝ).comp
          (contDiff_id.sub contDiff_const))).contDiffOn).mono (D.ball_subset_two a))
      fun z hz v => D.leviForm_gW_nonneg hG hK a hz v
  have h4 : PlurisubharmonicOn (fun w => (D.gW s K a (projX n w) : EReal))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hDo hpX (fun w hw => hw.1) h4X
  exact (h1'.add h2).add h4

/-! ### The density identity -/

/-- The singular part `mΦ + Ψ` of the global weight. -/
def thetaGen (m : ℕ) (Φ Ψ : X × unitDisc → EReal) (q : X × unitDisc) : EReal :=
  ((m : ℝ) : EReal) * Φ q + Ψ q

/-- The global weight `e^{-(mΦ + Ψ)} e^{-λ|t|²}` on `X × Δ`. -/
def weightGen (m : ℕ) (Φ Ψ : X × unitDisc → EReal) (q : X × unitDisc) : ℝ≥0∞ :=
  multiplierWeight 1 (thetaGen m Φ Ψ q) * ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))

theorem thetaGen_ne_top {m : ℕ} (hm : 0 < m) {Φ : X × unitDisc → EReal} (hΦ : ∀ q, Φ q ≠ ⊤)
    {Ψ : X × unitDisc → EReal} (hΨ : ∀ q, Ψ q ≠ ⊤) (q : X × unitDisc) :
    thetaGen m Φ Ψ q ≠ ⊤ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold thetaGen
  exact EReal.add_ne_top (mul_ne_top_of_pos hm' (hΦ q)) (hΨ q)

/-- **The density identity** `|u|² w = |coef_a u|² e^{-Ψ_a - λ|w - w_a|²}`. -/
theorem density_eqGen {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    {Φ : X × unitDisc → EReal} (hΦ : ∀ q, Φ q ≠ ⊤) {Ψ : X × unitDisc → EReal}
    (hΨ : ∀ q, Ψ q ≠ ⊤) (a : Fin D.m) (q : X × unitDisc)
    (u : (twistedPower L (positivePower G (K - 1)) m).Fiber q.1)
    (hq : q ∈ (D.chartP a).val.source)
    (hqz : (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    ENNReal.ofReal (‖u‖ ^ 2) * D.weightGen m Φ Ψ q =
      ENNReal.ofReal (‖(D.frameE K m a).val.continuousLinearMapAt ℂ q.1 u‖ ^ 2) *
        ballWeight (D.psiGen s K m Φ Ψ a) D.lam (D.ctrP a) ((D.chartP a).val q) := by
  rw [chartP_source] at hq
  have hx : q.1 ∈ (D.chartX a).val.source := hq.1
  have hxz : (D.chartX a).val q.1 ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    D.chartP_mem_prodDom.mp hqz
  have hbs := D.mem_baseSets hx hxz
  have hE := D.mem_frameE_baseSet K m hx hxz
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set NL := ‖(prefFrame L (D.pt a)).val.symm q.1 1‖ with hNL
  set NG := ‖(prefFrame G (D.pt a)).val.symm q.1 1‖ with hNG
  have hNL0 : 0 < NL := frameNorm_pos L.Fiber (prefFrame L (D.pt a)).val hbs.1
  have hNG0 : 0 < NG := frameNorm_pos G.Fiber (prefFrame G (D.pt a)).val hbs.2
  have hnorm : ‖u‖ = ‖(D.frameE K m a).val.continuousLinearMapAt ℂ q.1 u‖ * (NL ^ m * NG ^ K) := by
    rw [norm_eq_coef_mul_norm_frame (D.frameE K m a).val hE u, D.frameE_norm hK.1 m hx hxz]
  have hsymm : (D.chartP a).val.symm ((D.chartP a).val q) = q :=
    (D.chartP a).val.left_inv (by rw [chartP_source]; exact hq)
  have hpX : projX n ((D.chartP a).val q) = (D.chartX a).val q.1 := by
    rw [chartP_apply, projX_prodL]
  have hsx : (D.chartX a).val.symm ((D.chartX a).val q.1) = q.1 := (D.chartX a).val.left_inv hx
  have hρLP : D.ρLP a ((D.chartP a).val q) = D.ρL a ((D.chartX a).val q.1) := by
    rw [ρLP, D.coordinateMap_eq hqz, hpX]
  have hρGP : D.ρGP s a ((D.chartP a).val q) = s * D.ρG a ((D.chartX a).val q.1) := by
    rw [ρGP, D.coordinateMap_eq hqz, hpX]
  have hwL : D.ρL a ((D.chartX a).val q.1) = -Real.log (NL ^ 2) := by
    rw [ρL, frameWeight, hsx]
  have hwG : D.ρG a ((D.chartX a).val q.1) = -Real.log (NG ^ 2) := by
    rw [ρG, frameWeight, hsx]
  have hpsi : D.psiGen s K m Φ Ψ a ((D.chartP a).val q) +
      ((D.lam * ‖(D.chartP a).val q - D.ctrP a‖ ^ 2 : ℝ) : EReal) =
      thetaGen m Φ Ψ q + (((m : ℝ) * D.ρL a ((D.chartX a).val q.1) +
        (K : ℝ) * D.ρG a ((D.chartX a).val q.1) + D.lam * ‖q.2.val‖ ^ 2 : ℝ) : EReal) := by
    rw [psiGen, hρLP, hρGP, hsymm, hpX, ereal_three hm' (hΦ q) (hΨ q), thetaGen]
    congr 2
    rw [gW, D.norm_chartP_sub_ctrP a q]
    ring
  have hexp : Real.exp (-((m : ℝ) * D.ρL a ((D.chartX a).val q.1) +
      (K : ℝ) * D.ρG a ((D.chartX a).val q.1) + D.lam * ‖q.2.val‖ ^ 2)) =
      (NL ^ 2) ^ m * (NG ^ 2) ^ K * Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)) := by
    rw [hwL, hwG, show -((m : ℝ) * -Real.log (NL ^ 2) + (K : ℝ) * -Real.log (NG ^ 2) +
      D.lam * ‖q.2.val‖ ^ 2) = (m : ℝ) * Real.log (NL ^ 2) + (K : ℝ) * Real.log (NG ^ 2) +
      -(D.lam * ‖q.2.val‖ ^ 2) by ring, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  rw [ballWeight, hpsi, multiplierWeight_one_add_coe_real (thetaGen_ne_top hm hΦ hΨ q),
    hexp, weightGen, hnorm, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have : (NL ^ m * NG ^ K) ^ 2 = (NL ^ 2) ^ m * (NG ^ 2) ^ K := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm m 2, mul_comm K 2]
  rw [this, ENNReal.ofReal_mul (by positivity)]
  ring

/-! ### The gluing system -/

/-- **The gluing system of `p₁^*(L^m ⊗ G^K)` on `X × Δ` for the weight `mΦ + Ψ`**
(`claude-siu-gen:system`). -/
def toSystemGen [SFinite μ] (hL : IsSourceSmoothHermitianMetric L)
    (hG : IsSourceSmoothHermitianMetric G) {θ θG : ClosedRealOneOneForm n X}
    (hθ : IsOwnFirstChernForm L θ) (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ}
    (hK : D.GoodPower s K) (hm : 0 < m) {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    {Ψ : X × unitDisc → EReal}
    (hΨ : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
        (s • θG)).val Ψ) (hΨt : ∀ q, Ψ q ≠ ⊤) :
    DomainGluingSystem (n + 1) (X × unitDisc) (prodMeasure μ)
      (fun q => (twistedPower L (positivePower G (K - 1)) m).Fiber q.1)
      (D.weightGen m Φ Ψ) (Fin D.m) where
  chart a := (D.chartP a).val
  center := D.ctrP
  domR a := prodDom (ctr (n := n) (D.pt a)) (D.R a) 1
  domr a := prodDom (ctr (n := n) (D.pt a)) (D.R a / 2) 1
  domr' a := prodDom (ctr (n := n) (D.pt a)) (D.R a / 4) 1
  isOpen_domR a := isOpen_prodDom _ _ _
  isOpen_domr a := isOpen_prodDom _ _ _
  isOpen_domr' a := isOpen_prodDom _ _ _
  isBounded_domR a := isBounded_prodDom _ _ _
  domr'_sub a := prodDom_mono (by linarith [D.R_pos a]) le_rfl
  domr_sub a := prodDom_mono (by linarith [D.R_pos a]) le_rfl
  domR_sub a := D.prodDom_subset_target a
  cover q := by
    have hne : ∑ a, D.χ a q.1 ≠ 0 := by rw [D.sum_χ q.1]; exact one_ne_zero
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h := D.tsupport_χ a (subset_tsupport _ ha)
    exact ⟨a, by rw [chartP_source]; exact ⟨h.1, mem_univ _⟩, D.chartP_mem_prodDom.mpr h.2⟩
  coef a q := (D.frameE K m a).val.continuousLinearMapAt ℂ q.1
  frame a q := (D.frameE K m a).val.symm q.1 1
  coef_frame a q hq hqz := trivialization_coef_frame _
    (D.mem_frameE_baseSet K m (D.mem_of_chartP hq hqz).1 (D.mem_of_chartP hq hqz).2)
  eq_coef_smul_frame a q u hq hqz := trivialization_eq_coef_smul_frame _
    (D.mem_frameE_baseSet K m (D.mem_of_chartP hq hqz).1 (D.mem_of_chartP hq hqz).2) u
  transition_holo i l := D.transition_holo K m i l
  chart_holo i l := D.chart_holo i l
  dens a w := ENNReal.ofReal (D.dens a (projX n w))
  A := ENNReal.ofReal D.Aμ
  A_ne_top := ENNReal.ofReal_ne_top
  dens_le a w hw := ENNReal.ofReal_le_ofReal (D.dens_le a _ hw.1)
  one_le_A_mul_dens a w hw := by
    rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (D.one_le a _ hw.1)
  map_measure a f hf :=
    setLIntegral_chart_ball (D.chartP a) (ρ := fun w => D.dens a (projX n w))
      ((D.dens_cont a).comp (projX n).continuous.continuousOn fun w hw => by
        rw [pChart_target] at hw; exact hw.1)
      (map_pChart (D.pt a, discOrigin) (D.dens_cont a) (D.dens_map a))
      (isOpen_prodDom _ _ _) (D.prodDom_subset_target a) hf
  Ψ := D.psiGen s K m Φ Ψ
  Ψ_psh := D.psiGen_psh hL hG hθ hθG hK hm hΦ hΨ
  lam := D.lam
  lam_pos := D.lam_pos
  density_eq a q u hq hqz := D.density_eqGen hK hm (fun q => hΦ.1.quasiPlurisubharmonic.ne_top q)
    hΨt a q u hq hqz
  localCorr a f hf := productCorrection (ctr (n := n) (D.pt a)) (by linarith [D.R_pos a])
    (D.ctrP a) D.lam_pos (D.psiGen_psh hL hG hθ hθG hK hm hΦ hΨ a) hf
  χ a q := D.χ a q.1
  χ_smooth i l := D.χ_smoothP i l
  χ_nonneg i q := D.χ_nonneg i q.1
  sum_χ q := D.sum_χ q.1
  tsupport_χ a := D.tsupport_χP a
  M := D.M
  dbar_χ_le i l w hw := D.dbar_χ_le' i l hw

end SiuCover

end SGPT.PSH.SiuL2
