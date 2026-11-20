import SGPT.PSH.SiuL2Cover

/-!
# The gluing system of `p₁^*(L^m ⊗ G^K)` on `X × Δ` with a general quasi-psh weight

Blueprint `claude-siu-l2.tex`, node `claude-siu-l2:system`.

For cover data `D : SiuCover μ L G` (`θ = c₁(L, h_L)`, `θ_G = c₁(G, h_G)` Kähler), `s ≥ 0`, a power
`K` with `λ + s c_a ≤ K c_a` (`SiuCover.GoodPower`), `m > 0`, a weight
`Φ ∈ PSH(X × Δ, p₁^*θ)`, a `ψ_X ∈ PSH(X, s θ_G)` (only the `θ`-plurisubharmonicity is used) and a
`ψ_Δ` psh on `Δ`, `SiuCover.toSystem` is the `DomainGluingSystem` on `X × Δ` of the line bundle
`p₁^*(L^m ⊗ G^K)` (fibres `(L^m ⊗ G^K)_x`) for the weight

`w = e^{-(mΦ + ψ_X + ψ_Δ)} e^{-λ|t|²}`,

with the product charts at `(p_a, 0)`, the domains `B(z_a, R_a/4) × Δ ⊆ B(z_a, R_a/2) × Δ ⊆
B(z_a, R_a) × Δ`, the local solver `productCorrection`, and the local weights

`Ψ_a = m(ρ_L + Φ) + (s ρ_G + ψ_X) + ψ_Δ + [(K - s) ρ_G - λ|z - z_a|²]`,

`ρ_L, ρ_G` the frame weights `-log |e|²`.  Its contraction factor is at most `1/4`
(`SiuCover.kappa_toSystem_le`), with `λ` depending only on the cover.
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

theorem ereal_four {m : ℝ} (hm : 0 < m) {a b c : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (ρ₁ ρ₂ g Q : ℝ) :
    (m : EReal) * ((ρ₁ : EReal) + a) + ((ρ₂ : EReal) + b) + c + (g : EReal) + (Q : EReal) =
      ((m : EReal) * a + b + c) + ((m * ρ₁ + ρ₂ + g + Q : ℝ) : EReal) := by
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
      induction c using EReal.rec with
      | top => exact absurd rfl hc
      | bot => simp
      | coe c =>
        simp only [← EReal.coe_add, ← EReal.coe_mul]
        congr 1
        ring

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SiuCover

variable {μ : Measure X} {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ L G)

/-- The chart of `X` at index `a`. -/
abbrev chartX (a : Fin D.m) : ComplexChart n X := complexChartAt (n := n) (D.pt a)

/-- The product chart of `X × Δ` at index `a`. -/
abbrev chartP (a : Fin D.m) : ComplexChart (n + 1) (X × unitDisc) := pChart (n := n) (D.pt a, discOrigin)

/-- The centre `(z_a, 0)` of the product chart. -/
def ctrP (a : Fin D.m) : ComplexModel (n + 1) := prodL n (ctr (n := n) (D.pt a), 0)

/-- The frame `e_L^m ⊗ e_G^K` of `L^m ⊗ G^K = twistedPower L (positivePower G (K - 1)) m`. -/
def frameE (K m : ℕ) (a : Fin D.m) : AtlasFrame (twistedPower L (positivePower G (K - 1)) m) :=
  twistedPowerAtlasFrame (prefFrame L (D.pt a)) (positivePowerAtlasFrame (prefFrame G (D.pt a)) (K - 1)) m

/-- The curvature bound used in the local weights. -/
def lam : ℝ := 8 * (D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2 + 1

theorem lam_pos : 0 < D.lam := by unfold lam; positivity

/-- `K` is large enough for the local weights to carry `λ` after `s θ_G` is spent. -/
def GoodPower (s : ℝ) (K : ℕ) : Prop := 1 ≤ K ∧ ∀ a, D.lam + s * D.cG a ≤ (K : ℝ) * D.cG a

theorem exists_goodPower (s : ℝ) : ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → D.GoodPower s K := by
  refine ⟨1 + ∑ a, ⌈(D.lam + s * D.cG a) / D.cG a⌉₊, fun K hK => ⟨by omega, fun a => ?_⟩⟩
  have hpos : 0 < D.cG a := D.cG_pos a
  have h1 : ⌈(D.lam + s * D.cG a) / D.cG a⌉₊ ≤ K := by
    have : ⌈(D.lam + s * D.cG a) / D.cG a⌉₊ ≤ ∑ a, ⌈(D.lam + s * D.cG a) / D.cG a⌉₊ :=
      Finset.single_le_sum (f := fun a => ⌈(D.lam + s * D.cG a) / D.cG a⌉₊)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  have h2 : (D.lam + s * D.cG a) / D.cG a ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  rw [div_le_iff₀ hpos] at h2
  linarith

theorem ball_subset_two (a : Fin D.m) :
    ball (ctr (n := n) (D.pt a)) (D.R a) ⊆ ball (ctr (n := n) (D.pt a)) (2 * D.R a) :=
  ball_subset_ball (by linarith [D.R_pos a])

theorem ball_subset_targetX (a : Fin D.m) :
    ball (ctr (n := n) (D.pt a)) (D.R a) ⊆ (D.chartX a).val.target :=
  fun _ hz => (D.hball a (D.ball_subset_two a hz)).1

theorem mem_baseSets {a : Fin D.m} {x : X} (hx : x ∈ (D.chartX a).val.source)
    (hxz : (D.chartX a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    x ∈ (prefFrame L (D.pt a)).val.baseSet ∧ x ∈ (prefFrame G (D.pt a)).val.baseSet := by
  have h := (D.hball a (D.ball_subset_two a hxz)).2
  rwa [mem_preimage, (D.chartX a).val.left_inv hx] at h

theorem mem_frameE_baseSet (K m : ℕ) {a : Fin D.m} {x : X} (hx : x ∈ (D.chartX a).val.source)
    (hxz : (D.chartX a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    x ∈ (D.frameE K m a).val.baseSet :=
  twistedPowerAtlasFrame_mem _ _ (D.mem_baseSets hx hxz).1
    (positivePowerAtlasFrame_mem _ (D.mem_baseSets hx hxz).2 (K - 1)) m

theorem frameE_norm {K : ℕ} (hK : 1 ≤ K) (m : ℕ) {a : Fin D.m} {x : X}
    (hx : x ∈ (D.chartX a).val.source)
    (hxz : (D.chartX a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    ‖(D.frameE K m a).val.symm x 1‖ =
      ‖(prefFrame L (D.pt a)).val.symm x 1‖ ^ m * ‖(prefFrame G (D.pt a)).val.symm x 1‖ ^ K := by
  have hb := D.mem_baseSets hx hxz
  rw [frameE, twistedPower_frame_norm _ _ hb.1 (positivePowerAtlasFrame_mem _ hb.2 (K - 1)) m,
    positivePower_frame_norm _ hb.2 (K - 1), Nat.sub_add_cancel hK]

/-! ### Product domains in the product charts -/

theorem prodDom_subset_target (a : Fin D.m) :
    prodDom (ctr (n := n) (D.pt a)) (D.R a) 1 ⊆ (D.chartP a).val.target := by
  intro w hw
  rw [pChart_target]
  exact ⟨D.ball_subset_targetX a hw.1, by
    have := hw.2
    simpa [mem_unitDisc] using this⟩

theorem mem_prodDom_projX {a : Fin D.m} {r : ℝ} {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom (ctr (n := n) (D.pt a)) r 1) : projX n w ∈ ball (ctr (n := n) (D.pt a)) r :=
  hw.1

theorem mem_prodDom_projT {z₀ : ComplexModel n} {r : ℝ} {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom z₀ r 1) : projT n w ∈ (unitDisc : Set (ComplexModel 1)) :=
  hw.2

theorem chartP_apply (a : Fin D.m) (q : X × unitDisc) :
    (D.chartP a).val q = prodL n ((D.chartX a).val q.1, q.2.val) := rfl

theorem chartP_source (a : Fin D.m) :
    (D.chartP a).val.source = (D.chartX a).val.source ×ˢ univ :=
  pChart_source _

theorem chartP_mem_prodDom {a : Fin D.m} {r : ℝ} {q : X × unitDisc} :
    (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) r 1 ↔
      (D.chartX a).val q.1 ∈ ball (ctr (n := n) (D.pt a)) r := by
  rw [chartP_apply, prodDom, mem_preimage, ContinuousLinearEquiv.symm_apply_apply, prodMk_mem_set_prod_eq]
  have : q.2.val ∈ ball (0 : ComplexModel 1) 1 := q.2.property
  simp [this]

theorem symm_fst {a : Fin D.m} {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    ((D.chartP a).val.symm w).1 = (D.chartX a).val.symm (projX n w) :=
  pChart_symm_fst _ (D.prodDom_subset_target a hw)

theorem symm_snd {a : Fin D.m} {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    ((D.chartP a).val.symm w).2.val = projT n w :=
  pChart_symm_snd _ (D.prodDom_subset_target a hw)

/-! ### The local weights -/

/-- `ρ_L = -log |e_L|²` in the chart of index `a`. -/
def ρL (a : Fin D.m) (z : ComplexModel n) : ℝ := frameWeight (prefFrame L (D.pt a)) (D.chartX a) z

/-- `ρ_G = -log |e_G|²` in the chart of index `a`. -/
def ρG (a : Fin D.m) (z : ComplexModel n) : ℝ := frameWeight (prefFrame G (D.pt a)) (D.chartX a) z

/-- The local potential `ρ_L ∘ p₁` of `p₁^*θ` in the product chart. -/
def ρLP (a : Fin D.m) (w : ComplexModel (n + 1)) : ℝ :=
  D.ρL a (coordinateMap Prod.fst (D.chartP a) (D.chartX a) w)

/-- The smooth remainder `(K - s) ρ_G - λ|z - z_a|²`. -/
def gW (s : ℝ) (K : ℕ) (a : Fin D.m) (z : ComplexModel n) : ℝ :=
  ((K : ℝ) - s) * D.ρG a z - D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2

/-- The psh part `Ψ_a = m(ρ_L + Φ) + (s ρ_G + ψ_X) + ψ_Δ + g_a` of the local weight. -/
def psiP (s : ℝ) (K m : ℕ) (Φ : X × unitDisc → EReal) (ψX : X → EReal)
    (ψT : ComplexModel 1 → EReal) (a : Fin D.m) (w : ComplexModel (n + 1)) : EReal :=
  ((m : ℝ) : EReal) * ((D.ρLP a w : EReal) + Φ ((D.chartP a).val.symm w)) +
    (((s * D.ρG a (projX n w) : ℝ) : EReal) + ψX ((D.chartX a).val.symm (projX n w))) +
    ψT (projT n w) + (D.gW s K a (projX n w) : EReal)

theorem coordinateMap_eq {a : Fin D.m} {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    coordinateMap Prod.fst (D.chartP a) (D.chartX a) w = projX n w := by
  simp only [coordinateMap, Function.comp_apply]
  rw [D.symm_fst hw]
  exact (D.chartX a).val.right_inv (D.ball_subset_targetX a hw.1)

theorem prodDom_subset_potentialDomain (a : Fin D.m) :
    prodDom (ctr (n := n) (D.pt a)) (D.R a) 1 ⊆
      LocalPotentialPullback.potentialDomain Prod.fst (D.chartP a) (D.chartX a)
        (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) := by
  intro w hw
  refine ⟨⟨D.prodDom_subset_target a hw, ?_⟩, ?_⟩
  · change ((D.chartP a).val.symm w).1 ∈ (D.chartX a).val.source
    rw [D.symm_fst hw]
    exact (D.chartX a).val.map_target (D.ball_subset_targetX a hw.1)
  · change coordinateMap Prod.fst (D.chartP a) (D.chartX a) w ∈
      ball (ctr (n := n) (D.pt a)) (2 * D.R a)
    rw [D.coordinateMap_eq hw]
    exact D.ball_subset_two a hw.1

theorem isSmoothLocalPotential_ρL (hL : IsSourceSmoothHermitianMetric L)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) (a : Fin D.m) :
    IsSmoothLocalPotential θ.val (D.chartX a) (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) (D.ρL a) :=
  ⟨isOpen_ball, fun _ hz => (D.hball a hz).1,
    (contDiffOn_frameWeight hL _ _).mono fun _ hz => ⟨(D.hball a hz).1, (D.hball a hz).2.1⟩,
    fun z hz => (hθ (D.chartX a) (prefFrame L (D.pt a)) z (D.hball a hz).1 (D.hball a hz).2.1).symm⟩

theorem contDiffOn_ρG (hG : IsSourceSmoothHermitianMetric G) (a : Fin D.m) :
    ContDiffOn ℝ ∞ (D.ρG a) (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
  (contDiffOn_frameWeight hG _ _).mono fun _ hz => ⟨(D.hball a hz).1, (D.hball a hz).2.2⟩

theorem isSmoothLocalPotential_sρG (hG : IsSourceSmoothHermitianMetric G)
    {θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG) (s : ℝ) (a : Fin D.m) :
    IsSmoothLocalPotential (s • θG).val (D.chartX a) (ball (ctr (n := n) (D.pt a)) (2 * D.R a))
      (fun z => s * D.ρG a z) := by
  refine ⟨isOpen_ball, fun _ hz => (D.hball a hz).1,
    contDiffOn_const.mul (D.contDiffOn_ρG hG a), fun z hz => ?_⟩
  have h := smoothDDC_smul isOpen_ball (D.contDiffOn_ρG hG a) s hz
  simp only [smul_eq_mul] at h
  rw [h, ClosedRealOneOneForm.coeff_smul]
  congr 1
  exact (hθG (D.chartX a) (prefFrame G (D.pt a)) z (D.hball a hz).1 (D.hball a hz).2.2).symm

/-- `ρ + u ∘ e⁻¹` is psh for a smooth local potential `ρ` of `θ` and a `θ`-psh `u` (the
`ThetaPlurisubharmonic` form of `plurisubharmonicOn_add_localPotential`). -/
theorem plurisubharmonicOn_add_localPotential' {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) (d : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ d W ρ) :
    PlurisubharmonicOn (fun x => (ρ x : EReal) + φ (d.val.symm x)) W := by
  intro x hx
  obtain ⟨W', ρ', hxW', hρ', hpsh⟩ := hφ d x (hρ.2.1 hx)
  have hWo : IsOpen (W ∩ W') := hρ.1.inter hρ'.1
  have hsm : ContDiffOn ℝ ∞ (fun y => ρ y - ρ' y) (W ∩ W') :=
    (hρ.2.2.1.mono inter_subset_left).sub (hρ'.2.2.1.mono inter_subset_right)
  have hzero : ∀ y ∈ W ∩ W', smoothDDC (fun y => ρ y - ρ' y) y = 0 := by
    intro y hy
    rw [PositiveClasses.smoothDDC_sub hWo (hρ.2.2.1.mono inter_subset_left)
      (hρ'.2.2.1.mono inter_subset_right) hy, hρ.2.2.2 hy.1, hρ'.2.2.2 hy.2, sub_self]
  have hph := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hWo hsm hzero
  have hadd := (hpsh.mono inter_subset_right).add hph
  obtain ⟨U, hU, hxU, hdisc⟩ := hadd x ⟨hx, hxW'⟩
  refine ⟨U ∩ (W ∩ W'), hU.inter hWo, ⟨hxU, hx, hxW'⟩, (hdisc.mono inter_subset_left).congr ?_⟩
  intro y _
  show (chartFunction φ d y + (ρ' y : EReal)) + ((ρ y - ρ' y : ℝ) : EReal) =
    (ρ y : EReal) + φ (d.val.symm y)
  rw [add_assoc, ← EReal.coe_add, add_sub_cancel, add_comm]
  rfl

theorem leviForm_gW_nonneg (hG : IsSourceSmoothHermitianMetric G) {s : ℝ} {K : ℕ}
    (hK : D.GoodPower s K) (a : Fin D.m) {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) (v : ComplexModel n) :
    0 ≤ leviForm (D.gW s K a) z v := by
  have hz2 := D.ball_subset_two a hz
  have hρ2 : ContDiffAt ℝ 2 (D.ρG a) z :=
    (((D.contDiffOn_ρG hG a) z hz2).contDiffAt (isOpen_ball.mem_nhds hz2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hn2 : ContDiffAt ℝ 2 (fun y : ComplexModel n => D.lam * ‖y - ctr (n := n) (D.pt a)‖ ^ 2) z :=
    ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hLeviN : leviForm (fun y : ComplexModel n => D.lam * ‖y - ctr (n := n) (D.pt a)‖ ^ 2) z v =
      D.lam * ‖v‖ ^ 2 := by
    have e : (fun y : ComplexModel n => D.lam * ‖y - ctr (n := n) (D.pt a)‖ ^ 2) =
        fun y => (D.lam • fun u : ComplexModel n => ‖u‖ ^ 2) (y - ctr (n := n) (D.pt a)) := by
      funext y; simp [smul_eq_mul]
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul
      (contDiff_norm_sq ℝ).contDiffAt, leviForm_norm_sq]
  have hsplit : D.gW s K a = (((K : ℝ) - s) • D.ρG a) +
      -(fun y : ComplexModel n => D.lam * ‖y - ctr (n := n) (D.pt a)‖ ^ 2) := by
    funext y; simp only [gW, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have hkF : ContDiffAt ℝ 2 (((K : ℝ) - s) • D.ρG a) z := by
    have := hρ2.const_smul ((K : ℝ) - s); exact this
  set N : ComplexModel n → ℝ := fun y => D.lam * ‖y - ctr (n := n) (D.pt a)‖ ^ 2 with hNdef
  have hNn : ContDiffAt ℝ 2 (-N) z := hn2.neg
  rw [hsplit, leviForm_add hkF hNn, leviForm_neg, leviForm_smul hρ2, hLeviN]
  have h1 : D.cG a * ‖v‖ ^ 2 ≤ leviForm (D.ρG a) z v := D.levi_G a z hz v
  have h3 := hK.2 a
  have hc := D.cG_pos a
  have hlam := D.lam_pos
  have hv : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hKs : 0 ≤ (K : ℝ) - s := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 hKs
  have h4 : D.lam * ‖v‖ ^ 2 ≤ ((K : ℝ) - s) * D.cG a * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hv
  nlinarith

theorem psiP_psh (hL : IsSourceSmoothHermitianMetric L) (hG : IsSourceSmoothHermitianMetric G)
    {θ θG : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ)
    (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    {ψX : X → EReal} (hψX : ThetaPlurisubharmonic (s • θG).val ψX)
    {ψT : ComplexModel 1 → EReal} (hψT : PlurisubharmonicOn ψT (ball 0 1)) (a : Fin D.m) :
    PlurisubharmonicOn (D.psiP s K m Φ ψX ψT a) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) := by
  have hDo := isOpen_prodDom (ctr (n := n) (D.pt a)) (D.R a) 1
  have hpX : DifferentiableOn ℂ (projX n) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    (projX n).differentiable.differentiableOn
  have hpT : DifferentiableOn ℂ (projT n) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    (projT n).differentiable.differentiableOn
  -- (1) the `Φ` part
  have hpot := (LocalPotentialPullback.isSmoothLocalPotential_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (D.chartP a)
    (D.isSmoothLocalPotential_ρL hL hθ a)).mono hDo (D.prodDom_subset_potentialDomain a)
  have h1 : PlurisubharmonicOn (fun w => (D.ρLP a w : EReal) + Φ ((D.chartP a).val.symm w))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    plurisubharmonicOn_add_localPotential hΦ (D.chartP a) hpot
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1' := h1.const_mul hm'
  -- (2) the `ψ_X` part
  have h2X := plurisubharmonicOn_add_localPotential' hψX (D.chartX a)
    (D.isSmoothLocalPotential_sρG hG hθG s a)
  have h2 : PlurisubharmonicOn (fun w => ((s * D.ρG a (projX n w) : ℝ) : EReal) +
      ψX ((D.chartX a).val.symm (projX n w))) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hDo hpX
      (fun w hw => D.ball_subset_two a hw.1) h2X
  -- (3) the `ψ_Δ` part
  have h3 : PlurisubharmonicOn (fun w => ψT (projT n w)) (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hDo hpT
      (fun w hw => hw.2) hψT
  -- (4) the smooth part
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
  exact ((h1'.add h2).add h3).add h4

/-! ### The density identity -/

/-- The singular part `mΦ + ψ_X + ψ_Δ` of the global weight. -/
def thetaP (m : ℕ) (Φ : X × unitDisc → EReal) (ψX : X → EReal) (ψT : ComplexModel 1 → EReal)
    (q : X × unitDisc) : EReal :=
  ((m : ℝ) : EReal) * Φ q + ψX q.1 + ψT q.2.val

/-- The global weight `e^{-(mΦ + ψ_X + ψ_Δ)} e^{-λ|t|²}` on `X × Δ`. -/
def weightP (m : ℕ) (Φ : X × unitDisc → EReal) (ψX : X → EReal) (ψT : ComplexModel 1 → EReal)
    (q : X × unitDisc) : ℝ≥0∞ :=
  multiplierWeight 1 (thetaP m Φ ψX ψT q) * ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))

theorem mul_ne_top_of_pos {m : ℝ} (hm : 0 < m) {e : EReal} (he : e ≠ ⊤) : (m : EReal) * e ≠ ⊤ := by
  induction e using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hm]; exact bot_ne_top
  | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl he

theorem thetaP_ne_top {m : ℕ} (hm : 0 < m) {Φ : X × unitDisc → EReal} (hΦ : ∀ q, Φ q ≠ ⊤)
    {ψX : X → EReal} (hψX : ∀ x, ψX x ≠ ⊤) {ψT : ComplexModel 1 → EReal} (hψT : ∀ t, ψT t ≠ ⊤)
    (q : X × unitDisc) : thetaP m Φ ψX ψT q ≠ ⊤ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold thetaP
  exact EReal.add_ne_top (EReal.add_ne_top (mul_ne_top_of_pos hm' (hΦ q)) (hψX q.1)) (hψT _)

theorem norm_chartP_sub_ctrP (a : Fin D.m) (q : X × unitDisc) :
    ‖(D.chartP a).val q - D.ctrP a‖ ^ 2 =
      ‖(D.chartX a).val q.1 - ctr (n := n) (D.pt a)‖ ^ 2 + ‖q.2.val‖ ^ 2 := by
  rw [norm_sub_sq_prodL, chartP_apply, ctrP, projX_prodL, projX_prodL, projT_prodL, projT_prodL,
    sub_zero]

/-- **The density identity** `|u|² w = |coef_a u|² e^{-Ψ_a - λ|w - w_a|²}`. -/
theorem density_eq {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    {Φ : X × unitDisc → EReal} (hΦ : ∀ q, Φ q ≠ ⊤) {ψX : X → EReal} (hψX : ∀ x, ψX x ≠ ⊤)
    {ψT : ComplexModel 1 → EReal} (hψT : ∀ t, ψT t ≠ ⊤) (a : Fin D.m) (q : X × unitDisc)
    (u : (twistedPower L (positivePower G (K - 1)) m).Fiber q.1)
    (hq : q ∈ (D.chartP a).val.source)
    (hqz : (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    ENNReal.ofReal (‖u‖ ^ 2) * D.weightP m Φ ψX ψT q =
      ENNReal.ofReal (‖(D.frameE K m a).val.continuousLinearMapAt ℂ q.1 u‖ ^ 2) *
        ballWeight (D.psiP s K m Φ ψX ψT a) D.lam (D.ctrP a) ((D.chartP a).val q) := by
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
  have hpT : projT n ((D.chartP a).val q) = q.2.val := by rw [chartP_apply, projT_prodL]
  have hsx : (D.chartX a).val.symm ((D.chartX a).val q.1) = q.1 := (D.chartX a).val.left_inv hx
  have hρLP : D.ρLP a ((D.chartP a).val q) = D.ρL a ((D.chartX a).val q.1) := by
    rw [ρLP, D.coordinateMap_eq hqz, hpX]
  have hwL : D.ρL a ((D.chartX a).val q.1) = -Real.log (NL ^ 2) := by
    rw [ρL, frameWeight, hsx]
  have hwG : D.ρG a ((D.chartX a).val q.1) = -Real.log (NG ^ 2) := by
    rw [ρG, frameWeight, hsx]
  have hpsi : D.psiP s K m Φ ψX ψT a ((D.chartP a).val q) +
      ((D.lam * ‖(D.chartP a).val q - D.ctrP a‖ ^ 2 : ℝ) : EReal) =
      thetaP m Φ ψX ψT q + (((m : ℝ) * D.ρL a ((D.chartX a).val q.1) +
        (K : ℝ) * D.ρG a ((D.chartX a).val q.1) + D.lam * ‖q.2.val‖ ^ 2 : ℝ) : EReal) := by
    rw [psiP, hρLP, hsymm, hpX, hpT, hsx, ereal_four hm' (hΦ q) (hψX q.1) (hψT _), thetaP]
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
  rw [ballWeight, hpsi, multiplierWeight_one_add_coe_real (thetaP_ne_top hm hΦ hψX hψT q),
    hexp, weightP, hnorm, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have : (NL ^ m * NG ^ K) ^ 2 = (NL ^ 2) ^ m * (NG ^ 2) ^ K := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm m 2, mul_comm K 2]
  rw [this, ENNReal.ofReal_mul (by positivity)]
  ring

/-! ### The gluing system -/

theorem mem_of_chartP {a : Fin D.m} {q : X × unitDisc} (hq : q ∈ (D.chartP a).val.source)
    (hqz : (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    q.1 ∈ (D.chartX a).val.source ∧ (D.chartX a).val q.1 ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := by
  rw [chartP_source] at hq
  exact ⟨hq.1, D.chartP_mem_prodDom.mp hqz⟩

theorem transition_holo (K m : ℕ) (i l : Fin D.m) :
    DifferentiableOn ℂ (fun w => (D.frameE K m l).val.continuousLinearMapAt ℂ
        ((D.chartP l).val.symm w).1 ((D.frameE K m i).val.symm ((D.chartP l).val.symm w).1 1))
      {w | w ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∧
        (D.chartP l).val.symm w ∈ (D.chartP i).val.source ∧
        (D.chartP i).val ((D.chartP l).val.symm w) ∈ prodDom (ctr (n := n) (D.pt i)) (D.R i) 1} := by
  set SX : Set (ComplexModel n) := {z | z ∈ ball (ctr (n := n) (D.pt l)) (D.R l) ∧
    (D.chartX l).val.symm z ∈ (D.chartX i).val.source ∧
    (D.chartX i).val ((D.chartX l).val.symm z) ∈ ball (ctr (n := n) (D.pt i)) (D.R i)} with hSX
  have hX : DifferentiableOn ℂ (fun z => (D.frameE K m l).val.continuousLinearMapAt ℂ
      ((D.chartX l).val.symm z) ((D.frameE K m i).val.symm ((D.chartX l).val.symm z) 1)) SX := by
    refine differentiableOn_coef_frame (D.frameE K m i).val (D.frameE K m l).val (D.chartX l)
      (fun z hz => D.ball_subset_targetX l hz.1) fun z hz => ⟨D.mem_frameE_baseSet K m hz.2.1 hz.2.2, ?_⟩
    have hs : (D.chartX l).val.symm z ∈ (D.chartX l).val.source :=
      (D.chartX l).val.map_target (D.ball_subset_targetX l hz.1)
    exact D.mem_frameE_baseSet K m hs
      (by rw [(D.chartX l).val.right_inv (D.ball_subset_targetX l hz.1)]; exact hz.1)
  refine (hX.comp (projX n).differentiable.differentiableOn fun w hw => ?_).congr fun w hw => ?_
  · have h1 := D.symm_fst hw.1
    refine ⟨hw.1.1, ?_, ?_⟩
    · have h2 := hw.2.1
      rw [chartP_source] at h2
      rw [← h1]; exact h2.1
    · have h3 := D.chartP_mem_prodDom.mp hw.2.2
      rw [← h1]; exact h3
  · simp only [Function.comp_apply]
    rw [D.symm_fst hw.1]

theorem chart_holo (i l : Fin D.m) :
    DifferentiableOn ℂ (fun w => (D.chartP i).val ((D.chartP l).val.symm w))
      {w | w ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∧
        (D.chartP l).val.symm w ∈ (D.chartP i).val.source ∧
        (D.chartP i).val ((D.chartP l).val.symm w) ∈ prodDom (ctr (n := n) (D.pt i)) (D.R i) 1} := by
  have hT := RegularPatchNeighborhood.differentiableOn_chartTransition (D.chartX l) (D.chartX i)
  have hT' : DifferentiableOn ℂ (fun w => chartTransition (D.chartX l) (D.chartX i) (projX n w))
      {w | w ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∧
        (D.chartP l).val.symm w ∈ (D.chartP i).val.source ∧
        (D.chartP i).val ((D.chartP l).val.symm w) ∈ prodDom (ctr (n := n) (D.pt i)) (D.R i) 1} := by
    refine hT.comp (projX n).differentiable.differentiableOn fun w hw => ?_
    have h2 := hw.2.1
    rw [chartP_source] at h2
    refine ⟨D.ball_subset_targetX l hw.1.1, ?_⟩
    have h1 := D.symm_fst hw.1
    change (D.chartX l).val.symm (projX n w) ∈ (D.chartX i).val.source
    rw [← h1]; exact h2.1
  refine ((prodL n).differentiable.comp_differentiableOn (hT'.prodMk
    (projT n).differentiable.differentiableOn)).congr fun w hw => ?_
  simp only [Function.comp_apply]
  rw [chartP_apply]
  congr 2
  all_goals rw [D.symm_snd hw.1]

theorem dbar_χ_le' (i l : Fin D.m) {w : ComplexModel (n + 1)}
    (hw : w ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1) :
    dbarNormSq (fun w => ((D.χ i ((D.chartP l).val.symm w).1 : ℝ) : ℂ)) w ≤ D.M := by
  set g : ComplexModel n → ℂ := fun z => ((D.χ i ((D.chartX l).val.symm z) : ℝ) : ℂ) with hg
  have heq : (fun w => ((D.χ i ((D.chartP l).val.symm w).1 : ℝ) : ℂ)) =ᶠ[𝓝 w]
      fun w => g (projX n w) := by
    filter_upwards [(isOpen_prodDom _ _ _).mem_nhds hw] with w' hw'
    rw [D.symm_fst hw']
  have hsum : dbarNormSq (fun w => ((D.χ i ((D.chartP l).val.symm w).1 : ℝ) : ℂ)) w =
      dbarNormSq (fun w => g (projX n w)) w := by
    unfold dbarNormSq
    exact Finset.sum_congr rfl fun j _ => by rw [CauchyGreen.dbarDir_congr heq]
  have hgs : ContDiffOn ℝ ∞ g (D.chartX l).val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (D.χ_smooth i (D.chartX l))
  have hgd : DifferentiableAt ℝ g (projX n w) :=
    ((hgs.contDiffAt ((D.chartX l).val.open_target.mem_nhds
      (D.ball_subset_targetX l hw.1))).differentiableAt (by simp))
  rw [hsum, dbarNormSq_comp_projX hgd]
  exact D.dbar_χ_le i l (projX n w) hw.1

theorem tsupport_χP (a : Fin D.m) :
    tsupport (fun q : X × unitDisc => D.χ a q.1) ⊆
      (D.chartP a).val.source ∩ (D.chartP a).val ⁻¹' prodDom (ctr (n := n) (D.pt a)) (D.R a / 2) 1 := by
  intro q hq
  have h := D.tsupport_χ a (tsupport_comp_subset_preimage (f := Prod.fst) (D.χ a) continuous_fst hq)
  refine ⟨by rw [chartP_source]; exact ⟨h.1, mem_univ _⟩, D.chartP_mem_prodDom.mpr ?_⟩
  exact ball_subset_ball (by linarith [D.R_pos a]) h.2

theorem χ_smoothP (i l : Fin D.m) :
    ContDiffOn ℝ ∞ (fun w => D.χ i ((D.chartP l).val.symm w).1) (D.chartP l).val.target := by
  refine ((D.χ_smooth i (D.chartX l)).comp ((projX n).restrictScalars ℝ).contDiff.contDiffOn
    fun w hw => ?_).congr
    fun w hw => ?_
  · rw [pChart_target] at hw; exact hw.1
  · simp only [Function.comp_apply]
    rw [pChart_symm_fst _ hw]; rfl

/-- **The gluing system of `p₁^*(L^m ⊗ G^K)` on `X × Δ`** (`claude-siu-l2:system`). -/
def toSystem [SFinite μ] (hL : IsSourceSmoothHermitianMetric L)
    (hG : IsSourceSmoothHermitianMetric G) {θ θG : ClosedRealOneOneForm n X}
    (hθ : IsOwnFirstChernForm L θ) (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ}
    (hK : D.GoodPower s K) (hm : 0 < m) {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    {ψX : X → EReal} (hψX : ThetaPlurisubharmonic (s • θG).val ψX) (hψXt : ∀ x, ψX x ≠ ⊤)
    {ψT : ComplexModel 1 → EReal} (hψT : PlurisubharmonicOn ψT (ball 0 1))
    (hψTt : ∀ t, ψT t ≠ ⊤) :
    DomainGluingSystem (n + 1) (X × unitDisc) (prodMeasure μ)
      (fun q => (twistedPower L (positivePower G (K - 1)) m).Fiber q.1)
      (D.weightP m Φ ψX ψT) (Fin D.m) where
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
  Ψ := D.psiP s K m Φ ψX ψT
  Ψ_psh := D.psiP_psh hL hG hθ hθG hK hm hΦ hψX hψT
  lam := D.lam
  lam_pos := D.lam_pos
  density_eq a q u hq hqz := D.density_eq hK hm (fun q => hΦ.1.quasiPlurisubharmonic.ne_top q)
    hψXt hψTt a q u hq hqz
  localCorr a f hf := productCorrection (ctr (n := n) (D.pt a)) (by linarith [D.R_pos a])
    (D.ctrP a) D.lam_pos (D.psiP_psh hL hG hθ hθG hK hm hΦ hψX hψT a) hf
  χ a q := D.χ a q.1
  χ_smooth i l := D.χ_smoothP i l
  χ_nonneg i q := D.χ_nonneg i q.1
  sum_χ q := D.sum_χ q.1
  tsupport_χ a := D.tsupport_χP a
  M := D.M
  dbar_χ_le i l w hw := D.dbar_χ_le' i l hw

end SiuCover

end SGPT.PSH.SiuL2
