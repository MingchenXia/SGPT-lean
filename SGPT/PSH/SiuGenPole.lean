import SGPT.PSH.SiuGenCorrection
import SGPT.PSH.GlobalL2PointExtension

/-!
# Weights with an isolated logarithmic pole on `X × Δ`

Blueprint `claude-siu-gen.tex`, node `claude-siu-gen:pole`.

For cover data `D : SiuCover μ L G` (`θ_G = c₁(G, h_G)` Kähler), a chart index `a`, a point `p` of the
ball `B(z_a, R_a/4)` of the chart `z_a` of `X` and `t₀ ∈ Δ`, the function

`poleP D a p t₀ (x, t) = max((n+3) poleFun_{z_a, p}(x), (n+3) log |t - t₀|²)`

(`poleFun` is the cut-off pole of `SGPT.PSH.GlobalL2`, equal to `log |z_a(x) - p|²` near `p`)
lies in `PSH(X × Δ, p₁^*((n+3) B θ_G))` with `B` depending only on the cover
(`thetaPlurisubharmonic_poleP`), is bounded above by `(n+3) log 4`, satisfies
`poleP ≤ (n+3) log |w - w₀|²` near `w₀ = (p, t₀)` in the product chart (`poleP_le_logNormSq`), and
is bounded below at distance `≥ ρ` from `w₀` (`le_poleP`).  It is the weight of Siu's argument on
`X × Δ`: unlike the weights `ψ_X(x) + ψ_Δ(t)`, it has an isolated pole of order `n + 3` at
`(p, t₀)`.
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
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.NAPotential.NAGaga

/-! ### The pole in the disc direction -/

/-- `log |t - t₀|²` is psh on `ℂ`. -/
theorem plurisubharmonicOn_logNormSq_sub (t₀ : ComplexModel 1) :
    PlurisubharmonicOn (fun t : ComplexModel 1 => logNormSq (t - t₀)) univ := by
  have h := PlurisubharmonicOn.comp_affine (u := logNormSq (E := ComplexModel 1))
    (U := univ) (fun x _ => plurisubharmonicAt_logNormSq x)
    (ContinuousLinearMap.id ℂ (ComplexModel 1)) (-t₀)
  intro x _
  refine (h x (by simp)).congr (Eventually.of_forall fun y => ?_)
  simp [neg_add_eq_sub]

theorem logNormSq_mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {x : E} {y : F}
    (h : ‖x‖ ≤ ‖y‖) :
    logNormSq x ≤ logNormSq y :=
  ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2))

theorem coe_mul_mono {c : ℝ} (hc : 0 ≤ c) {a b : EReal} (h : a ≤ b) :
    (c : EReal) * a ≤ (c : EReal) * b :=
  mul_le_mul_of_nonneg_left h (by exact_mod_cast hc)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A function `B(t)` psh on the disc is `p₁^*σ`-psh on `X × Δ` for every semipositive `σ`. -/
theorem thetaPlurisubharmonic_comp_snd {σ : ClosedRealOneOneForm n X} (hσ : σ.val.IsSemipositive)
    {B : ComplexModel 1 → EReal} (hB : PlurisubharmonicOn B (ball 0 1)) :
    ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) σ).val
      (fun q : X × unitDisc => B q.2.val) := by
  have h0 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) σ).val
      (fun _ => 0) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (ClosedRealOneOneForm.pullback_isSemipositive _ hσ)
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := h0 e z hz
  have hWo : IsOpen (W ∩ e.val.target) := hρ.1.inter e.val.open_target
  refine ⟨W ∩ e.val.target, ρ, ⟨hzW, hz⟩, hρ.mono hWo inter_subset_left, ?_⟩
  set d : ComplexChart 1 unitDisc := complexChartAt (n := 1) discOrigin with hd
  have hdom : coordinateDomain (Prod.snd : X × unitDisc → unitDisc) e d = e.val.target := by
    ext w
    simp only [coordinateDomain, mem_inter_iff, mem_preimage, and_iff_left_iff_imp]
    intro _
    change (e.val.symm w).2 ∈ (chartAt (ComplexModel 1) discOrigin).source
    rw [discChart_source]; exact mem_univ _
  have hdiff : DifferentiableOn ℂ (coordinateMap (Prod.snd : X × unitDisc → unitDisc) e d)
      (W ∩ e.val.target) := by
    have h := coordinateMap_contDiffOn (contMDiff_snd (n := n) (m := 1) (X := X) (Y := unitDisc)) e d
    rw [hdom] at h
    exact (h.mono inter_subset_right).differentiableOn (by simp)
  have hmaps : MapsTo (coordinateMap (Prod.snd : X × unitDisc → unitDisc) e d) (W ∩ e.val.target)
      (ball 0 1) := fun w _ => (e.val.symm w).2.property
  have hBc := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hWo hdiff hmaps hB
  intro w hw
  refine ((hBc.add (hp.mono inter_subset_left)) w hw).congr (Eventually.of_forall fun y => ?_)
  change B (e.val.symm y).2.val + ((0 : EReal) + (ρ y : EReal)) =
    B (e.val.symm y).2.val + (ρ y : EReal)
  rw [zero_add]

variable [MeasurableSpace X] [BorelSpace X]

namespace SiuCover

variable {μ : Measure X} {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ L G)

/-! ### Pole radii and the uniform pole constant -/

/-- The pole radius of chart `a`. -/
def siuPoleR (a : Fin D.m) : ℝ := min (D.R a / 8) (1 / 2)

theorem siuPoleR_pos (a : Fin D.m) : 0 < D.siuPoleR a :=
  lt_min (by linarith [D.R_pos a]) (by norm_num)

theorem siuPoleR_le (a : Fin D.m) : D.siuPoleR a ≤ D.R a / 8 := min_le_left _ _

theorem closedBall_subset_of_mem {a : Fin D.m} {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {ρ : ℝ} (hρ : ρ ≤ 3 * D.R a / 4) :
    closedBall p ρ ⊆ closedBall (ctr (n := n) (D.pt a)) (D.R a) := by
  intro w hw
  rw [mem_closedBall] at hw hp ⊢
  linarith [dist_triangle w p (ctr (n := n) (D.pt a))]

theorem closedBall_subset_targetX (a : Fin D.m) :
    closedBall (ctr (n := n) (D.pt a)) (D.R a) ⊆ (D.chartX a).val.target :=
  fun _ hz => (D.hball a ((closedBall_subset_ball (by linarith [D.R_pos a])) hz)).1

theorem siuPoleRadii (a : Fin D.m) {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    PoleRadii (D.chartX a) p (D.R a / 2) (D.siuPoleR a) where
  r_pos := D.siuPoleR_pos a
  four_r_le := by linarith [D.siuPoleR_le a]
  r_sq_le := (pow_le_pow_left₀ (D.siuPoleR_pos a).le (min_le_right _ _) 2).trans
    half_sq_le_exp_neg_one
  closedBall_subset := (D.closedBall_subset_of_mem hp (by linarith [D.R_pos a])).trans
    (D.closedBall_subset_targetX a)

/-- One pole constant for all centres. -/
theorem exists_uniform_siuPoleB {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : Fin D.m, ∃ m : ℝ,
      (∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
        m * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v]) ∧
      2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * m := by
  have h := fun a : Fin D.m => exists_lineValue_lower_bound_of_isCompact' hKah.1
    (D.chartX a) (isCompact_closedBall (ctr (n := n) (D.pt a)) (D.R a))
    (D.closedBall_subset_targetX a)
  choose m hm hmω using h
  have hK := poleK_nonneg
  set B : ℝ := ∑ a, 2 * poleK / (Real.pi * m a * D.siuPoleR a ^ 2) + 1 with hBdef
  have hterm : ∀ a, 0 ≤ 2 * poleK / (Real.pi * m a * D.siuPoleR a ^ 2) := fun a => by
    have := hm a; have := D.siuPoleR_pos a; positivity
  have hB0 : 0 < B := by
    have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => hterm a
    linarith
  refine ⟨B, hB0, fun a => ⟨m a, hmω a, ?_⟩⟩
  have hr := D.siuPoleR_pos a
  have hma := hm a
  have hle : 2 * poleK / (Real.pi * m a * D.siuPoleR a ^ 2) ≤ B := by
    have := Finset.single_le_sum (f := fun a => 2 * poleK / (Real.pi * m a * D.siuPoleR a ^ 2))
      (fun a _ => hterm a) (Finset.mem_univ a)
    linarith
  rw [div_le_iff₀ (by positivity)] at hle ⊢
  have : 2 * poleK = 2 * poleK / (Real.pi * m a * D.siuPoleR a ^ 2) *
      (Real.pi * m a * D.siuPoleR a ^ 2) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ Real.pi * m a * D.siuPoleR a ^ 2)]

/-! ### The pole weight -/

/-- The pole `(n+3) poleFun` at `p` in the chart `a` of `X`. -/
def poleX (a : Fin D.m) (p : ComplexModel n) (x : X) : EReal :=
  (((n : ℝ) + 3 : ℝ) : EReal) * poleFun (D.chartX a) p (D.R a / 2) (Real.log (D.siuPoleR a ^ 2)) x

/-- The weight `max((n+3) poleFun_p(x), (n+3) log |t - t₀|²)` on `X × Δ`. -/
def poleP (a : Fin D.m) (p : ComplexModel n) (t₀ : ComplexModel 1) (q : X × unitDisc) : EReal :=
  max (D.poleX a p q.1) ((((n : ℝ) + 3 : ℝ) : EReal) * logNormSq (q.2.val - t₀))

theorem thetaPlurisubharmonic_poleP {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler)
    {B : ℝ} (hB0 : 0 < B) {a : Fin D.m} {mω : ℝ}
    (hmω : ∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v])
    (hBm : 2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω) {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) (t₀ : ComplexModel 1) :
    ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
        ((((n : ℝ) + 3) * B) • θG)).val (D.poleP a p t₀) := by
  set ωb : KahlerBackground n X := ⟨θG, hKah⟩
  have hP := D.siuPoleRadii a hp
  have hpsh := thetaPlurisubharmonic_poleFun ωb hP (m := mω)
    (fun w hw v => hmω w (D.closedBall_subset_of_mem hp (by linarith [D.R_pos a]) hw) v)
    hB0.le hBm
  have hX : ThetaPlurisubharmonic ((((n : ℝ) + 3) * B) • θG).val (D.poleX a p) := by
    have := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
      (c := (n : ℝ) + 3) (by positivity) hpsh
    rwa [smul_smul] at this
  have hXP := Pending.GlobalPotentialPullback.thetaPlurisubharmonic_comp
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) hX
  have hsemi : ((((n : ℝ) + 3) * B) • θG).val.IsSemipositive :=
    Pending.KahlerDomination.isSemipositive_smul (KahlerBackground.isSemipositive ωb)
      (by positivity)
  have hT : PlurisubharmonicOn (fun t : ComplexModel 1 =>
      (((n : ℝ) + 3 : ℝ) : EReal) * logNormSq (t - t₀)) (ball 0 1) :=
    ((plurisubharmonicOn_logNormSq_sub t₀).const_mul (by positivity)).mono (subset_univ _)
  have hTP := thetaPlurisubharmonic_comp_snd hsemi hT
  exact Pending.BoundedGlobalProduct.ThetaPlurisubharmonic.max hXP hTP

theorem poleX_le {a : Fin D.m} {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) (x : X) : D.poleX a p x ≤ 0 :=
  coe_mul_nonpos (by positivity) (poleFun_le (D.siuPoleRadii a hp) x)

/-- `poleP ≤ (n+3) log 4`. -/
theorem poleP_le {a : Fin D.m} {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {t₀ : ComplexModel 1}
    (ht₀ : ‖t₀‖ < 1) (q : X × unitDisc) :
    D.poleP a p t₀ q ≤ ((((n : ℝ) + 3) * Real.log 4 : ℝ) : EReal) := by
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine max_le ((D.poleX_le hp q.1).trans (by exact_mod_cast (by positivity : (0 : ℝ) ≤ _))) ?_
  have hq : ‖q.2.val‖ < 1 := mem_unitDisc.mp q.2.property
  have h2 : ‖q.2.val - t₀‖ ≤ 2 := by linarith [norm_sub_le q.2.val t₀]
  have hle : logNormSq (q.2.val - t₀) ≤ ((Real.log 4 : ℝ) : EReal) := by
    by_cases h0 : q.2.val - t₀ = 0
    · rw [h0, logNormSq_zero]; exact bot_le
    · rw [logNormSq_of_ne_zero h0]
      refine EReal.coe_le_coe_iff.mpr (Real.log_le_log (by positivity) ?_)
      nlinarith [norm_nonneg (q.2.val - t₀)]
  rw [EReal.coe_mul]
  exact coe_mul_mono (by positivity) hle

theorem poleP_ne_top {a : Fin D.m} {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {t₀ : ComplexModel 1}
    (ht₀ : ‖t₀‖ < 1) (q : X × unitDisc) : D.poleP a p t₀ q ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (D.poleP_le hp ht₀ q)

theorem norm_chartP_sub_sq (a : Fin D.m) (p : ComplexModel n) (t₀ : ComplexModel 1)
    (q : X × unitDisc) :
    ‖(D.chartP a).val q - prodL n (p, t₀)‖ ^ 2 =
      ‖(D.chartX a).val q.1 - p‖ ^ 2 + ‖q.2.val - t₀‖ ^ 2 := by
  have hpx : projX n ((D.chartP a).val q) = (D.chartX a).val q.1 := by
    rw [chartP_apply, projX_prodL]
  have hpt : projT n ((D.chartP a).val q) = q.2.val := by rw [chartP_apply, projT_prodL]
  rw [norm_sub_sq_prodL, hpx, hpt, projX_prodL, projT_prodL]

/-- **The isolated pole**: near `w₀ = (p, t₀)`, `poleP ≤ (n+3) log |w - w₀|²` in the product chart. -/
theorem poleP_le_logNormSq {a : Fin D.m} {p : ComplexModel n} (t₀ : ComplexModel 1)
    {q : X × unitDisc} (hq : q.1 ∈ (D.chartX a).val.source)
    (hd : ‖(D.chartP a).val q - prodL n (p, t₀)‖ ≤ D.siuPoleR a) :
    D.poleP a p t₀ q ≤
      (((n : ℝ) + 3 : ℝ) : EReal) * logNormSq ((D.chartP a).val q - prodL n (p, t₀)) := by
  have hsq := D.norm_chartP_sub_sq a p t₀ q
  have hz : ‖(D.chartX a).val q.1 - p‖ ≤ ‖(D.chartP a).val q - prodL n (p, t₀)‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖q.2.val - t₀‖])
  have ht : ‖q.2.val - t₀‖ ≤ ‖(D.chartP a).val q - prodL n (p, t₀)‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖(D.chartX a).val q.1 - p‖])
  have hR := D.siuPoleR_le a
  have hRa := D.R_pos a
  have hzR : (D.chartX a).val q.1 ∈ ball p (D.R a / 2) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hX : D.poleX a p q.1 = (((n : ℝ) + 3 : ℝ) : EReal) * logNormSq ((D.chartX a).val q.1 - p) := by
    rw [poleX, poleFun_of_mem hq hzR, poleChart_eq_logNormSq (hz.trans hd)]
  refine max_le ?_ ?_
  · rw [hX]; exact coe_mul_mono (by positivity) (logNormSq_mono hz)
  · exact coe_mul_mono (by positivity) (logNormSq_mono ht)

/-- **The lower bound away from the pole**: at distance `≥ ρ` from `w₀` (`ρ ≤ r`),
`poleP ≥ (n+3) log (ρ/2)²`. -/
theorem le_poleP {a : Fin D.m} {p : ComplexModel n} (t₀ : ComplexModel 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ D.siuPoleR a) {q : X × unitDisc}
    (hd : ρ ≤ ‖(D.chartP a).val q - prodL n (p, t₀)‖) :
    ((((n : ℝ) + 3) * Real.log ((ρ / 2) ^ 2) : ℝ) : EReal) ≤ D.poleP a p t₀ q := by
  have hsq := D.norm_chartP_sub_sq a p t₀ q
  have hρ2 : 0 < ρ / 2 := by linarith
  by_cases hz : ρ / 2 ≤ ‖(D.chartX a).val q.1 - p‖
  · refine le_trans ?_ (le_max_left _ _)
    exact coe_mul_le_coe_mul (by positivity) (log_le_poleFun hρ2 (by linarith) fun _ => hz)
  · have ht : ρ / 2 ≤ ‖q.2.val - t₀‖ := by
      by_contra ht
      push Not at hz ht
      have h1 : ‖(D.chartX a).val q.1 - p‖ ^ 2 < (ρ / 2) ^ 2 :=
        pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
      have h2 : ‖q.2.val - t₀‖ ^ 2 < (ρ / 2) ^ 2 := pow_lt_pow_left₀ ht (norm_nonneg _) two_ne_zero
      have h3 : ρ ^ 2 ≤ ‖(D.chartP a).val q - prodL n (p, t₀)‖ ^ 2 :=
        pow_le_pow_left₀ hρ.le hd 2
      nlinarith
    refine le_trans ?_ (le_max_right _ _)
    refine coe_mul_le_coe_mul (by positivity) ?_
    have hne : q.2.val - t₀ ≠ 0 := by
      intro h; rw [h, norm_zero] at ht; linarith
    rw [logNormSq_of_ne_zero hne]
    exact EReal.coe_le_coe_iff.mpr (Real.log_le_log (by positivity)
      (pow_le_pow_left₀ hρ2.le ht 2))

end SiuCover

end SGPT.PSH.SiuL2
