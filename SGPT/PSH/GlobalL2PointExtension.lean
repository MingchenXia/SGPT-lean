import SGPT.PSH.GlobalL2PointSection
import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiPoint
import SGPT.Foundations.Analysis.Pending.ChartPartition

/-!
# The uniform `L²` extension from a point

Blueprint `claude-global-l2:point-extension`, `claude-global-l2b.tex`, node
`claude-global-l2b:point-extension-proof`.  `globalPointExtension` proves
`GlobalPointExtensionStatement n X` (Xia, *Foundations of pluripotential theory*,
`thm:compact-point-extension`, in the `k ≫ 0` form of the book's `thm:OT_ext` for `Y = {x}`).

Proof (positive dimension, `globalPointExtension_pos`): fix cover data `D` for `δ/2`.  All the
auxiliary choices are made from finitely many data of `D`, so the final constant depends on
`(X, ω, μ, L, T, θ, δ)` only:

* the pole radius `r_a = min (R_a/8) (1/2)` and the cut-off scale `ε_a = r_a/4` of chart `a`;
* one `B` with `poleFun ∈ PSH(X, Bω)` for **every** centre `p ∈ B(z_a, R_a/4)` (the Levi lower
  bound of `poleSmooth` does not depend on the centre, `claude-global-l2b:profile`);
* a finite `ε_a`-net `T_a` of `closedBall (z_a) (R_a/4)` and, for `q ∈ T_a`, the chart cut-off
  `χ_{a,q}` (a bump `= 1` on `closedBall q (2ε_a)`, supported in `closedBall q (3ε_a)`), with a
  common bound `M_χ` of `|∂̄ χ_{a,q}|²` in all charts;
* the Ohsawa--Takegoshi constant from a point (TN `exists_extension_from_point`) for the radius
  `‖z_a‖ + R_a`.

For `x ∈ z_a⁻¹ B(z_a, R_a/4)` with `z_a(x) ∈ ball q ε_a`, `exists_section_through_point` applies
with the pole `ψ = (n+1) poleFun`, the cut-off `χ_{a,q}` and `k ≥ k₀`, `2(n+1)B ≤ kδ`.

Dimension zero (`globalPointExtension_zero`): `X` is discrete, the section `v` at `x`, `0`
elsewhere, is holomorphic, and `μ({x}) ≤ A vol(B(z_a, R_a))`.
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

/-- TN's `L²` extension from a point (`Pending.OhsawaTakegoshiPoint.exists_extension_from_point`),
restated for the standard measurable structure of `ComplexModel n` (TN states it for the Borel
structure, which is the same). -/
theorem exists_extension_from_point' (n : ℕ) : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
    ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
    ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
    ∀ y ∈ Ω, ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧ F y = 1 ∧
      (∫⁻ z in Ω, multiplierDensity φ c F z) ≤ ENNReal.ofReal C * multiplierWeight c (φ y) := by
  have key : ∀ (m : MeasurableSpace (ComplexModel n)) (hb : @BorelSpace (ComplexModel n) _ m),
      m = borel _ → (by
        letI := m; haveI := hb
        exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
          ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
          ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
          ∀ y ∈ Ω, ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧ F y = 1 ∧
            (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
              ENNReal.ofReal C * multiplierWeight c (φ y)) := by
    rintro m hb rfl
    exact Pending.OhsawaTakegoshiPoint.exists_extension_from_point n
  exact key inferInstance inferInstance BorelSpace.measurable_eq

theorem half_sq_le_exp_neg_one : (1 / 2 : ℝ) ^ 2 ≤ Real.exp (-1) := by
  have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
  norm_num; linarith

/-- `λ |z - c|²` is psh. -/
theorem plurisubharmonicOn_mul_normSq {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (c : ComplexModel n)
    (U : Set (ComplexModel n)) :
    PlurisubharmonicOn (fun z => ((lam * ‖z - c‖ ^ 2 : ℝ) : EReal)) U := by
  have h := plurisubharmonicOn_coe_of_levi_nonneg isOpen_univ
    (ρ := fun z : ComplexModel n => lam * ‖z - c‖ ^ 2)
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).contDiffOn
    (fun w _ v => by
      have e : (fun z : ComplexModel n => lam * ‖z - c‖ ^ 2) =
          fun y => (lam • fun u : ComplexModel n => ‖u‖ ^ 2) (y - c) := by
        funext y; simp [smul_eq_mul]
      rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul
        (contDiff_norm_sq ℝ).contDiffAt, leviForm_norm_sq]
      positivity)
  exact fun z _ => h z (mem_univ z)

theorem coe_mul_le_coe_mul {c : ℝ} (hc : 0 < c) {t : ℝ} {e : EReal} (h : (t : EReal) ≤ e) :
    ((c * t : ℝ) : EReal) ≤ (c : EReal) * e := by
  induction e using EReal.rec with
  | bot => exact absurd h (by simp)
  | coe s =>
      rw [← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hc.le)
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact le_top

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace CoverData

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- The pole radius of chart `a`. -/
def poleR (a : Fin D.m) : ℝ := min (D.R a / 8) (1 / 2)

/-- The cut-off scale of chart `a`. -/
def cutEps (a : Fin D.m) : ℝ := D.poleR a / 4

theorem poleR_pos (a : Fin D.m) : 0 < D.poleR a :=
  lt_min (by linarith [D.R_pos a]) (by norm_num)

theorem poleR_le (a : Fin D.m) : D.poleR a ≤ D.R a / 8 := min_le_left _ _

theorem cutEps_pos (a : Fin D.m) : 0 < D.cutEps a := by unfold cutEps; linarith [D.poleR_pos a]

theorem cutEps_le (a : Fin D.m) : D.cutEps a ≤ D.R a / 32 := by
  unfold cutEps; linarith [D.poleR_le a]

theorem closedBall_subset_of_mem {a : Fin D.m} {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {ρ : ℝ} (hρ : ρ ≤ 3 * D.R a / 4) :
    closedBall p ρ ⊆ closedBall (ctr (n := n) (D.pt a)) (D.R a) := by
  intro w hw
  rw [mem_closedBall] at hw hp ⊢
  linarith [dist_triangle w p (ctr (n := n) (D.pt a))]

theorem poleRadii (a : Fin D.m) {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    PoleRadii (D.chartA a) p (D.R a / 2) (D.poleR a) where
  r_pos := D.poleR_pos a
  four_r_le := by linarith [D.poleR_le a]
  r_sq_le := (pow_le_pow_left₀ (D.poleR_pos a).le (min_le_right _ _) 2).trans
    half_sq_le_exp_neg_one
  closedBall_subset := (D.closedBall_subset_of_mem hp (by linarith [D.R_pos a])).trans
    (D.closedBall_subset_target a)

/-- One pole constant for all centres. -/
theorem exists_uniform_poleB : ∃ B : ℝ, 0 < B ∧ ∀ a : Fin D.m, ∃ m : ℝ,
    (∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      m * ‖v‖ ^ 2 ≤ ωb.form.val.coeff (D.chartA a) w ![v, Complex.I • v]) ∧
    2 * poleK / D.poleR a ^ 2 ≤ Real.pi * B * m := by
  have h := fun a : Fin D.m => exists_lineValue_lower_bound_of_isCompact' ωb.isKahler.1
    (D.chartA a) (isCompact_closedBall (ctr (n := n) (D.pt a)) (D.R a))
    (D.closedBall_subset_target a)
  choose m hm hmω using h
  have hK := poleK_nonneg
  set B : ℝ := ∑ a, 2 * poleK / (Real.pi * m a * D.poleR a ^ 2) + 1 with hBdef
  have hterm : ∀ a, 0 ≤ 2 * poleK / (Real.pi * m a * D.poleR a ^ 2) := fun a => by
    have := hm a; have := D.poleR_pos a; positivity
  have hB0 : 0 < B := by
    have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => hterm a
    linarith
  refine ⟨B, hB0, fun a => ⟨m a, hmω a, ?_⟩⟩
  have hr := D.poleR_pos a
  have hma := hm a
  have hle : 2 * poleK / (Real.pi * m a * D.poleR a ^ 2) ≤ B := by
    have := Finset.single_le_sum (f := fun a => 2 * poleK / (Real.pi * m a * D.poleR a ^ 2))
      (fun a _ => hterm a) (Finset.mem_univ a)
    linarith
  rw [div_le_iff₀ (by positivity)] at hle ⊢
  have : 2 * poleK = 2 * poleK / (Real.pi * m a * D.poleR a ^ 2) *
      (Real.pi * m a * D.poleR a ^ 2) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ Real.pi * m a * D.poleR a ^ 2)]

/-- The pole `ψ = (n + 1) poleFun` at `p` in chart `a`. -/
def polePsi (a : Fin D.m) (p : ComplexModel n) (y : X) : EReal :=
  (((n : ℝ) + 1 : ℝ) : EReal) * poleFun (D.chartA a) p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y

/-- The bump of the cut-off `χ_{a,q}`. -/
def cutBump (a : Fin D.m) (q : ComplexModel n) : ContDiffBump q :=
  ⟨2 * D.cutEps a, 3 * D.cutEps a, by linarith [D.cutEps_pos a], by linarith [D.cutEps_pos a]⟩

/-- The cut-off `χ_{a,q}` (the bump in chart `a`, extended by zero). -/
def cutChi (a : Fin D.m) (q : ComplexModel n) : X → ℝ :=
  Pending.ChartPartition.chartExtend (D.chartA a) (D.cutBump a q)

theorem tsupport_cutBump (a : Fin D.m) (q : ComplexModel n) :
    tsupport (D.cutBump a q) = closedBall q (3 * D.cutEps a) :=
  (D.cutBump a q).tsupport_eq

theorem closedBall_cut_subset_target {a : Fin D.m} {q : ComplexModel n}
    (hq : q ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    closedBall q (3 * D.cutEps a) ⊆ (D.chartA a).val.target :=
  (D.closedBall_subset_of_mem hq (by linarith [D.cutEps_le a, D.R_pos a])).trans
    (D.closedBall_subset_target a)

theorem chartSmooth_cutChi {a : Fin D.m} {q : ComplexModel n}
    (hq : q ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    ChartSmooth (n := n) (D.cutChi a q) :=
  Pending.ChartPartition.chartSmooth_chartExtend (D.chartA a) (D.cutBump a q).contDiff
    (D.cutBump a q).hasCompactSupport.isCompact
    (by rw [D.tsupport_cutBump]; exact D.closedBall_cut_subset_target hq)

/-- A finite net of `closedBall z_a (R_a/4)` at scale `ε_a`. -/
theorem exists_net (a : Fin D.m) : ∃ Tn : Finset (ComplexModel n),
    (∀ q ∈ Tn, q ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) ∧
    ∀ z ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4), ∃ q ∈ Tn, z ∈ ball q (D.cutEps a) := by
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) (D.cutEps_pos a)
  refine ⟨htf.toFinset, fun q hq => hts (htf.mem_toFinset.mp hq), fun z hz => ?_⟩
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp (hcov hz)
  exact ⟨q, htf.mem_toFinset.mpr hq, hzq⟩

/-- A common bound of the `∂̄`-derivatives of the cut-offs of the nets in all charts. -/
theorem exists_cut_bound (Tn : Fin D.m → Finset (ComplexModel n))
    (hTn : ∀ a, ∀ q ∈ Tn a, q ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    ∃ Mχ : ℝ, 0 ≤ Mχ ∧ ∀ a, ∀ q ∈ Tn a, ∀ l, ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((D.cutChi a q ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ Mχ := by
  have h : ∀ (a : Fin D.m) (q : Tn a) (l : Fin D.m), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
        dbarNormSq (fun z => ((D.cutChi a q ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ C :=
    fun a q l => bound_dbarNormSq_χ (D.chartSmooth_cutChi (hTn a q q.2)) (D.pt l)
      (D.closedBall_subset_target l)
  choose C hC0 hC using h
  refine ⟨∑ a, ∑ q : Tn a, ∑ l, C a q l,
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun l _ => hC0 a q l,
    fun a q hq l z hz => (hC a ⟨q, hq⟩ l z hz).trans ?_⟩
  have h1 : C a ⟨q, hq⟩ l ≤ ∑ l', C a ⟨q, hq⟩ l' :=
    Finset.single_le_sum (f := fun l' => C a ⟨q, hq⟩ l') (fun l' _ => hC0 a _ l') (Finset.mem_univ l)
  have h2 : ∑ l', C a ⟨q, hq⟩ l' ≤ ∑ q' : Tn a, ∑ l', C a q' l' :=
    Finset.single_le_sum (f := fun q' : Tn a => ∑ l', C a q' l')
      (fun q' _ => Finset.sum_nonneg fun l' _ => hC0 a q' l')
      (Finset.mem_univ (⟨q, hq⟩ : Tn a))
  have h3 : ∑ q' : Tn a, ∑ l', C a q' l' ≤ ∑ a', ∑ q' : Tn a', ∑ l', C a' q' l' :=
    Finset.single_le_sum (f := fun a' => ∑ q' : Tn a', ∑ l', C a' q' l')
      (fun a' _ => Finset.sum_nonneg fun q' _ => Finset.sum_nonneg fun l' _ => hC0 a' q' l')
      (Finset.mem_univ a)
  linarith

/-- A common Ohsawa--Takegoshi constant for the chart balls. -/
theorem exists_OT_const : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin D.m,
    ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → Ω ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) →
    ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ y ∈ Ω,
      ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧ F y = 1 ∧
        (∫⁻ z in Ω, multiplierDensity φ 1 F z) ≤ ENNReal.ofReal C * multiplierWeight 1 (φ y) := by
  have h := fun a : Fin D.m => exists_extension_from_point' n (‖ctr (n := n) (D.pt a)‖ + D.R a)
    (by have := D.R_pos a; positivity)
  choose C hC hext using h
  have hsum : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ => (hC a).le
  refine ⟨∑ a, C a + 1, by linarith, fun a Ω hΩ hconv hΩR φ hφ y hy => ?_⟩
  obtain ⟨F, hF, hF1, hFi⟩ := hext a Ω hΩ hconv (fun z hz => by
      have := mem_ball_iff_norm.mp (hΩR hz)
      calc ‖z‖ = ‖(z - ctr (n := n) (D.pt a)) + ctr (n := n) (D.pt a)‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - ctr (n := n) (D.pt a)‖ + ‖ctr (n := n) (D.pt a)‖ := norm_add_le _ _
        _ < _ := by linarith) φ hφ 1 one_pos y hy
  refine ⟨F, hF, hF1, hFi.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_)
    zero_le)⟩
  have := Finset.single_le_sum (f := C) (fun a _ => (hC a).le) (Finset.mem_univ a)
  linarith

end CoverData

end SGPT.PSH.GlobalL2
