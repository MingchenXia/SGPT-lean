import SGPT.PSH.GlobalL2PoleProfile
import SGPT.PSH.GlobalL2Statement

/-!
# Quasi-plurisubharmonic functions with a logarithmic pole at a point

Blueprint `claude-global-l2b.tex`, nodes `claude-global-l2b:pole-function`,
`claude-global-l2b:point-pole`, `claude-global-l2b:point-pole-dim-zero`.

For an atlas chart `c`, a centre `p` with `closedBall p R₁ ⊆ c.target`, a radius `r` with
`4r ≤ R₁`, `r² ≤ e⁻¹`, and `a = log r²`, the function `poleFun c p R₁ a` equals
`poleSmooth p a ∘ c` on `c⁻¹ (ball p R₁ \ {p})`, `-∞` at `c⁻¹ p`, and the constant `1 + a ≤ 0`
elsewhere.  If `m > 0` bounds `ω(v, iv) ≥ m ‖v‖²` on `closedBall p R₁` and
`B ≥ 2K / (π m r²)` (`K = poleK`), then `poleFun ∈ PSH(X, B ω)` (`thetaPlurisubharmonic_poleFun`).
The constant `B` depends only on `m` and `r`, **not on `p`** (used for the uniform point
extension, `claude-global-l2:point-extension`).

`pointPoleStatement_of_pos` proves `PointPoleStatement n X` for `0 < n`.  For `n = 0` the
statement is false (`pointPole_conclusion_false_dim_zero`): `ComplexModel 0` is a point, so a
function equal to `log |z - z(x₀)|² = -∞` near `x₀` is `-∞` on an open set, which contradicts the
local nondegeneracy clause of `IsThetaPshPotential`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open Classical in
/-- The pole in the chart: `-∞` at `p`, `poleSmooth p a` elsewhere. -/
def poleChart (p : ComplexModel n) (a : ℝ) (z : ComplexModel n) : EReal :=
  if z = p then ⊥ else (poleSmooth p a z : EReal)

open Classical in
/-- The global pole function: the chart pole on `c⁻¹ (ball p R₁)`, the constant `1 + a`
elsewhere. -/
def poleFun (c : ComplexChart n M) (p : ComplexModel n) (R₁ a : ℝ) (y : M) : EReal :=
  if y ∈ c.val.source ∧ c.val y ∈ ball p R₁ then poleChart p a (c.val y)
  else ((1 + a : ℝ) : EReal)

/-- The hypotheses on the radii. -/
structure PoleRadii (c : ComplexChart n M) (p : ComplexModel n) (R₁ r : ℝ) : Prop where
  r_pos : 0 < r
  four_r_le : 4 * r ≤ R₁
  r_sq_le : r ^ 2 ≤ Real.exp (-1)
  closedBall_subset : closedBall p R₁ ⊆ c.val.target

/-- The image of `closedBall p (2r)` in `M`: off it the pole function is constant. -/
def poleCore (c : ComplexChart n M) (p : ComplexModel n) (r : ℝ) : Set M :=
  c.val.symm '' closedBall p (2 * r)

namespace PoleRadii

variable {c : ComplexChart n M} {p : ComplexModel n} {R₁ r : ℝ} (hP : PoleRadii c p R₁ r)
include hP

theorem R₁_pos : 0 < R₁ := by have := hP.r_pos; have := hP.four_r_le; linarith

theorem one_add_log_nonpos : 1 + Real.log (r ^ 2) ≤ 0 := by
  have h := Real.log_le_log (by have := hP.r_pos; positivity) hP.r_sq_le
  rw [Real.log_exp] at h
  linarith

theorem p_mem_target : p ∈ c.val.target :=
  hP.closedBall_subset (mem_closedBall_self hP.R₁_pos.le)

theorem ball_subset_target : ball p R₁ ⊆ c.val.target :=
  ball_subset_closedBall.trans hP.closedBall_subset

theorem isClosed_core : IsClosed (poleCore c p r) := by
  have hsub : closedBall p (2 * r) ⊆ c.val.target :=
    (closedBall_subset_closedBall (by have := hP.r_pos; have := hP.four_r_le; linarith)).trans
      hP.closedBall_subset
  exact ((isCompact_closedBall p (2 * r)).image_of_continuousOn
    (c.val.continuousOn_symm.mono hsub)).isClosed

end PoleRadii

theorem poleChart_eq_logNormSq {p z : ComplexModel n} {r : ℝ} (hzr : ‖z - p‖ ≤ r) :
    poleChart p (Real.log (r ^ 2)) z = logNormSq (z - p) := by
  by_cases hz : z = p
  · simp [poleChart, hz]
  · rw [poleChart, if_neg hz, poleSmooth_eq_log hz hzr,
      logNormSq_of_ne_zero (sub_ne_zero.mpr hz)]

theorem poleFun_of_mem {c : ComplexChart n M} {p : ComplexModel n} {R₁ a : ℝ} {y : M}
    (hy : y ∈ c.val.source) (hyR : c.val y ∈ ball p R₁) :
    poleFun c p R₁ a y = poleChart p a (c.val y) := by
  rw [poleFun, if_pos ⟨hy, hyR⟩]

theorem poleFun_eq_const {c : ComplexChart n M} {p : ComplexModel n} {R₁ r : ℝ}
    (hP : PoleRadii c p R₁ r) {y : M} (hy : y ∉ poleCore c p r) :
    poleFun c p R₁ (Real.log (r ^ 2)) y = ((1 + Real.log (r ^ 2) : ℝ) : EReal) := by
  by_cases hm : y ∈ c.val.source ∧ c.val y ∈ ball p R₁
  · rw [poleFun_of_mem hm.1 hm.2]
    have hfar : 2 * r < ‖c.val y - p‖ := by
      by_contra hle
      refine hy ⟨c.val y, ?_, c.val.left_inv hm.1⟩
      rw [mem_closedBall, dist_eq_norm]; exact not_lt.mp hle
    have hne : c.val y ≠ p := by
      intro h; rw [h, sub_self, norm_zero] at hfar; have := hP.r_pos; linarith
    rw [poleChart, if_neg hne, poleSmooth_eq_const hP.r_pos hfar.le]
  · rw [poleFun, if_neg hm]

theorem poleFun_le {c : ComplexChart n M} {p : ComplexModel n} {R₁ r : ℝ}
    (hP : PoleRadii c p R₁ r) (y : M) : poleFun c p R₁ (Real.log (r ^ 2)) y ≤ 0 := by
  have h0 := hP.one_add_log_nonpos
  have hconst : ((1 + Real.log (r ^ 2) : ℝ) : EReal) ≤ 0 := by exact_mod_cast h0
  unfold poleFun
  split_ifs with hm
  · unfold poleChart
    split_ifs
    · exact bot_le
    · exact (EReal.coe_le_coe_iff.mpr (poleSmooth_le _ _ _)).trans hconst
  · exact hconst

theorem poleFun_ne_bot {c : ComplexChart n M} {p : ComplexModel n} {R₁ a : ℝ} {y : M}
    (hy : y ∈ c.val.source → c.val y ≠ p) : poleFun c p R₁ a y ≠ ⊥ := by
  unfold poleFun
  split_ifs with hm
  · rw [poleChart, if_neg (hy hm.1)]; exact EReal.coe_ne_bot _
  · exact EReal.coe_ne_bot _

/-- The lower bound `log ρ² ≤ poleFun` at distance `≥ ρ` from the pole (`ρ ≤ r`). -/
theorem log_le_poleFun {c : ComplexChart n M} {p : ComplexModel n} {R₁ r ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) {y : M}
    (hy : y ∈ c.val.source → ρ ≤ ‖c.val y - p‖) :
    ((Real.log (ρ ^ 2) : ℝ) : EReal) ≤ poleFun c p R₁ (Real.log (r ^ 2)) y := by
  unfold poleFun
  split_ifs with hm
  · have hd := hy hm.1
    have hne : c.val y ≠ p := by
      intro h; rw [h, sub_self, norm_zero] at hd; linarith
    rw [poleChart, if_neg hne]
    exact EReal.coe_le_coe_iff.mpr (log_le_poleSmooth hρ hρr hd)
  · refine EReal.coe_le_coe_iff.mpr ?_
    have h1 : Real.log (ρ ^ 2) ≤ Real.log (r ^ 2) :=
      Real.log_le_log (by positivity) (pow_le_pow_left₀ hρ.le hρr 2)
    linarith

/-- Continuity of the pole function off the pole. -/
theorem continuousAt_poleFun {c : ComplexChart n M} {p : ComplexModel n} {R₁ r : ℝ}
    (hP : PoleRadii c p R₁ r) {y : M} (hy : y ∈ c.val.source → c.val y ≠ p) :
    ContinuousAt (poleFun c p R₁ (Real.log (r ^ 2))) y := by
  by_cases hm : y ∈ c.val.source ∧ c.val y ∈ ball p R₁
  · set S : Set M := c.val.source ∩ c.val ⁻¹' (ball p R₁ ∩ {z | z ≠ p}) with hS
    have hSo : IsOpen S := c.val.isOpen_inter_preimage (isOpen_ball.inter isOpen_ne)
    have hyS : y ∈ S := ⟨hm.1, hm.2, hy hm.1⟩
    have heq : poleFun c p R₁ (Real.log (r ^ 2)) =ᶠ[𝓝 y]
        fun y' => ((poleSmooth p (Real.log (r ^ 2)) (c.val y') : ℝ) : EReal) := by
      filter_upwards [hSo.mem_nhds hyS] with y' hy'
      rw [poleFun_of_mem hy'.1 hy'.2.1, poleChart, if_neg hy'.2.2]
    refine ContinuousAt.congr ?_ heq.symm
    refine continuous_coe_real_ereal.continuousAt.comp ?_
    exact ((continuousOn_poleSmooth p _).continuousAt (isOpen_ne.mem_nhds (hy hm.1))).comp
      (c.val.continuousOn.continuousAt (c.val.open_source.mem_nhds hm.1))
  · have hyc : y ∉ poleCore c p r := by
      rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ c.val.target := hP.closedBall_subset ((closedBall_subset_closedBall
        (by have := hP.r_pos; have := hP.four_r_le; linarith)) hw)
      refine hm ⟨c.val.map_target hwt, ?_⟩
      rw [c.val.right_inv hwt]
      exact closedBall_subset_ball (by have := hP.r_pos; have := hP.four_r_le; linarith) hw
    have heq : poleFun c p R₁ (Real.log (r ^ 2)) =ᶠ[𝓝 y]
        fun _ => ((1 + Real.log (r ^ 2) : ℝ) : EReal) := by
      filter_upwards [hP.isClosed_core.isOpen_compl.mem_nhds hyc] with y' hy'
      exact poleFun_eq_const hP hy'
    exact continuousAt_const.congr heq.symm

/-- **The pole function is `B ω`-plurisubharmonic**, `B ≥ 2K/(π m r²)`. -/
theorem thetaPlurisubharmonic_poleFun (ωb : KahlerBackground n M) {c : ComplexChart n M}
    {p : ComplexModel n} {R₁ r : ℝ} (hP : PoleRadii c p R₁ r) {m : ℝ}
    (hmω : ∀ w ∈ closedBall p R₁, ∀ v : ComplexModel n,
      m * ‖v‖ ^ 2 ≤ ωb.form.val.coeff c w ![v, Complex.I • v])
    {B : ℝ} (hB0 : 0 ≤ B) (hB : 2 * poleK / r ^ 2 ≤ Real.pi * B * m) :
    ThetaPlurisubharmonic (B • ωb.form).val (poleFun c p R₁ (Real.log (r ^ 2))) := by
  have hr := hP.r_pos
  set a := Real.log (r ^ 2) with ha
  refine thetaPlurisubharmonic_of_local fun y => ?_
  by_cases hyc : y ∈ c.val.source ∧ c.val y ∈ ball p R₁
  · have hyt : c.val y ∈ c.val.target := c.val.map_source hyc.1
    obtain ⟨Wω, ρ, hyW, hρ, hlev⟩ := exists_kahler_potential ωb c hyt B
    by_cases hp : c.val y = p
    · -- at the pole
      refine ⟨c, Wω ∩ ball p r, ρ, hyc.1, ⟨hyW, by rw [hp]; exact mem_ball_self hr⟩,
        hρ.mono (hρ.1.inter isOpen_ball) inter_subset_left, ?_⟩
      have hlog : PlurisubharmonicOn (fun w : ComplexModel n => logNormSq (w - p)) univ := by
        have h := PlurisubharmonicOn.comp_affine (u := logNormSq (E := ComplexModel n))
          (U := univ) (fun x _ => plurisubharmonicAt_logNormSq x)
          (ContinuousLinearMap.id ℂ (ComplexModel n)) (-p)
        intro x hx
        refine (h x (by simp)).congr (Eventually.of_forall fun y => ?_)
        simp [neg_add_eq_sub]
      have hρp := plurisubharmonicOn_const_add_kahler_potential ωb hB0 hρ hlev 0
      intro w hw
      refine ((hlog w (mem_univ w)).add (hρp w hw.1)).congr ?_
      filter_upwards [(hρ.1.inter isOpen_ball).mem_nhds hw] with w' hw'
      have hw't : w' ∈ c.val.target := hρ.2.1 hw'.1
      have hrR : w' ∈ ball p R₁ := ball_subset_ball (by have := hP.four_r_le; linarith) hw'.2
      simp only [chartFunction]
      rw [poleFun_of_mem (c.val.map_target hw't) (by rw [c.val.right_inv hw't]; exact hrR),
        c.val.right_inv hw't, poleChart_eq_logNormSq (le_of_lt (by
          rw [← dist_eq_norm]; exact hw'.2)), EReal.coe_zero, zero_add]
    · -- off the pole
      set z₀ := c.val y with hz₀
      have hd : 0 < ‖z₀ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
      have hdR : ‖z₀ - p‖ < R₁ := by rw [← dist_eq_norm]; exact hyc.2
      set ε := min (‖z₀ - p‖ / 2) (R₁ - ‖z₀ - p‖) with hε
      have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
      have hWo : IsOpen (Wω ∩ ball z₀ ε) := hρ.1.inter isOpen_ball
      have hsub : ∀ w ∈ Wω ∩ ball z₀ ε, w ≠ p ∧ w ∈ ball p R₁ := by
        intro w hw
        have h1 : ‖w - z₀‖ < ε := by rw [← dist_eq_norm]; exact hw.2
        have h2 : ε ≤ ‖z₀ - p‖ / 2 := min_le_left _ _
        have h3 : ε ≤ R₁ - ‖z₀ - p‖ := min_le_right _ _
        constructor
        · intro hwp
          rw [hwp] at h1
          have : ‖p - z₀‖ = ‖z₀ - p‖ := norm_sub_rev _ _
          linarith
        · rw [mem_ball, dist_eq_norm]
          have := norm_sub_le_norm_sub_add_norm_sub w z₀ p
          linarith
      refine ⟨c, Wω ∩ ball z₀ ε, ρ, hyc.1, ⟨hyW, mem_ball_self hε0⟩,
        hρ.mono hWo inter_subset_left, ?_⟩
      have hps := plurisubharmonicOn_coe_add_coe hWo (f := poleSmooth p a)
        ((contDiffOn_poleSmooth p a).mono fun w hw => (hsub w hw).1)
        (hρ.2.2.1.mono inter_subset_left) (fun w hw v => by
          have h1 := leviForm_poleSmooth_ge hr (hsub w hw).1 v
          rw [hlev w hw.1 v]
          have h2 := hmω w (ball_subset_closedBall (hsub w hw).2) v
          have hv : 0 ≤ ‖v‖ ^ 2 := by positivity
          have h3 : 2 * poleK / r ^ 2 * ‖v‖ ^ 2 ≤ Real.pi * B * m * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hB hv
          have h4 : Real.pi * B * (m * ‖v‖ ^ 2) ≤
              Real.pi * B * ωb.form.val.coeff c w ![v, Complex.I • v] :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith)
      intro w hw
      refine (hps w hw).congr ?_
      filter_upwards [hWo.mem_nhds hw] with w' hw'
      have hw't : w' ∈ c.val.target := hρ.2.1 hw'.1
      simp only [chartFunction]
      rw [poleFun_of_mem (c.val.map_target hw't) (by rw [c.val.right_inv hw't]; exact (hsub w' hw').2),
        c.val.right_inv hw't, poleChart, if_neg (hsub w' hw').1]
  · -- far from the pole: the function is constant
    have hyc' : y ∉ poleCore c p r := by
      rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ c.val.target := hP.closedBall_subset ((closedBall_subset_closedBall
        (by have := hP.four_r_le; linarith)) hw)
      refine hyc ⟨c.val.map_target hwt, ?_⟩
      rw [c.val.right_inv hwt]
      exact closedBall_subset_ball (by have := hP.four_r_le; linarith) hw
    set d := complexChartAt (n := n) y
    have hyd : y ∈ d.val.source := mem_complexChartAt_source y
    have hdt : d.val y ∈ d.val.target := d.val.map_source hyd
    obtain ⟨Wω, ρ, hyW, hρ, hlev⟩ := exists_kahler_potential ωb d hdt B
    set O : Set (ComplexModel n) := d.val.target ∩ d.val.symm ⁻¹' (poleCore c p r)ᶜ with hO
    have hOo : IsOpen O := d.val.isOpen_inter_preimage_symm hP.isClosed_core.isOpen_compl
    have hyO : d.val y ∈ O := ⟨hdt, by rw [mem_preimage, d.val.left_inv hyd]; exact hyc'⟩
    refine ⟨d, Wω ∩ O, ρ, hyd, ⟨hyW, hyO⟩, hρ.mono (hρ.1.inter hOo) inter_subset_left, ?_⟩
    have hc := plurisubharmonicOn_const_add_kahler_potential ωb hB0 hρ hlev (1 + a)
    intro w hw
    refine (hc w hw.1).congr ?_
    filter_upwards [(hρ.1.inter hOo).mem_nhds hw] with w' hw'
    simp only [chartFunction]
    rw [poleFun_eq_const hP hw'.2.2]

/-- In positive dimension every open neighbourhood of a point contains another point. -/
theorem exists_ne_mem_of_isOpen (hn : 0 < n) {U : Set M} (hU : IsOpen U) {x : M}
    (hx : x ∈ U) : ∃ y ∈ U, y ≠ x := by
  set c := complexChartAt (n := n) x
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  set V : Set (ComplexModel n) := c.val.target ∩ c.val.symm ⁻¹' U
  have hVo : IsOpen V := c.val.isOpen_inter_preimage_symm hU
  have hxV : c.val x ∈ V := ⟨c.val.map_source hxc, by rw [mem_preimage, c.val.left_inv hxc]; exact hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo _ hxV
  set e : ComplexModel n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  set w : ComplexModel n := c.val x + ((ε / 2 : ℝ) : ℂ) • e
  have hw : ‖w - c.val x‖ = ε / 2 := by
    simp only [w, add_sub_cancel_left, norm_smul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hwV : w ∈ V := hball (by rw [mem_ball, dist_eq_norm, hw]; linarith)
  refine ⟨c.val.symm w, hwV.2, fun h => ?_⟩
  have h1 : w = c.val x := by
    rw [← h, c.val.right_inv hwV.1]
  rw [h1, sub_self, norm_zero] at hw
  linarith

/-- Local nondegeneracy of the pole function in positive dimension. -/
theorem locallyNondegenerate_poleFun (hn : 0 < n) {c : ComplexChart n M} {p : ComplexModel n}
    {R₁ a : ℝ} {x₀ : M} (hx₀ : ∀ y ∈ c.val.source, c.val y = p → y = x₀) :
    LocallyNondegenerate (poleFun c p R₁ a) := by
  intro x U hU hxU
  obtain ⟨y, hyU, hyx⟩ : ∃ y ∈ U, y ≠ x₀ := by
    by_cases hx : x = x₀
    · exact exists_ne_mem_of_isOpen hn hU (hx ▸ hxU)
    · exact ⟨x, hxU, hx⟩
  exact ⟨y, hyU, poleFun_ne_bot fun hy hcy => hyx (hx₀ y hy hcy)⟩

variable (n M) in
/-- The chart data at a point: a radius `R₁` with `closedBall (z(x₀)) R₁` in the preferred chart
target and the pole radius `r = min (R₁/4) (1/2)`. -/
theorem exists_poleRadii (x₀ : M) : ∃ R₁ r : ℝ,
    PoleRadii (complexChartAt (n := n) x₀) ((complexChartAt (n := n) x₀).val x₀) R₁ r := by
  set c := complexChartAt (n := n) x₀
  have hp : c.val x₀ ∈ c.val.target := c.val.map_source (mem_complexChartAt_source x₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp c.val.open_target _ hp
  refine ⟨ε / 2, min (ε / 8) (1 / 2), ⟨lt_min (by positivity) (by norm_num), ?_, ?_, ?_⟩⟩
  · have := min_le_left (ε / 8) (1 / 2); linarith
  · have h1 : min (ε / 8) (1 / 2) ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (le_min (by positivity) (by norm_num)) (min_le_right _ _) 2
    have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
    have h2 : (1 / 2 : ℝ) ^ 2 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      norm_num; linarith
    linarith
  · exact (closedBall_subset_ball (by linarith)).trans hball

/-- **`PointPoleStatement` in positive dimension** (`claude-global-l2:point-pole`). -/
theorem pointPoleStatement_of_pos (hn : 0 < n) {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] : PointPoleStatement n X := by
  intro _ ωb x₀
  obtain ⟨R₁, r, hP⟩ := exists_poleRadii n X x₀
  set c := complexChartAt (n := n) x₀
  obtain ⟨m, hm, hmω⟩ := exists_lineValue_lower_bound_of_isCompact' ωb.isKahler.1 c
    (isCompact_closedBall _ R₁) hP.closedBall_subset
  have hr := hP.r_pos
  set B : ℝ := 2 * poleK / (Real.pi * m * r ^ 2) + 1 with hBdef
  have hK := poleK_nonneg
  have hB0 : 0 < B := by positivity
  have hB : 2 * poleK / r ^ 2 ≤ Real.pi * B * m := by
    have hpm : 0 < Real.pi * m := by positivity
    rw [hBdef, div_le_iff₀ (by positivity)]
    have : Real.pi * (2 * poleK / (Real.pi * m * r ^ 2) + 1) * m * r ^ 2 =
        2 * poleK + Real.pi * m * r ^ 2 := by
      field_simp
    rw [this]
    have : 0 ≤ Real.pi * m * r ^ 2 := by positivity
    linarith
  have hinj : ∀ y ∈ c.val.source, c.val y = c.val x₀ → y = x₀ := fun y hy h =>
    c.val.injOn hy (mem_complexChartAt_source x₀) h
  refine ⟨B, hB0, poleFun c (c.val x₀) R₁ (Real.log (r ^ 2)),
    ⟨thetaPlurisubharmonic_poleFun ωb hP hmω hB0.le hB, locallyNondegenerate_poleFun hn hinj⟩,
    poleFun_le hP, fun x hx => poleFun_ne_bot fun hxs h => hx (hinj x hxs h),
    fun x hx => (continuousAt_poleFun hP fun hxs h => hx (hinj x hxs h)).continuousWithinAt,
    r, hr, fun x hx hxr => ?_⟩
  rw [poleFun_of_mem hx (ball_subset_ball (by have := hP.four_r_le; linarith) hxr),
    poleChart_eq_logNormSq (le_of_lt (by rw [← dist_eq_norm]; exact hxr))]

/-- **`PointPoleStatement` fails in dimension zero**: for every `ω` and `x₀` the conclusion is
false, since `log |z - z(x₀)|² = -∞` on the whole (open) chart domain near `x₀`. -/
theorem pointPole_conclusion_false_dim_zero {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X] (ωb : KahlerBackground 0 X)
    (x₀ : X) : ¬ ∃ B : ℝ, 0 < B ∧ ∃ P : X → EReal,
      IsThetaPshPotential (B • ωb.form).val P ∧ (∀ x, P x ≤ 0) ∧ (∀ x, x ≠ x₀ → P x ≠ ⊥) ∧
      ContinuousOn P {x₀}ᶜ ∧ ∃ r : ℝ, 0 < r ∧ ∀ x ∈ (complexChartAt (n := 0) x₀).val.source,
        (complexChartAt (n := 0) x₀).val x ∈ ball ((complexChartAt (n := 0) x₀).val x₀) r →
          P x = logNormSq ((complexChartAt (n := 0) x₀).val x -
            (complexChartAt (n := 0) x₀).val x₀) := by
  rintro ⟨B, -, P, hP, -, -, -, r, hr, hloc⟩
  set c := complexChartAt (n := 0) x₀
  obtain ⟨y, hy, hyne⟩ := hP.2 x₀ c.val.source c.val.open_source (mem_complexChartAt_source x₀)
  have hball : c.val y ∈ ball (c.val x₀) r := by
    rw [Subsingleton.elim (c.val y) (c.val x₀)]; exact mem_ball_self hr
  rw [hloc y hy hball, Subsingleton.elim (c.val y - c.val x₀) 0, logNormSq_zero] at hyne
  exact hyne rfl

end SGPT.PSH.GlobalL2
