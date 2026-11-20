import SGPT.Okounkov.TranscendentalL2Hypersurface
import SGPT.Okounkov.TranscendentalL2Pole
import SGPT.Okounkov.TranscendentalL2Complement
import SGPT.Okounkov.TranscendentalL2Extension

/-!
# Transporting weights and data to the complement of the hypersurface

Plan `tok/RELGEN3` step P8 (blueprint `l2:transported-weight`, `l2:cutoff-pole`, chapter
`claude-tok-l2`).

* `exists_bump`: smooth cut-off functions on `ℂⁿ`.
* `exists_pole_family`: by compactness of `Z`, a finite family of preferred charts in which the
  cut-off pole `χ(w - e z) log |w - e z|²` has Levi form `≥ -C_P π β`, with `C_P` independent of
  `z` (the constant `C₁` of `l2:cutoff-pole` relative to `β`).
* `contDiffAt_comp_sigma`, `leviForm_comp_sigma`, `dbarDir_comp_sigma`: smoothness, Levi forms
  and `∂̄` of `u ∘ σ`, `σ = s ∘ d⁻¹` the holomorphic inverse of `d ∘ π` off the exceptional set, read
  in a chart of `Z`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Okounkov.TranscendentalRelGen

/-! ### Cut-off functions -/

/-- A smooth cut-off function equal to `1` on `B(0, ε/2)`, vanishing off `B(0, ε)`, with values
in `[0, 1]`. -/
theorem exists_bump {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ w, 0 ≤ χ w ∧ χ w ≤ 1) ∧ (∀ w, ‖w‖ < ε / 2 → χ w = 1) ∧
      (∀ w, ε ≤ ‖w‖ → χ w = 0) := by
  let b : ContDiffBump (0 : ComplexModel n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun w => ⟨b.nonneg, b.le_one⟩, fun w hw => ?_,
    fun w hw => ?_⟩
  · exact b.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hw.le)
  · exact b.zero_of_le_dist (by rw [dist_zero_right]; exact hw)

/-! ### The cut-off pole -/

section Pole

variable {n : ℕ}

theorem cutoffPole_eq_log {χ₀ : ComplexModel n → ℝ} {ρ : ℝ} (hχ1 : ∀ w, ‖w‖ < ρ → χ₀ w = 1)
    {w₀ w : ComplexModel n} (hw : ‖w - w₀‖ < ρ) :
    cutoffPole χ₀ w₀ w = Real.log (‖w - w₀‖ ^ 2) := by
  simp [cutoffPole, hχ1 _ hw]

theorem cutoffPole_eq_zero {χ₀ : ComplexModel n → ℝ} {ε : ℝ} (hχ0 : ∀ w, ε ≤ ‖w‖ → χ₀ w = 0)
    {w₀ w : ComplexModel n} (hw : ε ≤ ‖w - w₀‖) : cutoffPole χ₀ w₀ w = 0 := by
  simp [cutoffPole, hχ0 _ hw]

theorem cutoffPole_le {χ₀ : ComplexModel n → ℝ} {ε : ℝ}
    (hχ : ∀ w, 0 ≤ χ₀ w ∧ χ₀ w ≤ 1) (hχ0 : ∀ w, ε ≤ ‖w‖ → χ₀ w = 0)
    (w₀ w : ComplexModel n) : cutoffPole χ₀ w₀ w ≤ max 0 (Real.log (ε ^ 2)) := by
  unfold cutoffPole
  by_cases hw : ε ≤ ‖w - w₀‖
  · rw [hχ0 _ hw, zero_mul]; exact le_max_left _ _
  · push Not at hw
    obtain ⟨h0, h1⟩ := hχ (w - w₀)
    rcases eq_or_ne w w₀ with rfl | hne
    · simp
    have hpos : 0 < ‖w - w₀‖ ^ 2 := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      positivity
    have hlog : Real.log (‖w - w₀‖ ^ 2) ≤ Real.log (ε ^ 2) :=
      Real.log_le_log hpos (pow_le_pow_left₀ (norm_nonneg _) hw.le 2)
    rcases le_or_gt (Real.log (‖w - w₀‖ ^ 2)) 0 with hl | hl
    · exact (mul_nonpos_of_nonneg_of_nonpos h0 hl).trans (le_max_left _ _)
    · calc χ₀ (w - w₀) * Real.log (‖w - w₀‖ ^ 2) ≤ 1 * Real.log (‖w - w₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 hl.le
        _ ≤ max 0 (Real.log (ε ^ 2)) := by rw [one_mul]; exact hlog.trans (le_max_right _ _)

end Pole

section Family

variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **A finite family of pole charts** (blueprint `l2:transported-weight`, uniformity of `C₁`):
on a compact Kähler manifold there is `C_P ≥ 0` such that every `z` lies in a preferred chart `e`
with a cut-off `χ` (`= 1` on `B(0, ε/2)`, `= 0` off `B(0, ε)`, `B̄(e z, ε) ⊆ e.target`) for which
`Levi (χ(· - e z) log |· - e z|²) ≥ -C_P π β_e(·, i·)` on `e.target \ {e z}`. -/
theorem exists_pole_family [CompactSpace Z] (β : ClosedRealOneOneForm n Z)
    (hβ : β.val.IsKahler) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ z : Z, ∃ (a₀ : Z) (ε : ℝ) (χP : ComplexModel n → ℝ),
      z ∈ (complexChartAt (n := n) a₀).val.source ∧ 0 < ε ∧ ContDiff ℝ ∞ χP ∧
      closedBall ((complexChartAt (n := n) a₀).val z) ε ⊆
        (complexChartAt (n := n) a₀).val.target ∧
      (∀ w, 0 ≤ χP w ∧ χP w ≤ 1) ∧ (∀ w, ‖w‖ < ε / 2 → χP w = 1) ∧
      (∀ w, ε ≤ ‖w‖ → χP w = 0) ∧
      ∀ w ∈ (complexChartAt (n := n) a₀).val.target,
        w ≠ (complexChartAt (n := n) a₀).val z → ∀ v : ComplexModel n,
          -CP * (Real.pi * β.val.coeff (complexChartAt (n := n) a₀) w ![v, Complex.I • v]) ≤
            leviForm (cutoffPole χP ((complexChartAt (n := n) a₀).val z)) w v := by
  classical
  -- local data at every point
  have hloc : ∀ y₀ : Z, ∃ (ε : ℝ) (χ : ComplexModel n → ℝ) (C : ℝ), 0 < ε ∧
      closedBall ((complexChartAt (n := n) y₀).val y₀) (3 * ε) ⊆
        (complexChartAt (n := n) y₀).val.target ∧
      ContDiff ℝ ∞ χ ∧ (∀ w, 0 ≤ χ w ∧ χ w ≤ 1) ∧ (∀ w, ‖w‖ < ε / 2 → χ w = 1) ∧
      (∀ w, ε ≤ ‖w‖ → χ w = 0) ∧ 0 ≤ C ∧
      ∀ w₀ w : ComplexModel n, w ≠ w₀ →
        ‖w₀ - (complexChartAt (n := n) y₀).val y₀‖ < ε →
        w ∈ (complexChartAt (n := n) y₀).val.target → ∀ v : ComplexModel n,
          -C * (Real.pi * β.val.coeff (complexChartAt (n := n) y₀) w ![v, Complex.I • v]) ≤
            leviForm (cutoffPole χ w₀) w v := by
    intro y₀
    set e := complexChartAt (n := n) y₀ with he
    have hy₀t : e.val y₀ ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y₀)
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp e.val.open_target _ hy₀t
    set ε : ℝ := R / 4 with hεdef
    have hε : 0 < ε := by positivity
    have h3 : closedBall (e.val y₀) (3 * ε) ⊆ e.val.target :=
      (closedBall_subset_ball (by rw [hεdef]; linarith)).trans hRsub
    obtain ⟨χ, hχs, hχc, hχb, hχ1, hχ0⟩ := exists_bump (n := n) hε
    obtain ⟨C₁, hC₁, hlevi⟩ := exists_neg_le_leviForm_cutoffPole hχs hχc (half_pos hε)
      fun w hw => hχ1 w (by simpa using hw)
    obtain ⟨m, hm, hmle⟩ := exists_lineValue_lower_bound_of_isCompact (β := β.val) hβ.1 e
      (isCompact_closedBall (e.val y₀) (2 * ε))
      ((closedBall_subset_closedBall (by linarith)).trans h3)
    refine ⟨ε, χ, C₁ / (Real.pi * m), hε, h3, hχs, hχb, hχ1, hχ0, by positivity, ?_⟩
    intro w₀ w hw hw₀ hwt v
    have hβnn : 0 ≤ β.val.coeff e w ![v, Complex.I • v] := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((hβ.1 e w hwt).2 v hv).le
    by_cases hwK : w ∈ closedBall (e.val y₀) (2 * ε)
    · have h1 := hlevi w₀ w hw v
      have h2 := hmle w hwK v
      have hπm : 0 < Real.pi * m := by positivity
      have : -(C₁ / (Real.pi * m)) * (Real.pi * β.val.coeff e w ![v, Complex.I • v]) =
          -(C₁ / m) * β.val.coeff e w ![v, Complex.I • v] := by
        field_simp
      rw [this]
      have h3' : -(C₁ / m) * β.val.coeff e w ![v, Complex.I • v] ≤ -C₁ * ‖v‖ ^ 2 := by
        have : C₁ * ‖v‖ ^ 2 ≤ C₁ / m * β.val.coeff e w ![v, Complex.I • v] := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hm]
          nlinarith
        linarith
      linarith
    · -- far from the pole the cut-off pole vanishes near `w`
      have hfar : ε < ‖w - w₀‖ := by
        rw [mem_closedBall, not_le, dist_eq_norm] at hwK
        have := norm_sub_le_norm_sub_add_norm_sub w w₀ (e.val y₀)
        linarith
      have hev : cutoffPole χ w₀ =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {u : ComplexModel n | ε < ‖u - w₀‖} :=
          isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        filter_upwards [hopen.mem_nhds hfar] with u hu
        exact cutoffPole_eq_zero hχ0 (le_of_lt hu)
      rw [PshRadialRegularization.leviForm_congr hev, leviForm_const, neg_mul]
      have : 0 ≤ C₁ / (Real.pi * m) := by positivity
      exact neg_nonpos.mpr (mul_nonneg this (mul_nonneg Real.pi_pos.le hβnn))
  choose ε χ C hε h3 hχs hχb hχ1 hχ0 hC hlevi using hloc
  -- compactness
  set W : Z → Set Z := fun y₀ => (complexChartAt (n := n) y₀).val.source ∩
    (complexChartAt (n := n) y₀).val ⁻¹' ball ((complexChartAt (n := n) y₀).val y₀) (ε y₀)
    with hW
  have hWmem : ∀ y₀, W y₀ ∈ 𝓝 y₀ := by
    intro y₀
    have hy₀ := mem_complexChartAt_source (n := n) y₀
    exact inter_mem ((complexChartAt (n := n) y₀).val.open_source.mem_nhds hy₀)
      ((complexChartAt (n := n) y₀).val.continuousAt hy₀ (ball_mem_nhds _ (hε y₀)))
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover W (fun y₀ _ => hWmem y₀)
  set CP : ℝ := ∑ y₀ ∈ t, C y₀ with hCP
  have hCP0 : 0 ≤ CP := Finset.sum_nonneg fun y₀ _ => hC y₀
  refine ⟨CP, hCP0, fun z => ?_⟩
  obtain ⟨y₀, hy₀t, hzW⟩ : ∃ y₀ ∈ t, z ∈ W y₀ := by
    simpa using ht (mem_univ z)
  set e := complexChartAt (n := n) y₀ with he
  have hzd : ‖e.val z - e.val y₀‖ < ε y₀ := by
    have := hzW.2
    rwa [mem_preimage, mem_ball, dist_eq_norm] at this
  refine ⟨y₀, ε y₀, χ y₀, hzW.1, hε y₀, hχs y₀, ?_, hχb y₀, hχ1 y₀, hχ0 y₀, ?_⟩
  · refine (closedBall_subset_closedBall' ?_).trans (h3 y₀)
    have := hε y₀
    rw [dist_eq_norm]; linarith
  · intro w hwt hw v
    have h1 := hlevi y₀ (e.val z) w hw hzd hwt v
    have hβnn : 0 ≤ β.val.coeff e w ![v, Complex.I • v] := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((hβ.1 e w hwt).2 v hv).le
    have hle : C y₀ ≤ CP := Finset.single_le_sum (fun y _ => hC y) hy₀t
    have : -CP * (Real.pi * β.val.coeff e w ![v, Complex.I • v]) ≤
        -C y₀ * (Real.pi * β.val.coeff e w ![v, Complex.I • v]) := by
      have := mul_nonneg Real.pi_pos.le hβnn
      nlinarith
    exact this.trans h1

end Family

/-! ### Lower bounds for Levi forms in a chart -/

section LeviLB

variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- `u` is smooth near `w` in the chart `e`, with Levi form `≥ K π β_e(v, iv)` there. -/
def HasLeviLB (β : ClosedRealOneOneForm n Z) (u : Z → ℝ) (K : ℝ) (e : ComplexChart n Z)
    (w : ComplexModel n) : Prop :=
  ∃ O : Set (ComplexModel n), IsOpen O ∧ w ∈ O ∧ O ⊆ e.val.target ∧
    ContDiffOn ℝ ∞ (fun w' => u (e.val.symm w')) O ∧
    ∀ w' ∈ O, ∀ v : ComplexModel n,
      K * (Real.pi * β.val.coeff e w' ![v, Complex.I • v]) ≤
        leviForm (fun w'' => u (e.val.symm w'')) w' v

theorem HasLeviLB.add {β : ClosedRealOneOneForm n Z} {u₁ u₂ : Z → ℝ} {K₁ K₂ : ℝ}
    {e : ComplexChart n Z} {w : ComplexModel n} (h₁ : HasLeviLB β u₁ K₁ e w)
    (h₂ : HasLeviLB β u₂ K₂ e w) : HasLeviLB β (fun t => u₁ t + u₂ t) (K₁ + K₂) e w := by
  obtain ⟨O₁, hO₁, hw₁, hO₁t, hs₁, hl₁⟩ := h₁
  obtain ⟨O₂, hO₂, hw₂, -, hs₂, hl₂⟩ := h₂
  refine ⟨O₁ ∩ O₂, hO₁.inter hO₂, ⟨hw₁, hw₂⟩, fun w' hw' => hO₁t hw'.1,
    (hs₁.mono inter_subset_left).add (hs₂.mono inter_subset_right), fun w' hw' v => ?_⟩
  have c₁ : ContDiffAt ℝ 2 (fun w'' => u₁ (e.val.symm w'')) w' :=
    ((hs₁ w' hw'.1).contDiffAt (hO₁.mem_nhds hw'.1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have c₂ : ContDiffAt ℝ 2 (fun w'' => u₂ (e.val.symm w'')) w' :=
    ((hs₂ w' hw'.2).contDiffAt (hO₂.mem_nhds hw'.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hadd := leviForm_add c₁ c₂ v
  have e1 := hl₁ w' hw'.1 v
  have e2 := hl₂ w' hw'.2 v
  rw [add_mul]
  calc K₁ * (Real.pi * β.val.coeff e w' ![v, Complex.I • v]) +
        K₂ * (Real.pi * β.val.coeff e w' ![v, Complex.I • v])
      ≤ leviForm (fun w'' => u₁ (e.val.symm w'')) w' v +
          leviForm (fun w'' => u₂ (e.val.symm w'')) w' v := add_le_add e1 e2
    _ = leviForm (fun w'' => u₁ (e.val.symm w'') + u₂ (e.val.symm w'')) w' v := hadd.symm

theorem HasLeviLB.mono {β : ClosedRealOneOneForm n Z} (hβ : β.val.IsKahler) {u : Z → ℝ}
    {K K' : ℝ} {e : ComplexChart n Z} {w : ComplexModel n} (h : HasLeviLB β u K e w)
    (hK : K' ≤ K) : HasLeviLB β u K' e w := by
  obtain ⟨O, hO, hw, hOt, hs, hl⟩ := h
  refine ⟨O, hO, hw, hOt, hs, fun w' hw' v => le_trans ?_ (hl w' hw' v)⟩
  have hβnn : 0 ≤ β.val.coeff e w' ![v, Complex.I • v] := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((hβ.1 e w' (hOt hw')).2 v hv).le
  exact mul_le_mul_of_nonneg_right hK (mul_nonneg Real.pi_pos.le hβnn)

/-- A function vanishing near a point has Levi form `0` there. -/
theorem hasLeviLB_of_eventually_zero (β : ClosedRealOneOneForm n Z) {u : Z → ℝ}
    {t : Z} {N : Set Z} (hN : IsOpen N) (htN : t ∈ N) (hu : ∀ t' ∈ N, u t' = 0) :
    HasLeviLB β u 0 (complexChartAt (n := n) t) ((complexChartAt (n := n) t).val t) := by
  set e := complexChartAt (n := n) t
  have hte : t ∈ e.val.source := mem_complexChartAt_source t
  set O := e.val.target ∩ e.val.symm ⁻¹' N with hO
  have hOo : IsOpen O := e.val.isOpen_inter_preimage_symm hN
  have hzero : ∀ w' ∈ O, u (e.val.symm w') = 0 := fun w' hw' => hu _ hw'.2
  refine ⟨O, hOo, ⟨e.val.map_source hte, by rw [mem_preimage, e.val.left_inv hte]; exact htN⟩,
    inter_subset_left, (contDiffOn_const (c := (0 : ℝ))).congr hzero, fun w' hw' v => ?_⟩
  have hev : (fun w'' => u (e.val.symm w'')) =ᶠ[𝓝 w'] fun _ => (0 : ℝ) := by
    filter_upwards [hOo.mem_nhds hw'] with w'' hw''
    exact hzero w'' hw''
  rw [PshRadialRegularization.leviForm_congr hev, leviForm_const, zero_mul]

/-- **Levi form of a smooth `θ`-psh function, as a lower bound in a chart.** -/
theorem hasLeviLB_of_thetaPlurisubharmonicOn {β : ClosedRealOneOneForm n Z}
    {θ : SmoothRealForm n Z 2} {u : Z → EReal} {Ω : Set Z}
    (hu : ThetaPlurisubharmonicOn θ u Ω) {K : ℝ}
    (hK : ∀ (e : ComplexChart n Z) w, w ∈ e.val.target → ∀ v : ComplexModel n,
      K * (Real.pi * β.val.coeff e w ![v, Complex.I • v]) ≤
        -(Real.pi * θ.coeff e w ![v, Complex.I • v]))
    {uℝ : Z → ℝ} (e : ComplexChart n Z) {O : Set (ComplexModel n)} (hO : IsOpen O)
    (hOt : O ⊆ e.val.target ∩ e.val.symm ⁻¹' Ω)
    (hs : ContDiffOn ℝ ∞ (fun w => uℝ (e.val.symm w)) O)
    (heq : ∀ w ∈ O, chartFunction u e w = (uℝ (e.val.symm w) : EReal))
    {w : ComplexModel n} (hw : w ∈ O) : HasLeviLB β uℝ K e w :=
  ⟨O, hO, hw, fun _ hw' => (hOt hw').1, hs, fun w' hw' v =>
    (hK e w' (hOt hw').1 v).trans (leviForm_ge_of_thetaPlurisubharmonicOn hu e hO hs heq hw'
      (hOt hw').1 (hOt hw').2 v)⟩

end LeviLB

/-! ### The holomorphic inverse `σ = s ∘ d⁻¹` -/

section Sigma

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The open set of base coordinates where `σ = s ∘ d⁻¹` is defined off `B` and lands in the
chart `e`. -/
def sigmaDomain (B : Set X) (s : X → Z) (d : ComplexChart n X) (e : ComplexChart n Z) :
    Set (ComplexModel n) :=
  coordinateDomain s d e ∩ d.val.symm ⁻¹' Bᶜ

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
theorem isOpen_sigmaDomain {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) (e : ComplexChart n Z) : IsOpen (sigmaDomain B s d e) := by
  have h1 : IsOpen (Bᶜ ∩ s ⁻¹' e.val.source) :=
    hs.continuousOn.isOpen_inter_preimage hBc.isOpen_compl e.val.open_source
  have h2 := d.val.isOpen_inter_preimage_symm h1
  convert h2 using 1
  ext x
  simp only [sigmaDomain, coordinateDomain, mem_inter_iff, mem_preimage]
  tauto

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
theorem mem_sigmaDomain {B : Set X} {s : X → Z} {d : ComplexChart n X} {e : ComplexChart n Z}
    {x : ComplexModel n} (hx : x ∈ d.val.target) (hxB : d.val.symm x ∉ B)
    (hxe : s (d.val.symm x) ∈ e.val.source) : x ∈ sigmaDomain B s d e :=
  ⟨⟨hx, hxe⟩, hxB⟩

theorem contDiffAt_coordinateMap_sigma {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) (e : ComplexChart n Z) {x : ComplexModel n}
    (hx : x ∈ sigmaDomain B s d e) : ContDiffAt ℂ ∞ (coordinateMap s d e) x :=
  coordinateMap_contDiffAt_of_contMDiffAt d e hx.1
    (hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hx.2))

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
theorem comp_sigma_eq {B : Set X} {s : X → Z} {d : ComplexChart n X} {e : ComplexChart n Z}
    {x : ComplexModel n} (hx : x ∈ sigmaDomain B s d e) {α : Type*} (u : Z → α) :
    u (s (d.val.symm x)) = u (e.val.symm (coordinateMap s d e x)) := by
  simp only [coordinateMap, Function.comp_apply, e.val.left_inv hx.1.2]

omit [IsComplexManifold n X] [IsComplexManifold n Z] in
theorem continuousAt_sigma {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) {x : ComplexModel n} (hx : x ∈ d.val.target)
    (hxB : d.val.symm x ∉ B) : ContinuousAt (fun x' => s (d.val.symm x')) x :=
  ContinuousAt.comp (f := d.val.symm)
    ((hs.continuousOn).continuousAt (hBc.isOpen_compl.mem_nhds hxB))
    (d.val.continuousAt_symm hx)

/-- **`u ∘ σ` in a chart**: smoothness and the Levi form of `u ∘ σ` at `x` are those of
`u ∘ e⁻¹` at `S x = e(σ x)`, transported by the holomorphic map `S = e ∘ s ∘ d⁻¹`. -/
theorem leviForm_comp_sigma {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) (e : ComplexChart n Z) {u : Z → ℝ} {O : Set (ComplexModel n)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ (fun w => u (e.val.symm w)) O) {x : ComplexModel n}
    (hx : x ∈ sigmaDomain B s d e) (hxO : coordinateMap s d e x ∈ O) :
    ContDiffAt ℝ ∞ (fun x' => u (s (d.val.symm x'))) x ∧ ∀ ξ : ComplexModel n,
      leviForm (fun x' => u (s (d.val.symm x'))) x ξ =
        leviForm (fun w => u (e.val.symm w)) (coordinateMap s d e x)
          (fderiv ℝ (coordinateMap s d e) x ξ) := by
  set S := coordinateMap s d e with hS
  have hDo := isOpen_sigmaDomain hBc hs d e
  have hSc : ContinuousOn S (sigmaDomain B s d e) := fun y hy =>
    (contDiffAt_coordinateMap_sigma hBc hs d e hy).continuousAt.continuousWithinAt
  set U := sigmaDomain B s d e ∩ S ⁻¹' O with hU
  have hUo : IsOpen U := hSc.isOpen_inter_preimage hDo hO
  have hxU : x ∈ U := ⟨hx, hxO⟩
  have hSU : ContDiffOn ℂ ∞ S U := fun y hy =>
    (contDiffAt_coordinateMap_sigma hBc hs d e hy.1).contDiffWithinAt
  have hev : (fun x' => u (s (d.val.symm x'))) =ᶠ[𝓝 x] fun y => u (e.val.symm (S y)) := by
    filter_upwards [hDo.mem_nhds hx] with y hy
    exact comp_sigma_eq hy u
  refine ⟨?_, fun ξ => ?_⟩
  · have h1 : ContDiffAt ℝ ∞ (fun w => u (e.val.symm w)) (S x) :=
      (hu _ hxO).contDiffAt (hO.mem_nhds hxO)
    have h2 : ContDiffAt ℝ ∞ S x :=
      (contDiffAt_coordinateMap_sigma hBc hs d e hx).restrict_scalars ℝ
    exact (h1.comp x h2).congr_of_eventuallyEq hev
  · rw [PshRadialRegularization.leviForm_congr hev]
    exact LeviFormHolomorphicComp.leviForm_comp hUo hO hSU hu (fun y hy => hy.2) hxU ξ

/-- **`∂̄` of `v ∘ σ` in a chart.** -/
theorem dbarDir_comp_sigma {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) (e : ComplexChart n Z) {v : Z → ℂ} {x : ComplexModel n}
    (hx : x ∈ sigmaDomain B s d e)
    (hv : DifferentiableAt ℝ (fun w => v (e.val.symm w)) (coordinateMap s d e x))
    (ξ : ComplexModel n) :
    CauchyGreen.dbarDir ξ (fun x' => v (s (d.val.symm x'))) x =
      CauchyGreen.dbarDir (fderiv ℝ (coordinateMap s d e) x ξ) (fun w => v (e.val.symm w))
        (coordinateMap s d e x) := by
  have hDo := isOpen_sigmaDomain hBc hs d e
  have hev : (fun x' => v (s (d.val.symm x'))) =ᶠ[𝓝 x]
      fun y => v (e.val.symm (coordinateMap s d e y)) := by
    filter_upwards [hDo.mem_nhds hx] with y hy
    exact comp_sigma_eq hy v
  have hS : DifferentiableAt ℂ (coordinateMap s d e) x :=
    (contDiffAt_coordinateMap_sigma hBc hs d e hx).differentiableAt (by simp)
  rw [show CauchyGreen.dbarDir ξ (fun x' => v (s (d.val.symm x'))) x =
      CauchyGreen.dbarDir ξ (fun y => v (e.val.symm (coordinateMap s d e y))) x by
    simp only [CauchyGreen.dbarDir, hev.fderiv_eq]]
  exact dbarDir_comp_of_differentiableAt hS hv ξ

/-- `u ∘ σ` is smooth at `x` when `u ∘ e⁻¹` is smooth at `e(σ x)` (complex values). -/
theorem contDiffAt_comp_sigma {B : Set X} {s : X → Z} (hBc : IsClosed B)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (d : ComplexChart n X) (e : ComplexChart n Z) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {v : Z → F} {x : ComplexModel n} (hx : x ∈ sigmaDomain B s d e)
    (hv : ContDiffAt ℝ ∞ (fun w => v (e.val.symm w)) (coordinateMap s d e x)) :
    ContDiffAt ℝ ∞ (fun x' => v (s (d.val.symm x'))) x := by
  have hDo := isOpen_sigmaDomain hBc hs d e
  have hev : (fun x' => v (s (d.val.symm x'))) =ᶠ[𝓝 x]
      fun y => v (e.val.symm (coordinateMap s d e y)) := by
    filter_upwards [hDo.mem_nhds hx] with y hy
    exact comp_sigma_eq hy v
  have h2 : ContDiffAt ℝ ∞ (coordinateMap s d e) x :=
    (contDiffAt_coordinateMap_sigma hBc hs d e hx).restrict_scalars ℝ
  exact (hv.comp x h2).congr_of_eventuallyEq hev

end Sigma

/-! ### Functions defined through one chart -/

section ChartLift

variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]

open Classical in
/-- A function on the chart target, transported to `Z` and extended by `0`. -/
def chartLift {α : Type*} [Zero α] (e : ComplexChart n Z) (f : ComplexModel n → α) (t : Z) :
    α :=
  if t ∈ e.val.source then f (e.val t) else 0

theorem chartLift_symm {α : Type*} [Zero α] (e : ComplexChart n Z) (f : ComplexModel n → α)
    {w : ComplexModel n} (hw : w ∈ e.val.target) : chartLift e f (e.val.symm w) = f w := by
  classical
  unfold chartLift
  rw [if_pos (e.val.map_target hw), e.val.right_inv hw]

theorem chartLift_of_mem {α : Type*} [Zero α] (e : ComplexChart n Z) (f : ComplexModel n → α)
    {t : Z} (ht : t ∈ e.val.source) : chartLift e f t = f (e.val t) := by
  classical
  unfold chartLift
  rw [if_pos ht]

theorem isClosed_chart_symm_image [T2Space Z] (e : ComplexChart n Z) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) : IsClosed (e.val.symm '' K) :=
  (hK.image_of_continuousOn (e.val.continuousOn_symm.mono hKe)).isClosed

theorem chartLift_eq_zero {α : Type*} [Zero α] (e : ComplexChart n Z)
    {f : ComplexModel n → α} {K : Set (ComplexModel n)} (hf : ∀ w ∉ K, f w = 0) {t : Z}
    (ht : t ∉ e.val.symm '' K) : chartLift e f t = 0 := by
  classical
  unfold chartLift
  split_ifs with hte
  · exact hf _ fun hK => ht ⟨e.val t, hK, e.val.left_inv hte⟩
  · rfl

theorem notMem_chart_symm_image {e : ComplexChart n Z} {K : Set (ComplexModel n)}
    (hKe : K ⊆ e.val.target) {t : Z} (ht : t ∉ e.val.source) : t ∉ e.val.symm '' K := by
  rintro ⟨w, hw, rfl⟩
  exact ht (e.val.map_target (hKe hw))

end ChartLift

/-! ### The data `χ f` -/

section Data

variable {n : ℕ}

/-- `χ f'` is smooth on `ℂⁿ` when `χ` is supported in `B̄(w₀, δ)` and `f'` is holomorphic on
`B(w₀, 2δ)`. -/
theorem contDiff_cutData {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) {w₀ : ComplexModel n}
    {δ : ℝ} (hδ : 0 < δ) (hχ0 : ∀ w, δ ≤ ‖w - w₀‖ → χ w = 0) {f' : ComplexModel n → ℂ}
    (hf' : DifferentiableOn ℂ f' (ball w₀ (2 * δ))) :
    ContDiff ℝ ∞ (fun w => (χ w : ℂ) * f' w) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ ball w₀ (2 * δ)
  · have hf's : ContDiffAt ℝ ∞ f' w :=
      ((contDiffOn_of_differentiableOn_complex hf' isOpen_ball).contDiffAt
        (isOpen_ball.mem_nhds hw)).restrict_scalars ℝ
    exact ((ofRealCLM.contDiff.comp hχ).contDiffAt).mul hf's
  · have hfar : δ < ‖w - w₀‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hw; linarith
    have hopen : IsOpen {u : ComplexModel n | δ < ‖u - w₀‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    refine contDiffAt_const (c := (0 : ℂ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hfar] with u hu
    simp [hχ0 u hu.le]

theorem fderiv_eq_zero_of_far {χ : ComplexModel n → ℝ} {w₀ : ComplexModel n} {δ : ℝ}
    (hχ0 : ∀ w, δ ≤ ‖w - w₀‖ → χ w = 0) {w : ComplexModel n} (hw : δ < ‖w - w₀‖) :
    fderiv ℝ χ w = 0 := by
  have hopen : IsOpen {u : ComplexModel n | δ < ‖u - w₀‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hev : χ =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hw] with u hu
    exact hχ0 u hu.le
  rw [hev.fderiv_eq, fderiv_const_apply]

/-- **`∂̄ (χ f') = f' ∂̄ χ`** for holomorphic `f'`, as an estimate valid everywhere. -/
theorem norm_dbarDir_cutData_le {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {w₀ : ComplexModel n} {δ : ℝ} (hδ : 0 < δ) (hχ0 : ∀ w, δ ≤ ‖w - w₀‖ → χ w = 0)
    {f' : ComplexModel n → ℂ} (hf' : DifferentiableOn ℂ f' (ball w₀ (2 * δ)))
    (w η : ComplexModel n) :
    ‖CauchyGreen.dbarDir η (fun w => (χ w : ℂ) * f' w) w‖ ≤
      ‖f' w‖ * ‖fderiv ℝ χ w‖ * ‖η‖ := by
  by_cases hw : w ∈ ball w₀ (2 * δ)
  · have hfd : DifferentiableAt ℂ f' w := hf'.differentiableAt (isOpen_ball.mem_nhds hw)
    have hχd : DifferentiableAt ℝ (fun w => (χ w : ℂ)) w :=
      (ofRealCLM.differentiable.comp (hχ.differentiable (by simp))).differentiableAt
    rw [CauchyGreen.dbarDir_mul hχd (hfd.restrictScalars ℝ),
      OTChen.dbarDir_eq_zero_of_differentiableAt hfd, mul_zero, add_zero, norm_mul, mul_comm]
    have h1 := PointPole.norm_dbarDir_le (fun w => (χ w : ℂ)) w η
    have h2 : fderiv ℝ (fun w => (χ w : ℂ)) w = ofRealCLM.comp (fderiv ℝ χ w) :=
      (ofRealCLM.hasFDerivAt.comp w ((hχ.differentiable (by simp)) w).hasFDerivAt).fderiv
    have h3 : ‖fderiv ℝ (fun w => (χ w : ℂ)) w‖ ≤ ‖fderiv ℝ χ w‖ := by
      rw [h2]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have : ‖(ofRealCLM : ℝ →L[ℝ] ℂ)‖ = 1 := ofRealCLM_norm
      rw [this, one_mul]
    calc ‖f' w‖ * ‖CauchyGreen.dbarDir η (fun w => (χ w : ℂ)) w‖
        ≤ ‖f' w‖ * (‖fderiv ℝ (fun w => (χ w : ℂ)) w‖ * ‖η‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖f' w‖ * (‖fderiv ℝ χ w‖ * ‖η‖) := by gcongr
      _ = ‖f' w‖ * ‖fderiv ℝ χ w‖ * ‖η‖ := by ring
  · have hfar : δ < ‖w - w₀‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hw; linarith
    have hopen : IsOpen {u : ComplexModel n | δ < ‖u - w₀‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have hev : (fun w => (χ w : ℂ) * f' w) =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hfar] with u hu
      simp [hχ0 u hu.le]
    have h0 : CauchyGreen.dbarDir η (fun w => (χ w : ℂ) * f' w) w = 0 := by
      simp [CauchyGreen.dbarDir, hev.fderiv_eq]
    rw [h0, norm_zero]
    positivity

end Data

/-! ### The three weights -/

section Weights

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The real-valued weight `φ_N` (it agrees with `relgenWeight` where `ψ_E` is finite). -/
def realWeight (π : Z → X) (E : MeteredEffectiveQDivisor n Z) (d : ComplexChart n X)
    (ρ : ComplexModel n → ℝ) (h : Z → ℝ) (N : ℕ) (a : ℝ) (y : Z) : ℝ :=
  ((N : ℝ) + 1) * (E.weight y).toReal + a * (ρ (d.val (π y)) + h y)

omit [IsComplexManifold n X] in
theorem relgenWeight_eq_realWeight {π : Z → X} {E : MeteredEffectiveQDivisor n Z}
    {d : ComplexChart n X} {ρ : ComplexModel n → ℝ} {h : Z → ℝ} {N : ℕ} {a : ℝ} {y : Z}
    (hy : E.weight y ≠ ⊥) (hy' : E.weight y ≠ ⊤) :
    relgenWeight π E d ρ h N a y = (realWeight π E d ρ h N a y : EReal) := by
  unfold relgenWeight realWeight
  rw [← EReal.coe_toReal hy' hy, ← EReal.coe_mul, ← EReal.coe_add, EReal.toReal_coe]

/-- **Levi form of `φ_N`** (blueprint `l2:transported-weight`): `dd^c φ_N ≥ ((N+1)/c) β` at the
points of `V` where `ψ_E` is finite, in every chart. -/
theorem hasLeviLB_realWeight {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d (ball p r) ρ) (N : ℕ) {t : Z}
    (htV : t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) (htE : E.weight t ≠ ⊥)
    (e : ComplexChart n Z) (hte : t ∈ e.val.source) :
    HasLeviLB β (realWeight π E d ρ h N (((N : ℝ) + 1) / c)) (((N : ℝ) + 1) / c) e
      (e.val t) := by
  set a : ℝ := ((N : ℝ) + 1) / c with ha
  obtain ⟨O₁, hO₁, ht₁, hO₁t, hs₁, heq₁⟩ := exists_real_weight_of_isDivisorMetric hE htE e hte
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hV
  have hVo : IsOpen V := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.continuous
  set O₂ := e.val.target ∩ e.val.symm ⁻¹' V with hO₂
  have hO₂o : IsOpen O₂ := e.val.isOpen_inter_preimage_symm hVo
  have hφ := thetaPlurisubharmonicOn_weight hπ θ β hβ E hc hh hheq d hρ N (le_refl a)
  have hne_top : ∀ y, E.weight y ≠ ⊤ := weight_ne_top_of_isDivisorMetric hE
  refine hasLeviLB_of_thetaPlurisubharmonicOn hφ (K := a) ?_ e (hO₁.inter hO₂o)
    (fun w hw => hw.2) ?_ ?_ ⟨ht₁, e.val.map_source hte, by
      rw [mem_preimage, e.val.left_inv hte]; exact htV⟩
  · intro e' w _ v
    simp only [ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring_nf
    rfl
  · -- smoothness
    have hρF : ContDiffOn ℝ ∞ (fun w => ρ (coordinateMap π e d w)) O₂ :=
      hρ.2.2.1.comp ((coordinateMap_contDiffOn_real hπ e d).mono fun w hw =>
        ⟨hw.1, hw.2.1⟩) fun w hw => hw.2.2
    have hhe : ContDiffOn ℝ ∞ (fun w => h (e.val.symm w)) O₂ := (hh e).mono inter_subset_left
    have hsum := (hs₁.mono inter_subset_left).const_smul ((N : ℝ) + 1) |>.add
      (((hρF.add hhe).const_smul a).mono inter_subset_right)
    refine hsum.congr fun w _ => ?_
    simp only [realWeight, coordinateMap, Function.comp_apply, smul_eq_mul]
  · intro w hw
    have hfin : E.weight (e.val.symm w) ≠ ⊥ := by
      rw [heq₁ w hw.1]; exact EReal.coe_ne_bot _
    exact relgenWeight_eq_realWeight hfin (hne_top _)

/-- **Levi form of the relative Jacobian weight** (blueprint `l2:volume-weight`): off the
exceptional set, `dd^c ψ_R ≥ -Θ_R ≥ -C₂ β`, in every chart. -/
theorem hasLeviLB_relJacobianWeight {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric
      (GlobalRelativeJacobianIdeal.actualRelativeJacobianDivisor (n := n) hπ) ER)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y) (β : ClosedRealOneOneForm n Z) {C₂ : ℝ}
    (hdom : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ (-ER.curvature).val.coeff e z ![v, Complex.I • v] +
        C₂ * β.val.coeff e z ![v, Complex.I • v])
    {t : Z} (htA : t ∉ A) (e : ComplexChart n Z) (hte : t ∈ e.val.source) :
    HasLeviLB β (fun t => (ER.weight t).toReal) (-C₂) e (e.val t) := by
  have htR := relJacobianWeight_ne_bot hπ hER hAc hBc hpre hs hleft htA
  obtain ⟨O, hO, htO, hOt, hsO, heqO⟩ := exists_real_weight_of_isDivisorMetric hER htR e hte
  have hpsh : ThetaPlurisubharmonicOn ER.curvature.val ER.weight univ :=
    fun e' z hz _ => MeteredDivisorPositivity.thetaPlurisubharmonic_weight ER e' z hz
  refine hasLeviLB_of_thetaPlurisubharmonicOn hpsh (K := -C₂)
    (uℝ := fun t => (ER.weight t).toReal) ?_ e hO
    (fun w hw => ⟨hOt hw, mem_univ _⟩) hsO (fun w hw => heqO w hw) htO
  intro e' w hw v
  have h1 := hdom e' w hw v
  simp only [ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.neg_apply] at h1
  have hπ0 := Real.pi_pos
  nlinarith

end Weights

/-! ### The cut-off pole on `Z` -/

section PoleZ

variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Levi form of the pole in its chart**: `Levi (q χ log|· - w₀|²) ≥ -q C_P π β`. -/
theorem hasLeviLB_poleZ (β : ClosedRealOneOneForm n Z) (e : ComplexChart n Z)
    {χP : ComplexModel n → ℝ} (hχP : ContDiff ℝ ∞ χP) {w₀ : ComplexModel n} {CP : ℝ}
    (hlevi : ∀ w ∈ e.val.target, w ≠ w₀ → ∀ v : ComplexModel n,
      -CP * (Real.pi * β.val.coeff e w ![v, Complex.I • v]) ≤ leviForm (cutoffPole χP w₀) w v)
    (q : ℕ) {t : Z} (hte : t ∈ e.val.source) (htw : e.val t ≠ w₀) :
    HasLeviLB β (chartLift e fun w => (q : ℝ) * cutoffPole χP w₀ w) (-((q : ℝ) * CP)) e
      (e.val t) := by
  set O := e.val.target ∩ {w₀}ᶜ with hO
  have hOo : IsOpen O := e.val.open_target.inter isOpen_compl_singleton
  have heq : ∀ w ∈ O, chartLift e (fun w => (q : ℝ) * cutoffPole χP w₀ w) (e.val.symm w) =
      (q : ℝ) * cutoffPole χP w₀ w := fun w hw => chartLift_symm e _ hw.1
  have hsm : ContDiffOn ℝ ∞ (fun w => (q : ℝ) * cutoffPole χP w₀ w) O := fun w hw =>
    ((contDiffAt_cutoffPole hχP hw.2).const_smul (q : ℝ)).contDiffWithinAt
  refine ⟨O, hOo, ⟨e.val.map_source hte, htw⟩, inter_subset_left, hsm.congr heq, ?_⟩
  intro w hw v
  have hev : (fun w' => chartLift e (fun w => (q : ℝ) * cutoffPole χP w₀ w) (e.val.symm w')) =ᶠ[𝓝 w]
      fun w' => (q : ℝ) * cutoffPole χP w₀ w' := by
    filter_upwards [hOo.mem_nhds hw] with w' hw' using heq w' hw'
  rw [PshRadialRegularization.leviForm_congr hev]
  have h2 : ContDiffAt ℝ 2 (cutoffPole χP w₀) w :=
    (contDiffAt_cutoffPole hχP hw.2).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsmul := leviForm_smul h2 (q : ℝ) v
  change leviForm ((q : ℝ) • cutoffPole χP w₀) w v ≥ _
  rw [hsmul]
  have h3 := hlevi w hw.1 hw.2 v
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith

end PoleZ

end SGPT.Okounkov.TranscendentalL2
