import SGPT.Trace.OTExt4Patch

/-!
# Subcritical integrability of the normal pole and the splitting of the critical weight

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:pole`.  Inputs of the last paragraph of the
proof of FPT `lem:critical-gain-initial-gluing`:

* `lintegral_multiplierWeight_logPole_lt_top`: for a normal pole `R` of a compact submanifold of
  codimension `q` and `0 ≤ c < q`, `∫_X R^{-c} dμ < ∞` (near `W` by the flat comparison of the
  pole region `exists_poleRegion`, away from `W` since `R` is bounded below there).
* `multiplierWeight_one_le_split`: `e^{-Φ} ≤ e^{-(1+κ)Φ} L⁻¹ + L^{1/κ}` for `L > 0` (FPT's Hölder
  inequality with exponents `1 + κ` and `(1 + κ)/κ`, in the pointwise form used here).
* `rpow_log_sq_le`: `((log t)²)^s ≤ C t^{-1/2}` on `(0, 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

/-- `((log t)²)^s ≤ C t^{-1/2}` for `0 < t < 1`. -/
theorem rpow_log_sq_le {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t < 1 → (Real.log t ^ 2) ^ s ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  set a : ℝ := 1 / (4 * s) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨(16 * s ^ 2) ^ s, by positivity, fun t ht0 ht1 => ?_⟩
  have h1 := Real.abs_log_mul_self_rpow_lt t a ht0 ht1.le ha0
  have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht0 a
  rw [abs_mul, abs_of_pos hta, ← lt_div_iff₀ hta] at h1
  have h1' : |Real.log t| ≤ 4 * s * t ^ (-a) := by
    rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
    have : 1 / a = 4 * s := by rw [ha]; field_simp
    rw [this] at h1
    exact h1.le
  have h2 : Real.log t ^ 2 ≤ 16 * s ^ 2 * t ^ (-2 * a) := by
    have : Real.log t ^ 2 = |Real.log t| ^ 2 := (sq_abs _).symm
    rw [this]
    calc |Real.log t| ^ 2 ≤ (4 * s * t ^ (-a)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1' 2
      _ = 16 * s ^ 2 * t ^ (-2 * a) := by
        rw [mul_pow, show (-2 * a) = (-a) * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast ht0.le]
        ring
  calc (Real.log t ^ 2) ^ s ≤ (16 * s ^ 2 * t ^ (-2 * a)) ^ s :=
        Real.rpow_le_rpow (sq_nonneg _) h2 hs.le
    _ = (16 * s ^ 2) ^ s * t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le]
        congr 2
        rw [ha]; field_simp; ring

/-- **Splitting of the weight**: `e^{-u} ≤ e^{-(1+κ)u} L⁻¹ + L^{1/κ}` for `κ, L > 0`. -/
theorem multiplierWeight_one_le_split {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L) (u : EReal) :
    multiplierWeight 1 u ≤
      multiplierWeight (1 + κ) u * ENNReal.ofReal L⁻¹ + ENNReal.ofReal (L ^ (1 / κ)) := by
  induction u using EReal.rec with
  | bot =>
      rw [multiplierWeight_bot one_pos, multiplierWeight_bot (by linarith),
        ENNReal.top_mul (by simp [hL]), top_add]
  | top => rw [multiplierWeight_top one_pos]; exact zero_le
  | coe φ =>
      rw [multiplierWeight_coe, multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set w := Real.exp (-(1 * φ)) with hw
      have hw0 : 0 < w := Real.exp_pos _
      have hsplit : Real.exp (-((1 + κ) * φ)) = w * Real.exp (-(κ * φ)) := by
        rw [hw, ← Real.exp_add]; ring_nf
      have hwk : Real.exp (-(κ * φ)) = w ^ κ := by
        rw [hw, ← Real.exp_mul]; ring_nf
      rw [hsplit, hwk]
      by_cases hle : w ≤ L ^ (1 / κ)
      · have : 0 ≤ w * w ^ κ * L⁻¹ := by positivity
        linarith
      · rw [not_le] at hle
        have hLw : L < w ^ κ := by
          have := Real.rpow_lt_rpow (Real.rpow_nonneg hL.le _) hle hκ
          rwa [← Real.rpow_mul hL.le, one_div_mul_cancel hκ.ne', Real.rpow_one] at this
        have : w ≤ w * w ^ κ * L⁻¹ := by
          rw [mul_assoc, ← div_eq_mul_inv]
          have : 1 ≤ w ^ κ / L := by rw [le_div_iff₀ hL]; linarith
          nlinarith
        have : 0 ≤ L ^ (1 / κ) := Real.rpow_nonneg hL.le _
        linarith

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- `e^{-c log R} = R^{-c}` where `R > 0`. -/
theorem multiplierWeight_logPole {R : X → ℝ} {x : X} (hx : 0 < R x) (c : ℝ) :
    multiplierWeight c (logPole R x) = ENNReal.ofReal (R x ^ (-c)) := by
  rw [logPole, ENNReal.log_pos_real' (by rw [ENNReal.toReal_ofReal hx.le]; exact hx),
    ENNReal.toReal_ofReal hx.le, multiplierWeight_coe, Real.rpow_def_of_pos hx]
  ring_nf

/-- `e^{log R} = R`. -/
theorem exp_logPole (R : X → ℝ) (x : X) : EReal.exp (logPole R x) = ENNReal.ofReal (R x) := by
  rw [logPole, ENNReal.exp_log]

/-- A continuous function positive off the compact `W` is bounded below off every open
neighbourhood of `W`. -/
theorem exists_pos_le_off [CompactSpace X] {R : X → ℝ} (hRc : Continuous R)
    (hpos : ∀ x, x ∉ W → 0 < R x) {N : Set X} (hN : IsOpen N) (hWN : W ⊆ N) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x, x ∉ N → r₀ ≤ R x := by
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  rcases (Nᶜ).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun x hx => absurd (show x ∈ Nᶜ from hx) (by rw [he]; exact id)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hRc.continuousOn
  exact ⟨R x₀, hpos x₀ fun h => hx₀ (hWN h), fun x hx => hmin hx⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- The pole region of the normal pole at `p ∈ W` (`exists_poleRegion` for `Λ = log R`). -/
theorem poleRegion_logPole {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m) (hmn : m < n) {ωb : KahlerBackground n X}
    {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) (p : W) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ →
      closedBall (0 : ComplexModel n) ε ⊆ (FlatData.ofRegularAtDim (hW p.1 p.2)).flat.target ∧
      (∀ c : ℝ, 0 ≤ c → c < ((n - m : ℕ) : ℝ) →
        ∫⁻ x in finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' closedBall 0 ε,
          multiplierWeight c (logPole R x) ∂μ ≠ ⊤) ∧
      (∀ (g : X → ℂ) (O : Set X), IsOpen O →
        (∀ x ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x) →
        (∀ x ∈ O, x ∈ W → g x = 0) → ∀ K : Set X, IsCompact K →
        K ⊆ O ∩ finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' closedBall 0 ε →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ENNReal.ofReal (‖g x‖ ^ 2) ≤
          ENNReal.ofReal C * ENNReal.ofReal (R x)) := by
  set Fd := FlatData.ofRegularAtDim (hW p.1 p.2)
  have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
  have hp0 : fcoord Fd p.1 = 0 := (hW p.1 p.2).2.2.choose_spec.2.1
  obtain ⟨U, hU, C, hC⟩ := localForm_normalized hW hR.pole 0 p
  have hloc : ∃ U ∈ 𝓝 p.1, ∃ C : ℝ, ∀ y ∈ U, y ∉ W →
      |(logPole R y).toReal - Real.log (normalWeight n m (fcoord Fd y))| ≤ C := by
    refine ⟨U, hU, C, fun y hy hyW => ?_⟩
    have := hC y hy hyW
    rwa [neg_zero, EReal.coe_zero, add_zero] at this
  obtain ⟨ε₀, hε₀, hreg⟩ := exists_poleRegion hμ Fd hmn hpF hp0 hR.pole.continuous.measurable
    hR.pole.ne_top (fun x hx => (hR.pole.eq_bot_iff x).mp hx) hloc
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨h1, h2, h3, -, -⟩ := hreg ε hε hεε
  refine ⟨h1, h2, fun g O hO hg hg0 K hK hKO => ?_⟩
  obtain ⟨C', hC', hb⟩ := h3 g O hO hg hg0 K hK hKO
  exact ⟨C', hC', fun x hx => (hb x hx).trans_eq (by rw [exp_logPole])⟩

/-- **Subcritical integrability of the normal pole**: `∫_X R^{-c} dμ < ∞` for `0 ≤ c < q`. -/
theorem lintegral_multiplierWeight_logPole_lt_top [CompactSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m) (hWc : IsCompact W) (hmn : m < n)
    {ωb : KahlerBackground n X} {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) {c : ℝ}
    (hc0 : 0 ≤ c) (hcq : c < ((n - m : ℕ) : ℝ)) :
    ∫⁻ x, multiplierWeight c (logPole R x) ∂μ < ⊤ := by
  choose ε hε hreg using fun p : W => poleRegion_logPole hμ hW hmn hR p
  set A : W → Set X := fun p => finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 (ε p)
  set B : W → Set X := fun p =>
    finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' closedBall 0 (ε p)
  have hAo : ∀ p, IsOpen (A p) := fun p => isOpen_finv_image _
    (ball_subset_closedBall.trans (hreg p (ε p) (hε p) le_rfl).1)
  have hpA : ∀ p : W, p.1 ∈ A p := by
    intro p
    have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
    have hp0 : fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) p.1 = 0 :=
      (hW p.1 p.2).2.2.choose_spec.2.1
    exact ⟨0, mem_ball_self (hε p), by rw [← hp0, finv_fcoord _ hpF]⟩
  have hBm : ∀ p, MeasurableSet (B p) := fun p =>
    ((isCompact_closedBall 0 (ε p)).image_of_continuousOn
      ((continuousOn_finv _).mono (hreg p (ε p) (hε p) le_rfl).1)).isClosed.measurableSet
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover A hAo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hpA ⟨x, hx⟩⟩)
  set N : Set X := ⋃ p ∈ t, A p
  have hNo : IsOpen N := isOpen_biUnion fun p _ => hAo p
  obtain ⟨r₀, hr₀, hr₀le⟩ := exists_pos_le_off hR.continuous (fun x hx => hR.pos_of_notMem hx)
    hNo ht
  have hΛm : Measurable fun x => multiplierWeight c (logPole R x) :=
    (multiplierWeight_antitone hc0).measurable.comp hR.pole.continuous.measurable
  have hpt : ∀ x, multiplierWeight c (logPole R x) ≤
      ∑ p ∈ t, (B p).indicator (fun x => multiplierWeight c (logPole R x)) x +
        ENNReal.ofReal (r₀ ^ (-c)) := by
    intro x
    by_cases hx : x ∈ N
    · obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp hx
      refine le_trans (le_of_eq ?_) (le_add_right (Finset.single_le_sum
        (f := fun p => (B p).indicator (fun x => multiplierWeight c (logPole R x)) x)
        (fun _ _ => zero_le) hpt))
      rw [indicator_of_mem (image_mono ball_subset_closedBall hxp)]
    · have hRx := hr₀le x hx
      rw [multiplierWeight_logPole (hr₀.trans_le hRx)]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow_of_nonpos hr₀ hRx (by linarith)
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_add_right _ measurable_const, lintegral_finsetSum' _
    fun p _ => (hΛm.indicator (hBm p)).aemeasurable, lintegral_const]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr fun p _ => ?_,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)⟩
  rw [lintegral_indicator (hBm p)]
  exact lt_top_iff_ne_top.mpr ((hreg p (ε p) (hε p) le_rfl).2.1 c hc0 hcq)

end SGPT.Trace.OTExt4
