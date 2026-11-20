import SGPT.PSH.GlobalL2Local
import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiRegularReduction
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.FirstPass.BTTruncations

/-!
# Local `L²` corrections on balls, singular weights

Blueprint `claude-global-l2:local-singular`.  `localBallCorrection` proves
`LocalBallCorrectionStatement n`: for every plurisubharmonic `Ψ : ℂⁿ → [-∞, ∞)` on `B(z₀, R)`,
`c > 0` and smooth `a`, there is `G` holomorphic on `B(z₀, r)` with
`∫_{B(z₀,r)} |a - G|² e^{-Ψ - c|z-z₀|²} ≤ (2/c) ∫_{B(z₀,R)} |∂̄a|² e^{-Ψ - c|z-z₀|²}`.

Proof (as in TN's `Pending.OhsawaTakegoshiRegularReduction`): the truncations `max (Ψ, -N)` are
regularized on `B(z₀, (r+R)/2)` by decreasing smooth psh functions
(`HolomorphicPullback.exists_decreasingMollifierApproximation`); `localBallCorrectionSmooth`
applies to the smooth weights `Ψ_{N,j} + c|z - z₀|²`, and the correction limit lemma
`exists_correction_limit` (a normal-family argument, TN's
`exists_subseq_differentiableOn_extension_of_weighted_bounds`, followed by Fatou's lemma and
monotone convergence) passes first to `j → ∞` and then to `N → ∞`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-- `e^{-(x + t)} = e^{-x} e^{-t}` for `x < ⊤`. -/
theorem multiplierWeight_one_add_coe_real {x : EReal} (hx : x ≠ ⊤) (t : ℝ) :
    multiplierWeight 1 (x + (t : EReal)) =
      multiplierWeight 1 x * ENNReal.ofReal (Real.exp (-t)) := by
  induction x using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot one_pos, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
  | top => exact absurd rfl hx

theorem ballWeight_eq_mul {Ψ : ComplexModel n → EReal} {z : ComplexModel n} (hz : Ψ z ≠ ⊤)
    (c : ℝ) (z₀ : ComplexModel n) :
    ballWeight Ψ c z₀ z =
      multiplierWeight 1 (Ψ z) * ENNReal.ofReal (Real.exp (-(c * ‖z - z₀‖ ^ 2))) :=
  multiplierWeight_one_add_coe_real hz _

theorem ballWeight_coe (f : ComplexModel n → ℝ) (c : ℝ) (z₀ z : ComplexModel n) :
    ballWeight (fun z => (f z : EReal)) c z₀ z =
      ENNReal.ofReal (Real.exp (-(f z + c * ‖z - z₀‖ ^ 2))) := by
  rw [ballWeight, ← EReal.coe_add, multiplierWeight_coe, one_mul]

/-! ### The correction limit lemma -/

theorem norm_sq_le_two_mul (a F : ℂ) : ‖F‖ ^ 2 ≤ 2 * ‖a - F‖ ^ 2 + 2 * ‖a‖ ^ 2 := by
  have h : ‖F‖ ≤ ‖a - F‖ + ‖a‖ := by
    calc ‖F‖ = ‖a - (a - F)‖ := by ring_nf
      _ ≤ ‖a‖ + ‖a - F‖ := norm_sub_le _ _
      _ = ‖a - F‖ + ‖a‖ := add_comm _ _
  have h0 : 0 ≤ ‖F‖ := norm_nonneg _
  nlinarith [norm_nonneg (a - F), norm_nonneg a, sq_nonneg (‖a - F‖ - ‖a‖)]

/-- **Correction limit.**  Let `F_i` be holomorphic on an open `U` with
`∫_U |a - F_i|² w_i ≤ A < ∞` for increasing measurable weights `w_i`, `w_0` locally bounded below
by positive constants and `∫_U |a|² w_0 < ∞`.  Then a holomorphic `G` on `U` has
`∫_U |a - G|² sup_i w_i ≤ A`. -/
theorem exists_correction_limit {U : Set (ComplexModel n)} (hUo : IsOpen U)
    {a : ComplexModel n → ℂ} (ha : ContinuousOn a U)
    {w : ℕ → ComplexModel n → ℝ≥0∞} (hwm : ∀ x ∈ U, Monotone fun i => w i x)
    (hwmeas : ∀ i, AEMeasurable (w i) (volume.restrict U))
    (hlow : ∀ x ∈ U, ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball x ρ, ENNReal.ofReal δ ≤ w 0 y)
    {F : ℕ → ComplexModel n → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ i, ∫⁻ x in U, ENNReal.ofReal (‖a x - F i x‖ ^ 2) * w i x ≤ A)
    (hfin : ∫⁻ x in U, ENNReal.ofReal (‖a x‖ ^ 2) * w 0 x ≠ ⊤) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G U ∧
      ∫⁻ x in U, ENNReal.ofReal (‖a x - G x‖ ^ 2) * ⨆ i, w i x ≤ A := by
  have hUm : MeasurableSet U := hUo.measurableSet
  have hUU : (⋃ _ : ℕ, U) = U := iUnion_const U
  set B : ℝ≥0∞ := ∫⁻ x in U, ENNReal.ofReal (‖a x‖ ^ 2) * w 0 x with hBdef
  have haM : AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2) * w 0 x) (volume.restrict U) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((ha.aestronglyMeasurable hUm).norm.aemeasurable.pow_const 2)).mul (hwmeas 0)
  -- an `L²(w_0)` bound for the `F_i` themselves
  have hboundF : ∀ i, ∫⁻ x in U, ENNReal.ofReal (‖F i x‖ ^ 2) * w 0 x ≤ 2 * A + 2 * B := by
    intro i
    calc ∫⁻ x in U, ENNReal.ofReal (‖F i x‖ ^ 2) * w 0 x
        ≤ ∫⁻ x in U, (2 * (ENNReal.ofReal (‖a x - F i x‖ ^ 2) * w i x) +
            2 * (ENNReal.ofReal (‖a x‖ ^ 2) * w 0 x)) := by
          refine setLIntegral_mono' hUm fun x hx => ?_
          have h1 : ENNReal.ofReal (‖F i x‖ ^ 2) ≤
              2 * ENNReal.ofReal (‖a x - F i x‖ ^ 2) + 2 * ENNReal.ofReal (‖a x‖ ^ 2) := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            exact ENNReal.ofReal_le_ofReal (norm_sq_le_two_mul (a x) (F i x))
          calc ENNReal.ofReal (‖F i x‖ ^ 2) * w 0 x
              ≤ (2 * ENNReal.ofReal (‖a x - F i x‖ ^ 2) + 2 * ENNReal.ofReal (‖a x‖ ^ 2)) *
                  w 0 x := mul_le_mul_of_nonneg_right h1 zero_le
            _ = 2 * (ENNReal.ofReal (‖a x - F i x‖ ^ 2) * w 0 x) +
                  2 * (ENNReal.ofReal (‖a x‖ ^ 2) * w 0 x) := by ring
            _ ≤ _ := by
              gcongr
              exact hwm x hx (Nat.zero_le i)
      _ = 2 * (∫⁻ x in U, ENNReal.ofReal (‖a x - F i x‖ ^ 2) * w i x) + 2 * B := by
          rw [lintegral_add_right' _ (haM.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * A + 2 * B := by gcongr; exact hbound i
  have hAB : 2 * A + 2 * B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hA,
      ENNReal.mul_ne_top (by norm_num) hfin⟩
  obtain ⟨ψ, G, hψ, hG, hconv, -, -⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds (N := n) (α := Empty)
      (ι := Empty.elim) (g := Empty.elim) (U := fun _ => U) (fun _ => hUo) monotone_const
      (w := fun _ => w 0) (fun _ _ => monotone_const)
      (fun _ => by rw [hUU]; exact hwmeas 0)
      (fun x hx => by rw [hUU] at hx; exact hlow x hx)
      hF (fun _ e => e.elim) hAB (fun i => by simpa using hboundF i)
  rw [hUU] at hG hconv
  refine ⟨G, hG, ?_⟩
  -- Fatou for each fixed weight `w m`
  have hfixed : ∀ m, ∫⁻ x in U, ENNReal.ofReal (‖a x - G x‖ ^ 2) * w m x ≤ A := by
    intro m
    have hmeas : ∀ i, AEMeasurable
        (fun x => ENNReal.ofReal (‖a x - F (ψ i) x‖ ^ 2) * w m x) (volume.restrict U) :=
      fun i => (ENNReal.measurable_ofReal.comp_aemeasurable
        (((ha.sub (hF (ψ i)).continuousOn).aestronglyMeasurable hUm).norm.aemeasurable.pow_const
          2)).mul (hwmeas m)
    calc ∫⁻ x in U, ENNReal.ofReal (‖a x - G x‖ ^ 2) * w m x
        ≤ ∫⁻ x in U, liminf (fun i => ENNReal.ofReal (‖a x - F (ψ i) x‖ ^ 2) * w m x) atTop := by
          refine setLIntegral_mono' hUm fun x hx => ?_
          have ht : Tendsto (fun i => ENNReal.ofReal (‖a x - F (ψ i) x‖ ^ 2)) atTop
              (𝓝 (ENNReal.ofReal (‖a x - G x‖ ^ 2))) :=
            ENNReal.tendsto_ofReal (((tendsto_const_nhds.sub (hconv.tendsto_at hx)).norm).pow 2)
          by_cases h0 : ENNReal.ofReal (‖a x - G x‖ ^ 2) = 0
          · rw [h0, zero_mul]; exact zero_le
          · exact ((ENNReal.Tendsto.mul_const ht (Or.inl h0)).liminf_eq).ge
      _ ≤ liminf (fun i => ∫⁻ x in U, ENNReal.ofReal (‖a x - F (ψ i) x‖ ^ 2) * w m x) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop m] with i hi
          refine le_trans ?_ (hbound (ψ i))
          refine setLIntegral_mono' hUm fun x hx => ?_
          exact mul_le_mul_of_nonneg_left (hwm x hx (hi.trans (hψ.id_le i))) zero_le
  -- monotone convergence in the weight
  calc ∫⁻ x in U, ENNReal.ofReal (‖a x - G x‖ ^ 2) * ⨆ i, w i x
      = ∫⁻ x in U, ⨆ i, ENNReal.ofReal (‖a x - G x‖ ^ 2) * w i x := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.mul_iSup]
    _ = ⨆ i, ∫⁻ x in U, ENNReal.ofReal (‖a x - G x‖ ^ 2) * w i x := by
        refine lintegral_iSup' (fun i => (ENNReal.measurable_ofReal.comp_aemeasurable
          (((ha.sub hG.continuousOn).aestronglyMeasurable hUm).norm.aemeasurable.pow_const
            2)).mul (hwmeas i)) ?_
        refine (ae_restrict_iff' hUm).mpr (Eventually.of_forall fun x hx i j hij => ?_)
        exact mul_le_mul_of_nonneg_left (hwm x hx hij) zero_le
    _ ≤ A := iSup_le hfixed

/-! ### Bounded integrands on balls -/

theorem setLIntegral_ball_lt_top_of_bound {z₀ : ComplexModel n} {r : ℝ}
    {f : ComplexModel n → ℝ≥0∞} {M : ℝ} (hf : ∀ z ∈ ball z₀ r, f z ≤ ENNReal.ofReal M) :
    ∫⁻ z in ball z₀ r, f z < ⊤ := by
  calc ∫⁻ z in ball z₀ r, f z ≤ ∫⁻ _ in ball z₀ r, ENNReal.ofReal M :=
        setLIntegral_mono' isOpen_ball.measurableSet hf
    _ = ENNReal.ofReal M * volume (ball z₀ r) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem exists_bound_norm_sq_on_ball {z₀ : ComplexModel n} {r R : ℝ} (hrR : r < R)
    {a : ComplexModel n → ℂ} (ha : ContinuousOn a (ball z₀ R)) :
    ∃ M : ℝ, ∀ z ∈ ball z₀ r, ‖a z‖ ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
    (ha.mono (closedBall_subset_ball hrR))
  refine ⟨M ^ 2, fun z hz => ?_⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (hM z (ball_subset_closedBall hz)) 2

/-! ### The theorem -/

/-- **Local `L²` correction on a ball, singular weights** (`claude-global-l2:local-singular`). -/
theorem localBallCorrection : LocalBallCorrectionStatement n := by
  intro z₀ r R hr hrR c hc Ψ hΨ a ha
  set S : ℝ≥0∞ := ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z
    with hSdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hS : S = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  have hAtop : ENNReal.ofReal (2 / c) * S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  set R' : ℝ := (r + R) / 2 with hR'def
  have hrR' : r < R' := by rw [hR'def]; linarith
  have hR'R : R' < R := by rw [hR'def]; linarith
  have hr0 : (0 : ℝ) ≤ r := hr.le
  let Ω : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z₀ R, isOpen_ball⟩
  let A : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z₀ R', isOpen_ball⟩
  have hA : RelativelyCompactIn A Ω := by
    refine ⟨(isCompact_closedBall z₀ R').of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (closedBall_subset_ball hR'R)⟩
  have hΨΩ : PlurisubharmonicOn Ψ Ω := hΨ
  have hrA : ball z₀ r ⊆ ball z₀ R' := ball_subset_ball hrR'.le
  have hrR'' : ball z₀ r ⊆ ball z₀ R := ball_subset_ball hrR.le
  have haR : ContinuousOn a (ball z₀ R) := ha.continuousOn
  obtain ⟨Ma, hMa⟩ := exists_bound_norm_sq_on_ball hrR haR
  have hnsq : ∀ z : ComplexModel n, 0 ≤ c * ‖z - z₀‖ ^ 2 := fun z => by positivity
  have hnsqc : Continuous fun z : ComplexModel n => c * ‖z - z₀‖ ^ 2 := by fun_prop
  have hnsqs : ContDiff ℝ ∞ fun z : ComplexModel n => c * ‖z - z₀‖ ^ 2 :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hLeviNsq : ∀ z ξ : ComplexModel n,
      leviForm (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) z ξ = c * ‖ξ‖ ^ 2 := by
    intro z ξ
    have e : (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) =
        fun y => (c • fun w : ComplexModel n => ‖w‖ ^ 2) (y - z₀) := by
      funext y; simp [smul_eq_mul]
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul (contDiff_norm_sq ℝ).contDiffAt,
      leviForm_norm_sq]
  -- Stage 1: for fixed `N`, the smooth regularizations of `max (Ψ, -N)`
  have stage1 : ∀ N : ℕ, ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
      ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) *
          ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z ≤
        ENNReal.ofReal (2 / c) * S := by
    intro N
    obtain ⟨fs, hfs⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
      (truncationReal_isLocallyBoundedPshOn hΨΩ N) hA
    set Φ : ℕ → ComplexModel n → ℝ := fun j z => fs j z + c * ‖z - z₀‖ ^ 2 with hΦdef
    have hΦs : ∀ j, ContDiffOn ℝ ∞ (Φ j) (ball z₀ R') := fun j =>
      (hfs.1 j).1.add hnsqs.contDiffOn
    have hΦL : ∀ j, ∀ z ∈ ball z₀ R', ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm (Φ j) z ξ := by
      intro j z hz ξ
      have h1 : ContDiffAt ℝ 2 (fs j) z :=
        (((hfs.1 j).1.contDiffAt (isOpen_ball.mem_nhds hz))).of_le
          (WithTop.coe_le_coe.mpr le_top)
      have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) z :=
        (hnsqs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      have hsplit : Φ j = fs j + fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2 := rfl
      rw [hsplit, leviForm_add h1 h2, hLeviNsq]
      have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := A) (hfs.1 j).1
        (hfs.1 j).2.1 hz ξ
      linarith
    have hge : ∀ j, ∀ z ∈ ball z₀ R', truncationReal Ψ N z ≤ fs j z := fun j z hz =>
      (hfs.2.1 z hz).le_of_tendsto (hfs.2.2 z hz) j
    have hΨle : ∀ z ∈ ball z₀ R, Ψ z ≤ (truncationReal Ψ N z : EReal) := fun z hz => by
      rw [coe_truncationReal hΨΩ N hz]
      exact le_max_left _ _
    have hloc := fun j => localBallCorrectionSmooth z₀ r R' hr hrR' c hc (Φ j) (hΦs j) (hΦL j) a
      (ha.mono (ball_subset_ball hR'R.le))
    choose F hF hFb using hloc
    have hwle : ∀ j, ∀ z ∈ ball z₀ R', ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ballWeight Ψ c z₀ z := by
      intro j z hz
      have : ENNReal.ofReal (Real.exp (-Φ j z)) = multiplierWeight 1 ((Φ j z : ℝ) : EReal) := by
        rw [multiplierWeight_coe, one_mul]
      rw [this, ballWeight]
      refine multiplierWeight_antitone zero_le_one ?_
      rw [hΦdef]
      dsimp only
      rw [EReal.coe_add]
      gcongr
      exact (hΨle z (ball_subset_ball hR'R.le hz)).trans (EReal.coe_le_coe_iff.mpr (hge j z hz))
    have hbound : ∀ j, ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - F j z‖ ^ 2) *
        ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ENNReal.ofReal (2 / c) * S := by
      intro j
      refine (hFb j).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      calc ∫⁻ z in ball z₀ R', ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ j z))
          ≤ ∫⁻ z in ball z₀ R', ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z :=
            setLIntegral_mono' isOpen_ball.measurableSet fun z hz =>
              mul_le_mul_of_nonneg_left (hwle j z hz) zero_le
        _ ≤ S := lintegral_mono_set (ball_subset_ball hR'R.le)
    have hΦc : ∀ j, ContinuousOn (Φ j) (ball z₀ R') := fun j => (hΦs j).continuousOn
    obtain ⟨G, hG, hGint⟩ := exists_correction_limit isOpen_ball (haR.mono hrR'')
      (w := fun j z => ENNReal.ofReal (Real.exp (-Φ j z)))
      (fun z hz i j hij => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        have := (hfs.2.1 z (hrA hz)) hij
        simp only [hΦdef]; linarith)))
      (fun j => (ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
        (((hΦc j).mono hrA).neg.aemeasurable isOpen_ball.measurableSet))
      (fun x hx => by
        have hcont : ContinuousAt (Φ 0) x := (hΦc 0).continuousAt (isOpen_ball.mem_nhds (hrA hx))
        obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
        refine ⟨ρ, hρ, Real.exp (-(Φ 0 x + 1)), Real.exp_pos _, fun y hy => ?_⟩
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have h1 := hball (mem_ball.mp hy)
        rw [Real.dist_eq] at h1
        linarith [le_abs_self (Φ 0 y - Φ 0 x)])
      hF hAtop hbound
      (by
        obtain ⟨MΦ, hMΦ⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
          ((hΦc 0).mono (closedBall_subset_ball hrR'))
        refine (setLIntegral_ball_lt_top_of_bound (M := Ma * Real.exp MΦ) fun z hz => ?_).ne
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul (hMa z hz) (Real.exp_le_exp.mpr ?_)
          (Real.exp_pos _).le (le_trans (sq_nonneg _) (hMa z hz)))
        have := hMΦ z (ball_subset_closedBall hz)
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (Φ 0 z)])
    refine ⟨G, hG, le_trans ?_ hGint⟩
    refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [ballWeight_coe]
    have ht : Tendsto (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(truncationReal Ψ N z + c * ‖z - z₀‖ ^ 2))))) := by
      refine ENNReal.tendsto_ofReal (Real.continuous_exp.tendsto _ |>.comp ?_)
      exact ((hfs.2.2 z (hrA hz)).add tendsto_const_nhds).neg
    exact le_of_tendsto' ht fun j => le_iSup (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) j
  -- Stage 2: `N → ∞`
  choose G hG hGb using stage1
  have hwmeas2 : ∀ N, AEMeasurable (fun z => ballWeight (fun z => (truncationReal Ψ N z : EReal))
      c z₀ z) (volume.restrict (ball z₀ r)) := by
    intro N
    have hq : QuasiPlurisubharmonicOn (fun z => (truncationReal Ψ N z : EReal)) (ball z₀ R) :=
      fun x hx => (truncationReal_plurisubharmonicOn hΨΩ N x hx).quasiPlurisubharmonicAt
    have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      (μ := volume) isOpen_ball hq one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
    have h' : AEMeasurable (fun z => multiplierWeight 1 (truncationReal Ψ N z : EReal))
        (volume.restrict (ball z₀ R)) := h.congr (Eventually.of_forall fun z => by
          simp [multiplierDensity])
    have h'' := h'.mono_measure (Measure.restrict_mono hrR'' le_rfl)
    refine (h''.mul ((ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
      (hnsqc.neg.aemeasurable))).congr (Eventually.of_forall fun z => ?_)
    exact (ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal))
      (EReal.coe_ne_top _) c z₀).symm
  obtain ⟨G', hG', hG'int⟩ := exists_correction_limit isOpen_ball (haR.mono hrR'')
    (w := fun N z => ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z)
    (fun z hz i j hij => by
      simp only [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have := truncationReal_antitone hΨΩ (hrR'' hz) hij
      linarith)
    hwmeas2
    (fun x hx => by
      obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_ball x (hrR'' hx)
      obtain ⟨B, hB0, hB⟩ := hΨ.exists_nonnegative_compact_upper_bound
        (isCompact_closedBall x (ρ₀ / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
      refine ⟨ρ₀ / 2, by positivity, Real.exp (-(B + c * R ^ 2)), Real.exp_pos _, fun y hy => ?_⟩
      have hyR : y ∈ ball z₀ R := hball (ball_subset_ball (by linarith) hy)
      rw [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have htr : truncationReal Ψ 0 y ≤ B := by
        apply EReal.coe_le_coe_iff.mp
        rw [coe_truncationReal hΨΩ 0 hyR]
        refine max_le (hB y (ball_subset_closedBall hy)) ?_
        exact EReal.coe_le_coe_iff.mpr (by simpa using hB0)
      have hyz : ‖y - z₀‖ ^ 2 ≤ R ^ 2 := by
        have := mem_ball_iff_norm.mp hyR
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      nlinarith)
    hG hAtop hGb
    (by
      refine (setLIntegral_ball_lt_top_of_bound (M := Ma) fun z hz => ?_).ne
      have hw1 : ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z ≤ 1 := by
        rw [ballWeight_coe, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.exp_le_one_iff, neg_nonpos]
        have h0 : 0 ≤ truncationReal Ψ 0 z := by
          apply EReal.coe_le_coe_iff.mp
          rw [coe_truncationReal hΨΩ 0 (hrR'' hz)]
          exact le_max_right _ _ |>.trans' (by simp)
        linarith [hnsq z]
      calc ENNReal.ofReal (‖a z‖ ^ 2) * ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z
          ≤ ENNReal.ofReal (‖a z‖ ^ 2) * 1 := mul_le_mul_of_nonneg_left hw1 zero_le
        _ ≤ ENNReal.ofReal Ma := by rw [mul_one]; exact ENNReal.ofReal_le_ofReal (hMa z hz))
  refine ⟨G', hG', le_trans ?_ hG'int⟩
  refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hzR := hrR'' hz
  rw [ballWeight_eq_mul ((hΨ z hzR).ne_top) c z₀]
  have hfac : ∀ N : ℕ, ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z =
      multiplierWeight 1 (truncationReal Ψ N z : EReal) *
        ENNReal.ofReal (Real.exp (-(c * ‖z - z₀‖ ^ 2))) := fun N =>
    ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal)) (EReal.coe_ne_top _) c z₀
  rw [iSup_congr hfac, ← ENNReal.iSup_mul]
  exact mul_le_mul_of_nonneg_right (multiplierWeight_le_iSup_truncationReal hΨΩ one_pos hzR)
    zero_le

end SGPT.PSH.GlobalL2
