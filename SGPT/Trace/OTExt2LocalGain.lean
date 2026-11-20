import SGPT.Trace.OTExt2LocalSmooth
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization
import SGPT.Foundations.Analysis.Pending.HiepThreeTermEstimate

/-!
# FPT `lem:local-critical-gain-extension`

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:local-gain`.  Xia, *Foundations of
pluripotential theory*, q07, `lem:local-critical-gain-extension`:

> Let `m ≥ 0`, `q ≥ 1`, `D = B' × B'' ⋐ ℂ^m × ℂ^q` a product of balls centred at `0` of radii
> `r', r''` with `r'' < e^{-2}`.  Let `p` be plurisubharmonic near `D̄` and `f` holomorphic near
> `B̄'` with `∫_{B'} |f|² e^{-p(z', 0)} < ∞`.  Then there is `F` holomorphic on `D` with
> `F(z', 0) = f(z')` and
> `∫_D |F|² e^{-p} |w|^{-2q} (-log |w|²)^{-2} ≤ C ∫_{B'} |f|² e^{-p(z', 0)}`,
> `C` depending only on `m, q, r', r''`.

## Formalization

`ℂ^n = ℂ^m × ℂ^{n-m}`, `q = n - m ≥ 1`, `D = localDom n m r' r''`
(`|z'|² < r'²`, `|w|² < r''²`), `p : ℂⁿ → [-∞, ∞]` plurisubharmonic on an open `O ⊇ D̄`, `f`
holomorphic on an open `O' ⊇ B̄(0, r')`; `e^{-p}` is `multiplierWeight 1 p` (`= ∞` at the poles,
`0 · ∞ = 0`), the kernel is `criticalKernel n m` (`= ∞` on `{w = 0}`, a null set), Lebesgue
measures.  For `m = 0` the ball `B(0, r') ⊆ ℂ⁰` is a point and the right side is
`|f|² e^{-p(0)}`.  `LocalCriticalGainExtensionStatement n m` is the statement;
`localCriticalGainExtension` proves it, with `C = e^{π(r' + r'')²} C_q`.

## Proof

FPT's: for smooth weights `localCriticalGain_smooth` (applied to `P = p_j + π|z|²`); `p` is
approximated by the decreasing smooth psh radial regularizations `p_j` on a convex neighbourhood
of `D̄` (`PshRadialRegularization`, for the radial kernel `radialKernel`), the extensions `F_j` are
bounded in `L²(D)`, Montel's theorem gives a limit `F`, and Fatou's lemma the estimate.  If `p ≡ -∞`
near `D̄`, the finiteness hypothesis forces `f = 0` on `B'` and `F = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg normalWeight_eq_zero_iff)

variable {n : ℕ}

/-! ### A radial kernel -/

/-- The radial kernel `ρ(y) = χ(|y|²) / ∫ χ(|x|²)` (`χ = chenCutoff`). -/
def radialKernel (n : ℕ) (y : ComplexModel n) : ℝ :=
  chenCutoff (‖y‖ ^ 2) / ∫ x : ComplexModel n, chenCutoff (‖x‖ ^ 2)

theorem contDiff_chenCutoff_normSq :
    ContDiff ℝ ∞ (fun y : ComplexModel n => chenCutoff (‖y‖ ^ 2)) :=
  (contDiff_chenCutoff (k := ⊤)).comp (contDiff_norm_sq ℝ)

theorem tsupport_chenCutoff_normSq :
    tsupport (fun y : ComplexModel n => chenCutoff (‖y‖ ^ 2)) ⊆ closedBall 0 1 := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra h
  push Not at h
  exact hy (chenCutoff_of_ge (by nlinarith [norm_nonneg y]))

theorem integral_chenCutoff_normSq_pos : 0 < ∫ x : ComplexModel n, chenCutoff (‖x‖ ^ 2) := by
  have hc : Continuous (fun y : ComplexModel n => chenCutoff (‖y‖ ^ 2)) :=
    contDiff_chenCutoff_normSq.continuous
  have hcs : HasCompactSupport (fun y : ComplexModel n => chenCutoff (‖y‖ ^ 2)) :=
    HasCompactSupport.intro' (isCompact_closedBall 0 1) isClosed_closedBall
      (fun y hy => by
        by_contra h'
        exact hy (subset_closure (Function.mem_support.mpr h') |> tsupport_chenCutoff_normSq))
  rw [integral_pos_iff_support_of_nonneg (fun y => chenCutoff_nonneg _)
    (hc.integrable_of_hasCompactSupport hcs)]
  refine lt_of_lt_of_le (measure_ball_pos volume (0 : ComplexModel n) (by norm_num : (0 : ℝ) < 1 / 2))
    (measure_mono fun y hy => ?_)
  rw [Function.mem_support, chenCutoff_of_le]
  · norm_num
  · have := mem_ball_zero_iff.mp hy
    nlinarith [norm_nonneg y]

theorem isRadialKernel_radialKernel : IsRadialKernel (radialKernel n) := by
  have hI := integral_chenCutoff_normSq_pos (n := n)
  refine ⟨contDiff_chenCutoff_normSq.div_const _, fun y => div_nonneg (chenCutoff_nonneg _)
    hI.le, ?_, ?_, fun a ha y => ?_⟩
  · simp only [radialKernel]
    rw [integral_div, div_self hI.ne']
  · refine (closure_minimal (fun y hy => ?_) isClosed_closure).trans tsupport_chenCutoff_normSq
    refine subset_closure (Function.mem_support.mpr fun h => hy ?_)
    simp only [radialKernel, h, zero_div]
  · simp only [radialKernel, norm_smul, ha, one_mul]

/-! ### Convexity of the product of balls -/

theorem convex_localDom (m : ℕ) {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'') :
    Convex ℝ (localDom n m r' r'') := by
  have h1 : localDom n m r' r'' =
      (tangCLM n m).restrictScalars ℝ ⁻¹' ball 0 r' ∩ (normalCLM n m).restrictScalars ℝ ⁻¹' ball 0 r'' := by
    ext z
    simp only [localDom, mem_inter_iff, mem_preimage, mem_ball_zero_iff,
      ContinuousLinearMap.coe_restrictScalars', Set.mem_ofPred_eq, tanWeight, normalWeight_eq_norm_sq]
    rw [pow_lt_pow_iff_left₀ (norm_nonneg _) hr'.le two_ne_zero,
      pow_lt_pow_iff_left₀ (norm_nonneg _) hr''.le two_ne_zero]
  rw [h1]
  exact ((convex_ball 0 r').linear_preimage ((tangCLM n m).restrictScalars ℝ).toLinearMap).inter
    ((convex_ball 0 r'').linear_preimage ((normalCLM n m).restrictScalars ℝ).toLinearMap)

/-! ### Weights -/

theorem ofReal_exp_neg_le_multiplierWeight {a : EReal} {t : ℝ} (h : a ≤ (t : EReal)) :
    ENNReal.ofReal (Real.exp (-t)) ≤ multiplierWeight 1 a := by
  have := multiplierWeight_antitone (c := 1) zero_le_one h
  rwa [multiplierWeight_coe, one_mul] at this

theorem leviForm_pi_normSq (x v : ComplexModel n) :
    leviForm (fun z => Real.pi * ‖z‖ ^ 2) x v = Real.pi * ‖v‖ ^ 2 := by
  have h : (fun z : ComplexModel n => Real.pi * ‖z‖ ^ 2) =
      Real.pi • fun z => ‖ContinuousLinearMap.id ℂ (ComplexModel n) z‖ ^ 2 := by
    funext z; simp [smul_eq_mul]
  rw [h, leviForm_smul ((contDiff_normSq_clm _).contDiffAt.of_le two_le_infty),
    leviForm_normSq_clm]
  simp

/-! ### The general case -/

variable {m d : ℕ}

/-- **FPT `lem:local-critical-gain-extension`** in `ℂ^{m+d}`, `d ≥ 1`, with the constant
`e^{π(r' + r'')²} C_d`. -/
theorem localCriticalGain_add (hd : 1 ≤ d) {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'')
    (hr''e : r'' < Real.exp (-2))
    {O : Set (ComplexModel (m + d))} (hO : IsOpen O)
    (hDO : closure (localDom (m + d) m r' r'') ⊆ O)
    {p : ComplexModel (m + d) → EReal} (hp : PlurisubharmonicOn p O)
    {O' : Set (ComplexModel m)} (hO' : IsOpen O') (hBO' : closedBall 0 r' ⊆ O')
    {f : ComplexModel m → ℂ} (hf : DifferentiableOn ℂ f O')
    (hI : ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      multiplierWeight 1 (p (coordinateInclusion (m + d) m z')) ≠ ⊤) :
    ∃ F : ComplexModel (m + d) → ℂ, DifferentiableOn ℂ F (localDom (m + d) m r' r'') ∧
      (∀ z' ∈ ball (0 : ComplexModel m) r', F (coordinateInclusion (m + d) m z') = f z') ∧
      ∫⁻ z in localDom (m + d) m r' r'', ENNReal.ofReal (‖F z‖ ^ 2) * multiplierWeight 1 (p z) *
          criticalKernel (m + d) m z ≤
        ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) * localGainConst d *
          ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
            multiplierWeight 1 (p (coordinateInclusion (m + d) m z')) := by
  classical
  have hr''sq := sq_lt_exp_neg_four hr'' hr''e
  set D := localDom (m + d) m r' r'' with hDdef
  set ι := coordinateInclusion (m + d) m with hι
  set I := ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      multiplierWeight 1 (p (ι z')) with hIdef
  have hmn : m ≤ m + d := by omega
  have hDo : IsOpen D := isOpen_localDom m r' r''
  have hDconv : Convex ℝ D := convex_localDom m hr' hr''
  have hιD : ∀ w ∈ ball (0 : ComplexModel m) r', ι w ∈ D := fun w hw =>
    inclusion_mem_localDom hr'' hw hmn
  -- a convex neighbourhood
  obtain ⟨δ₀, hδ₀, hthick⟩ := (isCompact_closure_localDom (n := m + d) (m := m) hr' hr'').exists_cthickening_subset_open
    hO hDO
  set δ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set O₂ := thickening (2 * δ) D with hO₂def
  set Os := thickening δ D with hOsdef
  have hO₂O : O₂ ⊆ O := by
    refine (thickening_subset_cthickening _ _).trans ((cthickening_subset_of_subset _ subset_closure).trans ?_)
    rw [show 2 * δ = δ₀ by rw [hδdef]; ring]; exact hthick
  have hO₂o : IsOpen O₂ := isOpen_thickening
  have hO₂c : IsPreconnected O₂ := (hDconv.thickening _).isPreconnected
  have hpO₂ : PlurisubharmonicOn p O₂ := fun x hx => hp x (hO₂O hx)
  have hOso : IsOpen Os := isOpen_thickening
  have hDOs : closure D ⊆ Os := closure_subset_thickening hδ D
  have hDne : D.Nonempty := ⟨ι 0, hιD 0 (mem_ball_self hr')⟩
  have hinner : ∀ ε : ℝ, ε < δ → Os ⊆ innerDomain O₂ ε := by
    intro ε hε x hx
    refine ⟨δ, hε, fun y hy => ?_⟩
    rw [mem_thickening_iff_infDist_lt hDne] at hx ⊢
    have := infDist_le_infDist_add_dist (x := y) (y := x) (s := D)
    rw [mem_ball] at hy
    linarith
  by_cases hne : ∃ a ∈ O₂, p a ≠ ⊥
  swap
  · -- `p ≡ -∞` near `D̄`: then `f = 0` on `B'`
    push Not at hne
    have hf0 : ∀ w ∈ ball (0 : ComplexModel m) r', f w = 0 := by
      intro w hw
      by_contra hfw
      have hc : ContinuousAt (fun w => ‖f w‖ ^ 2) w :=
        ((hf.continuousOn.continuousAt (hO'.mem_nhds (hBO' (ball_subset_closedBall hw)))).norm).pow 2
      have hpos : 0 < ‖f w‖ ^ 2 := by have := norm_pos_iff.mpr hfw; positivity
      obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.mp
        ((hc.eventually (lt_mem_nhds (half_lt_self hpos))).and (isOpen_ball.mem_nhds hw))
      apply hI
      refine top_le_iff.mp ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ _ in ball w ρ, ⊤ := by
            rw [setLIntegral_const, ENNReal.top_mul (measure_ball_pos _ _ hρ).ne']
        _ ≤ ∫⁻ z' in ball w ρ, ENNReal.ofReal (‖f z'‖ ^ 2) * multiplierWeight 1 (p (ι z')) := by
            refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
            obtain ⟨h1, h2⟩ := hρb z hz
            have hb : p (ι z) = ⊥ := hne _ (self_subset_thickening (by positivity) D (hιD z h2))
            rw [hb, multiplierWeight_bot one_pos, ENNReal.mul_top (by
              rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith)]
        _ ≤ _ := lintegral_mono_set fun z hz => (hρb z hz).2
    refine ⟨fun _ => 0, differentiableOn_const _, fun w hw => (hf0 w hw).symm, ?_⟩
    simp
  -- the regularizations
  obtain ⟨a₀, ha₀O₂, ha₀⟩ := hne
  have hne' : ∃ a ∈ O₂, p a ≠ ⊥ := ⟨a₀, ha₀O₂, ha₀⟩
  set ρ := radialKernel (m + d)
  have hρ : IsRadialKernel ρ := isRadialKernel_radialKernel
  set εs : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hεsdef
  have hεs0 : ∀ j, 0 < εs j := fun j => div_pos hδ (by positivity)
  have hεsδ : ∀ j, εs j < δ := fun j => by
    rw [hεsdef, div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hεsanti : Antitone εs := fun i j hij => by
    simp only [hεsdef]
    apply div_le_div_of_nonneg_left hδ.le (by positivity)
    have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    linarith
  have hεslim : Tendsto εs atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set pj : ℕ → ComplexModel (m + d) → ℝ := fun j => radialRegularization ρ p (εs j) with hpjdef
  set Pj : ℕ → ComplexModel (m + d) → ℝ := fun j z => pj j z + Real.pi * ‖z‖ ^ 2 with hPjdef
  have hOsIn : ∀ j, Os ⊆ innerDomain O₂ (εs j) := fun j => hinner _ (hεsδ j)
  have hOsO₂ : Os ⊆ O₂ := thickening_mono (by linarith) D
  have hpjs : ∀ j, ContDiffOn ℝ ∞ (pj j) Os := fun j =>
    (contDiffOn_radialRegularization hρ hO₂o hO₂c hpO₂ hne' (hεs0 j)).mono (hOsIn j)
  have hsq : ContDiff ℝ ∞ (fun z : ComplexModel (m + d) => Real.pi * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hPs : ∀ j, ContDiffOn ℝ ∞ (Pj j) Os := fun j => (hpjs j).add hsq.contDiffOn
  have hPL : ∀ j, ∀ z ∈ Os, ∀ v : ComplexModel (m + d),
      Real.pi * ‖v‖ ^ 2 ≤ leviForm (Pj j) z v := by
    intro j z hz v
    have h1 := leviForm_radialRegularization_nonneg hρ hO₂o hO₂c hpO₂ hne' (hεs0 j) (hOsIn j hz) v
    have hc1 : ContDiffAt ℝ 2 (pj j) z :=
      ((hpjs j).contDiffAt (hOso.mem_nhds hz)).of_le two_le_infty
    have hc2 : ContDiffAt ℝ 2 (fun z : ComplexModel (m + d) => Real.pi * ‖z‖ ^ 2) z :=
      hsq.contDiffAt.of_le two_le_infty
    have h2 := leviForm_add hc1 hc2 v
    have : Pj j = pj j + fun z => Real.pi * ‖z‖ ^ 2 := rfl
    rw [this, h2, leviForm_pi_normSq]
    linarith
  have hle_p : ∀ j, ∀ x ∈ Os, p x ≤ (pj j x : EReal) := fun j x hx =>
    le_radialRegularization hρ hO₂o hO₂c hpO₂ hne' (hεs0 j) (hOsIn j hx)
  have hanti : ∀ x ∈ Os, Antitone fun j => pj j x := fun x hx =>
    antitone_radialRegularization_seq hρ hO₂o hO₂c hpO₂ hne' hεs0 hεsanti (hOsIn 0 hx)
  have hconvp : ∀ x ∈ Os, Tendsto (fun j => (pj j x : EReal)) atTop (𝓝 (p x)) := fun x hx =>
    tendsto_radialRegularization_seq hρ hO₂o hO₂c hpO₂ hne' hεs0 hεslim (hOsO₂ hx)
  have hDOs' : D ⊆ Os := subset_closure.trans hDOs
  have hιOs : ∀ w ∈ ball (0 : ComplexModel m) r', ι w ∈ Os := fun w hw => hDOs' (hιD w hw)
  -- the right sides
  have hexpP : ∀ j z, ENNReal.ofReal (Real.exp (-Pj j z)) =
      multiplierWeight 1 (pj j z : EReal) * ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2))) := by
    intro j z
    rw [multiplierWeight_coe, one_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp only [hPjdef]
    ring_nf
  have hIj : ∀ j, ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-Pj j (ι z'))) ≤ I := by
    intro j
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    gcongr
    calc ENNReal.ofReal (Real.exp (-Pj j (ι z))) ≤ ENNReal.ofReal (Real.exp (-pj j (ι z))) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          simp only [hPjdef]
          nlinarith [Real.pi_pos, sq_nonneg ‖ι z‖]
      _ ≤ multiplierWeight 1 (p (ι z)) := ofReal_exp_neg_le_multiplierWeight (hle_p j _ (hιOs z hz))
  choose F hF hFext hFest using fun j => localCriticalGain_smooth hd hr' hr'' hr''sq hOso hDOs
    (hPs j) (hPL j) hO' hBO' hf (ne_top_of_le_ne_top hI (hIj j))
  have hFest' : ∀ j, ∫⁻ z in D, ENNReal.ofReal (‖F j z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-Pj j z)) * criticalKernel (m + d) m z ≤ localGainConst d * I :=
    fun j => (hFest j).trans (by gcongr; exact hIj j)
  -- the uniform `L²` bound
  obtain ⟨B0, hB0'⟩ := (isCompact_closure_localDom (n := m + d) (m := m) hr' hr'').exists_bound_of_continuousOn
    ((hPs 0).continuousOn.mono hDOs)
  have hB0 : ∀ z ∈ D, Pj 0 z ≤ B0 := fun z hz =>
    (le_abs_self _).trans (by have := hB0' z (subset_closure hz); rwa [Real.norm_eq_abs] at this)
  have hR4 : ∀ z ∈ D, normalWeight (m + d) m z < Real.exp (-4) := fun z hz =>
    lt_trans hz.2 hr''sq
  have hU_ae := ae_restrict_localPunct (m := m) (d := d) (r' := r') (r'' := r'') hd
  have hKpos : ∀ z ∈ localPunct (m + d) m r' r'',
      0 < normalWeight (m + d) m z ^ d * Real.log (normalWeight (m + d) m z) ^ 2 ∧
      normalWeight (m + d) m z ^ d * Real.log (normalWeight (m + d) m z) ^ 2 ≤ 2 := by
    intro z hz
    have hR := hz.2.2
    have hR1 : normalWeight (m + d) m z < 1 :=
      (hR4 z (localPunct_subset m r' r'' hz)).trans (Real.exp_lt_one_iff.mpr (by norm_num))
    have hl : Real.log (normalWeight (m + d) m z) < 0 := Real.log_neg hR hR1
    exact ⟨mul_pos (pow_pos hR d) (by nlinarith), pow_mul_log_sq_le_two hR hR1.le hd⟩
  have hKeq : ∀ z, criticalKernel (m + d) m z =
      (ENNReal.ofReal (normalWeight (m + d) m z ^ d * Real.log (normalWeight (m + d) m z) ^ 2))⁻¹ :=
    fun z => by unfold criticalKernel; rw [show m + d - m = d by omega]
  have hK : ∀ z ∈ localPunct (m + d) m r' r'', (2 : ℝ≥0∞)⁻¹ ≤ criticalKernel (m + d) m z ∧
      criticalKernel (m + d) m z ≠ ⊤ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hKpos z hz
    rw [hKeq]
    refine ⟨ENNReal.inv_le_inv.mpr ?_, ENNReal.inv_ne_top.mpr (by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h1)⟩
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h2
      _ = 2 := ENNReal.ofReal_ofNat 2
  set BL : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp B0) * (localGainConst d * I) with hBLdef
  have hBL : BL < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (localGainConst_lt_top d) (lt_top_iff_ne_top.mpr hI))
  have hL2 : ∀ j, ∫⁻ z in D, ENNReal.ofReal (‖F j z‖ ^ 2) ≤ BL := by
    intro j
    have hae : ∀ᵐ z ∂(volume.restrict D), ENNReal.ofReal (‖F j z‖ ^ 2) ≤
        ENNReal.ofReal (2 * Real.exp B0) * (ENNReal.ofReal (‖F j z‖ ^ 2) *
          ENNReal.ofReal (Real.exp (-Pj j z)) * criticalKernel (m + d) m z) := by
      filter_upwards [hU_ae] with z hz
      have hzD := localPunct_subset m r' r'' hz
      obtain ⟨hK1, -⟩ := hK z hz
      have hPle : Pj j z ≤ B0 := by
        have h1 : pj j z ≤ pj 0 z := hanti z (hDOs' hzD) (Nat.zero_le j)
        have := hB0 z hzD
        simp only [hPjdef] at this ⊢
        linarith
      have hexp : ENNReal.ofReal (Real.exp (-B0)) ≤ ENNReal.ofReal (Real.exp (-Pj j z)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
      have hone : ENNReal.ofReal (2 * Real.exp B0) * ENNReal.ofReal (Real.exp (-B0)) * 2⁻¹ = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one, ENNReal.ofReal_ofNat, ENNReal.mul_inv_cancel (by norm_num)
          (by norm_num)]
      calc ENNReal.ofReal (‖F j z‖ ^ 2)
          = ENNReal.ofReal (2 * Real.exp B0) * ENNReal.ofReal (Real.exp (-B0)) * 2⁻¹ *
              ENNReal.ofReal (‖F j z‖ ^ 2) := by rw [hone, one_mul]
        _ ≤ ENNReal.ofReal (2 * Real.exp B0) * ENNReal.ofReal (Real.exp (-Pj j z)) *
              criticalKernel (m + d) m z * ENNReal.ofReal (‖F j z‖ ^ 2) := by gcongr
        _ = _ := by ring
    calc ∫⁻ z in D, ENNReal.ofReal (‖F j z‖ ^ 2)
        ≤ ∫⁻ z in D, ENNReal.ofReal (2 * Real.exp B0) * (ENNReal.ofReal (‖F j z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-Pj j z)) * criticalKernel (m + d) m z) := lintegral_mono_ae hae
      _ = ENNReal.ofReal (2 * Real.exp B0) * ∫⁻ z in D, ENNReal.ofReal (‖F j z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-Pj j z)) * criticalKernel (m + d) m z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ BL := by rw [hBLdef]; gcongr; exact hFest' j
  -- Montel
  obtain ⟨ψ, Flim, hψ, hFlim, hconv⟩ := exists_subseq_of_l2_bounded hDo F hF hBL hL2
  refine ⟨Flim, hFlim, fun z' hz' => ?_, ?_⟩
  · have h1 : Tendsto (fun k => F (ψ k) (ι z')) atTop (𝓝 (Flim (ι z'))) :=
      hconv.tendsto_at (hιD z' hz')
    have h2 : (fun k => F (ψ k) (ι z')) = fun _ => f z' := funext fun k => hFext (ψ k) z' hz'
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · -- Fatou
    set E0 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) with hE0
    set gk : ℕ → ComplexModel (m + d) → ℝ≥0∞ := fun k z => ENNReal.ofReal (‖F (ψ k) z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-Pj (ψ k) z)) * criticalKernel (m + d) m z with hgkdef
    set tgt : ComplexModel (m + d) → ℝ≥0∞ := fun z => ENNReal.ofReal (‖Flim z‖ ^ 2) *
      (multiplierWeight 1 (p z) * ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2)))) *
        criticalKernel (m + d) m z with htgtdef
    have hKm : Measurable (criticalKernel (m + d) m) := by
      unfold criticalKernel
      exact (ENNReal.measurable_ofReal.comp (((continuous_normalWeight m).measurable.pow_const _).mul
        ((Real.measurable_log.comp (continuous_normalWeight m).measurable).pow_const 2))).inv
    have hmeas : ∀ k, AEMeasurable (gk k) (volume.restrict D) := by
      intro k
      refine (AEMeasurable.mul ?_ ?_).mul hKm.aemeasurable
      · exact ENNReal.measurable_ofReal.comp_aemeasurable
          ((((hF (ψ k)).continuousOn).norm.pow 2).aemeasurable hDo.measurableSet)
      · exact ENNReal.measurable_ofReal.comp_aemeasurable
          ((Real.continuous_exp.comp_continuousOn
            ((hPs (ψ k)).continuousOn.mono hDOs').neg).aemeasurable hDo.measurableSet)
    have hpt : ∀ z ∈ localPunct (m + d) m r' r'', tgt z ≤ liminf (fun k => gk k z) atTop := by
      intro z hz
      have hzD := localPunct_subset m r' r'' hz
      by_cases h0 : ENNReal.ofReal (‖Flim z‖ ^ 2) = 0
      · simp only [htgtdef, h0, zero_mul]; exact bot_le
      · refine le_of_eq (Tendsto.liminf_eq ?_).symm
        have ha : Tendsto (fun k => ENNReal.ofReal (‖F (ψ k) z‖ ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (‖Flim z‖ ^ 2))) :=
          (ENNReal.continuous_ofReal.tendsto _).comp ((hconv.tendsto_at hzD).norm.pow 2)
        have hW1 : Tendsto (fun k => multiplierWeight 1 (pj (ψ k) z : EReal)) atTop
            (𝓝 (multiplierWeight 1 (p z))) :=
          ((continuous_multiplierWeight one_pos).tendsto _).comp
            ((hconvp z (hDOs' hzD)).comp hψ.tendsto_atTop)
        have hW : Tendsto (fun k => ENNReal.ofReal (Real.exp (-Pj (ψ k) z))) atTop
            (𝓝 (multiplierWeight 1 (p z) * ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2))))) := by
          simp only [hexpP]
          exact ENNReal.Tendsto.mul_const hW1 (Or.inr ENNReal.ofReal_ne_top)
        exact ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul ha (Or.inl h0) hW
          (Or.inr ENNReal.ofReal_ne_top)) (Or.inr (hK z hz).2)
    have hfat : ∫⁻ z in D, tgt z ≤ localGainConst d * I := by
      calc ∫⁻ z in D, tgt z ≤ ∫⁻ z in D, liminf (fun k => gk k z) atTop :=
            lintegral_mono_ae (hU_ae.mono hpt)
        _ ≤ liminf (fun k => ∫⁻ z in D, gk k z) atTop :=
            lintegral_liminf_le' (μ := volume.restrict D) (u := atTop) hmeas
        _ ≤ localGainConst d * I :=
            liminf_le_of_frequently_le' (Frequently.of_forall fun k => hFest' (ψ k))
    have hpt2 : ∀ z ∈ D, ENNReal.ofReal (‖Flim z‖ ^ 2) * multiplierWeight 1 (p z) *
        criticalKernel (m + d) m z ≤ E0 * tgt z := by
      intro z hz
      have hzn : ‖z‖ < r' + r'' := mem_ball_zero_iff.mp (localDom_subset_ball hr' hr'' hz)
      have hone : 1 ≤ E0 * ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2))) := by
        rw [hE0, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
        have : ‖z‖ ^ 2 ≤ (r' + r'') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn.le 2
        nlinarith [Real.pi_pos]
      calc ENNReal.ofReal (‖Flim z‖ ^ 2) * multiplierWeight 1 (p z) * criticalKernel (m + d) m z
          = 1 * (ENNReal.ofReal (‖Flim z‖ ^ 2) * multiplierWeight 1 (p z) *
              criticalKernel (m + d) m z) := (one_mul _).symm
        _ ≤ (E0 * ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2)))) *
              (ENNReal.ofReal (‖Flim z‖ ^ 2) * multiplierWeight 1 (p z) *
                criticalKernel (m + d) m z) := by gcongr
        _ = E0 * tgt z := by simp only [htgtdef]; ring
    calc ∫⁻ z in D, ENNReal.ofReal (‖Flim z‖ ^ 2) * multiplierWeight 1 (p z) *
          criticalKernel (m + d) m z
        ≤ ∫⁻ z in D, E0 * tgt z := setLIntegral_mono' hDo.measurableSet hpt2
      _ = E0 * ∫⁻ z in D, tgt z := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ E0 * (localGainConst d * I) := by gcongr
      _ = E0 * localGainConst d * I := (mul_assoc _ _ _).symm

/-! ### The statement -/

variable (n m) in
/-- **FPT `lem:local-critical-gain-extension`** (statement): for `m < n` (`q = n - m ≥ 1`) and
radii `r' > 0`, `0 < r'' < e^{-2}` there is `C > 0` such that for every `p` plurisubharmonic on an
open neighbourhood `O` of `D̄` and every `f` holomorphic on an open neighbourhood `O'` of
`B̄(0, r')` with `∫_{B'} |f|² e^{-p(z', 0)} < ∞` there is `F` holomorphic on `D` with
`F(z', 0) = f(z')` and `∫_D |F|² e^{-p} |w|^{-2q} (log |w|²)^{-2} ≤ C ∫_{B'} |f|² e^{-p(z', 0)}`. -/
def LocalCriticalGainExtensionStatement : Prop :=
  m < n → ∀ r' r'' : ℝ, 0 < r' → 0 < r'' → r'' < Real.exp (-2) →
  ∃ C : ℝ, 0 < C ∧
  ∀ (O : Set (ComplexModel n)), IsOpen O → closure (localDom n m r' r'') ⊆ O →
  ∀ p : ComplexModel n → EReal, PlurisubharmonicOn p O →
  ∀ (O' : Set (ComplexModel m)), IsOpen O' → closedBall 0 r' ⊆ O' →
  ∀ f : ComplexModel m → ℂ, DifferentiableOn ℂ f O' →
    ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      multiplierWeight 1 (p (coordinateInclusion n m z')) ≠ ⊤ →
  ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F (localDom n m r' r'') ∧
    (∀ z' ∈ ball (0 : ComplexModel m) r', F (coordinateInclusion n m z') = f z') ∧
    ∫⁻ z in localDom n m r' r'', ENNReal.ofReal (‖F z‖ ^ 2) * multiplierWeight 1 (p z) *
        criticalKernel n m z ≤
      ENNReal.ofReal C * ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
        multiplierWeight 1 (p (coordinateInclusion n m z'))

/-- **FPT `lem:local-critical-gain-extension`** holds. -/
theorem localCriticalGainExtension (n m : ℕ) : LocalCriticalGainExtensionStatement n m := by
  intro hmn r' r'' hr' hr'' hr''e
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  have hd : 1 ≤ d := by omega
  have hfin : ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) * localGainConst d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localGainConst_lt_top d).ne
  refine ⟨(ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) * localGainConst d).toReal + 1,
    by positivity, fun O hO hDO p hp O' hO' hBO' f hf hI => ?_⟩
  obtain ⟨F, hF, hext, hest⟩ := localCriticalGain_add hd hr' hr'' hr''e hO hDO hp hO' hBO' hf hI
  refine ⟨F, hF, hext, hest.trans ?_⟩
  gcongr
  calc ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) * localGainConst d
      = ENNReal.ofReal (ENNReal.ofReal (Real.exp (Real.pi * (r' + r'') ^ 2)) *
          localGainConst d).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end SGPT.Trace.OTExt2
