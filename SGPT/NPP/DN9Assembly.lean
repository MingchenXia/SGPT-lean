import SGPT.NPP.DN9Smooth
import SGPT.NPP.DN9Alg
import SGPT.NPP.DN10Clauses
import SGPT.NPP.DN10QPart
import SGPT.NPP.DN11Joint

/-!
# The chart-level joint estimate (`SGPT.NPP.DN5.LocalJointEstimate`)

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 2–6 in one chart).

`localJointEstimate : SGPT.NPP.DN5.LocalJointEstimate N`.  With `p = u + q` (plurisubharmonic,
nondegenerate) and `H = S_u + K₀ t²`:

* near `(z, |w|)`, `S_u = S_p - S_q` (lane DN11, splitting), so
  `L[H(·, |·|) + q] = L[S_p(·, |·|)] - L[S_q(·, |·|) - q] + K₀ |η|²`
  and `t ∂_t H = t ∂_t S_p - t ∂_t S_q + 2 K₀ t²`;
* `L[S_p(·, |·|)] ≥ -A₁ |w|² |v|² λ_p(2|w|) - A₂ (|v|² + |v||η|) λ_p(|w|)` (the estimate for
  smooth potentials, `smoothJointEstimate`, passed to `p` by lane DN11, `jointBound_of_smooth`);
* `L[S_q(·, |·|) - q] ≤ C_q(|w|²|v|² + |w||v||η| + |η|²)`, `|t ∂_t S_q| ≤ C_q t²`;
* `H ≥ u`, convexity, `t ∂_t H ≤ C_u`, and the improved slope bound;
* the scalar bookkeeping is `SGPT.NPP.DN9.clause3_alg` / `clause4_alg` with `K₀ ≥ C_q`
  absorbing `|η|²` and `|v|² ≤ α(v, iv)/m` on `K`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN9

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.NPP.DN5 SGPT.Analysis.KahlerNormal

variable {N : ℕ}

/-- The derivative of the corrected smoothing from the splitting. -/
theorem hasDerivAt_corrected {SP Sq Su : ℝ → ℝ} {t K₀ : ℝ} (hP : DifferentiableAt ℝ SP t)
    (hq : DifferentiableAt ℝ Sq t) (hev : Su =ᶠ[𝓝 t] fun t' => SP t' - Sq t') :
    HasDerivAt (fun t' => Su t' + K₀ * t' ^ 2) (deriv SP t - deriv Sq t + 2 * K₀ * t) t := by
  have h := (hP.hasDerivAt.sub hq.hasDerivAt).add ((hasDerivAt_pow 2 t).const_mul K₀)
  have h' := h.congr_of_eventuallyEq (f₁ := fun t' => Su t' + K₀ * t' ^ 2)
    (hev.mono fun t' ht' => by simp only [Pi.add_apply, Pi.sub_apply, ht'])
  refine h'.congr_deriv ?_
  norm_num
  ring

/-- Levi form of a combination `f₁ - f₂ + K₀ ‖·.2‖²`. -/
theorem leviForm_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G f₁ f₂ : E × ℂ → ℝ} {x : E × ℂ} (K₀ : ℝ)
    (hG : G =ᶠ[𝓝 x] fun y => f₁ y - f₂ y + K₀ * ‖y.2‖ ^ 2)
    (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) (a : E × ℂ) :
    leviForm G x a = leviForm f₁ x a - leviForm f₂ x a + K₀ * ‖a.2‖ ^ 2 := by
  have hg : ContDiffAt ℝ 2 (fun y : E × ℂ => ‖y.2‖ ^ 2) x :=
    ((contDiff_norm_sq ℂ).comp contDiff_snd).contDiffAt
  have e : (fun y : E × ℂ => f₁ y - f₂ y + K₀ * ‖y.2‖ ^ 2) =
      (f₁ + -f₂) + K₀ • fun y : E × ℂ => ‖y.2‖ ^ 2 := by
    funext y; simp [sub_eq_add_neg]
  rw [leviForm_congr hG, e,
    leviForm_add (u := f₁ + -f₂) (v := K₀ • fun y : E × ℂ => ‖y.2‖ ^ 2) (h₁.add h₂.neg)
      (hg.const_smul K₀),
    leviForm_add (u := f₁) (v := -f₂) h₁ h₂.neg, leviForm_neg, leviForm_smul hg]
  obtain ⟨v, η⟩ := a
  obtain ⟨z, w⟩ := x
  rw [leviForm_normSq_snd]
  ring

/-- `(z, w) ↦ S(z, |w|)` is `C²` near `w ≠ 0` when `S` is `C²` near `(z, |w|)`. -/
theorem contDiffAt_comp_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E × ℝ → ℝ} {z : E} {w : ℂ} (hS : ContDiffAt ℝ 2 S (z, ‖w‖)) (hw : w ≠ 0) :
    ContDiffAt ℝ 2 (fun x : E × ℂ => S (x.1, ‖x.2‖)) (z, w) := by
  have hin : ContDiffAt ℝ 2 (fun x : E × ℂ => ((x.1, ‖x.2‖) : E × ℝ)) (z, w) :=
    contDiffAt_fst.prodMk ((contDiffAt_norm ℂ hw).comp (z, w) contDiffAt_snd)
  exact hS.comp (z, w) hin

/-- Slices of a function `C¹` on a product of open sets are differentiable. -/
theorem differentiableAt_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : E × ℝ → ℝ} {V : Set E} {r : ℝ} (hV : IsOpen V) {k : WithTop ℕ∞} (hk : k ≠ 0)
    (hS : ContDiffOn ℝ k S (V ×ˢ Ioo 0 r)) {z : E} (hz : z ∈ V) {t : ℝ} (ht : t ∈ Ioo 0 r) :
    DifferentiableAt ℝ (fun t' => S (z, t')) t := by
  have h := (hS.contDiffAt (prod_mem_nhds (hV.mem_nhds hz) (isOpen_Ioo.mem_nhds ht))).differentiableAt
    hk
  exact h.comp t ((differentiableAt_const z).prodMk differentiableAt_id)

/-- **The chart-level joint estimate** (FPT `lem:chern-joint-smoothing`, Steps 2–6, in one
chart): `SGPT.NPP.DN5.LocalJointEstimate`. -/
theorem localJointEstimate : DN5.LocalJointEstimate N := by
  intro Φ O α W K K' R q u hΦ hW hK hKK' hK'W hR hO hα _ hαpos hq hpsh hne
  have hKW : K ⊆ W := fun z hz => hK'W (interior_subset (hKK' hz))
  have hKO : ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O := fun z hz =>
    hO (mk_mem_prod (interior_subset (hKK' hz)) (mem_closedBall_self hR.le))
  have hD : ChartData Φ O α W K := ⟨hΦ, hW, hα, hαpos, hK, hKW, hKO⟩
  -- the plurisubharmonic potential `p = u + q`
  obtain ⟨p, hpdef⟩ : ∃ p : ComplexModel N → EReal, p = fun y => u y + (q y : EReal) :=
    ⟨_, rfl⟩
  have hpp : PlurisubharmonicOn p W := by rw [hpdef]; exact hpsh
  have hpne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, p y ≠ ⊥ := by
    intro x hx V hV hxV
    obtain ⟨y, hyV, hy⟩ := hne x hx V hV hxV
    refine ⟨y, hyV, ?_⟩
    rw [hpdef]
    exact EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩
  -- the inputs of lanes DN10, DN11 and DN9
  obtain ⟨rc, K₀', hrc, hK₀', hcl⟩ := DN10.clauseEstimate Φ O α W K q u hD hq hpsh hne
  obtain ⟨Vq, rq, Cq, hVq, hKVq, hrq, hCq, hSq, hqb⟩ := DN10.qPartEstimate Φ O α W K q hD hq
  obtain ⟨Vp, rp, hVp, hKVp, hrp, hSp⟩ :=
    DN11.contDiffOn_localSmoothing_toReal hΦ hW hα hαpos hK hKW hKO hW hKW hpp hpne
  obtain ⟨Vs, rs, hVs, hKVs, hrs, hsplit⟩ :=
    DN11.localSmoothing_toReal_split hΦ hW hα hαpos hK hKW hKO hW hKW hpp hpne
      (g := q) hq.continuousOn (f := u) (fun y _ => by rw [hpdef])
  obtain ⟨r₁s, c, A₁, A₂, hr₁s, hc, hA₁, hA₂, hsm⟩ := smoothJointEstimate Φ O α W K hD
  obtain ⟨r₂, hr₂, -, hP⟩ := DN11.jointBound_of_smooth hΦ hW hα hαpos hK hKW hKO hW hKW hpp hpne
    (fun _ w v η a b => -(A₁ * ‖w‖ ^ 2 * ‖v‖ ^ 2 * (2 * ‖w‖ * b)) -
      A₂ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖) * (‖w‖ * a))
    (fun _ _ _ _ => by fun_prop) hr₁s
    (fun z hz w hw0 hw p' hp' hpsh' v η => hsm z hz w hw0 hw p' (hp'.of_le (by norm_cast)) hpsh' v η)
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul hα.continuousOn
    (fun z hz => (hαpos z hz).2) hK hKW
  -- the constants
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : ℝ, K₀ = max K₀' Cq := ⟨_, rfl⟩
  have hK₀q : Cq ≤ K₀ := by rw [hK₀def]; exact le_max_right _ _
  have hK₀K : K₀' ≤ K₀ := by rw [hK₀def]; exact le_max_left _ _
  have hK₀0 : 0 ≤ K₀ := hK₀'.trans hK₀K
  obtain ⟨Cu, C', C₁, hCu, hC', hC₁, hclz⟩ := hcl K₀ hK₀K
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℝ, r₀ = min (min (min rc rq) (min rp rs)) r₂ := ⟨_, rfl⟩
  have hr₀ : 0 < r₀ := by rw [hr₀def]; exact lt_min (lt_min (lt_min hrc hrq) (lt_min hrp hrs)) hr₂
  have hr₀c : r₀ ≤ rc := by
    rw [hr₀def]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₀q : r₀ ≤ rq := by
    rw [hr₀def]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr₀p : r₀ ≤ rp := by
    rw [hr₀def]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₀s : r₀ ≤ rs := by
    rw [hr₀def]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr₀2 : r₀ ≤ r₂ := by rw [hr₀def]; exact min_le_right _ _
  obtain ⟨rf, hrfdef⟩ : ∃ rf : ℝ, rf = min (r₀ / 2) (1 / 2) := ⟨_, rfl⟩
  have hrf : 0 < rf := by rw [hrfdef]; exact lt_min (half_pos hr₀) (by norm_num)
  have hrfr : rf ≤ r₀ / 2 := by rw [hrfdef]; exact min_le_left _ _
  have hrf1 : rf ≤ 1 / 2 := by rw [hrfdef]; exact min_le_right _ _
  have hrfc : rf ≤ rc := hrfr.trans ((half_le_self hr₀.le).trans hr₀c)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max ((A₁ * (Cu + 4 * Cq) + A₂ * Cq + Cq) / m)
      ((A₂ * (Cu + Cq) + Cq) / Real.sqrt m))
      (max ((A₁ * (C' + 4 * Cq) + A₂ * Cq + Cq) / m) ((A₂ * (C' + Cq) + Cq) / Real.sqrt m)) :=
    ⟨_, rfl⟩
  have hCa : (A₁ * (Cu + 4 * Cq) + A₂ * Cq + Cq) / m ≤ C := by
    rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCb : (A₂ * (Cu + Cq) + Cq) / Real.sqrt m ≤ C := by
    rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCc : (A₁ * (C' + 4 * Cq) + A₂ * Cq + Cq) / m ≤ C := by
    rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hCd : (A₂ * (C' + Cq) + Cq) / Real.sqrt m ≤ C := by
    rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  have hC0 : 0 ≤ C := (div_nonneg (by positivity) hm.le).trans hCa
  clear hK₀def hr₀def hrfdef hCdef
  refine ⟨rf, K₀, A₂ / m, C, C₁, hrf, hK₀0, div_nonneg hA₂ hm.le, hC0, by linarith,
    fun z hz => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := hclz z hz
  obtain ⟨q1, q2⟩ := hqb z hz
  -- the slope relation `t ∂_t H = t ∂_t S_p - t ∂_t S_q + 2 K₀ t²` for `0 < t < r₀`
  have hslope : ∀ t : ℝ, 0 < t → t < r₀ →
      DifferentiableAt ℝ (localCorrected Φ α u K₀ z) t ∧
      t * deriv (localCorrected Φ α u K₀ z) t =
        t * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) t -
          t * deriv (localSmoothing Φ α q z) t + 2 * K₀ * t ^ 2 := by
    intro t ht htr
    have hP' : DifferentiableAt ℝ (localSmoothing Φ α (fun y => (p y).toReal) z) t :=
      differentiableAt_slice (S := fun x : ComplexModel N × ℝ =>
        localSmoothing Φ α (fun y => (p y).toReal) x.1 x.2) hVp (by simp) hSp (hKVp hz)
        ⟨ht, htr.trans_le hr₀p⟩
    have hq' : DifferentiableAt ℝ (localSmoothing Φ α q z) t :=
      differentiableAt_slice (S := fun x : ComplexModel N × ℝ => localSmoothing Φ α q x.1 x.2)
        hVq (by simp) hSq (hKVq hz) ⟨ht, htr.trans_le hr₀q⟩
    have hev : localSmoothing Φ α (fun y => (u y).toReal) z =ᶠ[𝓝 t] fun t' =>
        localSmoothing Φ α (fun y => (p y).toReal) z t' - localSmoothing Φ α q z t' := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo 0 rs from ⟨ht, htr.trans_le hr₀s⟩)]
        with t' ht'
      rw [hsplit z (hKVs hz) t' ht']
      ring
    have hd := hasDerivAt_corrected (K₀ := K₀) hP' hq' hev
    refine ⟨hd.differentiableAt, ?_⟩
    have e : localCorrected Φ α u K₀ z =
        fun t' => localSmoothing Φ α (fun y => (u y).toReal) z t' + K₀ * t' ^ 2 := rfl
    rw [e, hd.deriv]
    ring
  -- `λ_H ≥ 0` from the monotonicity clause
  have hLHnn : ∀ t : ℝ, 0 < t → t < rf → 0 ≤ t * deriv (localCorrected Φ α u K₀ z) t := by
    intro t ht htf
    have htr : t < r₀ := by linarith
    have hHd := (hslope t ht htr).1
    have hlog : Real.log t < Real.log rc := Real.log_lt_log ht (by linarith)
    have h := (c2 (Real.log t) hlog).1
    have hd : HasDerivAt (fun s => localCorrected Φ α u K₀ z (Real.exp s))
        (deriv (localCorrected Φ α u K₀ z) t * t) (Real.log t) := by
      have hHd' : DifferentiableAt ℝ (localCorrected Φ α u K₀ z) (Real.exp (Real.log t)) := by
        rw [Real.exp_log ht]; exact hHd
      have := hHd'.hasDerivAt.comp (Real.log t) (Real.hasDerivAt_exp (Real.log t))
      rw [Real.exp_log ht] at this
      exact this
    rw [hd.deriv] at h
    linarith
  -- the Levi form decomposition at `(z, w)`, `0 < |w| < r₀`
  have hLevi : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₀ → ∀ (v : ComplexModel N) (η : ℂ),
      leviForm (fun x : ComplexModel N × ℂ => localCorrected Φ α u K₀ x.1 ‖x.2‖ + q x.1) (z, w)
        (v, η) =
      leviForm (fun x : ComplexModel N × ℂ =>
          localSmoothing Φ α (fun y => (p y).toReal) x.1 ‖x.2‖) (z, w) (v, η) -
        leviForm (fun x : ComplexModel N × ℂ => localSmoothing Φ α q x.1 ‖x.2‖ - q x.1) (z, w)
          (v, η) + K₀ * ‖η‖ ^ 2 := by
    intro w hw0 hwr v η
    have hw0' : w ≠ 0 := norm_pos_iff.mp hw0
    have hnhd : Vs ×ˢ ((fun y : ℂ => ‖y‖) ⁻¹' Ioo 0 rs) ∈ 𝓝 (z, w) :=
      prod_mem_nhds (hVs.mem_nhds (hKVs hz))
        ((isOpen_Ioo.preimage continuous_norm).mem_nhds ⟨hw0, hwr.trans_le hr₀s⟩)
    have hG : (fun x : ComplexModel N × ℂ => localCorrected Φ α u K₀ x.1 ‖x.2‖ + q x.1) =ᶠ[𝓝 (z, w)]
        fun x => localSmoothing Φ α (fun y => (p y).toReal) x.1 ‖x.2‖ -
          (localSmoothing Φ α q x.1 ‖x.2‖ - q x.1) + K₀ * ‖x.2‖ ^ 2 := by
      filter_upwards [hnhd] with x hx
      have hs := hsplit x.1 hx.1 ‖x.2‖ hx.2
      change localSmoothing Φ α (fun y => (u y).toReal) x.1 ‖x.2‖ + K₀ * ‖x.2‖ ^ 2 + q x.1 = _
      rw [hs]
      ring
    have h₁ : ContDiffAt ℝ 2 (fun x : ComplexModel N × ℂ =>
        localSmoothing Φ α (fun y => (p y).toReal) x.1 ‖x.2‖) (z, w) := by
      have hS : ContDiffAt ℝ 2 (fun x : ComplexModel N × ℝ =>
          localSmoothing Φ α (fun y => (p y).toReal) x.1 x.2) (z, ‖w‖) :=
        (hSp.contDiffAt (prod_mem_nhds (hVp.mem_nhds (hKVp hz))
          (isOpen_Ioo.mem_nhds ⟨hw0, hwr.trans_le hr₀p⟩))).of_le (by norm_cast)
      exact contDiffAt_comp_norm (S := fun x : ComplexModel N × ℝ =>
        localSmoothing Φ α (fun y => (p y).toReal) x.1 x.2) hS hw0'
    have h₂ : ContDiffAt ℝ 2 (fun x : ComplexModel N × ℂ =>
        localSmoothing Φ α q x.1 ‖x.2‖ - q x.1) (z, w) := by
      have hS := hSq.contDiffAt (prod_mem_nhds (hVq.mem_nhds (hKVq hz))
        (isOpen_Ioo.mem_nhds ⟨hw0, hwr.trans_le hr₀q⟩))
      have hq2 : ContDiffAt ℝ 2 (fun x : ComplexModel N × ℂ => q x.1) (z, w) :=
        ((hq.contDiffAt (hW.mem_nhds (hKW hz))).of_le (by norm_cast)).comp (z, w) contDiffAt_fst
      exact (contDiffAt_comp_norm (S := fun x : ComplexModel N × ℝ =>
        localSmoothing Φ α q x.1 x.2) hS hw0').sub hq2
    exact leviForm_comb K₀ hG h₁ h₂ (v, η)
  -- the slope bounds at `t = |w|`, `2|w|`
  have hX : ∀ t : ℝ, 0 < t → t < r₀ →
      t * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) t ≤
        t * deriv (localCorrected Φ α u K₀ z) t + Cq * t ^ 2 := by
    intro t ht htr
    have h := (hslope t ht htr).2
    have hq1 := (abs_le.mp (q1 t ht (htr.trans_le hr₀q))).2
    have : 0 ≤ 2 * K₀ * t ^ 2 := by positivity
    linarith
  refine ⟨fun t ht htf => c1 t ht (htf.trans_le hrfc), fun s hs => c2 s
    (hs.trans_le (Real.log_le_log hrf hrfc)), ?_, ?_⟩
  · -- the initial joint bound
    intro w hw0 hwf v η
    have hwrf2 : ‖w‖ < r₀ / 2 := hwf.trans_le hrfr
    have hwr : ‖w‖ < r₀ := hwrf2.trans (half_lt_self hr₀)
    have h2wr : 2 * ‖w‖ < r₀ := by
      have := mul_lt_mul_of_pos_left hwrf2 two_pos
      rwa [mul_div_cancel₀ _ two_ne_zero] at this
    have hw1 : ‖w‖ ≤ 1 := (hwf.trans_le hrf1).le.trans (by norm_num)
    have hα' := hmK z hz v
    have hL1 := hP z hz w hw0 (hwr.trans_le hr₀2) v η
    have hL2 := q2 w hw0 (hwr.trans_le hr₀q) v η
    have h1 : 2 * ‖w‖ * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) (2 * ‖w‖) ≤
        Cu + 4 * Cq * ‖w‖ ^ 2 := by
      have e : Cq * (2 * ‖w‖) ^ 2 = 4 * Cq * ‖w‖ ^ 2 := by ring
      calc _ ≤ 2 * ‖w‖ * deriv (localCorrected Φ α u K₀ z) (2 * ‖w‖) + Cq * (2 * ‖w‖) ^ 2 :=
            hX (2 * ‖w‖) (mul_pos two_pos hw0) h2wr
        _ ≤ Cu + Cq * (2 * ‖w‖) ^ 2 :=
            add_le_add (c3 (2 * ‖w‖) (mul_pos two_pos hw0) (h2wr.trans_le hr₀c)) le_rfl
        _ = _ := by rw [e]
    have h2 := hX ‖w‖ hw0 hwr
    have h3 : ‖w‖ * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) ‖w‖ ≤ Cu + Cq := by
      have hCqa : Cq * ‖w‖ ^ 2 ≤ Cq :=
        mul_le_of_le_one_right hCq (pow_le_one₀ (norm_nonneg w) hw1)
      exact h2.trans (add_le_add (c3 ‖w‖ hw0 (hwr.trans_le hr₀c)) hCqa)
    rw [hLevi w hw0 hwr v η]
    exact clause3_alg hA₁ hA₂ hCq hCu hK₀q hm (norm_nonneg w) hw1 (norm_nonneg v)
      (norm_nonneg η) hL1 hL2 h1 h2 h3 (hLHnn ‖w‖ hw0 hwf) hα' hCa hCb
  · -- the improved joint bound
    intro a L r hua hL hr hC₁r hlin w hw v η
    have hc4 := c4 a L r hua hL hr (hC₁r.trans_le hrfc) hlin
    clear hlin hua
    have hC₁1 : 1 < C₁ := lt_of_lt_of_le one_lt_two hC₁
    have hrf' : r < rf := calc
      r = 1 * r := (one_mul r).symm
      _ < C₁ * r := mul_lt_mul_of_pos_right hC₁1 hr
      _ < rf := hC₁r
    subst hw
    have hw0 : 0 < ‖w‖ := hr
    have hwrf2 : ‖w‖ < r₀ / 2 := hrf'.trans_le hrfr
    have hwr : ‖w‖ < r₀ := hwrf2.trans (half_lt_self hr₀)
    have h2wr : 2 * ‖w‖ < r₀ := by
      have := mul_lt_mul_of_pos_left hwrf2 two_pos
      rwa [mul_div_cancel₀ _ two_ne_zero] at this
    have hw1 : ‖w‖ ≤ 1 := (hrf'.trans_le hrf1).le.trans (by norm_num)
    have hα' := hmK z hz v
    have hL1 := hP z hz w hw0 (hwr.trans_le hr₀2) v η
    have hL2 := q2 w hw0 (hwr.trans_le hr₀q) v η
    have h1 : 2 * ‖w‖ * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) (2 * ‖w‖) ≤
        C' * (1 + L) * ‖w‖ + 4 * Cq * ‖w‖ ^ 2 := by
      have e : Cq * (2 * ‖w‖) ^ 2 = 4 * Cq * ‖w‖ ^ 2 := by ring
      calc _ ≤ 2 * ‖w‖ * deriv (localCorrected Φ α u K₀ z) (2 * ‖w‖) + Cq * (2 * ‖w‖) ^ 2 :=
            hX (2 * ‖w‖) (mul_pos two_pos hw0) h2wr
        _ ≤ C' * (1 + L) * ‖w‖ + Cq * (2 * ‖w‖) ^ 2 :=
            add_le_add (hc4 (2 * ‖w‖) (mul_pos two_pos hw0) le_rfl) le_rfl
        _ = _ := by rw [e]
    have h2 := hX ‖w‖ hw0 hwr
    have h3 : ‖w‖ * deriv (localSmoothing Φ α (fun y => (p y).toReal) z) ‖w‖ ≤
        C' * (1 + L) * ‖w‖ + Cq * ‖w‖ ^ 2 :=
      h2.trans (add_le_add (hc4 ‖w‖ hw0 (le_mul_of_one_le_left hw0.le one_le_two)) le_rfl)
    rw [hLevi w hw0 hwr v η]
    exact clause4_alg hA₁ hA₂ hCq hC' hK₀q hm (norm_nonneg w) hw1 (norm_nonneg v)
      (norm_nonneg η) hL hL1 hL2 h1 h2 h3 (hLHnn ‖w‖ hw0 hrf') hα' hCc hCd

end SGPT.NPP.DN9
