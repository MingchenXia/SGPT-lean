import SGPT.Okounkov.TranscendentalWNRegBeta

/-!
# Berman's Laplacian estimate for the β-family, uniformly in β

Package WN-REG (`claude-tok-wn-reg`, node `tok-wn-reg:beta-laplacian`), the analytic core of
Berman's Laplacian estimate for envelopes (`tok-wn:berman`): R. Berman, *From Monge–Ampère
equations to envelopes and geodesic rays in the zero temperature limit*, Math. Z. 291 (2019),
arXiv:1307.3008v3, Proposition 2.5 and its precise form (2.11); WN21 Theorem 2.5.

Let `Y` be a compact connected complex manifold of dimension `N > 0` with a Kähler background
`A`.  There are constants `a ≥ 0`, `Λ > 0`, `β₀ > 0`, depending only on `(Y, A)`, such that for
every `β ≥ β₀`, every chart-smooth `F` with `ddᶜF ≤ S·A` on complex lines (`S ≥ 0`), every
β-solution `u` of `(A + ddᶜu)^N = e^{β(u - F)} A^N` and every lower bound `m ≤ u`,

`A + ddᶜu ≤ (1 + S) Λ e^{a(u(x) - m)} · A`   on every complex line at every point `x`

(`betaSolution_line_le`).  The bound is linear in `S` (the upper bound of `ddᶜF`), as WN21 §7
needs (there `S ≍ e^k`), and its dependence on the point is through `u(x) - m` only.

## Proof (Błocki's form of the Aubin–Yau `C²` estimate, adapted to the β-equation)

The argument is TN's `AubinYauEstimate.exists_le_smul_of_mongeAmpere_eq_exp` (Błocki, LNM 2038,
Theorem 5.13) with one change, which is Berman's observation: for `G = β(u - F)` the term
`(log det u_{jk̄})_{ζζ̄} = G_{ζζ̄} + (log det ρ_{jk̄})_{ζζ̄} ≥ β u_{ζζ̄} - β(1 + S)C - K₁` contains the
*positive* multiple `β u_{ζζ̄}` of the quantity to be bounded.  At a maximum point of
`α = log η - a u` (`η` the largest eigenvalue of `A + ddᶜu` relative to `A`), Błocki's local
inequality gives `(β u_{ζζ̄} - K₀)/u_{ζζ̄} ≤ a N` (`le_of_isLocalMax_beta`), hence
`(β - aN) u_{ζζ̄} ≤ β(1 + S)C + K₁` and, for `β ≥ 2aN + 1`, `η ≤ (1 + S)Λ` there; then
`log η(x) - a u(x) ≤ log((1 + S)Λ) - a m` everywhere.  Berman uses Siu's inequality for
`log tr_ω ω'` instead; the largest-eigenvalue form avoids the curvature computation and reuses
TN's proved local estimate (`BlockiLocalEstimate.blocki_local_estimate`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Foundations.Analysis.Pending.AubinYauLocalStep
open SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants
open SGPT.Foundations.Analysis.Pending.AubinYauEstimate
open SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax
open SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate

/-! ### The local step for the β-equation -/

/-- **Błocki's local step with a positive right-hand side.**  At a local maximum `z₀` of
`log u_{ζζ̄} - log ρ_{ζζ̄} - a (u - ρ)` (`|ζ| = 1`, `u_{jk̄}(z₀)` positive definite,
`ρ_{vv̄}(z₀) ≥ c₀|v|²`, `(ρ_{ζζ̄})_{vv̄}(z₀) ≤ M₀|v|²`, `a c₀ ≥ M₀ / c₀`), a lower bound
`(log det u_{jk̄})_{ζζ̄}(z₀) ≥ β u_{ζζ̄}(z₀) - K₀` forces `β u_{ζζ̄}(z₀) - K₀ ≤ a n u_{ζζ̄}(z₀)`. -/
theorem le_of_isLocalMax_beta {n : ℕ} {u ρ : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hρ : ContDiff ℝ ∞ ρ) {z₀ ζ : ComplexModel n} (hζ : ‖ζ‖ = 1)
    (hpos : (complexHessian u z₀).PosDef) {a c₀ M₀ K₀ β : ℝ} (hc₀ : 0 < c₀)
    (hM₀ : 0 ≤ M₀)
    (hρlow : ∀ w, c₀ * ‖w‖ ^ 2 ≤ leviForm ρ z₀ w)
    (hρM : ∀ w, leviForm (fun y => leviForm ρ y ζ) z₀ w ≤ M₀ * ‖w‖ ^ 2)
    (hdet : β * leviForm u z₀ ζ - K₀ ≤
      leviForm (fun y => Real.log (complexHessian u y).det.re) z₀ ζ)
    (ha : M₀ / c₀ ≤ a * c₀)
    (hmax : IsLocalMax (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      a * (u z - ρ z)) z₀) :
    β * leviForm u z₀ ζ - K₀ ≤ a * n * leviForm u z₀ ζ := by
  classical
  set H := complexHessian u z₀ with hHdef
  set P := H⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.posSemidef.inv
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
  set Lu : ComplexModel n → ℝ := fun y => leviForm u y ζ with hLudef
  set Lρ : ComplexModel n → ℝ := fun y => leviForm ρ y ζ with hLρdef
  have hLu : ContDiff ℝ ∞ Lu := contDiff_leviForm hu ζ
  have hLρ : ContDiff ℝ ∞ Lρ := contDiff_leviForm hρ ζ
  have hLρ0 : c₀ ≤ Lρ z₀ := by
    have := hρlow ζ; rw [hζ] at this; simpa using this
  have hLρpos : 0 < Lρ z₀ := hc₀.trans_le hLρ0
  have hLupos : 0 < Lu z₀ := by
    have hw : (fun d => star (ζ d)) ≠ 0 := by
      intro h; apply hζ0; ext d; have := congrFun h d; simpa using this
    have := hpos.re_dotProduct_pos hw
    rw [show Lu z₀ = (star (fun d => star (ζ d)) ⬝ᵥ (H *ᵥ fun d => star (ζ d))).re from by
      rw [← ofReal_leviForm_eq_dotProduct hu z₀ ζ, Complex.ofReal_re]]
    exact this
  set trP := P.trace.re with htrP
  have htrP0 : 0 ≤ trP := re_trace_nonneg hP
  have h1 : ContDiffAt ℝ 2 (fun z => Real.log (Lu z)) z₀ :=
    (contDiffAt_two hLu z₀).log hLupos.ne'
  have h2 : ContDiffAt ℝ 2 (fun z => Real.log (Lρ z)) z₀ :=
    (contDiffAt_two hLρ z₀).log hLρpos.ne'
  have hfun : (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      a * (u z - ρ z)) = fun z => Real.log (Lu z) + ((-1) * Real.log (Lρ z) +
        (-a) * (u z + (-1) * ρ z)) := by
    funext z; simp only [hLudef, hLρdef]; ring
  have hu2 := contDiffAt_two hu z₀
  have hρ2 := contDiffAt_two hρ z₀
  have hB1 : ContDiffAt ℝ 2 (fun z => (-1) * Real.log (Lρ z)) z₀ := contDiffAt_const.mul h2
  have hB2 : ContDiffAt ℝ 2 (fun z => (-1) * ρ z) z₀ := contDiffAt_const.mul hρ2
  have hB3 : ContDiffAt ℝ 2 (fun z => u z + (-1) * ρ z) z₀ := hu2.add hB2
  have hB5 : ContDiffAt ℝ 2 (fun z => (-a) * (u z + (-1) * ρ z)) z₀ := contDiffAt_const.mul hB3
  have hB4 : ContDiffAt ℝ 2 (fun z => (-1) * Real.log (Lρ z) + (-a) * (u z + (-1) * ρ z)) z₀ :=
    hB1.add hB5
  have hHα : complexHessian (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      a * (u z - ρ z)) z₀ = complexHessian (fun z => Real.log (Lu z)) z₀ +
        (((-1 : ℝ) : ℂ) • complexHessian (fun z => Real.log (Lρ z)) z₀ +
        ((-a : ℝ) : ℂ) • (complexHessian u z₀ + ((-1 : ℝ) : ℂ) • complexHessian ρ z₀)) := by
    rw [hfun, complexHessian_fun_add h1 hB4, complexHessian_fun_add hB1 hB5,
      complexHessian_const_mul h2, complexHessian_const_mul hB3,
      complexHessian_fun_add hu2 hB2, complexHessian_const_mul hρ2]
  have hC2 : ContDiffAt ℝ 2 (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      a * (u z - ρ z)) z₀ := by
    rw [hfun]; exact h1.add hB4
  have hmp := AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos hC2 hmax hP
  rw [hHα] at hmp
  simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
    Complex.add_re, Complex.re_ofReal_mul] at hmp
  -- the four traces
  have hT1 : (β * Lu z₀ - K₀) / Lu z₀ ≤
      (P * complexHessian (fun z => Real.log (Lu z)) z₀).trace.re := by
    have hB := blocki_local_estimate hu hpos hζ0
    exact (div_le_div_of_nonneg_right hdet hLupos.le).trans hB
  have hT2 : (P * complexHessian (fun z => Real.log (Lρ z)) z₀).trace.re ≤ M₀ / c₀ * trP := by
    refine (re_trace_mul_complexHessian_log_le hP hLρ hLρpos).trans ?_
    have hM := re_trace_mul_complexHessian_le hP (contDiffAt_two hLρ z₀) hρM
    rw [div_le_iff₀ hLρpos]
    calc (P * complexHessian Lρ z₀).trace.re ≤ M₀ * trP := hM
      _ = M₀ / c₀ * trP * c₀ := by field_simp
      _ ≤ M₀ / c₀ * trP * Lρ z₀ := by
        exact mul_le_mul_of_nonneg_left hLρ0 (by positivity)
  have hT3 : (P * complexHessian u z₀).trace.re = n := by
    rw [hPdef, hHdef, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hpos.det_pos.ne')), trace_one]
    simp
  have hT4 : c₀ * trP ≤ (P * complexHessian ρ z₀).trace.re :=
    le_re_trace_mul_complexHessian hP (contDiffAt_two hρ z₀) hρlow
  rw [hT3] at hmp
  have ha0 : 0 ≤ a := by
    have h0 : 0 ≤ M₀ / c₀ := by positivity
    have : 0 ≤ a * c₀ := h0.trans ha
    exact nonneg_of_mul_nonneg_left this hc₀
  have hT4' : a * (c₀ * trP) ≤ a * (P * complexHessian ρ z₀).trace.re :=
    mul_le_mul_of_nonneg_left hT4 ha0
  have hMtr : M₀ / c₀ * trP ≤ a * (c₀ * trP) := by
    calc M₀ / c₀ * trP ≤ a * c₀ * trP := mul_le_mul_of_nonneg_right ha htrP0
      _ = a * (c₀ * trP) := by ring
  have hkey : (β * Lu z₀ - K₀) / Lu z₀ ≤ a * n := by linarith
  rw [div_le_iff₀ hLupos] at hkey
  simpa only [hLudef] using hkey

/-! ### The estimate -/

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

set_option maxHeartbeats 800000 in
/-- **Berman's Laplacian estimate for the β-family, uniformly in β** (Berman 2019, Prop. 2.5 and
(2.11); WN21 Theorem 2.5): on a compact connected complex manifold `Y` with a Kähler background
`A` there are `a ≥ 0`, `Λ > 0` and `β₀ > 0` such that for `β ≥ β₀`, every chart-smooth `F` with
`ddᶜF ≤ S·A` on complex lines (`S ≥ 0`), every β-solution `u` and every lower bound `m ≤ u`,
`A + ddᶜu ≤ (1 + S) Λ e^{a(u(x) - m)} A` on every complex line at every point `x`. -/
theorem betaSolution_line_le [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y) :
    ∃ a Λ β₀ : ℝ, 0 ≤ a ∧ 0 < Λ ∧ 0 < β₀ ∧
      ∀ (β : ℝ), β₀ ≤ β → ∀ (F : Y → ℝ) (hF : ChartSmooth (n := N) F) (S : ℝ), 0 ≤ S →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
          S * A.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ (U : BetaSolution A β F) (m : ℝ), (∀ y, m ≤ U.u y) →
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v : ComplexModel N,
        (A.form + ddcClosedForm U.u U.smooth).val.coeff e z ![v, Complex.I • v] ≤
          (1 + S) * Λ * Real.exp (a * (U.u (e.val.symm z) - m)) *
            A.form.val.coeff e z ![v, Complex.I • v] := by
  classical
  have hzero : ∀ (β : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ), β (line 0) = 0 := fun β =>
    β.map_coord_zero (0 : Fin 2) (by simp [line])
  -- trivial cases
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨0, 1, 1, le_rfl, one_pos, one_pos, fun β _ F hF S _ _ U m _ e z hz v =>
      (hY.false (e.val.symm z)).elim⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨0, 1, 1, le_rfl, one_pos, one_pos, fun β _ F hF S _ _ U m _ e z hz v => ?_⟩
    subst hN
    have hv : v = 0 := Subsingleton.elim _ _
    subst hv
    have h1 := hzero ((A.form + ddcClosedForm U.u U.smooth).val.coeff e z)
    have h2 := hzero (A.form.val.coeff e z)
    simp only [line] at h1 h2
    rw [h1, h2]
    simp
  -- the finite atlas of chart pieces and its constants
  choose W ρ ρ' R hR hpot hWball hρ' hρ'eq c C M K₁ hc hC hM hK₁ hbd using exists_piece hN A
  set e : Y → ComplexChart N Y := fun p => complexChartAt (n := N) p with hedef
  set O : Y → Set Y := fun p => (e p).val.source ∩ (e p).val ⁻¹' ball ((e p).val p) (R p)
    with hOdef
  have hO : ∀ p, IsOpen (O p) := fun p => (e p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => ⟨mem_complexChartAt_source p, mem_ball_self (hR p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  have hterm : ∀ p, 0 ≤ (M p / c p) / c p := fun p => by
    have := hM p; have := hc p; positivity
  set a : ℝ := ∑ p ∈ t, (M p / c p) / c p with hadef
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun p _ => hterm p
  have hap : ∀ p ∈ t, M p / c p ≤ a * c p := by
    intro p hp
    have h1 : (M p / c p) / c p ≤ a :=
      Finset.single_le_sum (f := fun p => (M p / c p) / c p) (fun q _ => hterm q) hp
    rw [div_le_iff₀ (hc p)] at h1
    exact h1
  have hΛterm : ∀ p, 0 ≤ (2 * C p + 2 * K₁ p) / c p := fun p => by
    have := hC p; have := hK₁ p; have := hc p; positivity
  set Λ : ℝ := 1 + ∑ p ∈ t, (2 * C p + 2 * K₁ p) / c p with hΛdef
  have hΛpos : 0 < Λ := by
    have := Finset.sum_nonneg fun p (_ : p ∈ t) => hΛterm p
    linarith
  refine ⟨a, Λ, 2 * a * N + 1, ha0, hΛpos, by positivity, ?_⟩
  intro β hβ F hF S hS hFS U m hm
  have hβ1 : 1 ≤ β := by
    have : 0 ≤ 2 * a * N := by positivity
    linarith
  have hβpos : 0 < β := by linarith
  set u := U.u with hudef
  set Aφ := A.form + ddcClosedForm U.u U.smooth with hAφdef
  have hApos : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 →
      0 < A.form.val.coeff e z (line v) := fun e z hz v hv => (A.isKahler.1 e z hz).2 v hv
  have hBpos : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 →
      0 < Aφ.val.coeff e z (line v) := fun e z hz v hv => (U.isKahler.1 e z hz).2 v hv
  have hφc : Continuous u := YauUniformEstimate.continuous_of_chartSmooth U.smooth
  -- STEP 1: the maximum of `log η - a u`
  obtain ⟨y, Mx, hbound, hattain⟩ := exists_max_log_ratio_add hN A.form.val Aφ.val hApos hBpos
    (f := fun x => -a * u x) (continuous_const.mul hφc)
  obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, y ∈ O p := by
    have := ht (mem_univ y)
    rw [mem_iUnion₂] at this
    obtain ⟨p, hp, hyp⟩ := this
    exact ⟨p, hp, hyp⟩
  obtain ⟨ζ, hζ1, hζ⟩ := hattain (e p) hyp.1
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  set z₀ := (e p).val y with hz₀def
  set V := ball ((e p).val p) (2 * R p) with hVdef
  have hz₀B : z₀ ∈ ball ((e p).val p) (R p) := hyp.2
  have hz₀V : z₀ ∈ V := ball_subset_ball (by linarith [hR p]) hz₀B
  have hz₀K : z₀ ∈ closedBall ((e p).val p) (R p) := ball_subset_closedBall hz₀B
  have hVW : V ⊆ W p :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [hR p]))).trans
      (hWball p)
  -- STEP 2: the local potential of `A + ddᶜu` in the chart, globally smooth near `z₀`
  set ψ : ComplexModel N → ℝ := fun w => u ((e p).val.symm w) with hψdef
  have hu_on : ContDiffOn ℝ ∞ (fun w => ρ p w + ψ w) (W p) :=
    (hpot p).2.2.1.add ((U.smooth (e p)).mono (hpot p).2.1)
  obtain ⟨u', hu', hu'eq⟩ := exists_contDiff_eqOn_ball (hpot p).1 hu_on
    (by linarith [hR p] : 0 < 2 * R p) (by linarith [hR p] : 2 * R p < 4 * R p) (hWball p)
  have hgermu : ∀ z ∈ V, u' =ᶠ[𝓝 z] fun w => ρ p w + ψ w := fun z hz =>
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hu'eq
  have hgermρ : ∀ z ∈ V, ρ' p =ᶠ[𝓝 z] ρ p := fun z hz =>
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (hρ'eq p)
  have hLu : ∀ z ∈ V, ∀ v, leviForm u' z v = Real.pi * Aφ.val.coeff (e p) z (line v) := by
    intro z hz v
    rw [leviForm_congr (hgermu z hz), coeff_add_line_eq_leviForm A U.smooth (hpot p) (hVW hz)]
    field_simp
    rfl
  have hLρ : ∀ z ∈ V, ∀ v, leviForm (ρ' p) z v = Real.pi * A.form.val.coeff (e p) z (line v) := by
    intro z hz v
    rw [leviForm_congr (hgermρ z hz), coeff_line_eq_leviForm A (hpot p) (hVW hz)]
    field_simp
  have hzt : ∀ z ∈ V, z ∈ (e p).val.target := fun z hz => (hpot p).2.1 (hVW hz)
  -- STEP 3: the comparison function has a local maximum at `z₀`
  set α : ComplexModel N → ℝ := fun z => Real.log (leviForm u' z ζ) -
    Real.log (leviForm (ρ' p) z ζ) - a * (u' z - ρ' p z) with hαdef
  have hαV : ∀ z ∈ V, α z = Real.log (Aφ.val.coeff (e p) z (line ζ) /
      A.form.val.coeff (e p) z (line ζ)) + (-a * u ((e p).val.symm z)) := by
    intro z hz
    have ha := hApos (e p) z (hzt z hz) ζ hζ0
    have hb := hBpos (e p) z (hzt z hz) ζ hζ0
    have hdiff : u' z - ρ' p z = u ((e p).val.symm z) := by
      rw [hu'eq hz, hρ'eq p hz]; simp only [hψdef]; ring
    simp only [hαdef]
    rw [hLu z hz, hLρ z hz, hdiff, Real.log_div hb.ne' ha.ne',
      Real.log_mul Real.pi_pos.ne' hb.ne', Real.log_mul Real.pi_pos.ne' ha.ne']
    ring
  have hαz₀ : α z₀ = Mx := by
    rw [hαV z₀ hz₀V, (e p).val.left_inv hyp.1]
    exact hζ
  have hmax : IsLocalMax α z₀ := by
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhds hz₀V) fun z hz => ?_
    rw [hαz₀, hαV z hz]
    exact hbound (e p) z (hzt z hz) ζ hζ0
  -- STEP 4: the hypotheses of the local step at `z₀`
  have hz₀t : z₀ ∈ (e p).val.target := hzt z₀ hz₀V
  have hposu : ∀ z ∈ V, (complexHessian u' z).PosDef := fun z hz =>
    posDef_complexHessian (contDiffAt_two hu' z) fun v hv => by
      rw [hLu z hz v]; exact mul_pos Real.pi_pos (hBpos _ _ (hzt z hz) v hv)
  have hposρ : ∀ z ∈ V, (complexHessian (ρ' p) z).PosDef := fun z hz =>
    posDef_complexHessian (contDiffAt_two (hρ' p) z) fun v hv => by
      rw [hLρ z hz v]; exact mul_pos Real.pi_pos (hApos _ _ (hzt z hz) v hv)
  set Fψ : ComplexModel N → ℝ := fun w => F ((e p).val.symm w) with hFψdef
  set Gt : ComplexModel N → ℝ := fun w => β * (ψ w - Fψ w) with hGtdef
  set Dρ : ComplexModel N → ℝ := fun w => (complexHessian (ρ' p) w).det.re with hDρdef
  have hdetV : ∀ z ∈ V, (complexHessian u' z).det.re = Real.exp (Gt z) * Dρ z := by
    intro z hz
    show (complexHessian u' z).det.re = Real.exp (Gt z) * (complexHessian (ρ' p) z).det.re
    rw [complexHessian_congr (hgermu z hz), complexHessian_congr (hgermρ z hz)]
    exact re_det_complexHessian_eq_exp (G := fun y => β * (U.u y - F y)) A U.smooth U.density
      (hpot p) (hVW hz)
  have hDρpos : ∀ z ∈ V, 0 < Dρ z := fun z hz => (Complex.pos_iff.mp (hposρ z hz).det_pos).1
  have hlogV : (fun w => Real.log (complexHessian u' w).det.re) =ᶠ[𝓝 z₀]
      fun w => Gt w + Real.log (Dρ w) := by
    filter_upwards [isOpen_ball.mem_nhds hz₀V] with z hz
    rw [hdetV z hz, Real.log_mul (Real.exp_pos _).ne' (hDρpos z hz).ne', Real.log_exp]
  have hψ2 : ContDiffAt ℝ 2 ψ z₀ := contDiffAt_two_chart U.smooth (e p) hz₀t
  have hFψ2 : ContDiffAt ℝ 2 Fψ z₀ := contDiffAt_two_chart hF (e p) hz₀t
  have hGt2 : ContDiffAt ℝ 2 Gt z₀ := contDiffAt_const.mul (hψ2.sub hFψ2)
  have hDρc : ContDiff ℝ ∞ Dρ :=
    Complex.reCLM.contDiff.comp (WirtingerLogDet.contDiff_det_complexHessian (hρ' p))
  have hlog2 : ContDiffAt ℝ 2 (fun w => Real.log (Dρ w)) z₀ :=
    (contDiffAt_two hDρc z₀).log (hDρpos z₀ hz₀V).ne'
  have hlevisum : leviForm (fun w => Real.log (complexHessian u' w).det.re) z₀ ζ =
      leviForm Gt z₀ ζ + leviForm (fun w => Real.log (Dρ w)) z₀ ζ := by
    rw [leviForm_congr hlogV]
    exact leviForm_add hGt2 hlog2 ζ
  -- `G_{ζζ̄} = β (u'_{ζζ̄} - ρ'_{ζζ̄} - F_{ζζ̄})`
  have hρp2 : ContDiffAt ℝ 2 (ρ p) z₀ :=
    contDiffAt_two_of_contDiffOn (hpot p).1 (hpot p).2.2.1 (hVW hz₀V)
  have hLψ : leviForm ψ z₀ ζ = leviForm u' z₀ ζ - leviForm (ρ' p) z₀ ζ := by
    rw [leviForm_congr (hgermu z₀ hz₀V), leviForm_congr (hgermρ z₀ hz₀V)]
    have := leviForm_add (u := ρ p) (v := ψ) hρp2 hψ2 ζ
    simp only [Pi.add_def] at this
    rw [this]; ring
  have hLGt : leviForm Gt z₀ ζ = β * (leviForm ψ z₀ ζ - leviForm Fψ z₀ ζ) := by
    have h := leviForm_smul (hψ2.sub hFψ2) β ζ
    rw [leviForm_sub' hψ2 hFψ2] at h
    exact h
  have hLF : leviForm Fψ z₀ ζ ≤ S * leviForm (ρ' p) z₀ ζ := by
    have h := hFS (e p) z₀ hz₀t ζ
    rw [ddc_line_eq hF (e p) hz₀t ζ] at h
    have h1 : A.form.val.coeff (e p) z₀ (line ζ) = leviForm (ρ' p) z₀ ζ / Real.pi := by
      rw [hLρ z₀ hz₀V]; field_simp
    change leviForm Fψ z₀ ζ / Real.pi ≤ S * A.form.val.coeff (e p) z₀ (line ζ) at h
    rw [h1, mul_div_assoc', div_le_div_iff_of_pos_right Real.pi_pos] at h
    exact h
  have hLρC : leviForm (ρ' p) z₀ ζ ≤ C p := by
    have := (hbd p z₀ hz₀K).2.1 ζ; rw [hζ1] at this; simpa using this
  have hLρ0 : 0 ≤ leviForm (ρ' p) z₀ ζ := by
    have := (hbd p z₀ hz₀K).1 ζ; rw [hζ1] at this
    have hcp := hc p
    nlinarith
  have hdet : β * leviForm u' z₀ ζ - (β * (1 + S) * C p + K₁ p) ≤
      leviForm (fun w => Real.log (complexHessian u' w).det.re) z₀ ζ := by
    rw [hlevisum, hLGt, hLψ]
    have h3 := (hbd p z₀ hz₀K).2.2.2 ζ hζ1.le
    simp only [hDρdef] at h3 ⊢
    have h4 : β * ((1 + S) * leviForm (ρ' p) z₀ ζ) ≤ β * ((1 + S) * C p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLρC (by linarith)) hβpos.le
    have h5 : β * leviForm Fψ z₀ ζ ≤ β * (S * leviForm (ρ' p) z₀ ζ) :=
      mul_le_mul_of_nonneg_left hLF hβpos.le
    nlinarith
  have hstep := le_of_isLocalMax_beta hu' (hρ' p) hζ1 (hposu z₀ hz₀V) (hc p) (hM p)
    ((hbd p z₀ hz₀K).1) ((hbd p z₀ hz₀K).2.2.1 ζ hζ1.le) hdet (hap p hpt) hmax
  -- STEP 5: `η(y) ≤ (1 + S) Λ`
  have hLupos : 0 < leviForm u' z₀ ζ := by
    rw [hLu z₀ hz₀V]; exact mul_pos Real.pi_pos (hBpos _ _ hz₀t ζ hζ0)
  have hLρpos : 0 < leviForm (ρ' p) z₀ ζ := by
    rw [hLρ z₀ hz₀V]; exact mul_pos Real.pi_pos (hApos _ _ hz₀t ζ hζ0)
  have hcLρ : c p ≤ leviForm (ρ' p) z₀ ζ := by
    have := (hbd p z₀ hz₀K).1 ζ; rw [hζ1] at this; simpa using this
  have hLuB : leviForm u' z₀ ζ ≤ (1 + S) * (2 * C p + 2 * K₁ p) := by
    -- `(β - aN) Lu ≤ β(1 + S)C + K₁` and `β - aN ≥ β/2`, `β ≥ 1`
    have hb2 : β / 2 ≤ β - a * N := by
      have : 2 * a * N + 1 ≤ β := hβ
      linarith
    have h1 : (β - a * N) * leviForm u' z₀ ζ ≤ β * (1 + S) * C p + K₁ p := by linarith
    have h2 : β / 2 * leviForm u' z₀ ζ ≤ β * (1 + S) * C p + K₁ p :=
      (mul_le_mul_of_nonneg_right hb2 hLupos.le).trans h1
    have hK : K₁ p ≤ β * K₁ p := by
      have := hK₁ p; nlinarith
    have h3 : β / 2 * leviForm u' z₀ ζ ≤ β / 2 * ((1 + S) * (2 * C p + 2 * K₁ p)) := by
      have hSK : 0 ≤ S * K₁ p := mul_nonneg hS (hK₁ p)
      have : β * (1 + S) * C p + K₁ p ≤ β / 2 * ((1 + S) * (2 * C p + 2 * K₁ p)) := by
        nlinarith
      linarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  have hΛp : (2 * C p + 2 * K₁ p) / c p ≤ Λ := by
    have := Finset.single_le_sum (f := fun p => (2 * C p + 2 * K₁ p) / c p)
      (fun q _ => hΛterm q) hpt
    rw [hΛdef]
    linarith
  have hratio0 : Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) =
      leviForm u' z₀ ζ / leviForm (ρ' p) z₀ ζ := by
    rw [hLu z₀ hz₀V, hLρ z₀ hz₀V, mul_div_mul_left _ _ Real.pi_pos.ne']
  have hratio : Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) ≤
      (1 + S) * Λ := by
    rw [hratio0, div_le_iff₀ hLρpos]
    have h1S : 0 ≤ 1 + S := by linarith
    have hcp := hc p
    calc leviForm u' z₀ ζ ≤ (1 + S) * (2 * C p + 2 * K₁ p) := hLuB
      _ = (1 + S) * ((2 * C p + 2 * K₁ p) / c p) * c p := by field_simp
      _ ≤ (1 + S) * Λ * c p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛp h1S) hcp.le
      _ ≤ (1 + S) * Λ * leviForm (ρ' p) z₀ ζ :=
          mul_le_mul_of_nonneg_left hcLρ (mul_nonneg h1S hΛpos.le)
  have hratiopos : 0 < Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) := by
    rw [hratio0]; exact div_pos hLupos hLρpos
  have hSΛ : 0 < (1 + S) * Λ := hratiopos.trans_le hratio
  have hMx : Mx ≤ Real.log ((1 + S) * Λ) - a * m := by
    rw [← hαz₀, hαV z₀ hz₀V, (e p).val.left_inv hyp.1]
    have h1 := Real.log_le_log hratiopos hratio
    have h2 : a * m ≤ a * u y := mul_le_mul_of_nonneg_left (hm y) ha0
    linarith
  -- STEP 6: everywhere
  intro e' z hz v
  rcases eq_or_ne v 0 with hv | hv
  · have h1 := hzero (Aφ.val.coeff e' z)
    have h2 := hzero (A.form.val.coeff e' z)
    simp only [line] at h1 h2
    rw [hv, h1, h2, mul_zero]
  have ha := hApos e' z hz v hv
  have hb := hBpos e' z hz v hv
  have h1 := hbound e' z hz v hv
  have hlog : Real.log (Aφ.val.coeff e' z (line v) / A.form.val.coeff e' z (line v)) ≤
      Real.log ((1 + S) * Λ) + a * (u (e'.val.symm z) - m) := by
    have h2 : -a * u (e'.val.symm z) = -(a * u (e'.val.symm z)) := by ring
    linarith
  have hle : Aφ.val.coeff e' z (line v) / A.form.val.coeff e' z (line v) ≤
      (1 + S) * Λ * Real.exp (a * (u (e'.val.symm z) - m)) := by
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (div_pos hb ha), Real.exp_add, Real.exp_log hSΛ] at this
  rw [div_le_iff₀ ha] at hle
  exact hle

end SGPT.Okounkov.TranscendentalWNReg
