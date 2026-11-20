import SGPT.Envelopes.TosC11dGlobal

/-!
# The hypotheses of the local estimate at the maximum point

Lane TOS-C11e (`claude-tos-c11e`, node `claude-tos-c11e:max-bound`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 2–4 (after Tosatti 2018 and
Chu–Tosatti–Weinkove), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

Let `u` solve the penalized equation `(A + ddᶜu)^N = e^{β(u - F)} A^N` (`BetaSolution`), let `w`
be the weight `-(τ/2) log(1 + S - |∇u|²/π) - A u` and let `M` be the maximum of
`(∇²u(v, v)/g(v, v)) e^{w}`, attained at `e⁻¹(z₀)`.  In normal coordinates `Φ` at `z₀`
diagonalizing the complex Hessian of `ρ + u ∘ e⁻¹` (`ρ` a local potential of `A`), all hypotheses
of `TosC11d.local_bound` hold for the potential `ψ = ρ ∘ Φ`, the function `a = u ∘ e⁻¹ ∘ Φ`, the
obstacle `F ∘ e⁻¹ ∘ Φ` and the weight `w ∘ e⁻¹ ∘ Φ` (all up to germs at `0`), so the bound
`D²a(0) ≤ Λ` of the local estimate gives `M ≤ π Λ e^{w(e⁻¹ z₀)}` (`max_le_of_frame`).

* `LocalBound` — the conclusion of `TosC11d.local_bound` for given constants (`exists_localBound`).
* `max_le_of_frame` — the bound for the maximum.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace SGPT.Envelopes.TosC11e

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Analysis.KahlerNormal
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.TosC11d

/-- The conclusion of the local estimate `TosC11d.local_bound` for the constants `A` (weight) and
`Λ` (bound): for `ψ` normal at `0` with metric jets bounded by `Cg`, the penalized equation near
`0`, `ψ + a` strictly plurisubharmonic at `0` with diagonal complex Hessian `diag(r)`, `rᵢ ≤ R`,
`‖DF(0)‖ ≤ CF`, `D²F(0) ≤ BF`, `s(0) ≤ S`, and `0` a maximum point of
`(∇²a(Y, Y)/g(Y, Y)) e^{w}` with `w = -(τ/2) log(1 + S - s) - A a`, `τ = (1 + 2 CF²)⁻¹`, one has
`D²a(0)(Y, Y) ≤ Λ ‖Y‖²`. -/
def LocalBound (n : ℕ) (Cg R S CF BF A Λ : ℝ) : Prop :=
  ∀ (ψ a F w : ComplexModel n → ℝ) (β M₀ : ℝ) (r : Fin n → ℝ),
    NormalAt ψ → ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → 0 ≤ β →
    (∀ v, ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v‖ ≤ Cg * ‖v‖) →
    (∀ v v', ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v'‖ ≤ Cg * ‖v‖ * ‖v'‖) →
    (∀ᶠ x in 𝓝 (0 : ComplexModel n), (complexHessian (fun y => ψ y + a y) x).det.re =
      Real.exp (β * (a x - F x)) * (complexHessian ψ x).det.re) →
    (∀ v, v ≠ 0 → 0 < leviForm (fun y => ψ y + a y) 0 v) →
    complexHessian (fun y => ψ y + a y) 0 = Matrix.diagonal (fun i => (r i : ℂ)) →
    (∀ i, r i ≤ R) → ‖fderiv ℝ F 0‖ ≤ CF →
    (∀ v, fderiv ℝ (fderiv ℝ F) 0 v v ≤ BF * ‖v‖ ^ 2) →
    sFun ψ a 0 ≤ S →
    (∀ᶠ x in 𝓝 (0 : ComplexModel n), w x =
      -((1 + 2 * CF ^ 2)⁻¹ / 2) * Real.log (1 + S - sFun ψ a x) - A * a x) →
    (∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ Y, Y ≠ 0 → quot ψ a x Y * Real.exp (w x) ≤ M₀) →
    (∃ V, V ≠ 0 ∧ quot ψ a 0 V * Real.exp (w 0) = M₀) →
    ∀ Y, fderiv ℝ (fderiv ℝ a) 0 Y Y ≤ Λ * ‖Y‖ ^ 2

/-- `TosC11d.local_bound` in terms of `LocalBound`. -/
theorem exists_localBound {n : ℕ} (hn : 0 < n) {Cg R S CF BF : ℝ} (hCg : 0 ≤ Cg) (hR : 0 < R)
    (hS : 0 ≤ S) : ∃ A Λ : ℝ, 0 < A ∧ LocalBound n Cg R S CF BF A Λ :=
  local_bound hn hCg hR hS

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The maximum of the weighted covariant Hessian quotient** (FPT `lem:penalized-real-hessian`,
Steps 2–4).  Let `U` solve the penalized equation for `β ≥ 0` and the obstacle `F`, let `ρ` be a
local potential of `A` on `W ∋ z₀` in the chart `e`, and let `Φ` be Kähler normal coordinates at
`z₀` (`Φ(0) = z₀`, `Φ^*A = ω₀` at `0` with vanishing derivative, metric jets bounded by `C₂, C₃`,
`‖DΦ(0)‖ ≤ C_A`, `|D²Φ(0)(v, v)| ≤ C_A²‖v‖²`) in which the complex Hessian of `ρ + u ∘ e⁻¹` at `z₀`
is `diag(r)`.  Assume `LocalBound` for constants `Cg, R, S, CF, BF, A, Λ` dominating the data at
`z₀`: `ddᶜu ≤ (R - 1) A` on lines, `‖D^k(F ∘ e⁻¹)(z₀)‖ ≤ B` (`k = 1, 2`) with `B C_A ≤ CF`,
`2 B C_A² ≤ BF`, and `|∇u|²(z₀) ≤ π S`.  If `w = -(τ/2) log(1 + S - |∇u|²/π) - A u` and
`(∇²u(v, v)/g(v, v)) e^{w} ≤ M` in the chart `e`, with equality at `z₀`, then
`M ≤ π Λ e^{w(e⁻¹ z₀)}`. -/
theorem max_le_of_frame (A : KahlerBackground N Y) {β : ℝ} (hβ : 0 ≤ β) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) (U : BetaSolution A β F) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {z₀ : ComplexModel N} (hz₀W : z₀ ∈ W)
    {Φ : ComplexModel N → ComplexModel N} {r : Fin N → ℝ} (hΦ : ContDiff ℂ ∞ Φ) (hΦ0 : Φ 0 = z₀)
    (hbij : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Function.Bijective (fderiv ℝ Φ x))
    (h0 : pullbackField Φ (A.form.val.coeff e) 0 = flatForm N)
    (hd : HasFDerivAt (pullbackField Φ (A.form.val.coeff e))
      (0 : ComplexModel N →L[ℝ] CoordinateRealTwoForm N) 0)
    {C2 C3 CA : ℝ} (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h2 : ∀ p q, ‖iteratedFDeriv ℝ 2
      (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C2)
    (h3 : ∀ p q, ‖iteratedFDeriv ℝ 3
      (fun w => pullbackField Φ (A.form.val.coeff e) w ![frameV p, frameV q]) 0‖ ≤ C3)
    (hDΦ : ‖fderiv ℝ Φ 0‖ ≤ CA) (hD2Φ : ∀ v, ‖fderiv ℝ (fderiv ℝ Φ) 0 v v‖ ≤ CA * CA * ‖v‖ ^ 2)
    (hdiag : (HolomorphicMixedDensity.jacobianMatrix Φ 0).transpose *
        complexHessian (fun z => ρ z + U.u (e.val.symm z)) z₀ *
          (HolomorphicMixedDensity.jacobianMatrix Φ 0).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => (r i : ℂ))
    {Cg R S CF BF Aℓ Λℓ : ℝ} (hloc : LocalBound N Cg R S CF BF Aℓ Λℓ)
    (hCg2 : 2 * N * (2 * N * (Real.pi * C2)) ≤ Cg) (hCg3 : 2 * N * (2 * N * (Real.pi * C3)) ≤ Cg)
    (hRline : ∀ v : ComplexModel N,
      (ddcClosedForm U.u U.smooth).val.coeff e z₀ ![v, Complex.I • v] ≤
        (R - 1) * A.form.val.coeff e z₀ ![v, Complex.I • v])
    {BD : ℝ} (hBD : 0 ≤ BD) (hF1 : ‖fderiv ℝ (fun z => F (e.val.symm z)) z₀‖ ≤ BD)
    (hF2 : ‖fderiv ℝ (fderiv ℝ (fun z => F (e.val.symm z))) z₀‖ ≤ BD)
    (hCF : BD * CA ≤ CF) (hBF : 2 * BD * CA ^ 2 ≤ BF)
    (hs : TosC11c.gradNormSq A U.u e z₀ ≤ Real.pi * S)
    {w : Y → ℝ} (hw : ∀ x, w x = -((1 + 2 * CF ^ 2)⁻¹ / 2) *
      Real.log (1 + S - TosC11c.gradNormSqFun A U.u x / Real.pi) - Aℓ * U.u x)
    {M : ℝ} (hle : ∀ z ∈ e.val.target, ∀ v, v ≠ 0 →
      TosC11c.hessQuot A U.u e z v * Real.exp (w (e.val.symm z)) ≤ M)
    (hatt : ∃ ζ, ζ ≠ 0 ∧ TosC11c.hessQuot A U.u e z₀ ζ * Real.exp (w (e.val.symm z₀)) = M) :
    M ≤ Real.pi * Λℓ * Real.exp (w (e.val.symm z₀)) := by
  set u := U.u with hudef
  have hu : ChartSmooth (n := N) u := U.smooth
  have hU := e.val.open_target
  have hz₀t : z₀ ∈ e.val.target := hpot.2.1 hz₀W
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans hDΦ
  have hΦR : ContDiff ℝ ∞ Φ := hΦ.restrict_scalars ℝ
  have hΦc : Continuous Φ := hΦR.continuous
  -- a smooth potential `ψ`, equal to `ρ ∘ Φ` near `0`
  obtain ⟨R₀, hR₀, hR₀W⟩ := Metric.isOpen_iff.mp hpot.1 z₀ hz₀W
  obtain ⟨ρ', hρ', hρ'eq⟩ := AubinYauUniformConstants.exists_contDiff_eqOn_ball hpot.1
    hpot.2.2.1 (by positivity : (0 : ℝ) < R₀ / 4) (by linarith : R₀ / 4 < R₀ / 2)
    ((closedBall_subset_ball (by linarith)).trans hR₀W)
  set ψ : ComplexModel N → ℝ := fun x => ρ' (Φ x) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := hρ'.comp hΦR
  have hO₁ : IsOpen (Φ ⁻¹' ball z₀ (R₀ / 4)) := isOpen_ball.preimage hΦc
  have h0O₁ : (0 : ComplexModel N) ∈ Φ ⁻¹' ball z₀ (R₀ / 4) := by
    show Φ 0 ∈ ball z₀ (R₀ / 4); rw [hΦ0]; exact mem_ball_self (by positivity)
  have hψgerm : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ψ =ᶠ[𝓝 x] fun y => ρ (Φ y) := by
    filter_upwards [hO₁.mem_nhds h0O₁] with x hx
    filter_upwards [hO₁.mem_nhds hx] with y hy
    exact hρ'eq hy
  have hWev : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Φ x ∈ W :=
    Filter.mem_of_superset (hO₁.mem_nhds h0O₁) fun x hx => hR₀W (ball_subset_ball (by linarith) hx)
  -- smooth functions `a` and `Fℓ`, equal to `u ∘ e⁻¹ ∘ Φ` and `F ∘ e⁻¹ ∘ Φ` near `0`
  have hO₂ : IsOpen (Φ ⁻¹' e.val.target) := hU.preimage hΦc
  have h0O₂ : (0 : ComplexModel N) ∈ Φ ⁻¹' e.val.target :=
    Set.mem_preimage.mpr (by rw [hΦ0]; exact hz₀t)
  obtain ⟨R₂, hR₂, hR₂O⟩ := Metric.isOpen_iff.mp hO₂ 0 h0O₂
  have hcomp : ∀ g : Y → ℝ, ChartSmooth (n := N) g →
      ContDiffOn ℝ ∞ (fun x => g (e.val.symm (Φ x))) (Φ ⁻¹' e.val.target) :=
    fun g hg => (hg e).comp hΦR.contDiffOn fun x hx => hx
  obtain ⟨a, ha, haeq⟩ := AubinYauUniformConstants.exists_contDiff_eqOn_ball hO₂ (hcomp u hu)
    (by positivity : (0 : ℝ) < R₂ / 4) (by linarith : R₂ / 4 < R₂ / 2)
    ((closedBall_subset_ball (by linarith)).trans hR₂O)
  obtain ⟨Fℓ, hFℓ, hFℓeq⟩ := AubinYauUniformConstants.exists_contDiff_eqOn_ball hO₂ (hcomp F hF)
    (by positivity : (0 : ℝ) < R₂ / 4) (by linarith : R₂ / 4 < R₂ / 2)
    ((closedBall_subset_ball (by linarith)).trans hR₂O)
  have hball : ball (0 : ComplexModel N) (R₂ / 4) ∈ 𝓝 (0 : ComplexModel N) :=
    isOpen_ball.mem_nhds (mem_ball_self (by positivity))
  have hagerm : ∀ᶠ x in 𝓝 (0 : ComplexModel N), a =ᶠ[𝓝 x] fun y => u (e.val.symm (Φ y)) := by
    filter_upwards [hball] with x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact haeq hy
  have haval : ∀ᶠ x in 𝓝 (0 : ComplexModel N), a x = u (e.val.symm (Φ x)) :=
    Filter.mem_of_superset hball fun x hx => haeq hx
  have hFval : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Fℓ x = F (e.val.symm (Φ x)) :=
    Filter.mem_of_superset hball fun x hx => hFℓeq hx
  have hFgerm : Fℓ =ᶠ[𝓝 (0 : ComplexModel N)] fun y => F (e.val.symm (Φ y)) := hFval
  -- the transfer identities near `0`
  have hgood : ∀ᶠ x in 𝓝 (0 : ComplexModel N),
      (∀ Yv, TosC11c.hessQuot A u e (Φ x) (fderiv ℝ Φ x Yv) = Real.pi * quot ψ a x Yv) ∧
        TosC11c.gradNormSq A u e (Φ x) = Real.pi * sFun ψ a x := by
    filter_upwards [hψgerm, hagerm, hWev, hbij] with x hψx hax hWx hbx
    exact hessQuot_eq_quot A hpot hΦ hu hψs hψx hax hWx hbx
  -- normal coordinates
  have hN : NormalAt ψ := normalAt_of_frame A hpot hΦ hψs hψgerm hWev hbij h0 hd
  obtain ⟨hj2, hj3⟩ := metric_jet_bounds A hpot hΦ hψs hψgerm hWev hC2 hC3 h2 h3
  -- the metric and the Levi forms at `0`
  have hψ0 := hψgerm.self_of_nhds
  have ha0 := hagerm.self_of_nhds
  have hW0 : Φ 0 ∈ W := hWev.self_of_nhds
  have hmet : ∀ v, metricOf ψ 0 v v =
      Real.pi * A.form.val.coeff e z₀ ![fderiv ℝ Φ 0 v, Complex.I • fderiv ℝ Φ 0 v] := fun v => by
    rw [metricOf_eq_chartMetric A hpot hΦ hψ0 hW0, hΦ0]
    rfl
  have hue2 : ContDiffAt ℝ 2 (fun z => u (e.val.symm z)) z₀ :=
    ((hu e).contDiffAt (hU.mem_nhds hz₀t)).of_le h2le
  have hlev : ∀ v, leviForm a 0 v =
      Real.pi * (ddcClosedForm u hu).val.coeff e z₀ ![fderiv ℝ Φ 0 v, Complex.I • fderiv ℝ Φ 0 v] :=
    fun v => by
      rw [leviForm_comp_eq hΦ hU (hu e) (show Φ 0 ∈ e.val.target by rw [hΦ0]; exact hz₀t) ha0 v,
        hΦ0, smoothDDC_complexDiagonal_eq_leviForm hue2, ddc_line_eq hu e hz₀t]
  have hψ2 : ContDiffAt ℝ 2 ψ 0 := hψs.contDiffAt.of_le h2le
  have ha2 : ContDiffAt ℝ 2 a 0 := ha.contDiffAt.of_le h2le
  have hlevsum : ∀ v, leviForm (fun y => ψ y + a y) 0 v =
      Real.pi * (A.form + ddcClosedForm u hu).val.coeff e z₀
        ![fderiv ℝ Φ 0 v, Complex.I • fderiv ℝ Φ 0 v] := fun v => by
    rw [show (fun y => ψ y + a y) = ψ + a from rfl, leviForm_add hψ2 ha2, leviForm_eq_metricOf,
      hmet, hlev, add_ddc_line]
    ring
  -- positivity
  have hpos : ∀ v, v ≠ 0 → 0 < leviForm (fun y => ψ y + a y) 0 v := fun v hv => by
    rw [hlevsum]
    refine mul_pos Real.pi_pos ((U.isKahler.1 e z₀ hz₀t).2 _ fun h => hv ?_)
    exact hbij.self_of_nhds.1 (by rw [h, map_zero])
  -- the complex Hessian at `0`
  have hρ : ContDiffOn ℝ ∞ ρ W := hpot.2.2.1
  have hueW : ContDiffOn ℝ ∞ (fun z => u (e.val.symm z)) W := (hu e).mono hpot.2.1
  have hsum0 : (fun y => ψ y + a y) =ᶠ[𝓝 (0 : ComplexModel N)]
      fun y => (fun z => ρ z + u (e.val.symm z)) (Φ y) := by
    filter_upwards [hψ0, ha0] with y h1 h2
    rw [h1, h2]
  have hdiag0 : complexHessian (fun y => ψ y + a y) 0 = Matrix.diagonal fun i => (r i : ℂ) := by
    rw [complexHessian_comp_eq hΦ hpot.1 (hρ.add hueW) hW0 hsum0, hΦ0, hdiag]
  -- the eigenvalues `rᵢ ≤ R`
  have hrR : ∀ i, r i ≤ R := fun i => by
    have h1 : r i = leviForm (fun y => ψ y + a y) 0 (coordinateVector i) := by
      rw [← complexHessian_diagonal_re, hdiag0, Matrix.diagonal_apply_eq, Complex.ofReal_re]
    have h2 : metricOf ψ 0 (coordinateVector i) (coordinateVector i) = 1 := by
      rw [hN.metric_zero, real_inner_self_eq_norm_sq]
      simp [coordinateVector]
    have h3 : (ddcClosedForm u hu).val.coeff e z₀
        ![fderiv ℝ Φ 0 (coordinateVector i), Complex.I • fderiv ℝ Φ 0 (coordinateVector i)] ≤
        (R - 1) * A.form.val.coeff e z₀
          ![fderiv ℝ Φ 0 (coordinateVector i), Complex.I • fderiv ℝ Φ 0 (coordinateVector i)] :=
      hRline _
    rw [h1, show (fun y => ψ y + a y) = ψ + a from rfl, leviForm_add hψ2 ha2,
      leviForm_eq_metricOf, h2, hlev]
    rw [hmet] at h2
    have h4 := mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
    rw [mul_left_comm, h2, mul_one] at h4
    linarith
  -- the obstacle
  have hFe2 : ContDiffAt ℝ 2 (fun z => F (e.val.symm z)) z₀ :=
    ((hF e).contDiffAt (hU.mem_nhds hz₀t)).of_le h2le
  have hΦ2 : ContDiffAt ℝ 2 Φ 0 := hΦR.contDiffAt.of_le h2le
  have hDF : ‖fderiv ℝ Fℓ 0‖ ≤ CF := by
    rw [hFgerm.fderiv_eq, show (fun y => F (e.val.symm (Φ y))) = (fun z => F (e.val.symm z)) ∘ Φ
      from rfl, fderiv_comp 0 (by rw [hΦ0]; exact hFe2.differentiableAt (by norm_num))
      (hΦ2.differentiableAt (by norm_num)), hΦ0]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ BD * CA := mul_le_mul hF1 hDΦ (norm_nonneg _) hBD
      _ ≤ CF := hCF
  have hD2F : ∀ v, fderiv ℝ (fderiv ℝ Fℓ) 0 v v ≤ BF * ‖v‖ ^ 2 := fun v => by
    rw [hFgerm.fderiv.fderiv_eq, show (fun y => F (e.val.symm (Φ y))) =
      (fun z => F (e.val.symm z)) ∘ Φ from rfl,
      TosC11b.fderiv_fderiv_comp (by rw [hΦ0]; exact hFe2) hΦ2, hΦ0]
    set f := fun z => F (e.val.symm z)
    have hw1 : ‖fderiv ℝ Φ 0 v‖ ≤ CA * ‖v‖ :=
      ((fderiv ℝ Φ 0).le_opNorm v).trans (mul_le_mul_of_nonneg_right hDΦ (norm_nonneg _))
    have b1 : fderiv ℝ (fderiv ℝ f) z₀ (fderiv ℝ Φ 0 v) (fderiv ℝ Φ 0 v) ≤ BD * (CA * ‖v‖) ^ 2 := by
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine ((fderiv ℝ (fderiv ℝ f) z₀).le_opNorm₂ _ _).trans ?_
      have := mul_le_mul hw1 hw1 (norm_nonneg _) (by positivity)
      calc _ = ‖fderiv ℝ (fderiv ℝ f) z₀‖ * (‖fderiv ℝ Φ 0 v‖ * ‖fderiv ℝ Φ 0 v‖) := by ring
        _ ≤ BD * ((CA * ‖v‖) * (CA * ‖v‖)) := mul_le_mul hF2 this (by positivity) hBD
        _ = BD * (CA * ‖v‖) ^ 2 := by ring
    have b2 : fderiv ℝ f z₀ (fderiv ℝ (fderiv ℝ Φ) 0 v v) ≤ BD * (CA * CA * ‖v‖ ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ f z₀).le_opNorm _).trans (mul_le_mul hF1 (hD2Φ v) (norm_nonneg _) hBD)
    have : BD * (CA * ‖v‖) ^ 2 + BD * (CA * CA * ‖v‖ ^ 2) = 2 * BD * CA ^ 2 * ‖v‖ ^ 2 := by ring
    nlinarith [sq_nonneg ‖v‖]
  -- the gradient length at `0`
  have hs0 : sFun ψ a 0 ≤ S := by
    have h := hgood.self_of_nhds.2
    rw [hΦ0] at h
    rw [h] at hs
    exact le_of_mul_le_mul_left hs Real.pi_pos
  -- the equation near `0`
  have heq : ∀ᶠ x in 𝓝 (0 : ComplexModel N), (complexHessian (fun y => ψ y + a y) x).det.re =
      Real.exp (β * (a x - Fℓ x)) * (complexHessian ψ x).det.re := by
    filter_upwards [hψgerm, hagerm, hWev, haval, hFval] with x hψx hax hWx hax' hFx
    rw [re_det_complexHessian_comp_eq A hpot hΦ hu (G := fun y => β * (u y - F y))
      (fun e' z hz => U.density e' z hz) hψx hax hWx, hax', hFx]
  -- the weight in the coordinates `Φ`
  set wℓ : ComplexModel N → ℝ := fun x => w (e.val.symm (Φ x)) with hwℓdef
  have hwℓ : ∀ᶠ x in 𝓝 (0 : ComplexModel N), wℓ x =
      -((1 + 2 * CF ^ 2)⁻¹ / 2) * Real.log (1 + S - sFun ψ a x) - Aℓ * a x := by
    filter_upwards [hgood, hWev, haval] with x hx hWx hax
    have hxt : Φ x ∈ e.val.target := hpot.2.1 hWx
    have hxs : e.val.symm (Φ x) ∈ e.val.source := e.val.map_target hxt
    have hgx : TosC11c.gradNormSqFun A u (e.val.symm (Φ x)) / Real.pi = sFun ψ a x := by
      rw [TosC11c.gradNormSqFun_eq A hu e hxs, e.val.right_inv hxt, hx.2,
        mul_div_cancel_left₀ _ Real.pi_ne_zero]
    simp only [hwℓdef]
    rw [hw, hgx, hax]
  -- the maximum and its attainment
  have hmax : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ∀ Yv, Yv ≠ 0 →
      quot ψ a x Yv * Real.exp (wℓ x) ≤ M / Real.pi := by
    filter_upwards [hgood, hWev, hbij] with x hx hWx hbx
    intro Yv hYv
    have hne : fderiv ℝ Φ x Yv ≠ 0 := fun h => hYv (hbx.1 (by rw [h, map_zero]))
    have h1 := hle (Φ x) (hpot.2.1 hWx) _ hne
    rw [hx.1] at h1
    rw [le_div_iff₀ Real.pi_pos]
    simp only [hwℓdef]
    linarith
  obtain ⟨ζ, hζ, hζM⟩ := hatt
  obtain ⟨V, hV⟩ := hbij.self_of_nhds.2 ζ
  have hV0 : V ≠ 0 := fun h => hζ (by rw [← hV, h, map_zero])
  have hquotV : TosC11c.hessQuot A u e z₀ ζ = Real.pi * quot ψ a 0 V := by
    rw [← hV, ← hgood.self_of_nhds.1 V, hΦ0]
  have hattℓ : ∃ V, V ≠ 0 ∧ quot ψ a 0 V * Real.exp (wℓ 0) = M / Real.pi := by
    refine ⟨V, hV0, ?_⟩
    rw [eq_div_iff Real.pi_ne_zero, ← hζM, hquotV]
    simp only [hwℓdef, hΦ0]
    ring
  -- the local estimate
  have hj2' : ∀ v, ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v‖ ≤ Cg * ‖v‖ := fun v =>
    (hj2 v).trans (mul_le_mul_of_nonneg_right hCg2 (norm_nonneg _))
  have hj3' : ∀ v v', ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v'‖ ≤ Cg * ‖v‖ * ‖v'‖ :=
    fun v v' => (hj3 v v').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCg3 (norm_nonneg _)) (norm_nonneg _))
  have hΛ := hloc ψ a Fℓ wℓ β (M / Real.pi) r hN ha hFℓ hβ hj2' hj3' heq hpos hdiag0 hrR hDF hD2F
    hs0 hwℓ hmax hattℓ
  -- conclusion
  have hq0 : quot ψ a 0 V ≤ Λℓ := by
    rw [quot_eq hN.smooth, hN.cov_zero, hN.metric_zero, real_inner_self_eq_norm_sq,
      div_le_iff₀ (pow_pos (norm_pos_iff.mpr hV0) 2)]
    exact hΛ V
  rw [← hζM, hquotV]
  have hexp := Real.exp_pos (w (e.val.symm z₀))
  have := mul_le_mul_of_nonneg_left hq0 Real.pi_pos.le
  nlinarith

end SGPT.Envelopes.TosC11e
