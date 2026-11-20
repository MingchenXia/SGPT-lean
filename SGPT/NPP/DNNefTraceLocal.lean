import SGPT.Envelopes.LapClassKahler
import SGPT.Okounkov.TranscendentalWNEnvelopeLocal
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# The Tsuji-weighted trace estimate at a maximum point

Lane DN (`thm:DNT23_C11bar`, nef and big classes).  Source: Berman, *From Monge–Ampère equations
to envelopes and geodesic rays in the zero temperature limit*, Math. Z. 291 (2019),
arXiv:1307.3008v3 (`references/berman19-zero-temperature`), proof of Proposition 3.5 ("nef and
big" Laplacian estimate) and Remark 3.6: the maximum principle is applied to
`log tr_ω ω_u - a(u - ψ)` where `ψ` is the potential of a Kähler current (Tsuji's trick).

The potential `ψ` is only quasi-plurisubharmonic, so the maximum point is handled by a
**touching argument**: at the maximum, `ψ` is touched from above by a smooth function, which
then has nonnegative Levi form (`SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.leviForm_nonneg_of_contact`).  This replaces the
local maximum of the smooth case (`LapClass.levTr_le_of_isLocalMax_gen`) by the weaker condition
"the Levi form of the test function is `≤ 0`" (`levTr_le_of_leviForm_nonpos`).

* `levTr_le_of_leviForm_nonpos`: the flat maximum principle step under the Levi condition.
* `traceForm_le_of_tsujiMax`: in the normal coordinates of the metric `ω` at a maximum point
  `y₀` of `log tr_ω(A + ddᶜu)/a - u + ψ`, with `A = η + κ'`, `ψ` an `η`-psh potential finite at
  `y₀`, `cκ ω ≤ κ' ≤ Cκ ω`, the equation `(A + ddᶜu)^N = e^{β(u - F)} ω^N` and
  `Δ_ω F + tr_ω η ≤ S`: `tr_ω(A + ddᶜu)(y₀) ≤ 2(N Cκ + S)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Metric MeasureTheory
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.NPP.DNNef

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent HolomorphicMixedDensity
open SGPT.Analysis.KahlerNormal SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg
open AubinYauEstimate AubinYauUniformConstants SGPT.Envelopes.LapClass

/-! ### The flat step under a Levi condition -/

section Flat

variable {n : ℕ}

/-- **The maximum principle step, Levi form version.**  As
`LapClass.levTr_le_of_isLocalMax_gen`, with the local maximum of
`log tr Hess ψ - 2K‖w‖² - a(ψ - σ)` at `0` replaced by the nonpositivity of its Levi form at `0`
(which is what a touching argument provides). -/
theorem levTr_le_of_leviForm_nonpos (hn : 0 < n) {ψ σ F : ComplexModel n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hσ : ContDiff ℝ ∞ σ) (hpos : (complexHessian ψ 0).PosDef)
    {γ T β K a C₁ S : ℝ} (hγ : 0 < γ) (hσlow : ∀ v, γ * ‖v‖ ^ 2 ≤ leviForm σ 0 v)
    (hσT : levTr σ 0 ≤ T) (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁) (ha : 2 * K + C₁ ≤ a * γ)
    (hβ : 2 * a * n < β)
    (hdetlow : β * (levTr ψ 0 - levTr σ 0 - levTr F 0) - C₁ ≤
      levTr (fun w => Real.log (complexHessian ψ w).det.re) 0)
    (hFS : levTr F 0 ≤ S)
    (hlevi : ∀ v, leviForm
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0 v ≤ 0) :
    levTr ψ 0 ≤ 2 * (T + S) := by
  classical
  set P := (complexHessian ψ 0)⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.inv.posSemidef
  obtain ⟨m, w, hw, htrP⟩ := exists_trace_eq_sum_leviForm hP
  set trP := P.trace.re with htrPdef
  have htrP0 : 0 ≤ trP := by rw [htrP]; positivity
  have hψ2 := AubinYauLocalStep.contDiffAt_two hψ (0 : ComplexModel n)
  have hσ2 := AubinYauLocalStep.contDiffAt_two hσ (0 : ComplexModel n)
  have hℓpos : ∀ p : Fin n, 0 < leviForm ψ 0 (coordinateVector p) := by
    intro p
    have hne : (Pi.single p (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have := congrFun h p
      simp at this
    have h1 := hpos.re_dotProduct_pos hne
    have h2 := dotProduct_mulVec_complexHessian_eq_leviForm hψ2 (Pi.single p (1 : ℂ))
    rw [coordCombination_single] at h2
    rw [h2] at h1
    simpa using h1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hℓ₀ : 0 < levTr ψ 0 := Finset.sum_pos (fun p _ => hℓpos p) hne
  have hnℓ : (n : ℝ) ≤ levTr ψ 0 * trP := by
    have h1 : ∀ p : Fin n, 1 ≤ leviForm ψ 0 (coordinateVector p) * trP := by
      intro p
      have hnorm : ‖(coordinateVector p : ComplexModel n)‖ = 1 := by
        simp [coordinateVector]
      exact AubinYauLocalStep.one_le_leviForm_mul_re_trace_inv hψ2 hpos hnorm
    have h2 := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h1 p
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← Finset.sum_mul] at h2
    exact h2
  have hL : ContDiff ℝ ∞ (levTr ψ) := by
    have : levTr ψ = fun y => ∑ p, leviForm ψ y (coordinateVector p) := rfl
    rw [this]
    exact ContDiff.sum fun p _ => BlockiLocalEstimate.contDiff_leviForm hψ _
  have hlogL : ContDiffAt ℝ 2 (fun w => Real.log (levTr ψ w)) 0 :=
    (AubinYauLocalStep.contDiffAt_two hL 0).log hℓ₀.ne'
  have hsq : ContDiffAt ℝ 2 (fun w : ComplexModel n => ‖w‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hΘ2 : ContDiffAt ℝ 2
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0 :=
    (hlogL.sub (contDiffAt_const.mul hsq)).sub (contDiffAt_const.mul (hψ2.sub hσ2))
  have hT0 : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re ≤ 0 := by
    rw [hw _ 0 hΘ2]
    exact Finset.sum_nonpos fun i _ => hlevi (w i)
  have hlevΘ : ∀ v, leviForm (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 -
      a * (ψ w - σ w)) 0 v = leviForm (fun w => Real.log (levTr ψ w)) 0 v -
        2 * K * ‖v‖ ^ 2 - a * (leviForm ψ 0 v - leviForm σ 0 v) := by
    intro v
    rw [SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' (hlogL.sub (contDiffAt_const.mul hsq))
      (contDiffAt_const.mul (hψ2.sub hσ2)),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL (contDiffAt_const.mul hsq),
      leviForm_const_mul hsq, leviForm_const_mul (hψ2.sub hσ2),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hψ2 hσ2, leviForm_norm_sq]
  have hTΘ : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re =
      (P * complexHessian (fun w => Real.log (levTr ψ w)) 0).trace.re - 2 * K * trP -
        a * ((P * complexHessian ψ 0).trace.re - (P * complexHessian σ 0).trace.re) := by
    rw [hw _ 0 hΘ2, hw _ 0 hlogL, hw _ 0 hψ2, hw _ 0 hσ2, htrP]
    simp only [hlevΘ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hTψ : (P * complexHessian ψ 0).trace.re = n := by
    rw [hPdef, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.det_pos.ne'),
      Matrix.trace_one]
    simp
  have hTσ : γ * trP ≤ (P * complexHessian σ 0).trace.re := by
    rw [hw _ 0 hσ2, htrP, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hσlow (w i)
  have hflat := levTr_logDet_div_le hn hψ hpos
  have hflat' := (div_le_div_of_nonneg_right hdetlow hℓ₀.le).trans hflat
  have hmain : (β * (levTr ψ 0 - levTr σ 0 - levTr F 0) - C₁) / levTr ψ 0 -
      2 * K * trP - a * (n - γ * trP) ≤ 0 := by
    have := hT0
    rw [hTΘ, hTψ] at this
    have ha0 : 0 ≤ a := by
      have : 0 ≤ a * γ := le_trans (by positivity) ha
      exact nonneg_of_mul_nonneg_left this hγ
    nlinarith [mul_le_mul_of_nonneg_left hTσ ha0]
  rw [div_sub' hℓ₀.ne', div_sub' hℓ₀.ne', div_le_iff₀ hℓ₀, zero_mul] at hmain
  by_contra hcon
  push Not at hcon
  have ha0 : 0 ≤ a := by
    have : 0 ≤ a * γ := le_trans (by positivity) ha
    exact nonneg_of_mul_nonneg_left this hγ
  have hβ0 : 0 < β := by
    have : 0 ≤ 2 * a * n := by positivity
    linarith
  have hC1 : C₁ ≤ C₁ * (levTr ψ 0 * trP) := by
    have : (1 : ℝ) ≤ levTr ψ 0 * trP := le_trans (by exact_mod_cast hn) hnℓ
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : β * (levTr ψ 0 - T - S) ≤ a * n * levTr ψ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hℓ₀.le htrP0)]
  have h2 : β * levTr ψ 0 / 2 < β * (levTr ψ 0 - T - S) := by nlinarith
  have h3 : a * n * levTr ψ 0 < β * levTr ψ 0 / 2 := by nlinarith
  linarith

end Flat


/-! ### The chart step at a Tsuji maximum point -/

section Estimate

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The trace bound at a Tsuji maximum point** (Berman 2019, proof of Proposition 3.5, the
"nef and big" case, with a Kähler-current weight).  Let `ω = w` (metric), `A` a Kähler form with
`A = η + κ'` in the chart `E` around `y₀ = E⁻¹ z₀`, `ψ` an `η`-psh potential with `ψ(y₀)` finite,
`u` smooth with `A + ddᶜu` Kähler and `(A + ddᶜu)^N = e^{β(u - F)} ω^N`.  If `y₀` maximizes
`log tr_ω(A + ddᶜu)/a - u + ψ`, then `tr_ω(A + ddᶜu)(y₀) ≤ 2(N Cκ + S)`, where
`cκ ω ≤ κ' ≤ Cκ ω` at `z₀` (through the local potentials) and `Δ_ω F + tr_ω η ≤ S` at `y₀`. -/
theorem traceForm_le_of_tsujiMax (hN : 0 < N) (w A : KahlerBackground N Y)
    (η : ClosedRealOneOneForm N Y) {β : ℝ} {F : Y → ℝ} (hF : ChartSmooth (n := N) F)
    {u : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (huK : (A.form + ddcClosedForm u hu).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
        Real.exp (β * (u (e.val.symm z) - F (e.val.symm z))) *
          actualTopPowerDensity (w.form.val.coeff e z))
    {ψ : Y → EReal} {E : ComplexChart N Y}
    {Wω Wκ Wη : Set (ComplexModel N)} {ρω ρκ ρη : ComplexModel N → ℝ}
    (hpotω : IsSmoothLocalPotential w.form.val E Wω ρω)
    (hpotκ : IsSmoothLocalPotential A.form.val E Wκ ρκ)
    (hpotη : IsSmoothLocalPotential η.val E Wη ρη)
    (hψη : PlurisubharmonicOn (fun z => chartFunction ψ E z + (ρη z : EReal)) Wη)
    {ρω' ρκ' ρη' u' : ComplexModel N → ℝ}
    (hρω' : ContDiff ℝ ∞ ρω') (hρκ' : ContDiff ℝ ∞ ρκ') (hρη' : ContDiff ℝ ∞ ρη')
    (hu' : ContDiff ℝ ∞ u')
    {V : Set (ComplexModel N)} (hVo : IsOpen V) (hVWω : V ⊆ Wω) (hVWκ : V ⊆ Wκ)
    (hVWη : V ⊆ Wη)
    (hρω'eq : EqOn ρω' ρω V) (hρκ'eq : EqOn ρκ' ρκ V) (hρη'eq : EqOn ρη' ρη V)
    (hu'eq : EqOn u' (fun w => ρκ w + u (E.val.symm w)) V) {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ V) {K₁ CA Kb a S cκ Cκ : ℝ} (hK₁ : 0 ≤ K₁) (hKb : 0 ≤ Kb) (hcκ : 0 < cκ)
    (ha0 : 0 < a)
    (hlog : ∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 →
      -K₁ ≤ leviForm (fun y => Real.log (complexHessian ρω' y).det.re) z₀ ζ)
    (hκlow : ∀ v, cκ * leviForm ρω' z₀ v ≤ leviForm ρκ' z₀ v - leviForm ρη' z₀ v)
    (hκup : ∀ v, leviForm ρκ' z₀ v - leviForm ρη' z₀ v ≤ Cκ * leviForm ρω' z₀ v)
    (L : ComplexModel N →L[ℂ] ComplexModel N)
    {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}
    (hsymm : ∀ p u, c p u = c u p) (hLbd : ∀ x, ‖L x‖ ≤ CA * ‖x‖)
    (hJ0 : IsUnit (jacobianMatrix (normalCoord z₀ L c) 0).det)
    (h0 : normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) 0) = 1)
    (hbar : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ∀ v : Fin N → ℂ,
      (star v ⬝ᵥ (normalizedHermitianMatrix
        (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) x) *ᵥ v)).re ≤
          (1 + Kb * ‖x‖ ^ 2) * (star v ⬝ᵥ v).re)
    (hFS : laplacian w.form.val F (E.val.symm z₀) + traceForm w.form.val η.val (E.val.symm z₀) ≤ S)
    (ha : 2 * Kb + K₁ * N * CA ^ 2 ≤ a * cκ) (hβ : 2 * a * N < β)
    {r₀ : ℝ} (hψ0 : ψ (E.val.symm z₀) = (r₀ : EReal))
    (hmax : ∀ y, ((Real.log (traceForm w.form.val (A.form + ddcClosedForm u hu).val y) / a - u y :
        ℝ) : EReal) + ψ y ≤
      ((Real.log (traceForm w.form.val (A.form + ddcClosedForm u hu).val (E.val.symm z₀)) / a -
        u (E.val.symm z₀) : ℝ) : EReal) + ψ (E.val.symm z₀)) :
    traceForm w.form.val (A.form + ddcClosedForm u hu).val (E.val.symm z₀) ≤
      2 * (Cκ * N + S) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  have hVt : V ⊆ E.val.target := hVWω.trans hpotω.2.1
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  set Tr := traceForm w.form.val (A.form + ddcClosedForm u hu).val with hTrdef
  have hα : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      IsOneOne ((A.form + ddcClosedForm u hu).val.coeff e z) :=
    fun e z hz => (huK.1 e z hz).1
  have hαη : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → IsOneOne (η.val.coeff e z) :=
    fun e z hz => η.property.2 e z hz
  -- Hessians of the local potentials
  have hHω : ∀ z ∈ V, complexHessian ρω' z = normalizedHermitianMatrix (w.form.val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρω'eq),
      ← normalizedHermitianMatrix_smoothDDC
        (contDiffAt_two_of_contDiffOn hpotω.1 hpotω.2.2.1 (hVWω hz)), hpotω.2.2.2 (hVWω hz)]
  have hHη : ∀ z ∈ V, complexHessian ρη' z = normalizedHermitianMatrix (η.val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρη'eq),
      ← normalizedHermitianMatrix_smoothDDC
        (contDiffAt_two_of_contDiffOn hpotη.1 hpotη.2.2.1 (hVWη hz)), hpotη.2.2.2 (hVWη hz)]
  have hκ2 : ∀ z ∈ V, ContDiffAt ℝ 2 ρκ z := fun z hz =>
    contDiffAt_two_of_contDiffOn hpotκ.1 hpotκ.2.2.1 (hVWκ hz)
  have hHκ0 : ∀ z ∈ V, complexHessian ρκ z = normalizedHermitianMatrix (A.form.val.coeff E z) := by
    intro z hz
    rw [← normalizedHermitianMatrix_smoothDDC (hκ2 z hz), hpotκ.2.2.2 (hVWκ hz)]
  have hHu : ∀ z ∈ V, complexHessian u' z =
      normalizedHermitianMatrix ((A.form + ddcClosedForm u hu).val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      normalizedHermitianMatrix_add_ddc A hu (hVt hz), ← hHκ0 z hz]
    exact AubinYauLocalStep.complexHessian_fun_add (hκ2 z hz)
      (contDiffAt_two_of_contDiffOn E.val.open_target (hu E) (hVt hz))
  have hρω'V : ContDiffOn ℝ 2 ρω' V := hρω'.contDiffOn.of_le h2
  have hρη'V : ContDiffOn ℝ 2 ρη' V := hρη'.contDiffOn.of_le h2
  have hu'V : ContDiffOn ℝ 2 u' V := hu'.contDiffOn.of_le h2
  -- the normal coordinate map
  have hΦ0 : normalCoord z₀ L c 0 = z₀ := normalCoord_zero z₀ L c
  have hΦc : ContDiff ℂ ∞ (normalCoord z₀ L c) := contDiff_normalCoord z₀ L c
  have hΦcR : ContDiff ℝ ∞ (normalCoord z₀ L c) := hΦc.restrict_scalars ℝ
  have hU₀ : IsOpen (normalCoord z₀ L c ⁻¹' V) := hVo.preimage hΦcR.continuous
  have h0U₀ : (0 : ComplexModel N) ∈ normalCoord z₀ L c ⁻¹' V := by
    show normalCoord z₀ L c 0 ∈ V
    rw [hΦ0]; exact hz₀
  have hdetJc : ContDiff ℂ ∞ (fun w => (jacobianMatrix (normalCoord z₀ L c) w).det) :=
    contDiff_det_jacobianMatrix z₀ L hsymm
  have hevJ : ∀ᶠ w in 𝓝 (0 : ComplexModel N),
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det := by
    filter_upwards [hdetJc.continuous.continuousAt.eventually_ne hJ0.ne_zero] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  -- the functions in the coordinates `w`
  obtain ⟨σt, hσt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρω' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨κt, hκt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρκ' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ηt, hηt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρη' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ψt, hψt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => u' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ut, hut⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => u (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  obtain ⟨Ft, hFt⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => F (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  have hσs : ContDiff ℝ ∞ σt := by rw [hσt]; exact hρω'.comp hΦcR
  have hκs : ContDiff ℝ ∞ κt := by rw [hκt]; exact hρκ'.comp hΦcR
  have hηs : ContDiff ℝ ∞ ηt := by rw [hηt]; exact hρη'.comp hΦcR
  have hψs : ContDiff ℝ ∞ ψt := by rw [hψt]; exact hu'.comp hΦcR
  have hcomp2 : ∀ {v : Y → ℝ}, ChartSmooth (n := N) v → ∀ w,
      normalCoord z₀ L c w ∈ V →
      ContDiffAt ℝ 2 (fun x => v (E.val.symm (normalCoord z₀ L c x))) w := by
    intro v hv w hw
    exact ContDiffAt.comp (g := fun z => v (E.val.symm z)) w
      (contDiffAt_two_of_contDiffOn E.val.open_target (hv E) (hVt hw))
      (hΦcR.contDiffAt.of_le h2)
  have hut2 : ContDiffAt ℝ 2 ut 0 := by rw [hut]; exact hcomp2 hu 0 h0U₀
  have hFt2 : ContDiffAt ℝ 2 Ft 0 := by rw [hFt]; exact hcomp2 hF 0 h0U₀
  -- Hessians in the coordinates `w`
  have hHσJ : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian σt x =
      (jacobianMatrix (normalCoord z₀ L c) x)ᵀ *
        normalizedHermitianMatrix (w.form.val.coeff E (normalCoord z₀ L c x)) *
          (jacobianMatrix (normalCoord z₀ L c) x).map (starRingEnd ℂ) := by
    intro x hx
    rw [hσt, complexHessian_comp_normalCoord z₀ L hVo hρω'V hx, hHω _ hx]
  have hHσpb : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian σt x =
      normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) x) := by
    intro x hx
    rw [hσt]
    exact complexHessian_comp_potential z₀ L w.isKahler hVo hVt hρω'V hHω hsymm hx
  have hσ0 : complexHessian σt 0 = 1 := by rw [hHσpb 0 h0U₀, h0]
  have hHηJ : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian ηt x =
      (jacobianMatrix (normalCoord z₀ L c) x)ᵀ *
        normalizedHermitianMatrix (η.val.coeff E (normalCoord z₀ L c x)) *
          (jacobianMatrix (normalCoord z₀ L c) x).map (starRingEnd ℂ) := by
    intro x hx
    rw [hηt, complexHessian_comp_normalCoord z₀ L hVo hρη'V hx, hHη _ hx]
  have hHψJ : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian ψt x =
      (jacobianMatrix (normalCoord z₀ L c) x)ᵀ * complexHessian u' (normalCoord z₀ L c x) *
        (jacobianMatrix (normalCoord z₀ L c) x).map (starRingEnd ℂ) := by
    intro x hx
    rw [hψt]
    exact complexHessian_comp_normalCoord z₀ L hVo hu'V hx
  have hHσpd : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det → (complexHessian σt x).PosDef := by
    intro x hx hJ
    rw [hHσJ x hx]
    exact posDef_transpose_mul_mul_conj (posDef_coeff hg (hVt hx)) hJ
  have hHψpd : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det → (complexHessian ψt x).PosDef := by
    intro x hx hJ
    rw [hHψJ x hx, hHu _ hx]
    exact posDef_transpose_mul_mul_conj (posDef_coeff huK.1 (hVt hx)) hJ
  have hψeq : ∀ x, normalCoord z₀ L c x ∈ V → ψt x = κt x + ut x := fun x hx => by
    rw [hψt, hκt, hut]
    simp only
    rw [hu'eq hx, hρκ'eq hx]
  -- the trace in the coordinates `w`
  have hNtr : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det →
      Tr (E.val.symm (normalCoord z₀ L c x)) =
        ((complexHessian σt x)⁻¹ * complexHessian ψt x).trace.re := by
    intro x hx hJ
    have hzt := hVt hx
    rw [hTrdef, traceForm_eq hg hα (E.val.map_target hzt), E.val.right_inv hzt, chartTrace,
      hHσJ x hx, hHψJ x hx, hHu _ hx, trace_inv_mul_congr hJ]
  have hNη : traceForm w.form.val η.val (E.val.symm z₀) =
      ((complexHessian σt 0)⁻¹ * complexHessian ηt 0).trace.re := by
    have hzt := hVt hz₀
    have hx : normalCoord z₀ L c 0 ∈ V := h0U₀
    rw [traceForm_eq hg hαη (E.val.map_target hzt), E.val.right_inv hzt, chartTrace,
      hHσJ 0 hx, hHηJ 0 hx, hΦ0, trace_inv_mul_congr hJ0]
  have hlapσ : ∀ (v : Y → ℝ) (hv : ChartSmooth (n := N) v) (x : ComplexModel N),
      normalCoord z₀ L c x ∈ V → IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det →
      laplacian w.form.val v (E.val.symm (normalCoord z₀ L c x)) =
        ((complexHessian σt x)⁻¹ *
          complexHessian (fun y => v (E.val.symm (normalCoord z₀ L c y))) x).trace.re := by
    intro v hv x hx hJ
    rw [hσt]
    exact laplacian_normalCoord z₀ L hg hVo hVt hρω'V hHω hv hx hJ
  have hy0 : E.val.symm (normalCoord z₀ L c 0) = E.val.symm z₀ := by rw [hΦ0]
  have hℓ0 : levTr ψt 0 = Tr (E.val.symm z₀) := by
    rw [← hy0, hNtr 0 h0U₀ hJ0, hσ0, inv_one, Matrix.one_mul,
      re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs 0)]
  have hℓpos0 : 0 < levTr ψt 0 := hℓ0 ▸ traceForm_pos hN hg huK _
  -- the barrier inequality near `0`
  have hLs : ContDiff ℝ ∞ (levTr ψt) := by
    have : levTr ψt = fun y => ∑ q, leviForm ψt y (coordinateVector q) := rfl
    rw [this]
    exact ContDiff.sum fun q _ => BlockiLocalEstimate.contDiff_leviForm hψs _
  have hevℓ : ∀ᶠ x in 𝓝 (0 : ComplexModel N), 0 < levTr ψt x :=
    continuousAt_const.eventually_lt hLs.continuous.continuousAt hℓpos0
  have hbarrier : ∀ᶠ x in 𝓝 (0 : ComplexModel N),
      Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2 ≤ Real.log (Tr (E.val.symm (normalCoord z₀ L c x))) := by
    have hsmall : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Kb * ‖x‖ ^ 2 < 1 / 2 := by
      have hc : Continuous fun x : ComplexModel N => Kb * ‖x‖ ^ 2 := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [hbar, hevJ, hU₀.mem_nhds h0U₀, hevℓ, hsmall] with x hb hJ hxU hℓx hsm
    have hb' : ∀ v : Fin N → ℂ, (star v ⬝ᵥ (complexHessian σt x *ᵥ v)).re ≤
        (1 + Kb * ‖x‖ ^ 2) * (star v ⬝ᵥ v).re := by
      rw [hHσpb x hxU]; exact hb
    have hb1 := one_sub_mul_re_trace_le (hHσpd x hxU hJ) (hHψpd x hxU hJ).posSemidef hb'
    rw [re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs x),
      ← hNtr x hxU hJ] at hb1
    have hδ0 : 0 ≤ Kb * ‖x‖ ^ 2 := by positivity
    have hlog1 : Real.log (levTr ψt x) - 2 * (Kb * ‖x‖ ^ 2) ≤
        Real.log ((1 - Kb * ‖x‖ ^ 2) * levTr ψt x) := by
      rw [Real.log_mul (by linarith) hℓx.ne']
      linarith [log_one_sub_ge hδ0 hsm.le]
    have hlog2 : Real.log ((1 - Kb * ‖x‖ ^ 2) * levTr ψt x) ≤
        Real.log (Tr (E.val.symm (normalCoord z₀ L c x))) :=
      Real.log_le_log (mul_pos (by linarith) hℓx) hb1
    linarith
  -- the touching argument: `ψ` is touched from above at `y₀`
  set g : ComplexModel N → ℝ := fun x =>
    (Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2) / a - (ψt x - κt x) with hgdef
  have hu_x : ∀ x, normalCoord z₀ L c x ∈ V → u (E.val.symm (normalCoord z₀ L c x)) = ψt x - κt x :=
    fun x hxU => by rw [hψeq x hxU, hut]; ring
  have hu_0 : u (E.val.symm z₀) = ψt 0 - κt 0 := by
    have := hu_x 0 h0U₀
    rwa [hΦ0] at this
  have htouch : ∀ᶠ x in 𝓝 (0 : ComplexModel N),
      ψ (E.val.symm (normalCoord z₀ L c x)) ≤ ((r₀ + g 0 - g x : ℝ) : EReal) := by
    filter_upwards [hbarrier, hU₀.mem_nhds h0U₀] with x hbx hxU
    have hm := hmax (E.val.symm (normalCoord z₀ L c x))
    rw [hψ0, ← EReal.coe_add] at hm
    have hle : g x ≤ Real.log (Tr (E.val.symm (normalCoord z₀ L c x))) / a -
        u (E.val.symm (normalCoord z₀ L c x)) := by
      rw [hgdef, hu_x x hxU]
      simp only
      have := div_le_div_of_nonneg_right hbx ha0.le
      linarith
    have hg0 : g 0 = Real.log (Tr (E.val.symm z₀)) / a - u (E.val.symm z₀) := by
      rw [hgdef, hu_0, ← hℓ0]
      simp
    -- move the real parts across
    set R := Real.log (Tr (E.val.symm (normalCoord z₀ L c x))) / a -
      u (E.val.symm (normalCoord z₀ L c x)) with hR
    have hm' : ψ (E.val.symm (normalCoord z₀ L c x)) ≤
        (((Real.log (Tr (E.val.symm z₀)) / a - u (E.val.symm z₀) + r₀) - R : ℝ) : EReal) := by
      have hne : ((R : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hne' : ((R : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      rw [EReal.coe_sub]
      exact EReal.le_sub_iff_add_le (Or.inl hne) (Or.inl hne') |>.mpr
        (by rw [add_comm]; exact hm)
    refine hm'.trans (EReal.coe_le_coe_iff.mpr ?_)
    rw [hg0]
    linarith
  -- the psh germ in the coordinates `w`
  have hpsh : PlurisubharmonicOn (fun x => ψ (E.val.symm (normalCoord z₀ L c x)) +
      (ρη (normalCoord z₀ L c x) : EReal)) (normalCoord z₀ L c ⁻¹' V) := by
    have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (F := normalCoord z₀ L c)
      hU₀ (hΦc.differentiable (by simp)).differentiableOn (fun x hx => hVWη hx) hψη
    simpa only [chartFunction] using h
  have hlevq : ∀ v, 0 ≤ leviForm (fun x => r₀ + g 0 - g x + ηt x) 0 v := by
    -- the open set where the test function is smooth
    set W₀ : Set (ComplexModel N) := normalCoord z₀ L c ⁻¹' V ∩ {x | 0 < levTr ψt x} with hW₀
    have hW₀o : IsOpen W₀ := hU₀.inter (isOpen_lt continuous_const hLs.continuous)
    have h0W₀ : (0 : ComplexModel N) ∈ W₀ := ⟨h0U₀, hℓpos0⟩
    have hq : ContDiffOn ℝ ∞ (fun x => r₀ + g 0 - g x + ηt x) W₀ := by
      have hlogs : ContDiffOn ℝ ∞ (fun x => Real.log (levTr ψt x)) W₀ :=
        hLs.contDiffOn.log fun x hx => hx.2.ne'
      have hgs : ContDiffOn ℝ ∞ g W₀ := by
        rw [hgdef]
        exact ((hlogs.sub (contDiffOn_const.mul ((contDiff_norm_sq ℝ).contDiffOn))).div_const a).sub
          (hψs.contDiffOn.sub hκs.contDiffOn)
      exact ((contDiffOn_const.sub hgs).add hηs.contDiffOn)
    refine fun v => SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.leviForm_nonneg_of_contact hW₀o (hpsh.mono inter_subset_left)
      hq h0W₀ ?_ ?_ v
    · filter_upwards [htouch, hU₀.mem_nhds h0U₀] with x hx hxU
      have hηx : ρη (normalCoord z₀ L c x) = ηt x := by rw [hηt]; exact (hρη'eq hxU).symm
      rw [hηx]
      calc ψ (E.val.symm (normalCoord z₀ L c x)) + ((ηt x : ℝ) : EReal)
          ≤ ((r₀ + g 0 - g x : ℝ) : EReal) + ((ηt x : ℝ) : EReal) := add_le_add hx le_rfl
        _ = ((r₀ + g 0 - g x + ηt x : ℝ) : EReal) := by rw [EReal.coe_add]
    · have hη0 : ρη (normalCoord z₀ L c 0) = ηt 0 := by rw [hηt]; exact (hρη'eq h0U₀).symm
      rw [hη0, hΦ0, hψ0, ← EReal.coe_add]
      congr 1
      ring
  -- convert into the Levi condition of the flat step
  have hlogL2 : ContDiffAt ℝ 2 (fun x => Real.log (levTr ψt x)) 0 :=
    (AubinYauLocalStep.contDiffAt_two hLs 0).log hℓpos0.ne'
  have hsq : ContDiffAt ℝ 2 (fun w : ComplexModel N => ‖w‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hψ2 := AubinYauLocalStep.contDiffAt_two hψs (0 : ComplexModel N)
  have hκ2' := AubinYauLocalStep.contDiffAt_two hκs (0 : ComplexModel N)
  have hη2' := AubinYauLocalStep.contDiffAt_two hηs (0 : ComplexModel N)
  have hlevi : ∀ v, leviForm (fun x => Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2 -
      a * (ψt x - (κt x - ηt x))) 0 v ≤ 0 := by
    intro v
    have hq := hlevq v
    have hA : ContDiffAt ℝ 2 (fun x => Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2) 0 :=
      hlogL2.sub (contDiffAt_const.mul hsq)
    have hB : ContDiffAt ℝ 2 (fun x => ψt x - κt x) 0 := hψ2.sub hκ2'
    have hG2 : ContDiffAt ℝ 2 g 0 := (hA.div_const a).sub hB
    -- the Levi form of the test function
    have e1 : leviForm (fun x => r₀ + g 0 - g x + ηt x) 0 v =
        -leviForm g 0 v + leviForm ηt 0 v := by
      have hfun : (fun x => r₀ + g 0 - g x + ηt x) =
          (ηt + -g) + fun _ => r₀ + g 0 := by
        funext x; simp only [Pi.add_apply, Pi.neg_apply]; ring
      rw [hfun, leviForm_add (u := ηt + -g) (v := fun _ => r₀ + g 0) (hη2'.add hG2.neg)
        contDiffAt_const, leviForm_const, leviForm_add (u := ηt) (v := -g) hη2' hG2.neg,
        leviForm_neg]
      ring
    have e2 : leviForm g 0 v = (leviForm (fun x => Real.log (levTr ψt x)) 0 v -
        2 * Kb * ‖v‖ ^ 2) / a - (leviForm ψt 0 v - leviForm κt 0 v) := by
      have hfun : g = (fun x => a⁻¹ * (Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2) -
          (ψt x - κt x)) := by
        funext x; rw [hgdef]; simp only; rw [div_eq_inv_mul]
      rw [hfun, SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' (contDiffAt_const.mul hA) hB,
        leviForm_const_mul hA, SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL2
        (contDiffAt_const.mul hsq), leviForm_const_mul hsq, leviForm_norm_sq,
        SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hψ2 hκ2', div_eq_inv_mul]
    have e3 : leviForm (fun x => Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2 -
        a * (ψt x - (κt x - ηt x))) 0 v = leviForm (fun x => Real.log (levTr ψt x)) 0 v -
          2 * Kb * ‖v‖ ^ 2 - a * (leviForm ψt 0 v - (leviForm κt 0 v - leviForm ηt 0 v)) := by
      rw [SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hA
        (contDiffAt_const.mul (hψ2.sub (hκ2'.sub hη2'))),
        SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL2 (contDiffAt_const.mul hsq),
        leviForm_const_mul hsq, leviForm_norm_sq, leviForm_const_mul (hψ2.sub (hκ2'.sub hη2')),
        SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hψ2 (hκ2'.sub hη2'),
        SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hκ2' hη2']
    rw [e1, e2] at hq
    rw [e3]
    have : (leviForm (fun x => Real.log (levTr ψt x)) 0 v - 2 * Kb * ‖v‖ ^ 2) / a -
        (leviForm ψt 0 v - leviForm κt 0 v) - leviForm ηt 0 v ≤ 0 := by linarith
    have h' := mul_le_mul_of_nonneg_left this ha0.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ ha0.ne'] at h'
    linarith
  -- the determinant term
  have hdetu' : ∀ z ∈ V, (complexHessian u' z).det.re =
      Real.exp (β * (u (E.val.symm z) - F (E.val.symm z))) *
        (complexHessian ρω' z).det.re := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρω'eq),
      YauUniformEstimate.re_det_complexHessian_eq hu hpotκ (hVWκ hz), hdens E z (hVt hz),
      re_det_complexHessian_potential w hpotω (hVWω hz)]
    ring
  have hdetρpos : ∀ z ∈ V, 0 < (complexHessian ρω' z).det.re := fun z hz => by
    rw [hHω z hz]
    exact (Complex.pos_iff.mp (posDef_coeff hg (hVt hz)).det_pos).1
  have hdetdecomp : (fun x => Real.log (complexHessian ψt x).det.re) =ᶠ[𝓝 0]
      fun x => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2) +
        (β * (ut x - Ft x) +
          Real.log (complexHessian ρω' (normalCoord z₀ L c x)).det.re) := by
    filter_upwards [hevJ, hU₀.mem_nhds h0U₀] with x hJ hxU
    have hherm : (complexHessian u' (normalCoord z₀ L c x)).IsHermitian :=
      complexHessian_isHermitian (AubinYauLocalStep.contDiffAt_two hu' _)
    have hJn : ‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ.ne_zero)
    rw [hHψJ x hxU, re_det_transpose_mul_mul_conj hherm, hdetu' _ hxU,
      Real.log_mul hJn (mul_pos (Real.exp_pos _) (hdetρpos _ hxU)).ne',
      Real.log_mul (Real.exp_pos _).ne' (hdetρpos _ hxU).ne', Real.log_exp, hut, hFt]
  have hdetρc : ContDiff ℝ ∞ (fun z => (complexHessian ρω' z).det.re) :=
    Complex.reCLM.contDiff.comp (WirtingerLogDet.contDiff_det_complexHessian hρω')
  have hLρV : ContDiffOn ℝ ∞ (fun z => Real.log (complexHessian ρω' z).det.re) V :=
    hdetρc.contDiffOn.log fun z hz => (hdetρpos z hz).ne'
  have hLρΦ2 : ContDiffAt ℝ 2
      (fun x => Real.log (complexHessian ρω' (normalCoord z₀ L c x)).det.re) 0 := by
    have h1 : ContDiffAt ℝ ∞ (fun z => Real.log (complexHessian ρω' z).det.re)
        (normalCoord z₀ L c 0) := hLρV.contDiffAt (hVo.mem_nhds h0U₀)
    exact (h1.comp (0 : ComplexModel N) hΦcR.contDiffAt).of_le h2
  have hlnJ2 : ContDiffAt ℝ 2
      (fun x => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2)) 0 := by
    have h1 : ContDiff ℝ ∞ (fun x => ‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2) :=
      (hdetJc.restrict_scalars ℝ).norm_sq ℝ
    exact (h1.contDiffAt.of_le h2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ0.ne_zero))
  have hlnJ0 := levTr_log_normSq_nonneg hdetJc hJ0.ne_zero
  have hLq : ∀ q : Fin N, ‖L (coordinateVector q)‖ ≤ CA := by
    intro q
    have := hLbd (coordinateVector q)
    rwa [show ‖(coordinateVector q : ComplexModel N)‖ = 1 by simp [coordinateVector],
      mul_one] at this
  have hcomp0 : ∀ (f : ComplexModel N → ℝ), ContDiffOn ℝ ∞ f V → ∀ v,
      leviForm (fun x => f (normalCoord z₀ L c x)) 0 v = leviForm f z₀ (L v) := by
    intro f hf v
    rw [LeviFormHolomorphicComp.leviForm_comp hU₀ hVo hΦc.contDiffOn hf (fun _ hx => hx) h0U₀,
      fderiv_normalCoord_apply z₀ L hsymm, normalLinear_apply, map_zero, _root_.zero_apply,
      sub_zero, hΦ0]
  have hLρbound : -(K₁ * N * CA ^ 2) ≤
      levTr (fun x => Real.log (complexHessian ρω' (normalCoord z₀ L c x)).det.re) 0 := by
    have hterm : ∀ q : Fin N, -(K₁ * CA ^ 2) ≤ leviForm
        (fun x => Real.log (complexHessian ρω' (normalCoord z₀ L c x)).det.re) 0
        (coordinateVector q) := by
      intro q
      rw [hcomp0 _ hLρV]
      exact neg_le_leviForm_of_norm_le hK₁ hlog (hLq q)
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    unfold levTr
    linarith
  have hutr : levTr ut 0 = levTr ψt 0 - levTr κt 0 := by
    have h1 : levTr ψt 0 = levTr κt 0 + levTr ut 0 := by
      rw [levTr_congr (Filter.eventuallyEq_of_mem (hU₀.mem_nhds h0U₀) hψeq),
        levTr_add (AubinYauLocalStep.contDiffAt_two hκs 0) hut2]
    linarith
  have hsigtr : levTr (fun x => κt x - ηt x) 0 = levTr κt 0 - levTr ηt 0 :=
    levTr_sub hκ2' hη2'
  have hFtr : levTr (fun x => Ft x + ηt x) 0 = levTr Ft 0 + levTr ηt 0 :=
    levTr_add hFt2 hη2'
  have hdetlow : β * (levTr ψt 0 - levTr (fun x => κt x - ηt x) 0 -
      levTr (fun x => Ft x + ηt x) 0) - K₁ * N * CA ^ 2 ≤
      levTr (fun x => Real.log (complexHessian ψt x).det.re) 0 := by
    rw [levTr_congr hdetdecomp,
      levTr_add hlnJ2 ((contDiffAt_const.mul (hut2.sub hFt2)).add hLρΦ2),
      levTr_add (contDiffAt_const.mul (hut2.sub hFt2)) hLρΦ2,
      levTr_const_mul (hut2.sub hFt2), levTr_sub hut2 hFt2, hutr, hsigtr, hFtr]
    linarith
  have hFS0 : levTr (fun x => Ft x + ηt x) 0 ≤ S := by
    rw [hFtr]
    have hFeq : levTr Ft 0 = laplacian w.form.val F (E.val.symm z₀) := by
      rw [← re_trace_complexHessian hFt2]
      have h := hlapσ F hF 0 h0U₀ hJ0
      rw [hσ0, inv_one, Matrix.one_mul, hy0, ← hFt] at h
      exact h.symm
    have hηeq : levTr ηt 0 = traceForm w.form.val η.val (E.val.symm z₀) := by
      rw [hNη, hσ0, inv_one, Matrix.one_mul, re_trace_complexHessian hη2']
    rw [hFeq, hηeq]
    exact hFS
  -- the background `κ' = A - η` in the coordinates `w`
  have hσnorm : ∀ v, leviForm ρω' z₀ (L v) = ‖v‖ ^ 2 := by
    intro v
    rw [← leviForm_eq_norm_sq_of_complexHessian_eq_one
      (AubinYauLocalStep.contDiffAt_two hσs 0) hσ0 v, hσt]
    exact (hcomp0 ρω' hρω'.contDiffOn v).symm
  have hkap : ∀ v, leviForm (fun x => κt x - ηt x) 0 v =
      leviForm ρκ' z₀ (L v) - leviForm ρη' z₀ (L v) := by
    intro v
    rw [SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hκ2' hη2', hκt, hηt,
      hcomp0 ρκ' hρκ'.contDiffOn, hcomp0 ρη' hρη'.contDiffOn]
  have hκlow' : ∀ v, cκ * ‖v‖ ^ 2 ≤ leviForm (fun x => κt x - ηt x) 0 v := by
    intro v
    rw [hkap, ← hσnorm]
    exact hκlow (L v)
  have hκT : levTr (fun x => κt x - ηt x) 0 ≤ Cκ * N := by
    have hterm : ∀ q : Fin N, leviForm (fun x => κt x - ηt x) 0 (coordinateVector q) ≤ Cκ := by
      intro q
      rw [hkap]
      refine (hκup _).trans ?_
      rw [hσnorm, show ‖(coordinateVector q : ComplexModel N)‖ = 1 by simp [coordinateVector]]
      simp
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    unfold levTr
    linarith
  have hfinal := levTr_le_of_leviForm_nonpos hN hψs (hκs.sub hηs) (hHψpd 0 h0U₀ hJ0) hcκ
    hκlow' hκT hKb (by positivity) ha hβ hdetlow hFS0 hlevi
  rw [← hℓ0]
  exact hfinal

end Estimate

end SGPT.NPP.DNNef
