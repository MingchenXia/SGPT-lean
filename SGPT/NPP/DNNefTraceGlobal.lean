import SGPT.NPP.DNNefTraceLocal

/-!
# The Tsuji-weighted trace estimate, uniform version

Lane DN (`thm:DNT23_C11bar`, nef and big classes).  Source: Berman 2019
(`references/berman19-zero-temperature`), proof of Proposition 3.5 and Remark 3.6: for a Kähler
current `η + ddᶜψ` (here: `ψ` an `η`-psh potential) the maximum principle applied to
`log tr_ω ω_u - a(u - ψ)` gives

  `tr_ω(A + ddᶜu) ≤ 2(T + S) e^{a(u - ψ - m)}`,  `m ≤ u - ψ`,

for every Kähler background `A` with `ω₀ ≤ A - η ≤ ω₀ + ω`, every `β ≥ β₀`, every smooth `u` with
`(A + ddᶜu)^N = e^{β(u - F)} ω^N` and every smooth `F` with `Δ_ω F + tr_ω η ≤ S`.  The constants
`a, T, β₀` depend only on `(Y, ω, ω₀)`, **not** on `A` or `η`: this uniformity is what allows the
approximation of a nef class by Kähler classes.

* `tsuji_traceForm_le`: the estimate.
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

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The coefficient of a form on a complex line is the Levi form of a local potential, over `π`. -/
theorem coeff_line_eq_leviForm_of_potential {a : SmoothRealForm N Y 2} {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ} (hpot : IsSmoothLocalPotential a e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) (v : ComplexModel N) :
    a.coeff e z ![v, Complex.I • v] = leviForm ρ z v / Real.pi := by
  rw [← hpot.2.2.2 hz, smoothDDC_complexDiagonal_eq_leviForm
    (contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hz)]

/-- The same, for a smooth function agreeing with the potential near `z`. -/
theorem leviForm_eq_pi_mul_coeff {a : SmoothRealForm N Y 2} {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ ρ' : ComplexModel N → ℝ} (hpot : IsSmoothLocalPotential a e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) (hρ' : ρ' =ᶠ[𝓝 z] ρ) (v : ComplexModel N) :
    leviForm ρ' z v = Real.pi * a.coeff e z ![v, Complex.I • v] := by
  rw [AubinYauUniformConstants.leviForm_congr hρ', coeff_line_eq_leviForm_of_potential hpot hz]
  field_simp

/-- **The Tsuji-weighted trace estimate, uniform in the background** (Berman 2019, proof of
Proposition 3.5 and Remark 3.6, with a Kähler-current weight).  For Kähler forms `ω = w` and
`ω₀` on a compact connected `Y` there are `a > 0`, `T ≥ 0`, `β₀ > 0` such that: for every closed
real `(1,1)`-form `η` and every Kähler background `A` with `ω₀ ≤ A - η ≤ ω₀ + ω` on complex lines,
every `β ≥ β₀`, every smooth `F` with `Δ_ω F + tr_ω η ≤ S`, every smooth `u` with `A + ddᶜu` Kähler
and `(A + ddᶜu)^N = e^{β(u - F)} ω^N`, every `η`-psh `ψ ≢ -∞` with `ψ ≤ u - m`, and every point
`y` with `ψ(y) = r` finite: `tr_ω(A + ddᶜu)(y) ≤ 2(T + S) e^{a(u(y) - r - m)}`. -/
theorem tsuji_traceForm_le [CompactSpace Y] [ConnectedSpace Y] (w ω₀ : KahlerBackground N Y) :
    ∃ a T β₀ : ℝ, 0 < a ∧ 0 ≤ T ∧ 0 < β₀ ∧
      ∀ (η : ClosedRealOneOneForm N Y) (A : KahlerBackground N Y),
        (∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
          ω₀.form.val.coeff e z ![v, Complex.I • v] ≤
              A.form.val.coeff e z ![v, Complex.I • v] - η.val.coeff e z ![v, Complex.I • v] ∧
            A.form.val.coeff e z ![v, Complex.I • v] - η.val.coeff e z ![v, Complex.I • v] ≤
              ω₀.form.val.coeff e z ![v, Complex.I • v] +
                w.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ β : ℝ, β₀ ≤ β → ∀ (F : Y → ℝ), ChartSmooth (n := N) F → ∀ (S : ℝ),
        (∀ y, laplacian w.form.val F y + traceForm w.form.val η.val y ≤ S) →
      ∀ (u : Y → ℝ) (hu : ChartSmooth (n := N) u),
        (A.form + ddcClosedForm u hu).val.IsKahler →
        (∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
          actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
            Real.exp (β * (u (e.val.symm z) - F (e.val.symm z))) *
              actualTopPowerDensity (w.form.val.coeff e z)) →
      ∀ (ψ : Y → EReal), ThetaPlurisubharmonic η.val ψ → (∃ y, ψ y ≠ ⊥) →
      ∀ (m : ℝ), (∀ y, ψ y ≤ ((u y - m : ℝ) : EReal)) →
      ∀ (y : Y) (r : ℝ), ψ y = (r : EReal) →
        traceForm w.form.val (A.form + ddcClosedForm u hu).val y ≤
          2 * (T + S) * Real.exp (a * (u y - r - m)) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨1, 0, 1, one_pos, le_rfl, one_pos,
      fun η A _ β _ F _ S _ u hu _ _ ψ _ _ m _ y => (hY.false y).elim⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨1, 0, 1, one_pos, le_rfl, one_pos, fun η A _ β _ F hF S hFS u hu _ _ ψ _ _ m _ y r _ => ?_⟩
    subst hN
    have h0 : ∀ (v : Y → ℝ) x, laplacian w.form.val v x = 0 := fun v x => by
      simp [laplacian, chartLaplacian, Matrix.trace]
    have ht0 : ∀ (α : SmoothRealForm 0 Y 2) x, traceForm w.form.val α x = 0 := fun α x => by
      simp [traceForm, chartTrace, Matrix.trace]
    have hS : 0 ≤ S := by have := hFS y; rwa [h0, ht0, add_zero] at this
    rw [ht0]
    positivity
  -- the pieces of `ω` and of `ω₀`
  choose Wω ρω ρω' Rω hRω hpotω hWω hρω' hρω'eq cω Cω Mω K₁ hcω hCω hMω hK₁ hbdω using
    exists_piece hN w
  choose W₀ ρ₀ ρ₀' R₀ hR₀ hpot₀ hW₀ hρ₀' hρ₀'eq c₀ C₀ M₀ K₀ hc₀ hC₀ hM₀ hK₀ hbd₀ using
    exists_piece hN ω₀
  set R : Y → ℝ := fun p => min (Rω p) (R₀ p) with hRdef
  have hR : ∀ p, 0 < R p := fun p => lt_min (hRω p) (hR₀ p)
  have hRωle : ∀ p, R p ≤ Rω p := fun p => min_le_left _ _
  have hR₀le : ∀ p, R p ≤ R₀ p := fun p => min_le_right _ _
  have hKt : ∀ p, closedBall ((complexChartAt (n := N) p).val p) (R p) ⊆
      (complexChartAt (n := N) p).val.target := fun p =>
    ((closedBall_subset_closedBall (by linarith [hRωle p, hRω p])).trans (hWω p)).trans
      (hpotω p).2.1
  choose CA Kb hCA hKb hnb using fun p =>
    exists_normal_barrier w.isKahler (complexChartAt (n := N) p)
      (isCompact_closedBall ((complexChartAt (n := N) p).val p) (R p)) (hKt p)
  obtain ⟨O, hOdef⟩ : ∃ O : Y → Set Y, O = fun p => (complexChartAt (n := N) p).val.source ∩
      (complexChartAt (n := N) p).val ⁻¹' ball ((complexChartAt (n := N) p).val p) (R p) :=
    ⟨_, rfl⟩
  have hO : ∀ p, IsOpen (O p) := fun p => by
    rw [hOdef]; exact (complexChartAt (n := N) p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => by
    rw [hOdef]; exact ⟨mem_complexChartAt_source p, mem_ball_self (hR p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  -- the constants of the pieces
  set cκ : Y → ℝ := fun p => c₀ p / (Cω p + 1) with hcκdef
  set Cκ : Y → ℝ := fun p => C₀ p / cω p + 1 with hCκdef
  have hcκ : ∀ p, 0 < cκ p := fun p => div_pos (hc₀ p) (by linarith [hCω p])
  have hCκ0 : ∀ p, 0 ≤ Cκ p := fun p => by
    have := hC₀ p; have := hcω p; positivity
  obtain ⟨a, hadef⟩ : ∃ a : ℝ,
      a = 1 + ∑ p ∈ t, (2 * Kb p + K₁ p * N * CA p ^ 2) / cκ p := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∑ p ∈ t, Cκ p * N := ⟨_, rfl⟩
  have hterm0 : ∀ p, 0 ≤ (2 * Kb p + K₁ p * N * CA p ^ 2) / cκ p := fun p => by
    have := hKb p; have := hK₁ p; have := hcκ p; positivity
  have ha0 : 0 < a := by
    rw [hadef]; linarith [Finset.sum_nonneg fun p (_ : p ∈ t) => hterm0 p]
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact Finset.sum_nonneg fun p _ => by have := hCκ0 p; positivity
  have hale : ∀ p ∈ t, 2 * Kb p + K₁ p * N * CA p ^ 2 ≤ a * cκ p := by
    intro p hp
    have h := Finset.single_le_sum (f := fun p =>
      (2 * Kb p + K₁ p * N * CA p ^ 2) / cκ p) (fun q _ => hterm0 q) hp
    have h' : (2 * Kb p + K₁ p * N * CA p ^ 2) / cκ p ≤ a := by
      rw [hadef]; linarith
    rwa [div_le_iff₀ (hcκ p)] at h'
  have hTle : ∀ p ∈ t, Cκ p * N ≤ T := fun p hp => by
    rw [hTdef]; exact Finset.single_le_sum (f := fun p => Cκ p * N)
      (fun q _ => by have := hCκ0 q; positivity) hp
  refine ⟨a, T, 2 * a * N + 1, ha0, hT0, by positivity, ?_⟩
  intro η A hAη β hβ F hF S hFS u hu huK hdens ψ hψ hψne m hm
  have hβ' : 2 * a * N < β := by linarith
  set Tr := traceForm w.form.val (A.form + ddcClosedForm u hu).val with hTrdef
  have htrpos : ∀ y, 0 < Tr y := traceForm_pos hN hg huK
  -- the weighted function and its maximum
  set H : Y → EReal := fun y => ψ y + ((Real.log (Tr y) / a - u y : ℝ) : EReal) with hHdef
  have hcontR : Continuous fun y => Real.log (Tr y) / a - u y :=
    (((continuous_traceForm hg (A.form + ddcClosedForm u hu)).log
      fun y => (htrpos y).ne').div_const a).sub
      (YauUniformEstimate.continuous_of_chartSmooth hu)
  have hHusc : UpperSemicontinuous H :=
    upperSemicontinuous_add_coe hψ.quasiPlurisubharmonic.upperSemicontinuous hcontR
  obtain ⟨y₀, -, hy₀⟩ := (hHusc.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty
    isCompact_univ
  have hHmax : ∀ y, H y ≤ H y₀ := fun y => hy₀ (mem_univ y)
  -- `ψ` is finite at the maximum point
  obtain ⟨y₁, hy₁⟩ := hψne
  have hψ0ne : ψ y₀ ≠ ⊥ := by
    intro hbot
    have h1 := hHmax y₁
    rw [hHdef] at h1
    simp only [hbot, EReal.bot_add, le_bot_iff] at h1
    exact hy₁ (EReal.add_eq_bot_iff.mp h1 |>.resolve_right (EReal.coe_ne_bot _))
  have hψ0top : ψ y₀ ≠ ⊤ := hψ.quasiPlurisubharmonic.ne_top y₀
  set r₀ := (ψ y₀).toReal with hr₀def
  have hψ0 : ψ y₀ = (r₀ : EReal) := (EReal.coe_toReal hψ0top hψ0ne).symm
  have hkey : Tr y₀ ≤ 2 * (T + S) := by
    obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, y₀ ∈ O p := by
      have := ht (mem_univ y₀)
      rw [mem_iUnion₂] at this
      obtain ⟨p, hp, h⟩ := this
      exact ⟨p, hp, h⟩
    rw [hOdef] at hyp
    set E := complexChartAt (n := N) p with hE
    set z₀ := E.val y₀ with hz₀def
    have hz₀B : z₀ ∈ ball (E.val p) (R p) := hyp.2
    have hz₀t : z₀ ∈ E.val.target := E.val.map_source hyp.1
    have hy₀eq : E.val.symm z₀ = y₀ := E.val.left_inv hyp.1
    have hz₀Kω : z₀ ∈ closedBall (E.val p) (Rω p) :=
      closedBall_subset_closedBall (hRωle p) (ball_subset_closedBall hz₀B)
    have hz₀K₀ : z₀ ∈ closedBall (E.val p) (R₀ p) :=
      closedBall_subset_closedBall (hR₀le p) (ball_subset_closedBall hz₀B)
    -- the local potentials of `A` and of `η` at `z₀`
    obtain ⟨WA, ρA, hz₀WA, hpotA⟩ :=
      LocalPotentials.closedRealOneOne_hasLocalPotentials A.form E z₀ hz₀t
    obtain ⟨Wη, ρη, hz₀Wη, hpotη, hψη⟩ := hψ E z₀ hz₀t
    -- a small ball inside all the domains
    have hO' : IsOpen (WA ∩ Wη ∩ ball (E.val p) (R p)) :=
      (hpotA.1.inter hpotη.1).inter isOpen_ball
    obtain ⟨ρr, hρr, hball⟩ := Metric.isOpen_iff.mp hO' z₀ ⟨⟨hz₀WA, hz₀Wη⟩, hz₀B⟩
    set r := ρr / 8 with hrdef
    have hr : 0 < r := by positivity
    have hcl : closedBall z₀ (4 * r) ⊆ WA ∩ Wη ∩ ball (E.val p) (R p) :=
      (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hball
    have hclA : closedBall z₀ (4 * r) ⊆ WA := fun x hx => (hcl hx).1.1
    have hclη : closedBall z₀ (4 * r) ⊆ Wη := fun x hx => (hcl hx).1.2
    have hclB : closedBall z₀ (4 * r) ⊆ ball (E.val p) (R p) := fun x hx => (hcl hx).2
    obtain ⟨ρA', hρA', hρA'eq⟩ := exists_contDiff_eqOn_ball hpotA.1 hpotA.2.2.1
      (by positivity : 0 < r) (by linarith : r < 4 * r) hclA
    obtain ⟨ρη', hρη', hρη'eq⟩ := exists_contDiff_eqOn_ball hpotη.1 hpotη.2.2.1
      (by positivity : 0 < r) (by linarith : r < 4 * r) hclη
    have hu_on : ContDiffOn ℝ ∞ (fun x => ρA x + u (E.val.symm x)) WA :=
      hpotA.2.2.1.add ((hu _).mono hpotA.2.1)
    obtain ⟨u', hu', hu'eq⟩ := exists_contDiff_eqOn_ball hpotA.1 hu_on
      (by positivity : 0 < r) (by linarith : r < 4 * r) hclA
    set V := ball z₀ r with hVdef
    have hVsub : V ⊆ closedBall z₀ (4 * r) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hVB : V ⊆ ball (E.val p) (R p) := hVsub.trans hclB
    have hz₀V : z₀ ∈ V := mem_ball_self hr
    have hVWω : V ⊆ Wω p := hVB.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [hRωle p, hRω p]))).trans (hWω p))
    have hVWA : V ⊆ WA := hVsub.trans hclA
    have hVWη : V ⊆ Wη := hVsub.trans hclη
    have hEqω : EqOn (ρω' p) (ρω p) V := fun x hx =>
      hρω'eq p (ball_subset_ball (by linarith [hRωle p, hRω p]) (hVB hx))
    -- the germs at `z₀`
    have hgermω : ρω' p =ᶠ[𝓝 z₀] ρω p :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀V) hEqω
    have hgerm₀ : ρ₀' p =ᶠ[𝓝 z₀] ρ₀ p :=
      Filter.eventuallyEq_of_mem ((isOpen_ball.mem_nhds hz₀V)) fun x hx =>
        hρ₀'eq p (ball_subset_ball (by linarith [hR₀le p, hR₀ p]) (hVB hx))
    have hgermA : ρA' =ᶠ[𝓝 z₀] ρA := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀V) hρA'eq
    have hgermη : ρη' =ᶠ[𝓝 z₀] ρη :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀V) hρη'eq
    have hz₀Wω : z₀ ∈ Wω p := hVWω hz₀V
    have hz₀W₀ : z₀ ∈ W₀ p := (hW₀ p) ((closedBall_subset_closedBall (by linarith [hR₀ p]))
      hz₀K₀)
    have hLω : ∀ v, leviForm (ρω' p) z₀ v = Real.pi * w.form.val.coeff E z₀ ![v, Complex.I • v] :=
      leviForm_eq_pi_mul_coeff (hpotω p) hz₀Wω hgermω
    have hL₀ : ∀ v, leviForm (ρ₀' p) z₀ v =
        Real.pi * ω₀.form.val.coeff E z₀ ![v, Complex.I • v] :=
      leviForm_eq_pi_mul_coeff (hpot₀ p) hz₀W₀ hgerm₀
    have hLA : ∀ v, leviForm ρA' z₀ v = Real.pi * A.form.val.coeff E z₀ ![v, Complex.I • v] :=
      leviForm_eq_pi_mul_coeff hpotA hz₀WA hgermA
    have hLη : ∀ v, leviForm ρη' z₀ v = Real.pi * η.val.coeff E z₀ ![v, Complex.I • v] :=
      leviForm_eq_pi_mul_coeff hpotη hz₀Wη hgermη
    have hbω := hbdω p z₀ hz₀Kω
    have hb₀ := hbd₀ p z₀ hz₀K₀
    have hκlow : ∀ v, cκ p * leviForm (ρω' p) z₀ v ≤ leviForm ρA' z₀ v - leviForm ρη' z₀ v := by
      intro v
      have h1 : cκ p * leviForm (ρω' p) z₀ v ≤ c₀ p * ‖v‖ ^ 2 := by
        have hup := hbω.2.1 v
        have hlow := hbω.1 v
        have hn0 : 0 ≤ leviForm (ρω' p) z₀ v := le_trans (by have := hcω p; positivity) hlow
        rw [hcκdef]
        simp only
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith [hCω p])]
        have hc0 := (hc₀ p).le
        nlinarith [sq_nonneg ‖v‖, mul_le_mul_of_nonneg_left hup hc0]
      have h2 := hb₀.1 v
      have h3 := (hAη E z₀ hz₀t v).1
      rw [hLA, hLη, ← mul_sub]
      rw [hL₀] at h2
      have := mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
      linarith
    have hκup : ∀ v, leviForm ρA' z₀ v - leviForm ρη' z₀ v ≤ Cκ p * leviForm (ρω' p) z₀ v := by
      intro v
      have h3 := (hAη E z₀ hz₀t v).2
      have h0 := hb₀.2.1 v
      have hlow := hbω.1 v
      rw [hL₀] at h0
      have hcω0 := hcω p
      have hC₀le : C₀ p * ‖v‖ ^ 2 ≤ C₀ p / cω p * leviForm (ρω' p) z₀ v := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcω0]
        nlinarith [mul_le_mul_of_nonneg_left hlow (hC₀ p), sq_nonneg ‖v‖]
      rw [hLA, hLη, ← mul_sub, hCκdef]
      simp only
      have := mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
      rw [hLω] at hC₀le ⊢
      nlinarith
    obtain ⟨Le, cc, hsymm, hLbd, h0, hbar⟩ := hnb p z₀ (ball_subset_closedBall hz₀B)
    have hmax' : ∀ y, ((Real.log (Tr y) / a - u y : ℝ) : EReal) + ψ y ≤
        ((Real.log (Tr (E.val.symm z₀)) / a - u (E.val.symm z₀) : ℝ) : EReal) +
          ψ (E.val.symm z₀) := by
      intro y
      rw [hy₀eq, add_comm, add_comm _ (ψ y₀)]
      exact hHmax y
    have h := traceForm_le_of_tsujiMax (S := S) (r₀ := r₀) hN w A η hF hu huK hdens (hpotω p)
      hpotA hpotη hψη
      (hρω' p) hρA' hρη' hu' isOpen_ball hVWω hVWA hVWη hEqω hρA'eq hρη'eq hu'eq hz₀V
      (hK₁ p) (hKb p) (hcκ p) ha0 ((hbω).2.2.2) hκlow hκup
      (Le : ComplexModel N →L[ℂ] ComplexModel N) hsymm hLbd
      (isUnit_det_jacobianMatrix_zero _ _ hsymm Le rfl) h0 hbar
      (by rw [hy₀eq]; exact hFS y₀) (hale p hpt) hβ' (by rw [hy₀eq]; exact hψ0) hmax'
    rw [hy₀eq] at h
    exact h.trans (by linarith [hTle p hpt])
  intro y r hyr
  have h1 := hHmax y
  rw [hHdef] at h1
  simp only at h1
  rw [hyr, hψ0, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  have hm0 : r₀ ≤ u y₀ - m := by
    have := hm y₀
    rw [hψ0, EReal.coe_le_coe_iff] at this
    exact this
  have hpos0 := htrpos y₀
  have hS2 : 0 < 2 * (T + S) := hpos0.trans_le hkey
  have h3 : Real.log (Tr y₀) ≤ Real.log (2 * (T + S)) := Real.log_le_log hpos0 hkey
  have h2 : Real.log (Tr y) ≤ Real.log (2 * (T + S)) + a * (u y - r - m) := by
    have h4 : Real.log (Tr y) / a ≤ Real.log (Tr y₀) / a - u y₀ + r₀ - r + u y := by linarith
    have h5 : Real.log (Tr y₀) / a ≤ Real.log (2 * (T + S)) / a :=
      div_le_div_of_nonneg_right h3 ha0.le
    have h6 : Real.log (Tr y) / a ≤ Real.log (2 * (T + S)) / a + (u y - r - m) := by linarith
    have h7 := mul_le_mul_of_nonneg_left h6 ha0.le
    rw [mul_add, mul_div_cancel₀ _ ha0.ne', mul_div_cancel₀ _ ha0.ne'] at h7
    exact h7
  have := Real.exp_le_exp.mpr h2
  rw [Real.exp_log (htrpos y), Real.exp_add, Real.exp_log hS2] at this
  exact this

end SGPT.NPP.DNNef
