import SGPT.Okounkov.TranscendentalWNRegEnvelope
import SGPT.Foundations.Analysis.SmoothDistribution

/-!
# `C^{1,1̄}` regularity from line-bounded smooth approximation

Package WN-REG (`claude-tok-wn-reg`, node `tok-wn-reg:c11bar-of-approx`).  A uniform limit of
chart-smooth functions `u_j` with `0 ≤ A + ddᶜu_j ≤ (b + ε) A` (`b` bounded above) is `C^{1,1̄}`
in the sense of `IsCOneOneBar`: in every chart its distributional complex Hessian has locally
bounded coefficients.  With Berman's estimate (`bermanSmoothEnvelopeStatement`) this gives
`C^{1,1̄}` regularity of envelopes of smooth obstacles (`isCOneOneBar_envelopeReal`), the input of
the contact formula (`tok-wn-reg:dnt-smooth-envelope`).

* `continuous_mul_of_continuousOn_of_tsupport` — a function continuous on an open set times a
  continuous function supported in it is continuous.
* `integral_mul_realHessian_eq` — two integrations by parts in one direction against a
  compactly supported smooth test function, for a function smooth only on an open set containing
  the support.
* `integral_mul_leviForm_eq` — `∫ g ∂_v∂̄_v φ = ∫ (∂_v∂̄_v g) φ`.
* `isCOneOneBar_of_hasSmoothLineBoundApproximation`, `isCOneOneBar_envelopeReal`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

/-! ### Products and integration by parts -/

/-- A function continuous on an open set `U`, times a continuous function with topological support
in `U`, is continuous. -/
theorem continuous_mul_of_continuousOn_of_tsupport {E : Type*} [TopologicalSpace E]
    {f h : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U) (hh : Continuous h)
    (hsupp : tsupport h ⊆ U) : Continuous (fun x => f x * h x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact (hf.continuousAt (hU.mem_nhds hx)).mul hh.continuousAt
  · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
    have h0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have hx0 : h x = 0 := h0.self_of_nhds
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

section IBP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Integrability of `f * h` for `f` continuous on an open `U` and `h` continuous with compact
support in `U`. -/
theorem integrable_mul_of_continuousOn {f h : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hh : Continuous h) (hc : HasCompactSupport h)
    (hsupp : tsupport h ⊆ U) : Integrable (fun x => f x * h x) := by
  refine (continuous_mul_of_continuousOn_of_tsupport hU hf hh hsupp).integrable_of_hasCompactSupport
    ?_
  exact hc.mul_left

/-- **Two integrations by parts in the direction `w`**: for `g` smooth on an open set `U` and a
smooth `φ` with compact support in `U`, `∫ g ∂²_wφ = ∫ (∂²_w g) φ`. -/
theorem integral_mul_realHessian_eq {g φ : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ U) (w : E) :
    ∫ x, g x * realHessian φ x w w = ∫ x, realHessian g x w w * φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  set Dφ : E → ℝ := fun x => fderiv ℝ φ x w with hDφ
  set Dg : E → ℝ := fun x => fderiv ℝ g x w with hDg
  have hDφs : ContDiff ℝ 1 Dφ := contDiff_fderiv_apply_of_two hφ2 w
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply (𝕜 := ℝ) w
  have hDφsupp : tsupport Dφ ⊆ U := (tsupport_fderiv_apply_subset ℝ w).trans hsupp
  have hDDφ : Continuous (fun x => fderiv ℝ Dφ x w) :=
    (hDφs.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDDφc : HasCompactSupport (fun x => fderiv ℝ Dφ x w) := hDφc.fderiv_apply (𝕜 := ℝ) w
  have hDDφsupp : tsupport (fun x => fderiv ℝ Dφ x w) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ w).trans hDφsupp
  -- smoothness of `g` and `Dg` on `U`
  have hgc : ContinuousOn g U := hg.continuousOn
  have hg1 : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
  have hDgs : ContDiffOn ℝ ∞ Dg U := hg1.clm_apply contDiffOn_const
  have hDgc : ContinuousOn Dg U := hDgs.continuousOn
  have hDDg : ContinuousOn (fun x => fderiv ℝ Dg x w) U :=
    (hDgs.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hgd : ∀ x ∈ U, DifferentiableAt ℝ g x := fun x hx =>
    (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hDgd : ∀ x ∈ U, DifferentiableAt ℝ Dg x := fun x hx =>
    (hDgs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  -- step 1: `∫ g ∂_w(∂_w φ) = -∫ ∂_w g ∂_w φ`
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := Dφ)
    (v := w) (integrable_mul_of_continuousOn hU hDgc hDφs.continuous hDφc hDφsupp)
    (integrable_mul_of_continuousOn hU hgc hDDφ hDDφc hDDφsupp)
    (integrable_mul_of_continuousOn hU hgc hDφs.continuous hDφc hDφsupp)
    (fun x hx => hgd x (hDφsupp hx)) (fun x _ => hDφs.differentiable one_ne_zero x)
  -- step 2: `∫ ∂_w g ∂_w φ = -∫ ∂_w(∂_w g) φ`
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := Dg) (g := φ)
    (v := w) (integrable_mul_of_continuousOn hU hDDg hφ.continuous hφc hsupp)
    (integrable_mul_of_continuousOn hU hDgc hDφs.continuous hDφc hDφsupp)
    (integrable_mul_of_continuousOn hU hDgc hφ.continuous hφc hsupp)
    (fun x hx => hDgd x (hsupp hx)) (fun x _ => hφ.differentiable (by simp) x)
  -- rewriting the second derivatives
  have hL : ∀ x, g x * realHessian φ x w w = g x * fderiv ℝ Dφ x w := fun x => by
    rw [fderiv_fderiv_apply_eq_realHessian hφ2 x w w]
  have hR : ∀ x, realHessian g x w w * φ x = fderiv ℝ Dg x w * φ x := fun x => by
    by_cases hx : x ∈ U
    · congr 1
      have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
        (hg1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      rw [realHessian_eq_fderiv, hDg, fderiv_clm_apply hD (differentiableAt_const w)]
      simp
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
      simp [this]
  simp_rw [hL, hR]
  have h2' : ∫ x, Dg x * fderiv ℝ φ x w = -∫ x, fderiv ℝ Dg x w * φ x := h2
  rw [h1]
  have : (fun x => fderiv ℝ g x w * Dφ x) = fun x => Dg x * fderiv ℝ φ x w := rfl
  rw [this, h2', neg_neg]

end IBP

section Levi

variable {n : ℕ}

/-- **`∫ g ∂_v∂̄_v φ = ∫ (∂_v∂̄_v g) φ`** for `g` smooth on an open `U` and a smooth `φ` with
compact support in `U`. -/
theorem integral_mul_leviForm_eq {g φ : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ U) (v : ComplexModel n) :
    ∫ x, g x * leviForm φ x v = ∫ x, leviForm g x v * φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hc : ∀ w, Continuous (fun x => realHessian φ x w w) := fun w =>
    continuous_realHessian hφ2 w w
  have hsub : ∀ w, Function.support (fun x => realHessian φ x w w) ⊆ tsupport φ :=
    fun w x hx => support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) fun h => hx (by
      simp [realHessian, h])
  have hcs : ∀ w, HasCompactSupport (fun x => realHessian φ x w w) := fun w => hφc.mono' (hsub w)
  have hsupp' : ∀ w, tsupport (fun x => realHessian φ x w w) ⊆ U := fun w =>
    (closure_minimal (hsub w) (isClosed_tsupport φ)).trans hsupp
  have hgc : ContinuousOn g U := hg.continuousOn
  have hA := integrable_mul_of_continuousOn hU hgc (hc v) (hcs v) (hsupp' v)
  have hB := integrable_mul_of_continuousOn hU hgc (hc (Complex.I • v)) (hcs (Complex.I • v))
    (hsupp' (Complex.I • v))
  have hφint : ∀ (r : ComplexModel n → ℝ), ContinuousOn r U →
      Integrable (fun x => r x * φ x) := fun r hr =>
    integrable_mul_of_continuousOn hU hr hφ.continuous hφc hsupp
  have hgv : ContinuousOn (fun x => realHessian g x v v) U := by
    have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ g)) U :=
      (hg.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen hU (by simp)
    simp only [realHessian_eq_fderiv]
    exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hgIv : ContinuousOn (fun x => realHessian g x (Complex.I • v) (Complex.I • v)) U := by
    have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ g)) U :=
      (hg.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen hU (by simp)
    simp only [realHessian_eq_fderiv]
    exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have e1 := integral_mul_realHessian_eq hU hg hφ hφc hsupp v
  have e2 := integral_mul_realHessian_eq hU hg hφ hφc hsupp (Complex.I • v)
  calc ∫ x, g x * leviForm φ x v
      = ((∫ x, g x * realHessian φ x v v) + ∫ x,
          g x * realHessian φ x (Complex.I • v) (Complex.I • v)) / 4 := by
        rw [← integral_add hA hB, ← integral_div]
        congr 1
        funext x
        simp only [leviForm]
        ring
    _ = ((∫ x, realHessian g x v v * φ x) + ∫ x,
          realHessian g x (Complex.I • v) (Complex.I • v) * φ x) / 4 := by rw [e1, e2]
    _ = ∫ x, leviForm g x v * φ x := by
        rw [← integral_add (hφint _ hgv) (hφint _ hgIv), ← integral_div]
        congr 1
        funext x
        simp only [leviForm]
        ring

end Levi

/-! ### `C^{1,1̄}` from line-bounded approximation -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The coefficients of a smooth form are bounded on lines over a compact subset of a chart. -/
theorem exists_line_le_of_isCompact (a : SmoothRealForm N Y 2) (e : ComplexChart N Y)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v : ComplexModel N,
      |a.coeff e z ![v, Complex.I • v]| ≤ C * ‖v‖ ^ 2 := by
  have hcont : ContinuousOn (a.coeff e) K := ((a.smooth e).continuousOn).mono hKt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz v => ?_⟩
  have h1 := (a.coeff e z).le_opNorm ![v, Complex.I • v]
  rw [Fin.prod_univ_two] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul, Complex.norm_I,
    one_mul] at h1
  calc |a.coeff e z ![v, Complex.I • v]| = ‖a.coeff e z ![v, Complex.I • v]‖ := rfl
    _ ≤ ‖a.coeff e z‖ * (‖v‖ * ‖v‖) := h1
    _ ≤ max C 0 * ‖v‖ ^ 2 := by
        rw [← pow_two]
        exact mul_le_mul_of_nonneg_right ((hC z hz).trans (le_max_left _ _)) (by positivity)

/-- **`C^{1,1̄}` from line-bounded smooth approximation** (`tok-wn-reg:c11bar-of-approx`): if `u`
is a uniform limit of chart-smooth `u_j` with `A + ddᶜu_j` Kähler and eventually
`A + ddᶜu_j ≤ (b + ε) A` on lines, with `b` bounded above, then `u` is `C^{1,1̄}`. -/
theorem isCOneOneBar_of_hasSmoothLineBoundApproximation (A : KahlerBackground N Y)
    {u b : Y → ℝ} (h : HasSmoothLineBoundApproximation A u b) {M : ℝ} (hM : ∀ x, b x ≤ M) :
    IsCOneOneBar (N := N) u := by
  obtain ⟨uj, huj, hunif, hKah, hline⟩ := h
  have hcont : Continuous u :=
    hunif.continuous (Eventually.of_forall (f := atTop) fun j =>
      YauUniformEstimate.continuous_of_chartSmooth (huj j)).frequently
  refine ⟨hcont, fun e K hK hKt => ?_⟩
  obtain ⟨CA, hCA0, hCA⟩ := exists_line_le_of_isCompact A.form.val e hK hKt
  set C : ℝ := Real.pi * (|M| + 2) * CA with hCdef
  refine ⟨C, fun φ hφ hφK v => ?_⟩
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
  have hsupp : tsupport φ ⊆ e.val.target := hφK.trans hKt
  -- the line bound for large `j`
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hline 1 one_pos)
  -- the Levi form of `u_j ∘ e⁻¹` on `K`
  have hlevi : ∀ j, j₀ ≤ j → ∀ z ∈ K,
      |leviForm (fun w => uj j (e.val.symm w)) z v| ≤ C * ‖v‖ ^ 2 := by
    intro j hj z hz
    have hzt := hKt hz
    have hup := hj₀ j hj e z hzt v
    have hlow := coefficientSemipositive_of_isKahler (hKah j) hzt v
    rw [add_ddc_line] at hup hlow
    rw [ddc_line_eq (huj j) e hzt v] at hup hlow
    have hAz := hCA z hz v
    have hA0 : 0 ≤ A.form.val.coeff e z ![v, Complex.I • v] :=
      coefficientSemipositive_of_isKahler A.isKahler hzt v
    have hAle : A.form.val.coeff e z ![v, Complex.I • v] ≤ CA * ‖v‖ ^ 2 :=
      (le_abs_self _).trans hAz
    set L := leviForm (fun w => uj j (e.val.symm w)) z v
    set a := A.form.val.coeff e z ![v, Complex.I • v]
    have hpi := Real.pi_pos
    have hbz := hM (e.val.symm z)
    have h1 : -a ≤ L / Real.pi := by linarith
    have h2 : L / Real.pi ≤ (M + 1 - 1) * a + a := by nlinarith
    have h1' : -(Real.pi * a) ≤ L := by
      have := mul_le_mul_of_nonneg_left h1 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne', mul_neg] at this
    have h2' : L ≤ Real.pi * ((|M| + 1) * a) := by
      have h3 : L / Real.pi ≤ (|M| + 1) * a := by
        have : (M + 1 - 1) * a + a ≤ (|M| + 1) * a := by
          nlinarith [le_abs_self M]
        linarith
      have := mul_le_mul_of_nonneg_left h3 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne'] at this
    rw [abs_le]
    have hva : 0 ≤ ‖v‖ ^ 2 := by positivity
    constructor
    · have : Real.pi * a ≤ Real.pi * (CA * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hAle hpi.le
      have : Real.pi * (CA * ‖v‖ ^ 2) ≤ C * ‖v‖ ^ 2 := by
        rw [hCdef]
        have : Real.pi * CA * ‖v‖ ^ 2 ≤ Real.pi * (|M| + 2) * CA * ‖v‖ ^ 2 := by
          have hM2 : 1 ≤ |M| + 2 := by linarith [abs_nonneg M]
          have : 0 ≤ Real.pi * CA * ‖v‖ ^ 2 := by positivity
          nlinarith
        linarith
      linarith
    · have : Real.pi * ((|M| + 1) * a) ≤ Real.pi * ((|M| + 1) * (CA * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAle (by positivity)) hpi.le
      have : Real.pi * ((|M| + 1) * (CA * ‖v‖ ^ 2)) ≤ C * ‖v‖ ^ 2 := by
        rw [hCdef]
        have : 0 ≤ Real.pi * CA * ‖v‖ ^ 2 := by positivity
        nlinarith
      linarith
  -- the integrals for `u_j`
  have hj : ∀ j, j₀ ≤ j →
      |∫ z, uj j (e.val.symm z) * leviForm φ z v| ≤ C * ‖v‖ ^ 2 * ∫ z, |φ z| := by
    intro j hjj
    rw [integral_mul_leviForm_eq e.val.open_target (huj j e) hφ hφc hsupp v]
    have hint : Integrable (fun z => leviForm (fun w => uj j (e.val.symm w)) z v * φ z) := by
      have hc2 : ContDiffOn ℝ ∞ (fun w => uj j (e.val.symm w)) e.val.target := huj j e
      have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (fun w => uj j (e.val.symm w))))
          e.val.target :=
        (hc2.fderiv_of_isOpen (m := ∞) e.val.open_target (by simp)).fderiv_of_isOpen
          e.val.open_target (by simp)
      refine integrable_mul_of_continuousOn e.val.open_target ?_ hφ.continuous hφc hsupp
      simp only [leviForm, realHessian_eq_fderiv]
      exact (((h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const).add
        ((h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const)).div_const 4
    calc |∫ z, leviForm (fun w => uj j (e.val.symm w)) z v * φ z|
        ≤ ∫ z, |leviForm (fun w => uj j (e.val.symm w)) z v * φ z| := abs_integral_le_integral_abs
      _ ≤ ∫ z, C * ‖v‖ ^ 2 * |φ z| := by
          refine integral_mono hint.abs ((hφ.continuous.abs.integrable_of_hasCompactSupport
            hφc.abs).const_mul _) fun z => ?_
          by_cases hz : z ∈ K
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hlevi j hjj z hz) (abs_nonneg _)
          · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφK h)
            simp [this]
      _ = C * ‖v‖ ^ 2 * ∫ z, |φ z| := integral_const_mul _ _
  -- passing to the limit
  have hLc : Continuous (fun z => leviForm φ z v) :=
    continuous_leviForm (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v
  have hLsub : Function.support (fun z => leviForm φ z v) ⊆ tsupport φ :=
    fun x hx => support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) fun h => hx (by
      simp [leviForm, realHessian, h])
  have hLcs : HasCompactSupport (fun z => leviForm φ z v) := hφc.mono' hLsub
  have hLint : Integrable (fun z => |leviForm φ z v|) :=
    hLc.abs.integrable_of_hasCompactSupport hLcs.abs
  have hLsupp : tsupport (fun z => leviForm φ z v) ⊆ e.val.target :=
    (closure_minimal hLsub (isClosed_tsupport φ)).trans hsupp
  have hucont : ContinuousOn (fun z => u (e.val.symm z)) e.val.target :=
    hcont.comp_continuousOn e.val.continuousOn_symm
  have hujcont : ∀ j, ContinuousOn (fun z => uj j (e.val.symm z)) e.val.target := fun j =>
    (huj j e).continuousOn
  have hIu : Integrable (fun z => u (e.val.symm z) * leviForm φ z v) :=
    integrable_mul_of_continuousOn e.val.open_target hucont hLc hLcs hLsupp
  have hIuj : ∀ j, Integrable (fun z => uj j (e.val.symm z) * leviForm φ z v) := fun j =>
    integrable_mul_of_continuousOn e.val.open_target (hujcont j) hLc hLcs hLsupp
  refine le_of_forall_pos_lt_add fun r hr => ?_
  -- choose `j` with `|u_j - u| < r / (1 + ∫|∂∂̄φ|)`
  set Iφ : ℝ := ∫ z, |leviForm φ z v| with hIφ
  have hIφ0 : 0 ≤ Iφ := integral_nonneg fun z => abs_nonneg _
  have hδ : 0 < r / (Iφ + 1) := div_pos hr (by linarith)
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp
    (Metric.tendstoUniformly_iff.mp hunif (r / (Iφ + 1)) hδ)
  set j := max j₀ j₁
  have hclose : ∀ y, |uj j y - u y| ≤ r / (Iφ + 1) := fun y => by
    have := hj₁ j (le_max_right _ _) y
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hdiff : |(∫ z, u (e.val.symm z) * leviForm φ z v) -
      ∫ z, uj j (e.val.symm z) * leviForm φ z v| ≤ r / (Iφ + 1) * Iφ := by
    rw [← integral_sub hIu (hIuj j)]
    calc |∫ z, (u (e.val.symm z) * leviForm φ z v - uj j (e.val.symm z) * leviForm φ z v)|
        ≤ ∫ z, |u (e.val.symm z) * leviForm φ z v - uj j (e.val.symm z) * leviForm φ z v| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, r / (Iφ + 1) * |leviForm φ z v| := by
          refine integral_mono (hIu.sub (hIuj j)).abs (hLint.const_mul _) fun z => ?_
          rw [← sub_mul, abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_right (hclose _) (abs_nonneg _)
      _ = r / (Iφ + 1) * Iφ := integral_const_mul _ _
  have hlt : r / (Iφ + 1) * Iφ < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hjb := hj j (le_max_left _ _)
  calc |∫ z, u (e.val.symm z) * leviForm φ z v|
      ≤ |∫ z, uj j (e.val.symm z) * leviForm φ z v| +
        |(∫ z, u (e.val.symm z) * leviForm φ z v) -
          ∫ z, uj j (e.val.symm z) * leviForm φ z v| := by
        have := abs_add_le (∫ z, uj j (e.val.symm z) * leviForm φ z v)
          ((∫ z, u (e.val.symm z) * leviForm φ z v) -
            ∫ z, uj j (e.val.symm z) * leviForm φ z v)
        simpa using this
    _ < C * ‖v‖ ^ 2 * (∫ z, |φ z|) + r := by linarith

end Manifold

/-! ### Envelopes of smooth obstacles are `C^{1,1̄}` -/

/-- **Envelopes of smooth obstacles are `C^{1,1̄}`** (`tok-wn-reg:c11bar-of-approx` with
`tok-wn-reg:berman-smooth`): on a compact connected complex manifold with a Kähler form `A`, the
envelope `P_A(F)` of a chart-smooth obstacle `F` is real-valued and `C^{1,1̄}`. -/
theorem isCOneOneBar_envelopeReal {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {F : Y → ℝ} (hF : ChartSmooth (n := N) F) :
    IsCOneOneBar (N := N) (envelopeReal A.form F) := by
  -- an upper bound `ddᶜF ≤ S A`
  have hFn : ChartSmooth (n := N) (fun x => -F x) := fun e => (hF e).neg
  obtain ⟨S, hS0, hS⟩ := KahlerDomination.exists_isSemipositive_add_smul
    (ddcClosedForm (fun x => -F x) hFn).val A.form.val A.isKahler.1
  have hFS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v] := by
    intro e z hz v
    have h := hS e z hz v
    have hneg : leviForm (fun w => -F (e.val.symm w)) z v =
        -leviForm (fun w => F (e.val.symm w)) z v :=
      leviForm_neg (fun w => F (e.val.symm w)) z v
    rw [ddc_line_eq hFn e hz v, hneg] at h
    rw [ddc_line_eq hF e hz v]
    have : -leviForm (fun w => F (e.val.symm w)) z v / Real.pi =
        -(leviForm (fun w => F (e.val.symm w)) z v / Real.pi) := by ring
    linarith
  obtain ⟨B, hB⟩ := YauContinuityMethod.exists_abs_le hF
  obtain ⟨a, Λ, ha, hΛ, h⟩ := bermanSmoothEnvelopeStatement N Y A
  obtain ⟨-, happrox⟩ := h F hF S hS0.le hFS (-B) fun y => (abs_le.mp (hB y)).1
  refine isCOneOneBar_of_hasSmoothLineBoundApproximation A happrox (M := (1 + S) * Λ *
    Real.exp (a * (B + B))) fun x => ?_
  have h1S : 0 ≤ (1 + S) * Λ := by
    have : 0 ≤ 1 + S := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ ha)) h1S
  linarith [(abs_le.mp (hB x)).2]

end SGPT.Okounkov.TranscendentalWNReg
