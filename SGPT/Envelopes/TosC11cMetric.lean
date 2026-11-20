import SGPT.Envelopes.TosC11cMaximum
import SGPT.Envelopes.TosC11cChart
import SGPT.Envelopes.TosC11bCovariant
import SGPT.Analysis.KahlerNormalUniform
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Riemannian metric of a Kähler form, gradient vectors and the covariant Hessian quotient

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:covariant-global`).  Source: Xia, *Foundations of
pluripotential theory*, `sec:real-hessian-envelopes` (Levi-Civita connection and covariant Hessian of
a smooth Riemannian metric; "by uniqueness, the vector fields obtained in different charts agree on
overlaps") and `lem:penalized-real-hessian`, Step 2 (the largest eigenvalue `ℓ` of `∇²a` relative to
`g₀`), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

* `twoFormMetric α (Y, Z) = α(Y, iZ)`, the Riemannian metric `ω(·, J·)` of a real two-form; symmetric
  for `(1,1)`-forms and positive definite for strictly positive ones; `twoFormMetricCLM` is the
  map `α ↦ twoFormMetric α`, bounded and linear.
* `gradVec g L`: for a positive definite `g`, the unique vector with `g(V, gradVec g L) = L V`
  (`apply_gradVec`, `eq_gradVec`); it is `(Z ↦ g(·, Z))⁻¹ L` and depends smoothly on `g`.
* `chartMetric A e`, `chartGrad A u e`, `hessQuot A u e z v = ∇²u(v, v)/g(v, v)`: the metric of the
  Kähler background `A`, the gradient vector of `u` and the quotient of the covariant Hessian of `u` by
  the metric, read in the chart `e`.  `hessQuot_chartTransition`: **the quotient is chart independent**
  (tensoriality, `TosC11b.covHess_comp`, and uniqueness of gradient vectors), so, with
  `exists_max_of_chartCompatible`, the largest eigenvalue of `∇²u` relative to `g` attains its maximum
  on a compact manifold (FPT Step 2).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Module
open scoped Topology ContDiff

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Analysis.KahlerNormal

section Linear

variable {n : ℕ}

/-- The bilinear form `(Y, Z) ↦ α(Y, iZ)` of a real two-form (the Riemannian metric `ω(·, J·)` of a
Kähler form). -/
def twoFormMetric (α : CoordinateRealTwoForm n) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun Y Z => α ![Y, Complex.I • Z])
      (fun Y Y' Z => twoForm_add_left α Y Y' _)
      (fun r Y Z => by rw [twoForm_smul_left, smul_eq_mul])
      (fun Y Z Z' => by rw [smul_add, twoForm_add_right])
      (fun r Y Z => by rw [smul_comm Complex.I r Z, twoForm_smul_right, smul_eq_mul]))
    ‖α‖ (fun Y Z => by
      have h := twoForm_norm_apply_le α Y (Complex.I • Z)
      rw [norm_smul, Complex.norm_I, one_mul] at h
      rw [LinearMap.mk₂_apply, Real.norm_eq_abs]
      exact h)

@[simp] theorem twoFormMetric_apply (α : CoordinateRealTwoForm n) (Y Z : ComplexModel n) :
    twoFormMetric α Y Z = α ![Y, Complex.I • Z] := rfl

/-- `α ↦ twoFormMetric α` is a bounded linear map. -/
theorem isBoundedLinearMap_twoFormMetric :
    @IsBoundedLinearMap ℝ (CoordinateRealTwoForm n)
      (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) _ NormedAddCommGroup.toSeminormedAddCommGroup
      NormedSpace.toModule NormedAddCommGroup.toSeminormedAddCommGroup NormedSpace.toModule
      (twoFormMetric (n := n)) :=
  { map_add := fun α β => by ext Y Z; simp
    map_smul := fun r α => by ext Y Z; simp
    bound := ⟨1, one_pos, fun α => by
      rw [one_mul]
      exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg α) _⟩ }

/-- The metric of a `(1,1)`-form is symmetric. -/
theorem twoFormMetric_symm {α : CoordinateRealTwoForm n} (hα : IsOneOne α) (Y Z : ComplexModel n) :
    twoFormMetric α Y Z = twoFormMetric α Z Y := by
  simp only [twoFormMetric_apply]
  rw [twoForm_swap α (Complex.I • Y) Z, twoForm_I_left hα, neg_neg]

/-- **Riesz map of a positive definite form**: `Z ↦ g(·, Z)` is bijective onto the dual. -/
theorem flip_bijective {g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) : Function.Bijective g.flip := by
  have hinj : Function.Injective g.flip := by
    intro Z Z' h
    by_contra hne
    have hd : Z - Z' ≠ 0 := sub_ne_zero.mpr hne
    have h0 : g.flip (Z - Z') = 0 := by rw [map_sub, h, sub_self]
    have := hg _ hd
    have h1 : g (Z - Z') (Z - Z') = 0 := by
      have := congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L (Z - Z')) h0
      simp only [ContinuousLinearMap.flip_apply, zero_apply] at this
      exact this
    linarith
  refine ⟨hinj, ?_⟩
  have hfin : finrank ℝ (ComplexModel n) = finrank ℝ (ComplexModel n →L[ℝ] ℝ) := by
    rw [← LinearMap.toContinuousLinearMap.finrank_eq]
    exact Subspace.dual_finrank_eq.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := g.flip.toLinearMap)).mp hinj

/-- The Riesz isomorphism `Z ↦ g(·, Z)` of a positive definite form. -/
def flipEquiv (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) : ComplexModel n ≃L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective g.flip.toLinearMap (flip_bijective hg)).toContinuousLinearEquiv

theorem coe_flipEquiv (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    (flipEquiv g hg : ComplexModel n →L[ℝ] (ComplexModel n →L[ℝ] ℝ)) = g.flip := by
  ext Z
  rfl

/-- The **gradient vector** of a covector `L` for the form `g`. -/
def gradVec (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (L : ComplexModel n →L[ℝ] ℝ) :
    ComplexModel n :=
  ContinuousLinearMap.inverse g.flip L

theorem gradVec_eq_symm (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (L : ComplexModel n →L[ℝ] ℝ) :
    gradVec g L = (flipEquiv g hg).symm L := by
  rw [gradVec, ← coe_flipEquiv g hg, ContinuousLinearMap.inverse_equiv]
  rfl

/-- `g(V, gradVec g L) = L V`. -/
theorem apply_gradVec {g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) (L : ComplexModel n →L[ℝ] ℝ) (V : ComplexModel n) :
    g V (gradVec g L) = L V := by
  rw [gradVec_eq_symm g hg]
  have h := (flipEquiv g hg).apply_symm_apply L
  have h2 := congrArg (fun M : ComplexModel n →L[ℝ] ℝ => M V) h
  rw [← h2]
  rfl

/-- **Uniqueness of gradient vectors.** -/
theorem eq_gradVec {g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) {L : ComplexModel n →L[ℝ] ℝ} {G : ComplexModel n}
    (hG : ∀ V, g V G = L V) : G = gradVec g L := by
  apply (flip_bijective hg).1
  ext V
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, hG, apply_gradVec hg]

end Linear

section Covariant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Koszul form in terms of the derivative of the metric. -/
theorem koszul_eq {g : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E} (hg : DifferentiableAt ℝ g z)
    (Y Z W : E) : TosC11b.koszul g z Y Z W =
      (fderiv ℝ g z Y Z W + fderiv ℝ g z Z Y W - fderiv ℝ g z W Y Z) / 2 := by
  simp only [TosC11b.koszul, TosC11b.fderiv_apply_apply hg]

/-- The Koszul form only depends on the germ of the metric. -/
theorem koszul_congr {g g' : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E} (h : g =ᶠ[𝓝 z] g')
    (Y Z W : E) : TosC11b.koszul g z Y Z W = TosC11b.koszul g' z Y Z W := by
  have hev : ∀ U V : E, (fun x => g x U V) =ᶠ[𝓝 z] (fun x => g' x U V) := fun U V =>
    h.mono fun x hx => by simp only [hx]
  simp only [TosC11b.koszul]
  rw [(hev Z W).fderiv_eq, (hev Y W).fderiv_eq, (hev Y Z).fderiv_eq]

/-- The covariant Hessian only depends on the germs of the metric and of the function. -/
theorem covHess_congr {g g' : E → E →L[ℝ] E →L[ℝ] ℝ} {a a' : E → ℝ} {z : E}
    (hg : g =ᶠ[𝓝 z] g') (ha : a =ᶠ[𝓝 z] a') (Y Z G : E) :
    TosC11b.covHess g a z Y Z G = TosC11b.covHess g' a' z Y Z G := by
  simp only [TosC11b.covHess]
  rw [koszul_congr hg, ha.fderiv.fderiv_eq]

/-- The covariant Hessian is homogeneous of degree two on the diagonal. -/
theorem covHess_smul {g : E → E →L[ℝ] E →L[ℝ] ℝ} {a : E → ℝ} {z : E}
    (hg : DifferentiableAt ℝ g z) (t : ℝ) (v G : E) :
    TosC11b.covHess g a z (t • v) (t • v) G = t ^ 2 * TosC11b.covHess g a z v v G := by
  simp only [TosC11b.covHess, koszul_eq hg, map_smul, smul_apply, smul_eq_mul]
  ring

end Covariant

section Chart

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-- The Riemannian metric `A(·, J·)` of the Kähler background `A`, read in the chart `e`. -/
def chartMetric (A : KahlerBackground N Y) (e : ComplexChart N Y) (z : ComplexModel N) :
    ComplexModel N →L[ℝ] ComplexModel N →L[ℝ] ℝ :=
  twoFormMetric (A.form.val.coeff e z)

theorem chartMetric_pos (A : KahlerBackground N Y) (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) : ∀ v, v ≠ 0 → 0 < chartMetric A e z v v :=
  fun v hv => (A.isKahler.1 e z hz).2 v hv

theorem chartMetric_symm (A : KahlerBackground N Y) (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) (U V : ComplexModel N) : chartMetric A e z U V = chartMetric A e z V U :=
  twoFormMetric_symm (A.isKahler.1 e z hz).1 U V

theorem contDiffOn_chartMetric (A : KahlerBackground N Y) (e : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (chartMetric A e) e.val.target := by
  have h := (isBoundedLinearMap_twoFormMetric (n := N)).contDiff.comp_contDiffOn
    (A.form.val.smooth e)
  exact h

/-- **The metric transforms as a tensor**: `g_e = τ^* g_f` on the overlap, `τ = f ∘ e⁻¹`. -/
theorem chartMetric_eq_pullback (A : KahlerBackground N Y) (e f : ComplexChart N Y)
    {w : ComplexModel N} (hw : w ∈ (chartTransition e f).source) :
    chartMetric A e w = TosC11b.pullbackBilin (chartMetric A f) (chartTransition e f) w := by
  ext U V
  simp only [TosC11b.pullbackBilin_apply, chartMetric, twoFormMetric_apply]
  rw [A.form.val.compatible e f w hw]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact chartTransitionDerivative_complex_smul e f w hw Complex.I V

/-- The gradient vector of `u` for the metric of `A`, read in the chart `e`. -/
def chartGrad (A : KahlerBackground N Y) (u : Y → ℝ) (e : ComplexChart N Y) (z : ComplexModel N) :
    ComplexModel N :=
  gradVec (chartMetric A e z) (fderiv ℝ (fun w => u (e.val.symm w)) z)

/-- The quotient `∇²u(v, v)/g(v, v)` of the covariant Hessian of `u` by the metric of `A`, read in the
chart `e`. -/
def hessQuot (A : KahlerBackground N Y) (u : Y → ℝ) (e : ComplexChart N Y) (z v : ComplexModel N) :
    ℝ :=
  TosC11b.covHess (chartMetric A e) (fun w => u (e.val.symm w)) z v v (chartGrad A u e z) /
    chartMetric A e z v v

/-- The quotient is invariant under nonzero rescaling of the vector. -/
theorem hessQuot_smul (A : KahlerBackground N Y) (u : Y → ℝ) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) {t : ℝ} (ht : t ≠ 0) :
    hessQuot A u e z (t • v) = hessQuot A u e z v := by
  have hg : DifferentiableAt ℝ (chartMetric A e) z :=
    ((contDiffOn_chartMetric A e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt
      (by simp)
  simp only [hessQuot]
  rw [covHess_smul hg]
  have hden : chartMetric A e z (t • v) (t • v) = t ^ 2 * chartMetric A e z v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [hden, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

/-- **The covariant Hessian quotient is chart independent** (FPT, `sec:real-hessian-envelopes`): for
`x` in the sources of `e` and `f`, `∇²u(v, v)/g(v, v)` read in `e` equals the quotient read in `f` at
the transported vector `D(f ∘ e⁻¹) v`. -/
theorem hessQuot_chartTransition (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (e f : ComplexChart N Y) {x : Y} (hxe : x ∈ e.val.source)
    (hxf : x ∈ f.val.source) (v : ComplexModel N) :
    hessQuot A u e (e.val x) v =
      hessQuot A u f (f.val x) (chartTransitionDerivative e f (e.val x) v) := by
  set z := e.val x with hzdef
  set τ := chartTransition e f with hτdef
  have hz : z ∈ τ.source := Pending.RelativeEigenvalueMax.mem_chartTransition_source hxe hxf
  have hτz : τ z = f.val x := Pending.RelativeEigenvalueMax.chartTransition_apply_chart hxe
  have hzt : z ∈ e.val.target := e.val.map_source hxe
  have hft : τ z ∈ f.val.target := chartTransition_mem_target e f hz
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hτ2 : ContDiffAt ℝ 2 τ z := (chartTransition_contDiffAt_real e f hz).of_le h2
  have ha2 : ContDiffAt ℝ 2 (fun w => u (f.val.symm w)) (τ z) :=
    ((hu f).contDiffAt (f.val.open_target.mem_nhds hft)).of_le h2
  have hgd : DifferentiableAt ℝ (chartMetric A f) (τ z) :=
    ((contDiffOn_chartMetric A f).contDiffAt (f.val.open_target.mem_nhds hft)).differentiableAt
      (by simp)
  have hmet : chartMetric A e =ᶠ[𝓝 z] TosC11b.pullbackBilin (chartMetric A f) τ := by
    filter_upwards [τ.open_source.mem_nhds hz] with w hw using chartMetric_eq_pullback A e f hw
  have hfun := chart_eventuallyEq u e f hz
  set Gf := chartGrad A u f (τ z) with hGfdef
  set Ge := chartGrad A u e z with hGedef
  have hGf : ∀ V, chartMetric A f (τ z) V Gf = fderiv ℝ (fun w => u (f.val.symm w)) (τ z) V :=
    apply_gradVec (chartMetric_pos A f hft) _
  have hdiff_a : DifferentiableAt ℝ (fun w => u (f.val.symm w)) (τ z) :=
    ha2.differentiableAt (by norm_num)
  have hdiff_τ : DifferentiableAt ℝ τ z := hτ2.differentiableAt (by norm_num)
  -- the gradient vectors correspond
  have hDτGe : fderiv ℝ τ z Ge = Gf := by
    apply eq_gradVec (chartMetric_pos A f hft)
    intro V
    obtain ⟨V', hV'⟩ := (Pending.RelativeEigenvalueMax.chartTransitionDerivative_bijective
      hxe hxf).2 V
    have hV'' : fderiv ℝ τ z V' = V := hV'
    rw [← hV'']
    have h1 : chartMetric A f (τ z) (fderiv ℝ τ z V') (fderiv ℝ τ z Ge) =
        chartMetric A e z V' Ge := by
      rw [chartMetric_eq_pullback A e f hz]; rfl
    have hGe : chartMetric A e z V' Ge = fderiv ℝ (fun w => u (e.val.symm w)) z V' :=
      apply_gradVec (chartMetric_pos A e hzt) _ V'
    rw [h1, hGe, hfun.fderiv_eq, fderiv_comp z hdiff_a hdiff_τ]
    rfl
  have hcomp := (TosC11b.covHess_comp (g := chartMetric A f) (φ := τ)
    (a := fun w => u (f.val.symm w)) (w := z) hgd (chartMetric_symm A f hft) hτ2 ha2 hGf
    hDτGe).2 v v
  have hnum : TosC11b.covHess (chartMetric A e) (fun w => u (e.val.symm w)) z v v Ge =
      TosC11b.covHess (chartMetric A f) (fun w => u (f.val.symm w)) (τ z)
        (fderiv ℝ τ z v) (fderiv ℝ τ z v) Gf := by
    rw [covHess_congr hmet hfun]
    exact hcomp
  have hden : chartMetric A e z v v = chartMetric A f (τ z) (fderiv ℝ τ z v) (fderiv ℝ τ z v) := by
    rw [chartMetric_eq_pullback A e f hz]; rfl
  simp only [hessQuot]
  rw [← hGedef, hnum, hden, ← hτz]
  rfl

/-- The gradient vector depends continuously on the point. -/
theorem continuousOn_chartGrad (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (e : ComplexChart N Y) :
    ContinuousOn (chartGrad A u e) e.val.target := by
  intro z hz
  have hU := e.val.open_target
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (chartMetric A e) z :=
    (contDiffOn_chartMetric A e).continuousOn.continuousAt (hU.mem_nhds hz)
  have hflip : ContinuousAt (fun w => (chartMetric A e w).flip) z :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel N) (ComplexModel N) ℝ).continuous.continuousAt.comp
      hg
  have hinv : ContinuousAt (fun w => ContinuousLinearMap.inverse (chartMetric A e w).flip) z := by
    have h := (contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)
      (flipEquiv (chartMetric A e z) (chartMetric_pos A e hz))).continuousAt
    rw [coe_flipEquiv] at h
    exact ContinuousAt.comp (g := ContinuousLinearMap.inverse)
      (f := fun w => (chartMetric A e w).flip) (x := z) h hflip
  have hDa : ContinuousAt (fderiv ℝ (fun w => u (e.val.symm w))) z :=
    ((hu e).continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hz)
  exact hinv.clm_apply hDa

/-- The derivative of the metric in terms of the derivative of the coefficients of `A`. -/
theorem fderiv_chartMetric_apply (A : KahlerBackground N Y) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (U V W : ComplexModel N) :
    fderiv ℝ (chartMetric A e) z U V W =
      fderiv ℝ (A.form.val.coeff e) z U ![V, Complex.I • W] := by
  have hgd : DifferentiableAt ℝ (chartMetric A e) z :=
    ((contDiffOn_chartMetric A e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt
      (by simp)
  have hcd : DifferentiableAt ℝ (A.form.val.coeff e) z :=
    ((A.form.val.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt
      (by simp)
  rw [← TosC11b.fderiv_apply_apply hgd]
  exact fderiv_continuousAlternatingMap_apply_const_apply hcd ![V, Complex.I • W] U

/-- The covariant Hessian quotient is continuous on `target × sphere`. -/
theorem continuousOn_hessQuot (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (e : ComplexChart N Y) :
    ContinuousOn (fun p : ComplexModel N × ComplexModel N => hessQuot A u e p.1 p.2)
      (e.val.target ×ˢ sphere 0 1) := by
  have hU := e.val.open_target
  set S : Set (ComplexModel N × ComplexModel N) := e.val.target ×ˢ sphere 0 1 with hS
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => u (e.val.symm w))) e.val.target :=
    (hu e).fderiv_of_isOpen hU (by simp)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ (fun w => u (e.val.symm w)))) e.val.target :=
    hD1.continuousOn_fderiv_of_isOpen hU (by simp)
  have hDc : ContinuousOn (fderiv ℝ (A.form.val.coeff e)) e.val.target :=
    (A.form.val.smooth e).continuousOn_fderiv_of_isOpen hU (by simp)
  have hc : ContinuousOn (A.form.val.coeff e) e.val.target := (A.form.val.smooth e).continuousOn
  have hG := continuousOn_chartGrad A hu e
  have hmaps : MapsTo Prod.fst S e.val.target := fun p hp => hp.1
  have hfst : ContinuousOn (Prod.fst : ComplexModel N × ComplexModel N → ComplexModel N) S :=
    continuous_fst.continuousOn
  have hsnd : ContinuousOn (Prod.snd : ComplexModel N × ComplexModel N → ComplexModel N) S :=
    continuous_snd.continuousOn
  have hGc : ContinuousOn (fun p : ComplexModel N × ComplexModel N => chartGrad A u e p.1) S :=
    hG.comp hfst hmaps
  have heq : EqOn (fun p : ComplexModel N × ComplexModel N => hessQuot A u e p.1 p.2)
      (fun p => (fderiv ℝ (fderiv ℝ (fun w => u (e.val.symm w))) p.1 p.2 p.2 -
        (fderiv ℝ (A.form.val.coeff e) p.1 p.2 ![p.2, Complex.I • chartGrad A u e p.1] +
          fderiv ℝ (A.form.val.coeff e) p.1 p.2 ![p.2, Complex.I • chartGrad A u e p.1] -
          fderiv ℝ (A.form.val.coeff e) p.1 (chartGrad A u e p.1) ![p.2, Complex.I • p.2]) / 2) /
        A.form.val.coeff e p.1 ![p.2, Complex.I • p.2]) S := by
    intro p hp
    have hgd : DifferentiableAt ℝ (chartMetric A e) p.1 :=
      ((contDiffOn_chartMetric A e).contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by simp)
    simp only [hessQuot, TosC11b.covHess, koszul_eq hgd, fderiv_chartMetric_apply A e hp.1]
    rfl
  refine ContinuousOn.congr ?_ heq
  have hev : Continuous (fun q : CoordinateRealTwoForm N × (Fin 2 → ComplexModel N) => q.1 q.2) :=
    continuous_eval
  have hvec : ∀ {X Z : ComplexModel N × ComplexModel N → ComplexModel N}, ContinuousOn X S →
      ContinuousOn Z S →
      ContinuousOn (fun p => (![X p, Complex.I • Z p] : Fin 2 → ComplexModel N)) S := by
    intro X Z hX hZ
    refine continuousOn_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hX
    · exact hZ.const_smul Complex.I
  have hterm : ∀ {X V W : ComplexModel N × ComplexModel N → ComplexModel N}, ContinuousOn X S →
      ContinuousOn V S → ContinuousOn W S →
      ContinuousOn (fun p => fderiv ℝ (A.form.val.coeff e) p.1 (X p) ![V p, Complex.I • W p]) S :=
    fun hX hV hW => hev.comp_continuousOn (((hDc.comp hfst hmaps).clm_apply hX).prodMk
      (hvec hV hW))
  have h1 : ContinuousOn (fun p : ComplexModel N × ComplexModel N =>
      fderiv ℝ (fderiv ℝ (fun w => u (e.val.symm w))) p.1 p.2 p.2) S :=
    ((hD2.comp hfst hmaps).clm_apply hsnd).clm_apply hsnd
  have h2 := hterm hsnd hsnd hGc
  have h3 := hterm hGc hsnd hsnd
  have h4 : ContinuousOn (fun p : ComplexModel N × ComplexModel N =>
      A.form.val.coeff e p.1 ![p.2, Complex.I • p.2]) S :=
    hev.comp_continuousOn ((hc.comp hfst hmaps).prodMk (hvec hsnd hsnd))
  have hne : ∀ p ∈ S, A.form.val.coeff e p.1 ![p.2, Complex.I • p.2] ≠ 0 := fun p hp =>
    (chartMetric_pos A e hp.1 p.2 (ne_zero_of_mem_sphere one_ne_zero ⟨p.2, hp.2⟩)).ne'
  exact (h1.sub (((h2.add h2).sub h3).div_const 2)).div h4 hne

/-- **The largest eigenvalue of the covariant Hessian, weighted, attains its maximum** (FPT
`lem:penalized-real-hessian`, Step 2): for a chart-smooth `u` and a continuous `w` on a compact
nonempty manifold of positive dimension, there are `y` and `M` with
`(∇²u(v, v)/g(v, v)) e^{w} ≤ M` in every chart, at every point and for every `v ≠ 0`, with equality at
`y` for a unit vector, in every chart at `y`.  (FPT's `Q = log ℓ + η(s) - Aa` is the logarithm of this
quantity with `w = η(s) - Aa`.) -/
theorem exists_max_hessQuot [CompactSpace Y] [Nonempty Y] (hN : 0 < N) (A : KahlerBackground N Y)
    {u : Y → ℝ} (hu : ChartSmooth (n := N) u) {w : Y → ℝ} (hw : Continuous w) :
    ∃ (y : Y) (M : ℝ),
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v, v ≠ 0 →
        hessQuot A u e z v * Real.exp (w (e.val.symm z)) ≤ M) ∧
      ∀ e : ComplexChart N Y, y ∈ e.val.source → ∃ ζ : ComplexModel N, ‖ζ‖ = 1 ∧
        hessQuot A u e (e.val y) ζ * Real.exp (w y) = M := by
  obtain ⟨y, M, h1, h2⟩ := exists_max_of_chartCompatible hN
    (fun e z v => hessQuot A u e z v * Real.exp (w (e.val.symm z)))
    (fun e => (continuousOn_hessQuot A hu e).mul
      ((Real.continuous_exp.comp hw).comp_continuousOn
        (e.val.continuousOn_symm.comp continuous_fst.continuousOn fun p hp => hp.1)))
    (fun e z hz v t ht => by rw [hessQuot_smul A u e hz v ht])
    (fun e f x hxe hxf v => by
      rw [hessQuot_chartTransition A hu e f hxe hxf v, e.val.left_inv hxe, f.val.left_inv hxf])
  refine ⟨y, M, h1, fun e hy => ?_⟩
  obtain ⟨ζ, hζ, hval⟩ := h2 e hy
  refine ⟨ζ, hζ, ?_⟩
  rw [e.val.left_inv hy] at hval
  exact hval

/-- **Gradient vectors are transported by the chart transitions**: `Dτ(e x) G_e = G_f` for
`τ = f ∘ e⁻¹` (FPT: "by uniqueness, the vector fields obtained in different charts agree"). -/
theorem fderiv_chartTransition_chartGrad (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (e f : ComplexChart N Y) {x : Y} (hxe : x ∈ e.val.source)
    (hxf : x ∈ f.val.source) :
    fderiv ℝ (chartTransition e f) (e.val x) (chartGrad A u e (e.val x)) =
      chartGrad A u f (f.val x) := by
  set z := e.val x with hzdef
  set τ := chartTransition e f with hτdef
  have hz : z ∈ τ.source := Pending.RelativeEigenvalueMax.mem_chartTransition_source hxe hxf
  have hτz : τ z = f.val x := Pending.RelativeEigenvalueMax.chartTransition_apply_chart hxe
  have hzt : z ∈ e.val.target := e.val.map_source hxe
  have hft : τ z ∈ f.val.target := chartTransition_mem_target e f hz
  have hdiff_a : DifferentiableAt ℝ (fun w => u (f.val.symm w)) (τ z) :=
    ((hu f).contDiffAt (f.val.open_target.mem_nhds hft)).differentiableAt (by simp)
  have hdiff_τ : DifferentiableAt ℝ τ z :=
    (chartTransition_contDiffAt_real e f hz).differentiableAt (by simp)
  have hfun := chart_eventuallyEq u e f hz
  rw [← hτz]
  apply eq_gradVec (chartMetric_pos A f hft)
  intro V
  obtain ⟨V', hV'⟩ := (Pending.RelativeEigenvalueMax.chartTransitionDerivative_bijective
    hxe hxf).2 V
  have hV'' : fderiv ℝ τ z V' = V := hV'
  rw [← hV'']
  have h1 : chartMetric A f (τ z) (fderiv ℝ τ z V') (fderiv ℝ τ z (chartGrad A u e z)) =
      chartMetric A e z V' (chartGrad A u e z) := by
    rw [chartMetric_eq_pullback A e f hz]; rfl
  rw [h1, chartGrad, apply_gradVec (chartMetric_pos A e hzt), hfun.fderiv_eq,
    fderiv_comp z hdiff_a hdiff_τ]
  rfl

/-- The squared length of the gradient of `u` for the metric of `A` (FPT's `s = |∂u|²_k`, up to the
normalization of the metric), read in the chart `e`: `Du(G) = g(G, G)`. -/
def gradNormSq (A : KahlerBackground N Y) (u : Y → ℝ) (e : ComplexChart N Y)
    (z : ComplexModel N) : ℝ :=
  fderiv ℝ (fun w => u (e.val.symm w)) z (chartGrad A u e z)

/-- The squared gradient length is chart independent. -/
theorem gradNormSq_chartTransition (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (e f : ComplexChart N Y) {x : Y} (hxe : x ∈ e.val.source)
    (hxf : x ∈ f.val.source) : gradNormSq A u e (e.val x) = gradNormSq A u f (f.val x) := by
  have hz : e.val x ∈ (chartTransition e f).source :=
    Pending.RelativeEigenvalueMax.mem_chartTransition_source hxe hxf
  have hτz : chartTransition e f (e.val x) = f.val x :=
    Pending.RelativeEigenvalueMax.chartTransition_apply_chart hxe
  have hft : chartTransition e f (e.val x) ∈ f.val.target := chartTransition_mem_target e f hz
  have hdiff_a : DifferentiableAt ℝ (fun w => u (f.val.symm w)) (chartTransition e f (e.val x)) :=
    ((hu f).contDiffAt (f.val.open_target.mem_nhds hft)).differentiableAt (by simp)
  have hdiff_τ : DifferentiableAt ℝ (chartTransition e f) (e.val x) :=
    (chartTransition_contDiffAt_real e f hz).differentiableAt (by simp)
  simp only [gradNormSq]
  rw [(chart_eventuallyEq u e f hz).fderiv_eq, fderiv_comp _ hdiff_a hdiff_τ,
    ContinuousLinearMap.comp_apply, fderiv_chartTransition_chartGrad A hu e f hxe hxf, hτz]

/-- The squared gradient length is nonnegative: `Du(G) = g(G, G) ≥ 0`. -/
theorem gradNormSq_nonneg (A : KahlerBackground N Y) (u : Y → ℝ) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) : 0 ≤ gradNormSq A u e z := by
  simp only [gradNormSq]
  rw [← apply_gradVec (chartMetric_pos A e hz) _ (chartGrad A u e z)]
  by_cases h0 : chartGrad A u e z = 0
  · rw [h0]; simp
  · exact (chartMetric_pos A e hz _ h0).le

/-- The squared gradient length as a function on `Y` (read in the preferred chart). -/
def gradNormSqFun (A : KahlerBackground N Y) (u : Y → ℝ) (x : Y) : ℝ :=
  gradNormSq A u (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x)

theorem gradNormSqFun_eq (A : KahlerBackground N Y) {u : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (e : ComplexChart N Y) {x : Y} (hx : x ∈ e.val.source) :
    gradNormSqFun A u x = gradNormSq A u e (e.val x) :=
  gradNormSq_chartTransition A hu _ e (mem_complexChartAt_source x) hx

/-- The squared gradient length is continuous on `Y`. -/
theorem continuous_gradNormSqFun (A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) : Continuous (gradNormSqFun A u) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hU := e.val.open_target
  have hzt : e.val x ∈ e.val.target := e.val.map_source hx
  have hcont : ContinuousOn (gradNormSq A u e) e.val.target := by
    have hDa : ContinuousOn (fderiv ℝ (fun w => u (e.val.symm w))) e.val.target :=
      (hu e).continuousOn_fderiv_of_isOpen hU (by simp)
    exact hDa.clm_apply (continuousOn_chartGrad A hu e)
  have hca : ContinuousAt (fun y => gradNormSq A u e (e.val y)) x :=
    (hcont.continuousAt (hU.mem_nhds hzt)).comp
      (e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hx))
  refine hca.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  exact (gradNormSqFun_eq A hu e hy).symm

end Chart

end SGPT.Envelopes.TosC11c
