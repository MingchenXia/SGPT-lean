import SGPT.Foundations.Analysis.Pending.XiaoPoissonProducer
import SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
import SGPT.Foundations.Analysis.Pending.YauHolderBound
import SGPT.Foundations.Analysis.Pending.MixedCoordinateDensity

/-!
# The trace of a real `(1,1)`-form with respect to a Kähler form; constant-trace representatives

Blueprint `claude-hodge`, package `HodgeTrace`; route of
Xia, *Foundations of pluripotential theory*, `thm:global-ddc-lemma` (first paragraph of its proof).

Let `(X, ω)` be a compact connected Kähler manifold (`w : KahlerBackground n X`).  For a real
`(1,1)`-form `γ` let `H_γ(z)` be its normalized coefficient matrix in a chart
(`normalizedHermitianMatrix`, so that `γ = (i/2π) ∑ H_{jk} dz_j ∧ dz̄_k`).  The **trace** of `γ`
with respect to a Hermitian form `g` is

`tr_g γ = Re tr(H_g⁻¹ H_γ)`,

computed in the preferred chart at each point (`trace`); it does not depend on the chart
(`chartTrace_eq_of_mem`), it is chart-smooth (`chartSmooth_trace`), linear in `γ`, `tr_ω ω = n`
(`trace_self`), and `tr_ω (ddᶜ u) = Δ_ω u` is the Laplacian of TN (`trace_ddcClosedForm`,
`trace_eq_add_laplacian_of_coeff`).

Solving `Δ_ω u = tr_ω θ - c` (TN `XiaoPoissonProducer.exists_unique_smooth_mean_zero_poisson`)
gives the main results:

* `exists_constantTrace_bottChernRel` / `exists_constantTrace_representative`: **every real
  Bott–Chern `(1,1)`-class contains a closed real `(1,1)`-form of constant trace**
  (`claude-hodge:prop-constant-trace-rep`);
* `coeff_eq_of_bottChernRel_of_constantTrace`: **such a representative is unique** (its
  coefficients are determined on all chart targets) (`claude-hodge:lem-constant-trace-unique`).

Constant-trace forms are the `ω`-harmonic `(1,1)`-forms; their coclosedness (package
`HodgeStar`) and TN's finite-dimensional weak harmonic kernel give the finite dimensionality of
`H^{1,1}(X, ℝ)` (package `HodgeFinite`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix ComplexOrder

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The trace in a chart and on the manifold -/

theorem normalizedHermitianMatrix_zero :
    normalizedHermitianMatrix (0 : CoordinateRealTwoForm n) = 0 :=
  normalizedHermitianMatrixₗ.map_zero

/-- The trace of the real two-form `γ` with respect to the Hermitian form `g` in the chart `e`:
`Re tr(H_g(z)⁻¹ H_γ(z))`. -/
def chartTrace (g γ : SmoothRealForm n M 2) (e : ComplexChart n M) (z : ComplexModel n) : ℝ :=
  (Matrix.trace ((normalizedHermitianMatrix (g.coeff e z))⁻¹ *
    normalizedHermitianMatrix (γ.coeff e z))).re

/-- **The trace `tr_g γ`** of a real two-form `γ` with respect to a Hermitian form `g`, read in the
preferred chart at each point. -/
def trace (g γ : SmoothRealForm n M 2) (y : M) : ℝ :=
  chartTrace g γ (complexChartAt (n := n) y) ((complexChartAt (n := n) y).val y)

/-- **Chart independence of the trace** of a `(1,1)`-form: both coefficient matrices transform by
`H ↦ Jᵀ H J̄` along a chart transition, and `tr(H⁻¹K)` is invariant. -/
theorem chartTrace_eq_of_mem {g γ : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (hγ : γ.IsTypeOneOne) {e f : ComplexChart n M} {y : M} (hye : y ∈ e.val.source)
    (hyf : y ∈ f.val.source) :
    chartTrace g γ e (e.val y) = chartTrace g γ f (f.val y) := by
  have hz : e.val y ∈ (chartTransition e f).source :=
    RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  have hτz : chartTransition e f (e.val y) = f.val y :=
    RelativeEigenvalueMax.chartTransition_apply_chart hye
  have hmem : chartTransition e f (e.val y) ∈ f.val.target :=
    ((chartTransition e f).map_source hz).1
  have hH : normalizedHermitianMatrix (g.coeff e (e.val y)) =
      (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y))ᵀ *
        normalizedHermitianMatrix (g.coeff f (chartTransition e f (e.val y))) *
          (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y)).map
            (starRingEnd ℂ) := by
    rw [coeff_eq_compLinearMap g e f hz, normalizedHermitianMatrix_compLinearMap (hg f _ hmem).1,
      standardMatrix_transitionLinear]
  have hK : normalizedHermitianMatrix (γ.coeff e (e.val y)) =
      (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y))ᵀ *
        normalizedHermitianMatrix (γ.coeff f (chartTransition e f (e.val y))) *
          (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y)).map
            (starRingEnd ℂ) := by
    rw [coeff_eq_compLinearMap γ e f hz, normalizedHermitianMatrix_compLinearMap (hγ f _ hmem),
      standardMatrix_transitionLinear]
  simp only [chartTrace]
  rw [hH, hK, trace_inv_mul_congr (isUnit_det_jacobianMatrix e f hye hyf), hτz]

/-- The trace is computed in any chart. -/
theorem trace_eq {g γ : SmoothRealForm n M 2} (hg : g.IsHermitian) (hγ : γ.IsTypeOneOne)
    {e : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) :
    trace g γ y = chartTrace g γ e (e.val y) :=
  chartTrace_eq_of_mem hg hγ (mem_complexChartAt_source y) hye

/-- The trace read on a chart target. -/
theorem trace_symm_eq {g γ : SmoothRealForm n M 2} (hg : g.IsHermitian) (hγ : γ.IsTypeOneOne)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target) :
    trace g γ (e.val.symm z) = chartTrace g γ e z := by
  rw [trace_eq hg hγ (e.val.map_target hz), e.val.right_inv hz]

/-! ### Smoothness -/

/-- The entries of the coefficient matrix of a smooth two-form are smooth on chart targets. -/
theorem contDiffOn_normalizedHermitianMatrix_apply (γ : SmoothRealForm n M 2)
    (e : ComplexChart n M) (j k : Fin n) :
    ContDiffOn ℝ ∞ (fun z => normalizedHermitianMatrix (γ.coeff e z) j k) e.val.target := by
  have h1 : ContDiffOn ℝ ∞
      (fun z => ((γ.coeff e z ![coordinateVector j, Complex.I • coordinateVector k] : ℝ) : ℂ))
      e.val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_apply (γ.smooth e) _)
  have h2 : ContDiffOn ℝ ∞
      (fun z => ((γ.coeff e z ![coordinateVector j, coordinateVector k] : ℝ) : ℂ))
      e.val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_apply (γ.smooth e) _)
  exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul h2))

/-- The chart trace with respect to a Hermitian form is smooth on the chart target. -/
theorem contDiffOn_chartTrace {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (γ : SmoothRealForm n M 2) (e : ComplexChart n M) :
    ContDiffOn ℝ ∞ (chartTrace g γ e) e.val.target := by
  have h : chartTrace g γ e = fun z => Complex.reCLM (∑ j, ∑ k,
      (normalizedHermitianMatrix (g.coeff e z))⁻¹ j k *
        normalizedHermitianMatrix (γ.coeff e z) k j) := by
    funext z
    simp only [chartTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.reCLM_apply]
  rw [h]
  refine Complex.reCLM.contDiff.comp_contDiffOn
    (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_)
  exact (YauHolderBound.contDiffOn_inv_apply hg e j k).mul
    (contDiffOn_normalizedHermitianMatrix_apply γ e k j)

/-- **The trace is chart-smooth.** -/
theorem chartSmooth_trace {g γ : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (hγ : γ.IsTypeOneOne) : ChartSmooth (n := n) (trace g γ) := fun e =>
  (contDiffOn_chartTrace hg γ e).congr fun _ hz => trace_symm_eq hg hγ hz

/-! ### Linearity, `tr_ω ω = n` and `tr_ω ddᶜu = Δ_ω u` -/

/-- The trace of a sum of closed `(1,1)`-forms. -/
theorem trace_add (g : SmoothRealForm n M 2) (γ γ' : ClosedRealOneOneForm n M) (y : M) :
    trace g (γ + γ').val y = trace g γ.val y + trace g γ'.val y := by
  simp only [trace, chartTrace, ClosedRealOneOneForm.coeff_add, normalizedHermitianMatrix_add,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re]

/-- The trace of a real multiple of a closed `(1,1)`-form. -/
theorem trace_smul (g : SmoothRealForm n M 2) (c : ℝ) (γ : ClosedRealOneOneForm n M) (y : M) :
    trace g (c • γ).val y = c * trace g γ.val y := by
  simp only [trace, chartTrace, ClosedRealOneOneForm.coeff_smul, normalizedHermitianMatrix_smul,
    Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- The trace `γ ↦ tr_g γ` as a linear map on closed real `(1,1)`-forms. -/
def traceLinearMap (g : SmoothRealForm n M 2) : ClosedRealOneOneForm n M →ₗ[ℝ] (M → ℝ) where
  toFun γ := trace g γ.val
  map_add' γ γ' := funext fun y => trace_add g γ γ' y
  map_smul' c γ := funext fun y => trace_smul g c γ y

@[simp] theorem traceLinearMap_apply (g : SmoothRealForm n M 2) (γ : ClosedRealOneOneForm n M) :
    traceLinearMap g γ = trace g γ.val := rfl

/-- `tr_g g = n` for a Hermitian form `g`. -/
theorem trace_self {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (y : M) :
    trace g g y = n := by
  have hz : (complexChartAt (n := n) y).val y ∈ (complexChartAt (n := n) y).val.target :=
    (complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)
  have hdet := (posDef_coeff hg hz).det_pos.ne'
  simp only [trace, chartTrace]
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.trace_one]
  simp

/-- If `γ' = γ + ddᶜh` on every chart target, then `tr_g γ' = tr_g γ + Δ_g h`. -/
theorem trace_eq_add_laplacian_of_coeff (g : SmoothRealForm n M 2) {γ γ' : SmoothRealForm n M 2}
    {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      γ'.coeff e z = γ.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z) (y : M) :
    trace g γ' y = trace g γ y + laplacian g h y := by
  have hz : (complexChartAt (n := n) y).val y ∈ (complexChartAt (n := n) y).val.target :=
    (complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)
  have h2 : ContDiffAt ℝ 2 (fun w => h ((complexChartAt (n := n) y).val.symm w))
      ((complexChartAt (n := n) y).val y) :=
    ((hh _).contDiffAt ((complexChartAt (n := n) y).val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  simp only [trace, chartTrace]
  rw [heq _ _ hz, normalizedHermitianMatrix_add, normalizedHermitianMatrix_smoothDDC h2,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rfl

/-- **`tr_g ddᶜψ = Δ_g ψ`.** -/
theorem trace_ddcClosedForm (g : SmoothRealForm n M 2) (ψ : M → ℝ)
    (hψ : ChartSmooth (n := n) ψ) (y : M) :
    trace g (ManifoldTubePositivity.ddcClosedForm ψ hψ).val y = laplacian g ψ y := by
  have h := trace_eq_add_laplacian_of_coeff g (γ := (0 : ClosedRealOneOneForm n M).val)
    (γ' := (ManifoldTubePositivity.ddcClosedForm ψ hψ).val) hψ
    (fun e z _ => by rw [ManifoldTubePositivity.ddcClosedForm_coeff,
      ClosedRealOneOneForm.coeff_zero, zero_add]) y
  rw [h]
  have h0 : trace g (0 : ClosedRealOneOneForm n M).val y = 0 := by
    simp only [trace, chartTrace, ClosedRealOneOneForm.coeff_zero, normalizedHermitianMatrix_zero,
      Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  rw [h0, zero_add]

/-! ### Constant-trace forms -/

/-- The closed real `(1,1)`-forms of constant trace with respect to the Kähler form `ω`: the
`ω`-harmonic `(1,1)`-forms. -/
def constantTraceSubmodule (w : KahlerBackground n M) :
    Submodule ℝ (ClosedRealOneOneForm n M) where
  carrier := {γ | ∃ c : ℝ, ∀ y, trace w.form.val γ.val y = c}
  add_mem' := by
    rintro γ γ' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', fun y => by rw [trace_add, hc, hc']⟩
  zero_mem' := ⟨0, fun y => by
    simp only [trace, chartTrace, ClosedRealOneOneForm.coeff_zero, normalizedHermitianMatrix_zero,
      Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]⟩
  smul_mem' := by
    rintro a γ ⟨c, hc⟩
    exact ⟨a * c, fun y => by rw [trace_smul, hc]⟩

theorem mem_constantTraceSubmodule_iff (w : KahlerBackground n M) (γ : ClosedRealOneOneForm n M) :
    γ ∈ constantTraceSubmodule w ↔ ∃ c : ℝ, ∀ y, trace w.form.val γ.val y = c := Iff.rfl

/-- The Kähler form itself has constant trace `n`. -/
theorem form_mem_constantTraceSubmodule (w : KahlerBackground n M) :
    w.form ∈ constantTraceSubmodule w :=
  ⟨n, trace_self w.isKahler.1⟩

section Global

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **Every real `(1,1)`-form is Bott–Chern cohomologous to a form of constant trace**
(`claude-hodge:prop-constant-trace-rep`): with `c` the mean of `tr_ω θ` for the Kähler volume and
`u` the smooth solution of `Δ_ω u = tr_ω θ - c`, the form `θ - ddᶜu` has trace `c`. -/
theorem exists_constantTrace_bottChernRel (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ γ ∈ constantTraceSubmodule w, ClosedRealOneOneForm.BottChernRel θ γ := by
  set μ := IntegrationCurrent.kahlerVolume w with hμ
  set t : M → ℝ := trace w.form.val θ.val with ht_def
  have ht : ChartSmooth (n := n) t := chartSmooth_trace w.isKahler.1 θ.property.2
  have htc : Continuous t := ProductTestForms.ChartSmooth.continuous ht
  have hti : Integrable t μ :=
    integrableOn_univ.mp (htc.continuousOn.integrableOn_compact isCompact_univ)
  have hV := KahlerLaplacianSolvability.kahlerVolume_real_univ_pos w
  set c : ℝ := (∫ x, t x ∂μ) / μ.real univ with hc_def
  set h : M → ℝ := fun x => t x - c with hh_def
  have hh : ChartSmooth (n := n) h := fun e => (ht e).sub contDiffOn_const
  have hint : ∫ x, h x ∂μ = 0 := by
    rw [hh_def, integral_sub hti (integrable_const c), integral_const, smul_eq_mul, hc_def,
      mul_div_cancel₀ _ hV.ne', sub_self]
  obtain ⟨u, hu, -, hΔ, -⟩ := XiaoPoissonProducer.exists_unique_smooth_mean_zero_poisson w h hh hint
  refine ⟨θ - ManifoldTubePositivity.ddcClosedForm u hu, ⟨c, fun y => ?_⟩, ?_⟩
  · have hsub := congrFun ((traceLinearMap w.form.val).map_sub θ
      (ManifoldTubePositivity.ddcClosedForm u hu)) y
    simp only [traceLinearMap_apply, Pi.sub_apply] at hsub
    rw [hsub, trace_ddcClosedForm, hΔ y, hh_def]
    ring
  · refine ⟨fun x => -u x, fun e => (hu e).neg, fun e z hz => ?_⟩
    rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ManifoldTubePositivity.ddcClosedForm_coeff,
      smoothDDC_neg e.val.open_target (hu e) hz]

/-- **Every real Bott–Chern `(1,1)`-class contains a closed real `(1,1)`-form of constant trace.** -/
theorem exists_constantTrace_representative (w : KahlerBackground n M) (α : RealBottChern n M) :
    ∃ γ ∈ constantTraceSubmodule w, RealBottChern.ofRepresentative γ = α := by
  induction α using Quotient.inductionOn with
  | h θ =>
    obtain ⟨γ, hγ, hrel⟩ := exists_constantTrace_bottChernRel w θ
    exact ⟨γ, hγ, ((RealBottChern.ofRepresentative_eq_iff θ γ).mpr hrel).symm⟩

/-- **Uniqueness of the constant-trace representative** (`claude-hodge:lem-constant-trace-unique`):
two cohomologous forms of constant trace have the same coefficients on every chart target. If
`γ' = γ + ddᶜh`, then `Δ_ω h = c' - c` is constant, hence `0` by Stokes, so `h` is constant. -/
theorem coeff_eq_of_bottChernRel_of_constantTrace (w : KahlerBackground n M)
    {γ γ' : ClosedRealOneOneForm n M} (hγ : γ ∈ constantTraceSubmodule w)
    (hγ' : γ' ∈ constantTraceSubmodule w) (hrel : ClosedRealOneOneForm.BottChernRel γ γ')
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    γ'.val.coeff e z = γ.val.coeff e z := by
  obtain ⟨h, hh, heq⟩ := hrel
  obtain ⟨c, hc⟩ := hγ
  obtain ⟨c', hc'⟩ := hγ'
  have h2 : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun z => h (e.val.symm z)) e.val.target :=
    fun e => (hh e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlap : ∀ y, laplacian w.form.val h y = c' - c := by
    intro y
    have := trace_eq_add_laplacian_of_coeff w.form.val hh heq y
    rw [hc, hc'] at this
    linarith
  have hV := KahlerLaplacianSolvability.kahlerVolume_real_univ_pos w
  have hint := KahlerLaplacianStokes.integral_laplacian_eq_zero w h2
  simp only [hlap, integral_const, smul_eq_mul] at hint
  have hcc : c' - c = 0 := (mul_eq_zero.mp hint).resolve_left hV.ne'
  obtain ⟨d, hd⟩ := KahlerLaplacianStokes.exists_eq_const_of_laplacian_eq_zero w h2
    (fun y => by rw [hlap, hcc])
  have hloc : (fun y => h (e.val.symm y)) =ᶠ[𝓝 z] fun _ => d := by
    filter_upwards [] with y
    exact hd _
  rw [heq e z hz, smoothDDC_congr hloc, GlobalPotentialTransforms.smoothDDC_const, add_zero]

/-- Class form of the uniqueness: cohomologous constant-trace forms agree on all chart targets. -/
theorem coeff_eq_of_ofRepresentative_eq (w : KahlerBackground n M)
    {γ γ' : ClosedRealOneOneForm n M} (hγ : γ ∈ constantTraceSubmodule w)
    (hγ' : γ' ∈ constantTraceSubmodule w)
    (h : RealBottChern.ofRepresentative γ = RealBottChern.ofRepresentative γ')
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    γ'.val.coeff e z = γ.val.coeff e z :=
  coeff_eq_of_bottChernRel_of_constantTrace w hγ hγ'
    ((RealBottChern.ofRepresentative_eq_iff γ γ').mp h) e hz

end Global

end SGPT.Hodge
