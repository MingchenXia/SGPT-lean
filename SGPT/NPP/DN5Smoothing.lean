import SGPT.NPP.DN5Fibre
import SGPT.Analysis.KahlerNormalCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The smoothing `Ψ`: unitary form, chart independence, linearity

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 216–224: "`Ψ_u(x, w) =
∫_{T_x X} u(F(x, wζ)) χ(|ζ|²_h) dζ_h` … in unitary coordinates of `T_x X` the kernel has total
mass one … linear in `u`").

* `chartSmoothing_eq_frame` — **unitary form**: if `L : ℂⁿ ≃ ℂⁿ` is a complex frame normalizing
  `ω` at `z` (`ω_z(L u, L v) = flatForm(u, v)`), then
  `Ψ^e_g(z, t) = ∫ g(F(e⁻¹ z, t L s)) χ(‖s‖²) ds`, the Euclidean radial mean of
  `s ↦ g(F(x, L s))` (`SGPT.NPP.DN3.radialMean`).
* `chartSmoothing_chart_change`, `smoothing_eq_chartSmoothing` — **chart independence**.
* `chartSmoothing_eq_localSmoothing` — the chart expression as a chart-level mean
  (`SGPT.NPP.DN5.localSmoothing`) of `g ∘ e⁻¹` along `Φ = e ∘ F`.
* `smoothing_neg`, `chartSmoothing_add_const`, `chartSmoothing_mono` — linearity and positivity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Analysis.KahlerNormal

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Linear changes of variables -/

/-- Real Haar change of variables for a linear automorphism of `ℂⁿ`. -/
theorem integral_eq_abs_det_mul_integral_comp (T : ComplexModel N ≃L[ℝ] ComplexModel N)
    (f : ComplexModel N → ℝ) :
    (∫ v, f v) = |LinearMap.det T.toLinearEquiv.toLinearMap| * ∫ v, f (T v) := by
  have hdet : LinearMap.det T.toLinearEquiv.toLinearMap ≠ 0 :=
    T.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (ComplexModel N)) hdet
  have hcoe : (T.toLinearEquiv.toLinearMap : ComplexModel N → ComplexModel N) = T := by
    funext x
    rfl
  rw [hcoe] at hmap
  have hi := integral_map_equiv (μ := volume) T.toHomeomorph.toMeasurableEquiv f
  change (∫ v, f v ∂Measure.map T volume) = ∫ v, f (T v) at hi
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    abs_inv] at hi
  calc
    (∫ v, f v) = |LinearMap.det T.toLinearEquiv.toLinearMap| *
        (|LinearMap.det T.toLinearEquiv.toLinearMap|⁻¹ * ∫ v, f v) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_mul]
    _ = _ := congrArg (fun a => |LinearMap.det T.toLinearEquiv.toLinearMap| * a) hi

theorem abs_det_pos (T : ComplexModel N ≃L[ℝ] ComplexModel N) :
    0 < |LinearMap.det T.toLinearEquiv.toLinearMap| :=
  abs_pos.mpr T.toLinearEquiv.isUnit_det'.ne_zero

/-! ### Normalizing frames -/

/-- `L` is a complex frame normalizing `ω` at the chart point `z`:
`ω_z(L u, L v) = flatForm(u, v)` (unitary coordinates of `T_x Y`). -/
def IsNormalizingFrame (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z : ComplexModel N)
    (L : ComplexModel N ≃L[ℂ] ComplexModel N) : Prop :=
  ∀ u v, wY.form.val.coeff e z ![L u, L v] = flatForm N ![u, v]

variable {wY : KahlerBackground N Y} {e e' : ComplexChart N Y} {z : ComplexModel N}
  {L : ComplexModel N ≃L[ℂ] ComplexModel N}

theorem exists_normalizingFrame (wY : KahlerBackground N Y) (hz : z ∈ e.val.target) :
    ∃ L, IsNormalizingFrame wY e z L :=
  exists_normalizing_linear (wY.isKahler.1 e z hz).1 (wY.isKahler.1 e z hz).2

theorem fibreNormSq_frame (hL : IsNormalizingFrame wY e z L) (s : ComplexModel N) :
    fibreNormSq wY e z (L s) = ‖s‖ ^ 2 := by
  unfold fibreNormSq DN2.chartNormSq
  rw [← L.map_smul Complex.I s, hL, flatForm_apply_I_smul_self, ← mul_assoc,
    mul_inv_cancel₀ Real.pi_ne_zero, one_mul]

theorem fibreWeight_frame (hL : IsNormalizingFrame wY e z L) (s : ComplexModel N) :
    fibreWeight wY e z (L s) = DN3.kernel N s := by
  rw [fibreWeight, fibreNormSq_frame hL, DN3.kernel]

theorem integral_fibreWeight (hL : IsNormalizingFrame wY e z L) :
    ∫ ξ, fibreWeight wY e z ξ =
      |LinearMap.det (L.restrictScalars ℝ).toLinearEquiv.toLinearMap| := by
  rw [integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)]
  have : ∀ s, fibreWeight wY e z ((L.restrictScalars ℝ) s) = DN3.kernel N s :=
    fun s => fibreWeight_frame hL s
  simp_rw [this, DN3.integral_kernel, mul_one]

theorem integral_fibreWeight_pos (wY : KahlerBackground N Y) (hz : z ∈ e.val.target) :
    0 < ∫ ξ, fibreWeight wY e z ξ := by
  obtain ⟨L, hL⟩ := exists_normalizingFrame wY hz
  rw [integral_fibreWeight hL]
  exact abs_det_pos _

theorem integrable_fibreWeight (wY : KahlerBackground N Y) (hz : z ∈ e.val.target) :
    Integrable (fibreWeight wY e z) := by
  by_contra h
  have := integral_fibreWeight_pos (e := e) wY hz
  rw [integral_undef h] at this
  exact lt_irrefl _ this

theorem fibreWeight_nonneg (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    (z ξ : ComplexModel N) : 0 ≤ fibreWeight wY e z ξ :=
  DN3.chi_nonneg N _

/-- **The unitary form of the smoothing**: in a normalizing frame `L`,
`Ψ^e_g(z, t) = ∫ g(F(e⁻¹ z, t L s)) χ(‖s‖²) ds`. -/
theorem chartSmoothing_eq_frame (A : FibreAtlas N Y) (hL : IsNormalizingFrame wY e z L)
    (g : Y → ℝ) (t : ℝ) :
    chartSmoothing wY A g e z t = ∫ s, g (fibreMap A e z (t • L s)) * DN3.kernel N s := by
  unfold chartSmoothing
  rw [integral_fibreWeight hL,
    integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)
      (fun ξ => g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ)]
  have : ∀ s, g (fibreMap A e z (t • (L.restrictScalars ℝ) s)) *
      fibreWeight wY e z ((L.restrictScalars ℝ) s) = g (fibreMap A e z (t • L s)) * DN3.kernel N s :=
    fun s => by
      change g (fibreMap A e z (t • L s)) * fibreWeight wY e z (L s) = _
      rw [fibreWeight_frame hL s]
  simp_rw [this]
  exact mul_div_cancel_left₀ _ (abs_det_pos (L.restrictScalars ℝ)).ne'

/-! ### Chart independence -/

/-- The derivative of a coordinate change as a complex linear automorphism. -/
theorem exists_transitionEquiv (hz : z ∈ e.val.target) (hz' : e.val.symm z ∈ e'.val.source) :
    ∃ T : ComplexModel N ≃L[ℂ] ComplexModel N,
      ∀ v, T v = chartTransitionDerivative e e' z v := by
  have hzs : z ∈ (chartTransition e e').source := mem_transition_source_iff.mpr ⟨hz, hz'⟩
  set z' := chartTransition e e' z with hz'def
  have hz't : z' ∈ e'.val.target := e'.val.map_source hz'
  have hz's : e'.val.symm z' ∈ e.val.source := by
    rw [hz'def, transition_apply, e'.val.left_inv hz']
    exact e.val.map_target hz
  have hz's' : z' ∈ (chartTransition e' e).source := mem_transition_source_iff.mpr ⟨hz't, hz's⟩
  have hback : chartTransition e' e z' = z := transition_inv_apply hz hz'
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℂ (chartTransition e e') z)
    (fderiv ℂ (chartTransition e' e) z') ?_ ?_, ?_⟩
  · intro v
    rw [← transitionDerivative_apply_eq_complex hzs, ← transitionDerivative_apply_eq_complex hz's']
    have h := congrArg (fun T : ComplexModel N →L[ℝ] ComplexModel N => T v)
      (transitionDerivative_inv_comp hz hz')
    simpa using h
  · intro v
    rw [← transitionDerivative_apply_eq_complex hz's', ← transitionDerivative_apply_eq_complex hzs]
    have h := congrArg (fun T : ComplexModel N →L[ℝ] ComplexModel N => T v)
      (transitionDerivative_inv_comp hz't hz's)
    rw [hback] at h
    simpa using h
  · intro v
    rw [transitionDerivative_apply_eq_complex hzs]
    rfl

/-- A normalizing frame transported by the coordinate change is normalizing. -/
theorem isNormalizingFrame_trans (hz : z ∈ e.val.target) (hz' : e.val.symm z ∈ e'.val.source)
    (hL : IsNormalizingFrame wY e z L) {T : ComplexModel N ≃L[ℂ] ComplexModel N}
    (hT : ∀ v, T v = chartTransitionDerivative e e' z v) :
    IsNormalizingFrame wY e' (chartTransition e e' z) (L.trans T) := by
  intro u v
  have hzs : z ∈ (chartTransition e e').source := mem_transition_source_iff.mpr ⟨hz, hz'⟩
  have h := wY.form.val.compatible e e' z hzs ![L u, L v]
  have hvec : (fun i => chartTransitionDerivative e e' z (![L u, L v] i)) =
      ![(L.trans T) u, (L.trans T) v] := by
    funext i
    fin_cases i <;> simp [hT]
  rw [hvec] at h
  rw [← h]
  exact hL u v

/-- **Chart independence of the smoothing.** -/
theorem chartSmoothing_chart_change (A : FibreAtlas N Y) (hz : z ∈ e.val.target)
    (hz' : e.val.symm z ∈ e'.val.source) (g : Y → ℝ) (t : ℝ) :
    chartSmoothing wY A g e' (chartTransition e e' z) t = chartSmoothing wY A g e z t := by
  obtain ⟨L, hL⟩ := exists_normalizingFrame wY hz
  obtain ⟨T, hT⟩ := exists_transitionEquiv hz hz'
  rw [chartSmoothing_eq_frame A (isNormalizingFrame_trans hz hz' hL hT),
    chartSmoothing_eq_frame A hL]
  congr 1
  funext s
  rw [fibreMap_chart_change A hz hz' (t • L s)]
  congr 3
  rw [ContinuousLinearEquiv.trans_apply, hT, map_smul]

/-- **The smoothing in an arbitrary chart.** -/
theorem smoothing_eq_chartSmoothing (A : FibreAtlas N Y) {x : Y} (hx : x ∈ e.val.source)
    (g : Y → ℝ) (t : ℝ) :
    smoothing wY A g x t = chartSmoothing wY A g e (e.val x) t := by
  set e₀ := complexChartAt (n := N) x
  have hx₀ : x ∈ e₀.val.source := mem_complexChartAt_source x
  have hz₀ : e₀.val x ∈ e₀.val.target := e₀.val.map_source hx₀
  have h := chartSmoothing_chart_change (wY := wY) (e' := e) A hz₀
    (by rw [e₀.val.left_inv hx₀]; exact hx) g t
  have hτ : chartTransition e₀ e (e₀.val x) = e.val x := by
    rw [transition_apply, e₀.val.left_inv hx₀]
  rw [hτ] at h
  exact h.symm

theorem smoothing_eq_chartSmoothing_symm (A : FibreAtlas N Y) (hz : z ∈ e.val.target)
    (g : Y → ℝ) (t : ℝ) :
    smoothing wY A g (e.val.symm z) t = chartSmoothing wY A g e z t := by
  rw [smoothing_eq_chartSmoothing A (e.val.map_target hz), e.val.right_inv hz]

/-- The chart expression of the smoothing as a chart-level mean along `Φ = e ∘ F`, when the
sampled points lie in the chart. -/
theorem chartSmoothing_eq_localSmoothing (A : FibreAtlas N Y) (g : Y → ℝ) (t : ℝ)
    (hsrc : ∀ ξ, fibreWeight wY e z ξ ≠ 0 → fibreMap A e z (t • ξ) ∈ e.val.source) :
    chartSmoothing wY A g e z t =
      localSmoothing (fun z ξ => e.val (fibreMap A e z ξ)) (wY.form.val.coeff e)
        (fun y => g (e.val.symm y)) z t := by
  unfold chartSmoothing localSmoothing
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  change g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ =
    g (e.val.symm (e.val (fibreMap A e z (t • ξ)))) * fibreWeight wY e z ξ
  by_cases hw : fibreWeight wY e z ξ = 0
  · rw [hw, mul_zero, mul_zero]
  · rw [e.val.left_inv (hsrc ξ hw)]

/-! ### Linearity and positivity -/

/-- **`neg`**: `Ψ_{-g} = -Ψ_g`. -/
theorem smoothing_neg (A : FibreAtlas N Y) (g : Y → ℝ) (x : Y) (t : ℝ) :
    smoothing wY A (fun y => -g y) x t = -smoothing wY A g x t := by
  simp only [smoothing, chartSmoothing, neg_mul, integral_neg, neg_div]

/-- **`add_const`** (mass one), given integrability of the integrand. -/
theorem chartSmoothing_add_const (A : FibreAtlas N Y) (hz : z ∈ e.val.target) {g : Y → ℝ}
    {t : ℝ} (hint : Integrable (fun ξ => g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ))
    (c : ℝ) :
    chartSmoothing wY A (fun y => g y + c) e z t = chartSmoothing wY A g e z t + c := by
  unfold chartSmoothing
  have hpos := integral_fibreWeight_pos (e := e) wY hz
  simp_rw [add_mul]
  rw [integral_add hint ((integrable_fibreWeight wY hz).const_mul c), integral_const_mul,
    add_div, mul_div_cancel_right₀ _ hpos.ne']

/-- **`mono`**, given integrability and an almost everywhere comparison of the integrands. -/
theorem chartSmoothing_mono (A : FibreAtlas N Y) (hz : z ∈ e.val.target) {g g' : Y → ℝ}
    {t : ℝ} (hint : Integrable (fun ξ => g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ))
    (hint' : Integrable (fun ξ => g' (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ))
    (hle : ∀ᵐ ξ, fibreWeight wY e z ξ ≠ 0 →
      g (fibreMap A e z (t • ξ)) ≤ g' (fibreMap A e z (t • ξ))) :
    chartSmoothing wY A g e z t ≤ chartSmoothing wY A g' e z t := by
  unfold chartSmoothing
  have hpos := integral_fibreWeight_pos (e := e) wY hz
  refine div_le_div_of_nonneg_right ?_ hpos.le
  refine integral_mono_ae hint hint' ?_
  filter_upwards [hle] with ξ hξ
  by_cases hw : fibreWeight wY e z ξ = 0
  · rw [hw, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hξ hw) (fibreWeight_nonneg wY e z ξ)

end SGPT.NPP.DN5
