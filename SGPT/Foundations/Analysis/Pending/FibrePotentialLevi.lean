import SGPT.Foundations.Analysis.Pending.PositivityLeviLink
import SGPT.Foundations.Analysis.Pending.VerticalDensityFactorization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The pairing `∫_X v · ddᶜ(φ ∘ e) ∧ β_a^q` is the Levi distribution of `v ∘ e⁻¹`

Source: Demailly, CADG III.1 (the Levi form tested on `χ · β_a^{n-1}`) and I.5.8.  TN.4 plan, step
B6, finding F6 route (i), piece (i-1): after the Stokes
step on `X × X`, the potential part of `R_ε` on a Levi test form is `∫_X v_ε · ddᶜ(φ ∘ e) ∧ β_a^q`
(`VerticalDensityFactorization.integrationCurrent_chain_pullback`); in the chart this is
`(q!/π^{q+1}) ∫ v_ε ∘ e⁻¹ · L_φ(a)`, i.e. `(q!/π^{q+1}) Levi_a([v_ε ∘ e⁻¹])(φ)`, the last term of
`PositivityLeviLink.LeviTestIdentity`.

* `leviDDCTest e ψ a φ = Π₁₁ ddᶜ(φ ∘ e) ∧ β_a^q`, a top-degree test form;
* `topDensity_leviDDCTest_coeff`: its density in `e` is `(q!/π^{q+1}) L_φ(a)` where `ψ ≡ 1` near
  `supp φ` (flat core `DirectionalLeviDensity.topDensity_smoothDDC_perpQuadratic` with `f = φ`);
* `integral_mul_topRatio_leviDDCTest`: for a continuous `v`,
  `∫_X v · (ddᶜ(φ ∘ e) ∧ β_a^q / ωⁿ) dV = (q!/π^{q+1}) · Levi_a([v ∘ e⁻¹])(φ)`.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.FibrePotentialLevi

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms
  ManifoldTubePositivity DirectionalLeviDensity ThetaPshChartLimitGluing IntegrationCurrentChart
  PositivityLeviLink ClosedTopCurrents ClosedProductCurrents

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X]

/-- `ddᶜ(φ ∘ e)` as a closed real `(1,1)`-form. -/
def ddcTest (e : ComplexChart (q + 1) X) (φ : 𝓓(chartTarget e, ℝ)) :
    ClosedRealOneOneForm (q + 1) X :=
  ddcClosedForm (chartExtend e φ) (chartSmooth_testFunction e φ)

/-- **The top-degree test form** `Π₁₁ ddᶜ(φ ∘ e) ∧ β_a^q`. -/
def leviDDCTest (e : ComplexChart (q + 1) X) (ψ φ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (q + 1)) : testSpace (q + 1) X (q + 1) :=
  slotForm (ddcTest e φ).val q fun _ => leviSlot e ψ a

theorem ddcTest_coeff_eq {e : ComplexChart (q + 1) X} {φ : 𝓓(chartTarget e, ℝ)}
    {z : ComplexModel (q + 1)} (hz : z ∈ e.val.target) :
    (ddcTest e φ).val.coeff e z = smoothDDC φ z := by
  rw [ddcTest, ddcClosedForm_coeff, smoothDDC_congr (chartExtend_eventuallyEq hz)]

/-- Off `e⁻¹(supp φ)` the form `ddᶜ(φ ∘ e)` vanishes in every chart. -/
theorem ddcTest_coeff_eq_zero {e : ComplexChart (q + 1) X} {φ : 𝓓(chartTarget e, ℝ)}
    (e' : ComplexChart (q + 1) X) {z : ComplexModel (q + 1)} (hz : z ∈ e'.val.target)
    (hx : e'.val.symm z ∉ e.val.symm '' tsupport φ) :
    (ddcTest e φ).val.coeff e' z = 0 :=
  ddcForm_coeff_eq_zero (chartSmooth_testFunction e φ) hz fun h =>
    hx (tsupport_chartExtend_subset φ.hasCompactSupport φ.tsupport_subset le_rfl h)

/-- **The density of the top test form** in `e`: `(q!/π^{q+1}) L_φ(a)`, at every point of the chart,
when `ψ ≡ 1` near `supp φ`. -/
theorem topDensity_leviDDCTest_coeff {e : ComplexChart (q + 1) X} {ψ φ : 𝓓(chartTarget e, ℝ)}
    {a : ComplexModel (q + 1)} (ha : ‖a‖ = 1)
    (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1)
    {z : ComplexModel (q + 1)} (hz : z ∈ e.val.target) :
    topDensity (((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
        SmoothRealForm (q + 1) X (2 * (q + 1))).coeff e z) =
      ((q.factorial : ℝ) / Real.pi ^ (q + 1)) * leviForm φ z a := by
  have hφ2 : ContDiffAt ℝ 2 (φ : ComplexModel (q + 1) → ℝ) z :=
    φ.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [leviDDCTest, slotForm_coeff, ddcTest_coeff_eq hz,
    pi11_eq_self (MongeAmpere.smoothDDC_isOneOne hφ2)]
  by_cases hzs : z ∈ tsupport φ
  · simp only [leviSlot_coeff_eq hz (hψ z hzs)]
    exact topDensity_smoothDDC_perpQuadratic hφ2 a ha
  · have h0 : (φ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hzs
    rw [smoothDDC_congr h0, smoothDDC_zero, wedgeProd_cons_zero, topDensity_zero,
      leviForm_eq_zero_of_notMem_tsupport hzs, mul_zero]

/-- Off `e⁻¹(supp φ)` the top test form vanishes in every chart. -/
theorem leviDDCTest_coeff_eq_zero {e : ComplexChart (q + 1) X} {ψ φ : 𝓓(chartTarget e, ℝ)}
    {a : ComplexModel (q + 1)} (e' : ComplexChart (q + 1) X) {z : ComplexModel (q + 1)}
    (hz : z ∈ e'.val.target) (hx : e'.val.symm z ∉ e.val.symm '' tsupport φ) :
    ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
        SmoothRealForm (q + 1) X (2 * (q + 1))).coeff e' z = 0 := by
  rw [leviDDCTest, slotForm_coeff, ddcTest_coeff_eq_zero e' hz hx, pi11_zero,
    wedgeProd_cons_zero]

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The pairing with a continuous function, read in the chart**:
`∫_X v · (Π₁₁ ddᶜ(φ ∘ e) ∧ β_a^q / ωⁿ) dV = (q!/π^{q+1}) · Levi_a([v ∘ e⁻¹])(φ)`. -/
theorem integral_mul_topRatio_leviDDCTest (w : KahlerBackground (q + 1) X)
    {e : ComplexChart (q + 1) X} {ψ φ : 𝓓(chartTarget e, ℝ)} {a : ComplexModel (q + 1)}
    (ha : ‖a‖ = 1) (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (q + 1) → ℝ) =ᶠ[𝓝 z] 1)
    {v : X → ℝ} (hv : Continuous v)
    (hvl : LocallyIntegrableOn (fun z => v (e.val.symm z)) (chartTarget e) volume) :
    ∫ x, v x * topRatio w.form.val ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
        SmoothRealForm (q + 1) X (2 * (q + 1))) x ∂(kahlerVolume w) =
      ((q.factorial : ℝ) / Real.pi ^ (q + 1)) *
        distributionalLeviCLM a (regularDistribution volume (fun z => v (e.val.symm z)) hvl) φ := by
  set Λ : SmoothRealForm (q + 1) X (2 * (q + 1)) :=
    ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
      SmoothRealForm (q + 1) X (2 * (q + 1))) with hΛ
  set K := tsupport (φ : ComplexModel (q + 1) → ℝ) with hK
  have hKt : K ⊆ e.val.target := φ.tsupport_subset
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hzero : ∀ x ∉ e.val.symm '' K, v x * topRatio w.form.val Λ x = 0 := by
    intro x hx
    have hxs : x ∈ (complexChartAt (n := q + 1) x).val.source := mem_complexChartAt_source x
    have hc := leviDDCTest_coeff_eq_zero (ψ := ψ) (a := a) (complexChartAt (n := q + 1) x)
      ((complexChartAt (n := q + 1) x).val.map_source hxs)
      (by rwa [(complexChartAt (n := q + 1) x).val.left_inv hxs])
    simp only [topRatio, chartRatio, hΛ, hc, topDensity_zero, zero_div, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_kahlerVolume_image (G := fun x => v x * topRatio w.form.val Λ x) w e hKm hKt
      (hv.mul (continuous_topRatio w.isKahler.1 Λ)),
    distributionalLeviCLM_regularDistribution_apply, ← integral_const_mul]
  have hpt : ∀ z ∈ K, volDensity w e z * (v (e.val.symm z) * topRatio w.form.val Λ (e.val.symm z)) =
      ((q.factorial : ℝ) / Real.pi ^ (q + 1)) * (v (e.val.symm z) * leviForm φ z a) := by
    intro z hz
    have hzt := hKt hz
    rw [topRatio_eq_chartRatio w.isKahler.1 _ (e.val.map_target hzt), e.val.right_inv hzt,
      chartRatio, hΛ, topDensity_leviDDCTest_coeff ha hψ hzt]
    change volDensity w e z * (v (e.val.symm z) * (_ / volDensity w e z)) = _
    field_simp [(volDensity_pos w e hzt).ne']
  rw [setIntegral_congr_fun hKm hpt]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  rw [leviForm_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end SGPT.Foundations.Analysis.Pending.FibrePotentialLevi
