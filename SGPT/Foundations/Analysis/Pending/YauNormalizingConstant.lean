import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The normalising constant of the limit equation vanishes (class invariance)

Let `Y` be a compact connected complex manifold of dimension `N > 0` with a Kähler form `A`, `F` a
function with `∫_Y e^F A^N = ∫_Y A^N`, and `φ` chart-smooth with `A_φ = A + ddᶜφ` Kähler and

`A_φ^N = e^{F + κ} A^N`  (chart densities)

for a constant `κ`.  Then `κ = 0` (`eq_zero_of_mongeAmpere_eq_exp_add`).

This is the last step of P3(d) of N5 (the limit `ε → 0` of the `ε`-continuity path produces
`(A + ddᶜψ)^N = e^{F + κ} A^N` with `κ = lim ε sup φ_ε`) in TN23's plan
the proof of Yau's theorem; statement the statement under discussion (T3), split settled
in C-0063, confirmed by TN23 in C-0065.  Textbook: Székelyhidi, *An Introduction to Extremal Kähler
Metrics*, §3.4 (the normalisation `∫ e^F ωⁿ = ∫ ωⁿ` is forced by the class).

## Proof

`∫_Y A_φ^N = ∫_Y A^N` (class invariance of the total mass of a top power,
`NefMixedMass.slotIntegral_add_ddc`, i.e. `MixedMassClassInvariance`), the density ratio of `A_φ^N`
against `A^N` is `e^{F + κ}` at every point, so `e^κ ∫ e^F A^N = ∫ A^N`; with the normalisation and
`∫ A^N > 0` (`N > 0`, `Y ≠ ∅`), `e^κ = 1`.  No regularity of `F` is used.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.YauNormalizingConstant

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses IntegrationCurrent
  TopDegreeDensity ManifoldTubePositivity NefMixedMass ProductTestForms StronglyPositiveForms

noncomputable section

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The density ratio of `A_φ^N` against `A^N` is `e^{F + κ}` at every point. -/
theorem topRatio_formPow_eq_exp (A : KahlerBackground N Y) {F φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) {κ : ℝ}
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (F (e.val.symm z) + κ) * actualTopPowerDensity (A.form.val.coeff e z))
    (x : Y) :
    topRatio A.form.val (formPow (A.form + ddcClosedForm φ hφ).val N) x =
      Real.exp (F x + κ) := by
  have hx := mem_complexChartAt_source (n := N) x
  have hz := (complexChartAt (n := N) x).val.map_source hx
  have hpos : 0 < actualTopPowerDensity (A.form.val.coeff (complexChartAt (n := N) x)
      ((complexChartAt (n := N) x).val x)) := by
    have h := topDensity_formPow_pos A.isKahler.1 hz
    rwa [formPow_coeff, topDensity_formPower] at h
  simp only [topRatio, chartRatio, formPow_coeff, topDensity_formPower]
  rw [hdens _ _ hz, (complexChartAt (n := N) x).val.left_inv hx, mul_div_assoc,
    div_self hpos.ne', mul_one]

/-- **Class invariance of the total mass**: `∫_Y A_φ^N = ∫_Y A^N`. -/
theorem integral_topRatio_formPow_add_ddc [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (A : KahlerBackground N Y) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) :
    ∫ x, topRatio A.form.val (formPow (A.form + ddcClosedForm φ hφ).val N) x
        ∂(kahlerVolume A) = (kahlerVolume A).real univ := by
  simp_rw [NefCoreKahlerCurrent.topRatio_formPow_eq_slotForm']
  rw [← slotIntegral, slotIntegral_add_ddc A (fun _ => A.form) (fun _ => φ) (fun _ => hφ),
    slotIntegral]
  simp_rw [← NefCoreKahlerCurrent.topRatio_formPow_eq_slotForm', topRatio_formPow A.isKahler.1]
  simp [integral_const]

/-- **`κ = 0` by class invariance** (step P3(d) of N5 of Yau's theorem; I-0831 C-0062 T3): on a
compact connected complex manifold of dimension `N > 0` with a Kähler form `A`, if
`∫ e^F A^N = ∫ A^N`, `A + ddᶜφ` is Kähler and `(A + ddᶜφ)^N = e^{F + κ} A^N` in every chart, then
`κ = 0`. -/
theorem eq_zero_of_mongeAmpere_eq_exp_add [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (hN : 0 < N) (A : KahlerBackground N Y) {F φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hnorm : ∫ y, Real.exp (F y) ∂(kahlerVolume A) = (kahlerVolume A).real univ) {κ : ℝ}
    (hdens : ∀ e z, z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (F (e.val.symm z) + κ) * actualTopPowerDensity (A.form.val.coeff e z)) :
    κ = 0 := by
  have hvol : 0 < (kahlerVolume A).real univ := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    exact NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A
  have h := integral_topRatio_formPow_add_ddc A hφ
  simp_rw [topRatio_formPow_eq_exp A hφ hdens, Real.exp_add] at h
  rw [integral_mul_const, hnorm] at h
  have h1 : Real.exp κ = 1 := by
    have h2 : (kahlerVolume A).real univ * (Real.exp κ - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hvol.ne'
    · linarith
  exact Real.exp_eq_one_iff κ |>.mp h1

end

end SGPT.Foundations.Analysis.Pending.YauNormalizingConstant
