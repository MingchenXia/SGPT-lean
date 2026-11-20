import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.XiaoHermitianFormEstimate

set_option autoImplicit false

/-!
# Xiao's one-slot density identity for actual exterior products

The cofactor formula is transferred from normalized Hermitian matrices to
`actualTopPowerDensity` and `actualMixedTopDensity`. A Monge–Ampère density
equation and a one-slot mixed density bound then produce the trace bound and
semipositivity of the actual difference form. No trace or form comparison is
introduced as an assumption for that conclusion.
-/

namespace SGPT.Foundations.Analysis.Pending.XiaoMixedDensityTrace

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  FirstPass.PositiveClasses StronglyPositiveForms SubmanifoldMassConcentration

/-- The one-slot cofactor identity, with the genuine exterior-product densities. -/
theorem actualTopPowerDensity_mul_trace {m : ℕ} {A B : RealForm (m + 1) 2}
    (hA : IsOneOne A) (hB : IsOneOne B) (hAp : IsStrictlyPositive A) :
    actualTopPowerDensity A *
        ((normalizedHermitianMatrix A)⁻¹ * normalizedHermitianMatrix B).trace.re =
      (m + 1 : ℝ) * actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) := by
  have hdiag : actualTopPowerDensity A =
      (mixedCoefficient (fun _ : Fin (m + 1) => normalizedHermitianMatrix A)).re /
        Real.pi ^ (m + 1) := by
    rw [← actualMixedTopDensity_const A]
    exact ConcentrationMassComparison.actualMixedTopDensity_eq_re (fun _ => hA)
  have hfamily : ∀ i : Fin (m + 1), IsOneOne
      ((Fin.cons B (fun _ : Fin m => A) : Fin (m + 1) → RealForm (m + 1) 2) i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact hB
    · exact hA
  have hmap : (fun i : Fin (m + 1) =>
      normalizedHermitianMatrix
        ((Fin.cons B (fun _ : Fin m => A) : Fin (m + 1) → RealForm (m + 1) 2) i)) =
      Fin.cons (normalizedHermitianMatrix B)
        (fun _ : Fin m => normalizedHermitianMatrix A) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hmix := ConcentrationMassComparison.actualMixedTopDensity_eq_re hfamily
  rw [hmap] at hmix
  have hid := KahlerLaplacianStokes.re_mixedCoefficient_const_mul_re_trace
    (ConcentrationMassComparison.normalizedHermitianMatrix_posDef hA hAp)
    (normalizedHermitianMatrix B)
  rw [hdiag, hmix]
  calc
    _ = ((mixedCoefficient (fun _ : Fin (m + 1) => normalizedHermitianMatrix A)).re *
        ((normalizedHermitianMatrix A)⁻¹ * normalizedHermitianMatrix B).trace.re) /
          Real.pi ^ (m + 1) := by ring
    _ = _ := by rw [hid]; ring

/-- The Monge–Ampère equation and a mixed density bound produce the trace estimate. -/
theorem trace_le_of_density_bound {m : ℕ} {A B : RealForm (m + 1) 2}
    (hA : IsOneOne A) (hB : IsOneOne B) (hAp : IsStrictlyPositive A)
    {c v γ M : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hMA : actualTopPowerDensity A = c * v)
    (hmix : actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) ≤ γ * M * v) :
    ((normalizedHermitianMatrix A)⁻¹ * normalizedHermitianMatrix B).trace.re ≤
      (m + 1 : ℝ) * γ * M / c := by
  have hid := actualTopPowerDensity_mul_trace hA hB hAp
  have hbound : c *
      ((normalizedHermitianMatrix A)⁻¹ * normalizedHermitianMatrix B).trace.re * v ≤
      ((m + 1 : ℝ) * γ * M) * v := by
    calc
      _ = (m + 1 : ℝ) *
          actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) := by
        rw [← hid, hMA]
        ring
      _ ≤ (m + 1 : ℝ) * (γ * M * v) :=
        mul_le_mul_of_nonneg_left hmix (by positivity)
      _ = _ := by ring
  have hcancel := le_of_mul_le_mul_right hbound hv
  apply (le_div_iff₀ hc).2
  simpa only [mul_comm] using hcancel

/-- Xiao's good-set form comparison follows from the actual density data. -/
theorem coefficientSemipositive_sub_smul_of_density_bound {m : ℕ}
    {A B : RealForm (m + 1) 2} (hA : IsOneOne A) (hB : IsOneOne B)
    (hAp : IsStrictlyPositive A) (hBp : IsStrictlyPositive B)
    {c v γ M : ℝ} (hc : 0 < c) (hv : 0 < v) (hγ : 0 < γ) (hM : 0 < M)
    (hMA : actualTopPowerDensity A = c * v)
    (hmix : actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) ≤ γ * M * v) :
    CoefficientSemipositive (A - (c / ((m + 1 : ℝ) * γ * M)) • B) := by
  have hT : 0 < (m + 1 : ℝ) * γ * M / c := by positivity
  simpa only [inv_div] using
    XiaoHermitianFormEstimate.coefficientSemipositive_sub_inv_smul hA hB hAp hBp hT
      (trace_le_of_density_bound hA hB hAp hc hv hMA hmix)

/-- The same genuine density comparison gives a semipositive smooth difference globally. -/
theorem isSemipositive_sub_smul_of_density_bound {m : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    (A B : ClosedRealOneOneForm (m + 1) X) (hA : A.val.IsKahler) (hB : B.val.IsKahler)
    {c γ M : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hM : 0 < M)
    (v : ComplexChart (m + 1) X → ComplexModel (m + 1) → ℝ)
    (hv : ∀ e z, z ∈ e.val.target → 0 < v e z)
    (hMA : ∀ e z, z ∈ e.val.target →
      actualTopPowerDensity (A.val.coeff e z) = c * v e z)
    (hmix : ∀ e z, z ∈ e.val.target →
      actualMixedTopDensity (Fin.cons (B.val.coeff e z)
        (fun _ : Fin m => A.val.coeff e z)) ≤ γ * M * v e z) :
    (A - (c / ((m + 1 : ℝ) * γ * M)) • B).val.IsSemipositive := by
  intro e z hz
  simpa only [CoefficientSemipositive, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul] using
    coefficientSemipositive_sub_smul_of_density_bound (A.property.2 e z hz)
      (B.property.2 e z hz) (hA.1 e z hz).2 (hB.1 e z hz).2
      hc (hv e z hz) hγ hM (hMA e z hz) (hmix e z hz)

end SGPT.Foundations.Analysis.Pending.XiaoMixedDensityTrace
