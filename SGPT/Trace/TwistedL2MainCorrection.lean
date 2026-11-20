import SGPT.Trace.TwistedL2MainFunctional

/-!
# The actual correction section represented by an `H₁` element

An `H₁` element is an `L²(μ|U)` class in the measurable unit frame. On the
actual open set the strictly positive weight makes division by its square root
well-defined. The pointwise section below is the original bundle-valued
correction, not a replacement scalar problem. This file does not claim that it
is smooth, holomorphic, or has the desired weak derivative.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The actual bundle section associated to an `H₁` representative; its
values outside `U` are irrelevant. -/
def correctionSection (u : Lp ℂ 2 (T.μ.restrict T.U)) (x : X) : T.L.Fiber x :=
  ((T.sqrtW x : ℂ)⁻¹ * (u : X → ℂ) x) • unitFrame T.L x

omit [BorelSpace X] in
/-- In every actual holomorphic frame the correction coefficient is the
unit-frame coefficient multiplied by the same scalar `L²` representative. -/
theorem frameCoeff_correctionSection (u : Lp ℂ 2 (T.μ.restrict T.U))
    (e : AtlasFrame T.L) {x : X} (hx : x ∈ e.val.baseSet) :
    (e.val ⟨x, T.correctionSection u x⟩).2 =
      ((T.sqrtW x : ℂ)⁻¹ * (u : X → ℂ) x) * unitCoeff e x := by
  exact frameCoeff_smul_unitFrame e hx _

/-- The actual chart/frame coefficient of the correction section. -/
def chartCorrectionCoeff (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c : ComplexChart n X) (e : AtlasFrame T.L) (z : ComplexModel n) : ℂ :=
  chartCoeff T.L c e (T.correctionSection u) z

omit [BorelSpace X] in
/-- On the actual chart/frame domain this coefficient is read through the
measurable unit-frame coefficient, with no chart-independence assumed. -/
theorem chartCorrectionCoeff_of_mem (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c : ComplexChart n X) (e : AtlasFrame T.L) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain T.L c e) :
    T.chartCorrectionCoeff u c e z =
      ((T.sqrtW (c.val.symm z) : ℂ)⁻¹ * (u : X → ℂ) (c.val.symm z)) *
        unitCoeff e (c.val.symm z) := by
  exact T.frameCoeff_correctionSection u e hz.2

/-- The weighted unit-frame coordinate of the correction is the original
`L²` representative, pointwise on `U`. -/
theorem H1coord_correctionSection (u : Lp ℂ 2 (T.μ.restrict T.U))
    {x : X} (hx : x ∈ T.U) : T.H1coord (T.correctionSection u) x = (u : X → ℂ) x := by
  have hw : (T.sqrtW x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (T.sqrtW_pos hx)
  rw [H1coord, correctionSection, inner_unitFrame_smul]
  calc (T.sqrtW x : ℂ) * ((T.sqrtW x : ℂ)⁻¹ * (u : X → ℂ) x) =
        ((T.sqrtW x : ℂ) * (T.sqrtW x : ℂ)⁻¹) * (u : X → ℂ) x := by ring
    _ = (u : X → ℂ) x := by rw [mul_inv_cancel₀ hw, one_mul]

/-- The original weighted fibre norm of the correction equals the squared
modulus of the scalar `L²` representative on `U`. -/
theorem correctionSection_weighted_norm_sq (u : Lp ℂ 2 (T.μ.restrict T.U))
    {x : X} (hx : x ∈ T.U) :
    ‖T.correctionSection u x‖ ^ 2 * T.H1weight x = ‖(u : X → ℂ) x‖ ^ 2 := by
  rw [← T.norm_H1coord_sq (T.correctionSection u) hx, T.H1coord_correctionSection u hx]

/-- The weighted fibre-norm lintegral of the actual correction is the squared
norm of the `L²` class, including an empty open set. -/
theorem lintegral_correctionSection_eq_norm_sq (u : Lp ℂ 2 (T.μ.restrict T.U)) :
    (∫⁻ x in T.U, ENNReal.ofReal
      (‖T.correctionSection u x‖ ^ 2 * T.H1weight x) ∂T.μ) =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  have hint : Integrable (fun x => ‖(u : X → ℂ) x‖ ^ 2) (T.μ.restrict T.U) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp u).1).mp (Lp.memLp u)
  have hnorm : ‖u‖ ^ 2 = ∫ x, ‖(u : X → ℂ) x‖ ^ 2 ∂(T.μ.restrict T.U) := by
    have h : ⟪u, u⟫_ℂ =
        ∫ x, ⟪(u : X → ℂ) x, (u : X → ℂ) x⟫_ℂ ∂(T.μ.restrict T.U) :=
      MeasureTheory.L2.inner_def u u
    rw [inner_self_eq_norm_sq_to_K] at h
    have h2 : (∫ x, ⟪(u : X → ℂ) x, (u : X → ℂ) x⟫_ℂ ∂(T.μ.restrict T.U)) =
        ∫ x, ((‖(u : X → ℂ) x‖ ^ 2 : ℝ) : ℂ) ∂(T.μ.restrict T.U) := by
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [h2, integral_complex_ofReal] at h
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h)
  calc
    (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.correctionSection u x‖ ^ 2 * T.H1weight x) ∂T.μ)
        = ∫⁻ x, ENNReal.ofReal (‖(u : X → ℂ) x‖ ^ 2) ∂(T.μ.restrict T.U) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem T.isOpen_U.measurableSet] with x hx
          rw [T.correctionSection_weighted_norm_sq u hx]
    _ = ENNReal.ofReal (∫ x, ‖(u : X → ℂ) x‖ ^ 2 ∂(T.μ.restrict T.U)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)).symm
    _ = ENNReal.ofReal (‖u‖ ^ 2) := by rw [← hnorm]

/-- Assuming the finite-family functional bound, the actual bundle-valued
correction has the exact original weighted `L²` bound and satisfies all local
adjoint-test equations. The weak equation and holomorphic gluing remain to be
proved separately. -/
theorem exists_bundle_correction_of_functional
    (hfunctional : TwistedFunctionalBoundStatement n X)
    (hfinite : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ∃ u : Lp ℂ 2 (T.μ.restrict T.U),
      (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.correctionSection u x‖ ^ 2 * T.H1weight x) ∂T.μ) ≤
        (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) ∧
      ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing := by
  obtain ⟨u, hnorm, htest⟩ := T.exists_local_test_solution_of_functional hfunctional hfinite
  refine ⟨u, ?_, htest⟩
  let m : ℝ≥0∞ := ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ
  have hsq : ‖u‖ ^ 2 ≤ m.toReal := by
    calc ‖u‖ ^ 2 ≤ Real.sqrt m.toReal ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = m.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  calc
    (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.correctionSection u x‖ ^ 2 * T.H1weight x) ∂T.μ)
        = ENNReal.ofReal (‖u‖ ^ 2) := T.lintegral_correctionSection_eq_norm_sq u
    _ ≤ ENNReal.ofReal m.toReal := ENNReal.ofReal_le_ofReal hsq
    _ = m := ENNReal.ofReal_toReal hfinite.ne

end TwistedDatum
end SGPT.Trace.TwistedL2
