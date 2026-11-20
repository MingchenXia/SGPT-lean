import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.Pending.LocalCurrents

set_option autoImplicit false

/-! # Actual coordinate readings of distribution-valued two-forms

Literal standard real coordinates construct the complementary current
reader.  Differential and geometric divisor identities are separate.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalCurrentPullbackDdc TopDegreeDensity CoordinateWedgeAssoc
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem pair_update_left (v w : ComplexModel (m + 1)) :
    Function.update ![0, w] 0 v = ![v, w] := by
  ext i
  fin_cases i <;> simp

private theorem pair_update_right (v w : ComplexModel (m + 1)) :
    Function.update ![v, 0] 1 w = ![v, w] := by
  ext i
  fin_cases i <;> simp

private def coefficientPair (A : DistributionForm U 2) :
    ComplexModel (m + 1) →ₗ[ℝ] ComplexModel (m + 1) →ₗ[ℝ] 𝓓'(U, ℝ) where
  toFun v :=
    { toFun := fun w => A ![v, w]
      map_add' w z := by
        simpa only [pair_update_right] using A.map_update_add (v := ![v, 0]) (i := 1) w z
      map_smul' c w := by
        simpa only [pair_update_right, RingHom.id_apply] using
          A.map_update_smul (v := ![v, 0]) (i := 1) c w }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    change A ![v + w, z] = A ![v, z] + A ![w, z]
    simpa only [pair_update_left] using
      A.map_update_add (v := ![0, z]) (i := 0) v w
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change A ![c • v, w] = c • A ![v, w]
    simpa only [pair_update_left] using
      A.map_update_smul (v := ![0, w]) (i := 0) c v

private theorem coefficient_expansion (A : DistributionForm U 2)
    (v w : ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)) :
    A ![v, w] φ = ∑ a, ∑ b,
      (coordCLM (m + 1) a v * coordCLM (m + 1) b w) *
        A ![realBasis (m + 1) a, realBasis (m + 1) b] φ := by
  change coefficientPair A v w φ = _
  have hv : coefficientPair A v = ∑ a, coordCLM (m + 1) a v •
      coefficientPair A (realBasis (m + 1) a) := by
    conv_lhs => rw [← sum_coordCLM_smul v]
    simp only [map_sum, map_smul]
  have hw (a : Fin ((m + 1) * 2)) : coefficientPair A (realBasis (m + 1) a) w =
      ∑ b, coordCLM (m + 1) b w •
        coefficientPair A (realBasis (m + 1) a) (realBasis (m + 1) b) := by
    conv_lhs => rw [← sum_coordCLM_smul w]
    simp only [map_sum, map_smul]
  rw [hv]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [hw]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change _ * (_ * A ![realBasis (m + 1) a, realBasis (m + 1) b] φ) = _
  ring

private theorem coefficient_skew (A : DistributionForm U 2)
    (v w : ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)) :
    A ![w, v] φ = -A ![v, w] φ := by
  have h := A.map_swap (v := ![v, w]) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have he : ![v, w] ∘ Equiv.swap (0 : Fin 2) 1 = ![w, v] := by
    ext i
    fin_cases i <;> simp
  rw [he] at h
  exact congrArg (fun T : 𝓓'(U, ℝ) => T φ) h

/-- The actual tested alternating coefficients as a continuous real two-form. -/
def testedTwoForm (A : DistributionForm U 2) (φ : 𝓓(U, ℝ)) : RealForm (m + 1) 2 :=
  (1 / 2 : ℝ) • ∑ a, ∑ b,
    A ![realBasis (m + 1) a, realBasis (m + 1) b] φ •
      coordinateWedge (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) a))
        (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) b))

/-- The genuine dual-frame reconstruction retains every real coefficient. -/
theorem testedTwoForm_apply (A : DistributionForm U 2) (φ : 𝓓(U, ℝ))
    (v w : ComplexModel (m + 1)) : testedTwoForm A φ ![v, w] = A ![v, w] φ := by
  simp only [testedTwoForm, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sum_apply, smul_eq_mul, coordinateWedge_one_one_apply,
    CoordinateWedgeAssoc.oneForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_sub,
    Finset.sum_sub_distrib]
  have hfirst : ∑ a, ∑ b,
      A ![realBasis (m + 1) a, realBasis (m + 1) b] φ *
        (coordCLM (m + 1) a v * coordCLM (m + 1) b w) = A ![v, w] φ := by
    rw [coefficient_expansion A v w φ]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsecond : ∑ a, ∑ b,
      A ![realBasis (m + 1) a, realBasis (m + 1) b] φ *
        (coordCLM (m + 1) a w * coordCLM (m + 1) b v) = -A ![v, w] φ := by
    have h := coefficient_expansion A w v φ
    rw [coefficient_skew A v w φ] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfirst, hsecond]
  ring

/-- A distribution-valued two-form read against the actual complementary
constant forms, with the literal standard-frame normalization. -/
def complementaryRead (A : DistributionForm U 2) : LocalProductCurrent (m + 1) U m :=
  (1 / 2 : ℝ) • ∑ a, ∑ b, LinearMap.smulRight
    (formDensity (coordinateWedge
      (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) a))
      (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) b))))
    (A ![realBasis (m + 1) a, realBasis (m + 1) b])

private def densityAt (γ : formSpan (m + 1) m) : RealForm (m + 1) 2 →ₗ[ℝ] ℝ where
  toFun β := formDensity β γ
  map_add' β β' := by
    rw [formDensity_apply, formDensity_apply, formDensity_apply,
      coordinateWedge_add_right]
    exact topDensity_add (n := m + 1) _ _
  map_smul' c β := by
    change formDensity (c • β) γ = c * formDensity β γ
    rw [formDensity_apply, formDensity_apply, coordinateWedge_smul_right]
    exact topDensity_smul (n := m + 1) _ _

/-- Every actual compact scalar test pairs with the reconstructed two-form. -/
theorem complementaryRead_apply (A : DistributionForm U 2)
    (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    complementaryRead A γ φ = formDensity (testedTwoForm A φ) γ := by
  change complementaryRead A γ φ = densityAt γ (testedTwoForm A φ)
  simp only [complementaryRead, testedTwoForm, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, map_smul, map_sum, _root_.smul_apply,
    _root_.sum_apply, smul_eq_mul]
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

end SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
