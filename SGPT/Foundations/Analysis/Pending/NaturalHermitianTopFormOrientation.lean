import SGPT.Foundations.Analysis.Pending.XiaoComplexProducts
import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Actual normalized positive top forms and original complex chart orientation -/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation

open FirstPass FirstPass.MongeAmpere XiaoComplexProducts ConstantFormProducts

variable {n : ℕ}

private theorem castForm_contDiff {r s : ℕ} (h : r = s) :
    ContDiff ℝ ∞ (castForm (n := n) h) := by
  subst s
  exact contDiff_id

/-- Full original norm-smoothness of every actual coordinate exterior power. -/
theorem coordinatePower_smooth {U : Set (ComplexModel n)}
    {A : ComplexModel n → CoordinateRealTwoForm n} (hA : ContDiffOn ℝ ∞ A U) :
    ∀ k : ℕ, ContDiffOn ℝ ∞ (fun z => coordinateWedgePower (A z) k) U := by
  intro k
  induction k with
  | zero => exact contDiffOn_const
  | succ k ih =>
    cases k with
    | zero => exact hA
    | succ k =>
      have h : (fun z => coordinateWedgePower (A z) (k + 2)) =
          (fun z => castForm (by omega : (k + 1) * 2 + 2 = (k + 2) * 2)
            (coordinateWedge (coordinateWedgePower (A z) (k + 1)) (A z))) := by
        funext z
        ext v
        rw [castForm_apply, coordinateWedgePower_add_two_apply]
      rw [h]
      exact (castForm_contDiff _).comp_contDiffOn (contDiffOn_exteriorProduct ih hA)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Genuine original global power form, in the exact original n*2 interleaved-frame degree convention. -/
def tensorPowerForm (w : SmoothRealForm n M 2) (k : ℕ) : SmoothRealForm n M (k * 2) where
  coeff e z := coordinateWedgePower (w.coeff e z) k
  smooth e := coordinatePower_smooth (w.smooth e) k
  compatible := by
    intro e f z hz v
    have h : w.coeff e z = (w.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext u
      exact w.compatible e f z hz u
    rw [h, coordinateWedgePower_compContinuousLinearMap]
    rfl

/-- The actual normalized Hermitian top form, with its original full tensor coefficients. -/
def normalizedHermitianTopForm (w : SmoothRealForm n M 2) : SmoothRealForm n M (n * 2) :=
  ((n.factorial : ℝ)⁻¹) • tensorPowerForm w n

/-- Exact full vector-tuple readback of the normalized actual top form. -/
theorem normalizedHermitianTopForm_coeff (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) (v : Fin (n * 2) → ComplexModel n) :
    (normalizedHermitianTopForm w).coeff e z v =
      (n.factorial : ℝ)⁻¹ * coordinateWedgePower (w.coeff e z) n v := rfl

/-- Strict positivity is on the actual INTERLEAVED real complex frame, including dimension zero. -/
theorem normalizedHermitianTopForm_positive (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    0 < (normalizedHermitianTopForm w).coeff e z (coordinateRealFrame (n := n)) := by
  rw [normalizedHermitianTopForm_coeff]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  exact mul_pos (inv_pos.mpr hf) (actualTopPowerDensity_pos (hw e z hz).1 (hw e z hz).2)

/-- The genuine full original tensor law and positive interleaved densities prove positive real determinant. -/
theorem chartTransition_det_pos (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source) :
    0 < LinearMap.det (chartTransitionDerivative e f z : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
  have hzf : chartTransition e f z ∈ f.val.target := f.val.map_source hz.2
  have he := actualTopPowerDensity_pos (hw e z hz.1).1 (hw e z hz.1).2
  have hf := actualTopPowerDensity_pos (hw f (chartTransition e f z) hzf).1
    (hw f (chartTransition e f z) hzf).2
  have hcoeff : w.coeff e z = (w.coeff f (chartTransition e f z)).compContinuousLinearMap
      (chartTransitionDerivative e f z) := by
    ext u
    exact w.compatible e f z hz u
  have h := actualTopPowerDensity_compContinuousLinearMap
    (w.coeff f (chartTransition e f z)) (chartTransitionDerivative e f z)
  rw [← hcoeff] at h
  have hmul : 0 < LinearMap.det (chartTransitionDerivative e f z :
      ComplexModel n →ₗ[ℝ] ComplexModel n) * actualTopPowerDensity (w.coeff f (chartTransition e f z)) :=
    h ▸ he
  exact pos_of_mul_pos_left hmul hf.le

/-- Genuine original derivative equivalence and compatibility of the actual interleaved complex orientation. -/
theorem exists_original_chart_orientation_equivalence (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) :
    ∃ A : ComplexModel n ≃L[ℝ] ComplexModel n,
      (A : ComplexModel n →L[ℝ] ComplexModel n) = chartTransitionDerivative e f z ∧
      Orientation.map (Fin (n * 2)) A.toLinearEquiv (coordinateRealBasis n).orientation =
        (coordinateRealBasis n).orientation := by
  let C := chartTransitionDerivative e f z
  have hpos : 0 < LinearMap.det C.toLinearMap := chartTransition_det_pos w hw e f z hz
  have hker : C.ker = ⊥ := by
    by_contra h
    exact hpos.ne' (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hrange : C.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact (LinearMap.injective_iff_surjective (f := C.toLinearMap)).mp (LinearMap.ker_eq_bot.mp hker)
  let A := ContinuousLinearEquiv.ofBijective C hker hrange
  have hA : (A : ComplexModel n →L[ℝ] ComplexModel n) = C :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  refine ⟨A, hA, ?_⟩
  have hposA : 0 < LinearMap.det (A.toLinearEquiv : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
    change 0 < LinearMap.det (A : ComplexModel n →L[ℝ] ComplexModel n).toLinearMap
    rw [hA]
    exact hpos
  have h := ((coordinateRealBasis n).orientation_comp_linearEquiv_eq_iff_det_pos A.toLinearEquiv).mpr hposA
  simpa only [Module.Basis.orientation_map] using h

end SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation
