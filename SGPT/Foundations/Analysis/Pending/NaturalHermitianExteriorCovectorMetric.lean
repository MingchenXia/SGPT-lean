import SGPT.Foundations.Analysis.Pending.NaturalHermitianDualMetric
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Mathlib.Algebra.Module.TransferInstance

/-! # Actual metric covectors and positive metrics in every exterior degree -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCovectorMetric

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients NaturalHermitianMusicalInverse
  NaturalHermitianDualMetric

variable {n : ℕ}

/-- A separate covector copy; no norm on the original continuous dual is replaced. -/
structure MetricCovector (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) where
  val : ComplexModel n →L[ℝ] ℝ

variable (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
  (hJ : IsOneOne a) (hp : IsStrictlyPositive a)

/-- Literal underlying-copy equivalence with the original continuous real dual. -/
def metricCovectorEquiv : MetricCovector a hJ hp ≃ (ComplexModel n →L[ℝ] ℝ) where
  toFun := MetricCovector.val
  invFun := MetricCovector.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance metricCovectorAddCommGroup : AddCommGroup (MetricCovector a hJ hp) :=
  (metricCovectorEquiv a hJ hp).addCommGroup

instance metricCovectorModule : Module ℝ (MetricCovector a hJ hp) :=
  (metricCovectorEquiv a hJ hp).module ℝ

/-- Genuine copy map as a real linear equivalence. -/
def metricCovectorLinearEquiv : MetricCovector a hJ hp ≃ₗ[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  (metricCovectorEquiv a hJ hp).linearEquiv ℝ

instance metricCovectorFiniteDimensional : FiniteDimensional ℝ (MetricCovector a hJ hp) :=
  FiniteDimensional.of_injective (metricCovectorLinearEquiv a hJ hp).toLinearMap
    (metricCovectorLinearEquiv a hJ hp).injective

/-- Original positivity produces the actual metric norm only on the new covector copy. -/
instance metricCovectorCore : InnerProductSpace.Core ℝ (MetricCovector a hJ hp) where
  inner x y := dualMetricCLM (associatedMetricCLM a).inverse x.val y.val
  conj_inner_symm x y := by
    simpa only [starRingEnd_apply, star_trivial] using (dualMetric_symm_positive hJ hp).1 y.val x.val
  add_left x y z := by
    change dualMetricCLM (associatedMetricCLM a).inverse (x.val + y.val) z.val = _
    simp only [map_add, add_apply]
  smul_left x y r := by
    change dualMetricCLM (associatedMetricCLM a).inverse (r • x.val) y.val = _
    simp only [map_smul, smul_apply, smul_eq_mul, starRingEnd_apply,
      star_trivial]
  re_inner_nonneg x := by
    change 0 ≤ dualMetricCLM (associatedMetricCLM a).inverse x.val x.val
    by_cases hx : x.val = 0
    · rw [hx, map_zero]
    · exact le_of_lt ((dualMetric_symm_positive hJ hp).2 _ hx)
  definite x hx := by
    apply (metricCovectorEquiv a hJ hp).injective
    change x.val = 0
    by_contra hne
    exact ((dualMetric_symm_positive hJ hp).2 _ hne).ne' hx

instance metricCovectorNormedAddCommGroup : NormedAddCommGroup (MetricCovector a hJ hp) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance metricCovectorInnerProductSpace : InnerProductSpace ℝ (MetricCovector a hJ hp) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (MetricCovector a hJ hp))

/-- The complete metric-copy dictionary retains the original operator norm on its target. -/
def metricCovectorContinuousEquiv : MetricCovector a hJ hp ≃L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  (metricCovectorLinearEquiv a hJ hp).toContinuousLinearEquiv

/-- Literal underlying original covector readback. -/
theorem metricCovectorContinuousEquiv_apply (x : MetricCovector a hJ hp) :
    metricCovectorContinuousEquiv a hJ hp x = x.val := rfl

/-- Exact actual dual inner product, calibrated in the original continuous dual. -/
theorem metricCovector_inner (x y : MetricCovector a hJ hp) :
    inner ℝ x y = y.val ((associatedMetricCLM a).inverse x.val) := rfl

/-- Actual completeness of the new metric covector norm, from its proved finite dimension. -/
theorem metricCovector_complete : CompleteSpace (MetricCovector a hJ hp) := inferInstance

/-- Arbitrary original covectors give actual decomposable exterior covector tensors. -/
def exteriorCovectorDecomposable (q : ℕ) (α : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    ⋀[ℝ]^q (MetricCovector a hJ hp) :=
  exteriorPower.ιMulti ℝ q (fun i => (metricCovectorEquiv a hJ hp).symm (α i))

/-- Full Gram determinant for every pair of original covector families and every degree. -/
theorem exteriorCovector_inner_decomposable (q : ℕ)
    (α β : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    inner ℝ (exteriorCovectorDecomposable a hJ hp q α)
        (exteriorCovectorDecomposable a hJ hp q β) =
      Matrix.det (Matrix.of fun i j => β i ((associatedMetricCLM a).inverse (α j))) := by
  exact exteriorPower.inner_ιMulti_ιMulti _ _

/-- Genuine strict positivity on the whole exterior power, including nondecomposable tensors. -/
theorem exteriorCovector_inner_self_pos (q : ℕ) (x : ⋀[ℝ]^q (MetricCovector a hJ hp))
    (hx : x ≠ 0) : 0 < inner ℝ x x := real_inner_self_pos.mpr hx

/-- Actual completeness of every exterior metric norm, including zero and excessive degrees. -/
theorem exteriorCovector_complete (q : ℕ) :
    CompleteSpace (⋀[ℝ]^q (MetricCovector a hJ hp)) := inferInstance

/-- Genuine exterior dimension of the actual metric covector space in every degree. -/
theorem exteriorCovector_finrank (q : ℕ) :
    Module.finrank ℝ (⋀[ℝ]^q (MetricCovector a hJ hp)) = (n * 2).choose q := by
  rw [exteriorPower.finrank_eq, (metricCovectorLinearEquiv a hJ hp).finrank_eq,
    ← (metricMusicalEquiv hp).toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (coordinateRealBasis n), Fintype.card_fin]

/-- Every tensor above the original real dimension actually vanishes. -/
theorem exteriorCovector_above_dimension (q : ℕ) (hq : n * 2 < q)
    (x : ⋀[ℝ]^q (MetricCovector a hJ hp)) : x = 0 := by
  have hz : Module.finrank ℝ (⋀[ℝ]^q (MetricCovector a hJ hp)) = 0 := by
    rw [exteriorCovector_finrank a hJ hp q, Nat.choose_eq_zero_of_lt hq]
  let : Subsingleton (⋀[ℝ]^q (MetricCovector a hJ hp)) :=
    (Module.finrank_zero_iff (R := ℝ)).mp hz
  exact Subsingleton.elim _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Original Hermitian chart data alone supplies the actual all-degree positive exterior metrics. -/
theorem original_chart_exterior_metric (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    let a := w.coeff e z
    let hJ := (hw e z hz).1
    let hp := (hw e z hz).2
    (∀ α β : Fin q → (ComplexModel n →L[ℝ] ℝ),
      inner ℝ (exteriorCovectorDecomposable a hJ hp q α)
          (exteriorCovectorDecomposable a hJ hp q β) =
        Matrix.det (Matrix.of fun i j => dualMetricCoefficients w e z (α j) (β i))) ∧
    (∀ x : ⋀[ℝ]^q (MetricCovector a hJ hp), x ≠ 0 → 0 < inner ℝ x x) ∧
    Module.finrank ℝ (⋀[ℝ]^q (MetricCovector a hJ hp)) = (n * 2).choose q := by
  refine ⟨?_, ?_, exteriorCovector_finrank _ _ _ q⟩
  · intro α β
    exact exteriorCovector_inner_decomposable _ _ _ q α β
  · intro x hx
    exact exteriorCovector_inner_self_pos _ _ _ q x hx

end SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCovectorMetric
