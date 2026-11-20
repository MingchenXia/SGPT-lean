import SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCovectorMetric
import SGPT.Foundations.Analysis.Pending.DistributionTranslationJets
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-! # A genuine all-degree exterior metric dictionary to the original continuous forms -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianOriginalFormMetric

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianDualMetric NaturalHermitianExteriorCovectorMetric

variable {n : ℕ}

/-- Actual basis correspondence for the canonical exterior determinant dual pairing. -/
def exteriorDualEquiv (q : ℕ) :
    (⋀[ℝ]^q (Module.Dual ℝ (ComplexModel n))) ≃ₗ[ℝ]
      Module.Dual ℝ (⋀[ℝ]^q (ComplexModel n)) :=
  ((coordinateRealBasis n).dualBasis.exteriorPower q).equiv
    ((coordinateRealBasis n).exteriorPower q).dualBasis (Equiv.refl _)

/-- The internally produced equivalence is literally the canonical full exterior pairing. -/
theorem exteriorDualEquiv_toLinearMap (q : ℕ) :
    (exteriorDualEquiv (n := n) q).toLinearMap = exteriorPower.pairingDual ℝ (ComplexModel n) q := by
  apply ((coordinateRealBasis n).dualBasis.exteriorPower q).ext
  intro s
  change exteriorDualEquiv q (((coordinateRealBasis n).dualBasis.exteriorPower q) s) = _
  calc
    _ = ((coordinateRealBasis n).exteriorPower q).dualBasis s := Module.Basis.equiv_apply _ _ _ _
    _ = ((coordinateRealBasis n).exteriorPower q).coord s :=
      congrFun (Module.Basis.coe_dualBasis ((coordinateRealBasis n).exteriorPower q)) s
    _ = _ := by
      rw [exteriorPower.basis_coord]
      simp only [exteriorPower.ιMultiDual, exteriorPower.basis_apply, Module.Basis.coe_dualBasis]

private def continuousUpgrade (q : ℕ) (A : (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) :
    (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ where
  toContinuousMultilinearMap := multilinearMapToContinuousOfFiniteDimensional A.toMultilinearMap
  map_eq_zero_of_eq' v i j h hij := by
    simpa using A.map_eq_zero_of_eq v h hij

private theorem continuousUpgrade_apply (q : ℕ)
    (A : (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) (v : Fin q → ComplexModel n) :
    continuousUpgrade q A v = A v := multilinearMapToContinuousOfFiniteDimensional_apply _ v

/-- Pointwise preserving finite-dimensional continuous upgrade is a genuine linear equivalence. -/
def algebraicContinuousEquiv (q : ℕ) :
    ((ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) where
  toFun := continuousUpgrade q
  invFun := ContinuousAlternatingMap.toAlternatingMap
  left_inv A := by ext v; exact continuousUpgrade_apply q A v
  right_inv A := by ext v; exact continuousUpgrade_apply q A.toAlternatingMap v
  map_add' A B := by
    ext v
    simp only [continuousUpgrade_apply, AlternatingMap.add_apply, ContinuousAlternatingMap.add_apply]
  map_smul' r A := by
    ext v
    simp only [continuousUpgrade_apply, AlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      RingHom.id_apply]

instance algebraicFormFiniteDimensional (q : ℕ) :
    FiniteDimensional ℝ ((ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) :=
  FiniteDimensional.of_injective
    (exteriorPower.alternatingMapLinearEquiv : ((ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      Module.Dual ℝ (⋀[ℝ]^q (ComplexModel n))).toLinearMap
    exteriorPower.alternatingMapLinearEquiv.injective

instance originalFormFiniteDimensional (q : ℕ) :
    FiniteDimensional ℝ ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (algebraicContinuousEquiv q).symm.toLinearMap
    (algebraicContinuousEquiv q).symm.injective

variable (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
  (hJ : IsOneOne a) (hp : IsStrictlyPositive a)

/-- Literal metric covector copy to the algebraic dual of the original normed model. -/
def metricCovectorAlgebraicEquiv : MetricCovector a hJ hp ≃ₗ[ℝ] Module.Dual ℝ (ComplexModel n) :=
  (metricCovectorLinearEquiv a hJ hp).trans
    (LinearMap.toContinuousLinearMap : Module.Dual ℝ (ComplexModel n) ≃ₗ[ℝ]
      (ComplexModel n →L[ℝ] ℝ)).symm

/-- Actual exterior functor of the genuine covector equivalence, with both inverses proved. -/
def metricExteriorAlgebraicEquiv (q : ℕ) :
    (⋀[ℝ]^q (MetricCovector a hJ hp)) ≃ₗ[ℝ] (⋀[ℝ]^q (Module.Dual ℝ (ComplexModel n))) :=
  LinearEquiv.ofBijective (exteriorPower.map q (metricCovectorAlgebraicEquiv a hJ hp).toLinearMap)
    ⟨exteriorPower.map_injective_field (metricCovectorAlgebraicEquiv a hJ hp).injective,
      exteriorPower.map_surjective (metricCovectorAlgebraicEquiv a hJ hp).surjective⟩

/-- Actual algebraic dictionary, formed from the perfect pairing and the exterior universal property. -/
def originalFormLinearEquiv (q : ℕ) :
    (⋀[ℝ]^q (MetricCovector a hJ hp)) ≃ₗ[ℝ] ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  (((metricExteriorAlgebraicEquiv a hJ hp q).trans (exteriorDualEquiv q)).trans
    (exteriorPower.alternatingMapLinearEquiv : ((ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      Module.Dual ℝ (⋀[ℝ]^q (ComplexModel n))).symm).trans (algebraicContinuousEquiv q)

/-- Genuine continuous dictionary and inverse in the original form coefficient operator norm. -/
def originalFormDictionary (q : ℕ) :
    (⋀[ℝ]^q (MetricCovector a hJ hp)) ≃L[ℝ] ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  (originalFormLinearEquiv a hJ hp q).toContinuousLinearEquiv

/-- Full canonical exterior-pairing readback for every tensor and original vector tuple. -/
theorem originalFormDictionary_apply (q : ℕ) (x : ⋀[ℝ]^q (MetricCovector a hJ hp))
    (v : Fin q → ComplexModel n) :
    originalFormDictionary a hJ hp q x v =
      exteriorPower.pairingDual ℝ (ComplexModel n) q
        (exteriorPower.map q (metricCovectorAlgebraicEquiv a hJ hp).toLinearMap x)
        (exteriorPower.ιMulti ℝ q v) := by
  change continuousUpgrade q (exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorDualEquiv q (metricExteriorAlgebraicEquiv a hJ hp q x))) v = _
  rw [continuousUpgrade_apply, exteriorPower.alternatingMapLinearEquiv_symm_apply]
  change exteriorDualEquiv q (metricExteriorAlgebraicEquiv a hJ hp q x)
    (exteriorPower.ιMulti ℝ q v) = _
  exact congrArg (fun L : (⋀[ℝ]^q (Module.Dual ℝ (ComplexModel n))) →ₗ[ℝ]
    Module.Dual ℝ (⋀[ℝ]^q (ComplexModel n)) => L (metricExteriorAlgebraicEquiv a hJ hp q x)
      (exteriorPower.ιMulti ℝ q v)) (exteriorDualEquiv_toLinearMap q)

/-- Exact determinant evaluation of arbitrary original covectors through the genuine dictionary. -/
theorem originalFormDictionary_decomposable_apply (q : ℕ)
    (α : Fin q → (ComplexModel n →L[ℝ] ℝ)) (v : Fin q → ComplexModel n) :
    originalFormDictionary a hJ hp q (exteriorCovectorDecomposable a hJ hp q α) v =
      Matrix.det (Matrix.of fun i j => α j (v i)) := by
  rw [originalFormDictionary_apply]
  change exteriorPower.pairingDual ℝ (ComplexModel n) q
    (exteriorPower.map q (metricCovectorAlgebraicEquiv a hJ hp).toLinearMap
      (exteriorPower.ιMulti ℝ q (fun i => (metricCovectorEquiv a hJ hp).symm (α i))))
      (exteriorPower.ιMulti ℝ q v) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

/-- Actual continuous bilinear form metric, preserving the existing coefficient norm and topology. -/
def originalFormMetric (q : ℕ) : ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
    ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)
    (⋀[ℝ]^q (MetricCovector a hJ hp)) ℝ).flip
      (originalFormDictionary a hJ hp q).symm.toContinuousLinearMap).comp
    ((innerSL ℝ).comp (originalFormDictionary a hJ hp q).symm.toContinuousLinearMap)

/-- Literal full metric value through the genuine inverse dictionary. -/
theorem originalFormMetric_apply (q : ℕ)
    (η θ : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    originalFormMetric a hJ hp q η θ =
      inner ℝ ((originalFormDictionary a hJ hp q).symm η)
        ((originalFormDictionary a hJ hp q).symm θ) := rfl

/-- Symmetry and whole coefficient-space strict positivity are internally produced. -/
theorem originalFormMetric_symm_positive (q : ℕ) :
    (∀ η θ : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ,
      originalFormMetric a hJ hp q η θ = originalFormMetric a hJ hp q θ η) ∧
    ∀ η : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ, η ≠ 0 → 0 < originalFormMetric a hJ hp q η η := by
  refine ⟨?_, ?_⟩
  · intro η θ
    simp only [originalFormMetric_apply]
    exact real_inner_comm _ _
  · intro η hη
    rw [originalFormMetric_apply]
    apply real_inner_self_pos.mpr
    intro hzero
    apply hη
    have h := congrArg (originalFormDictionary a hJ hp q) hzero
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h

/-- Original decomposable form metric has the literal true inverse-metric Gram determinant. -/
theorem originalFormMetric_decomposable (q : ℕ)
    (α β : Fin q → (ComplexModel n →L[ℝ] ℝ)) :
    originalFormMetric a hJ hp q
        (originalFormDictionary a hJ hp q (exteriorCovectorDecomposable a hJ hp q α))
        (originalFormDictionary a hJ hp q (exteriorCovectorDecomposable a hJ hp q β)) =
      Matrix.det (Matrix.of fun i j => β i ((associatedMetricCLM a).inverse (α j))) := by
  rw [originalFormMetric_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  exact exteriorCovector_inner_decomposable a hJ hp q α β

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Every actual original Hermitian chart point supplies all-degree genuine positive form metrics. -/
theorem original_chart_all_degree_form_metric (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    let a := w.coeff e z
    let hJ := (hw e z hz).1
    let hp := (hw e z hz).2
    (∀ η θ : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ,
      originalFormMetric a hJ hp q η θ = originalFormMetric a hJ hp q θ η) ∧
    (∀ η : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ, η ≠ 0 → 0 < originalFormMetric a hJ hp q η η) ∧
    ∀ α β : Fin q → (ComplexModel n →L[ℝ] ℝ),
      originalFormMetric a hJ hp q
          (originalFormDictionary a hJ hp q (exteriorCovectorDecomposable a hJ hp q α))
          (originalFormDictionary a hJ hp q (exteriorCovectorDecomposable a hJ hp q β)) =
        Matrix.det (Matrix.of fun i j => dualMetricCoefficients w e z (α j) (β i)) := by
  refine ⟨(originalFormMetric_symm_positive _ _ _ q).1,
    (originalFormMetric_symm_positive _ _ _ q).2, ?_⟩
  intro α β
  exact originalFormMetric_decomposable _ _ _ q α β

end SGPT.Foundations.Analysis.Pending.NaturalHermitianOriginalFormMetric
