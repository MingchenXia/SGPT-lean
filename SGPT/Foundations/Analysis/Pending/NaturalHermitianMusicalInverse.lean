import SGPT.Foundations.Analysis.Pending.NaturalHermitianRiemannianBundle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual musical equivalences and norm-smooth inverse Hermitian metric -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianMusicalInverse

open FirstPass NaturalHermitianMetricCoefficients NaturalHermitianRiemannianBundle

variable {n : ℕ}

/-- Genuine invertibility of the literal original positive metric in the existing norms. -/
theorem metric_musical_invertible {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) : (associatedMetricCLM a).IsInvertible := by
  have hker : (associatedMetricCLM a).ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    change associatedMetricCLM a u = 0 at hu
    by_contra hne
    have huu := congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L u) hu
    exact (ha u hne).ne' (by
      change associatedMetric a u u = 0
      simpa only [associatedMetricCLM_apply, zero_apply] using huu)
  have hdim : Module.finrank ℝ (ComplexModel n) =
      Module.finrank ℝ (ComplexModel n →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ (ComplexModel n) =
          Module.finrank ℝ (Module.Dual ℝ (ComplexModel n)) := Subspace.dual_finrank_eq.symm
      _ = Module.finrank ℝ (ComplexModel n →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : Module.Dual ℝ (ComplexModel n) ≃ₗ[ℝ]
          (ComplexModel n →L[ℝ] ℝ)).finrank_eq
  have hrange : (associatedMetricCLM a).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    exact LinearMap.ker_eq_bot.mp hker
  exact ⟨ContinuousLinearEquiv.ofBijective (associatedMetricCLM a) hker hrange,
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- Actual musical equivalence, produced by positivity rather than supplied as a datum. -/
def metricMusicalEquiv {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) : ComplexModel n ≃L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  Classical.choose (metric_musical_invertible ha)

/-- Exact original forward metric calibration. -/
theorem metricMusicalEquiv_toCLM {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) :
    (metricMusicalEquiv ha : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) =
      associatedMetricCLM a := Classical.choose_spec (metric_musical_invertible ha)

/-- Both genuine inverse identities of the actual continuous linear inverse. -/
theorem metric_inverse_identities {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) :
    (∀ α : ComplexModel n →L[ℝ] ℝ,
      associatedMetricCLM a ((associatedMetricCLM a).inverse α) = α) ∧
    ∀ u : ComplexModel n, (associatedMetricCLM a).inverse (associatedMetricCLM a u) = u := by
  rcases metric_musical_invertible ha with ⟨A, hA⟩
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  exact ⟨A.apply_symm_apply, A.symm_apply_apply⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

local instance realSmoothManifold : IsManifold 𝓘(ℝ, ComplexModel n) ∞ M :=
  NaturalHermitianRiemannianBundle.real_smooth_manifold

/-- Literal actual inverse metric field, using the existing total operator inverse. -/
def inverseMetricCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n :=
  (metricCoefficients w e z).inverse

/-- The actual inverse metric field is smooth in the whole operator norm on its original target. -/
theorem inverseMetricCoefficients_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) : ContDiffOn ℝ ∞ (inverseMetricCoefficients w e) e.val.target := by
  intro z hz
  have hG := ((metric_coefficients_data w hw).1 e) z hz
  have hI := (metric_musical_invertible (hw e z hz).2).contDiffAt_map_inverse (n := ∞)
  exact hI.comp_contDiffWithinAt z hG

/-- Actual norm-smooth inverse fields and their full original metric readback. -/
theorem exists_smooth_inverse_metric_coefficients (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ H : ComplexChart n M → ComplexModel n →
        (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n,
      (∀ e, ContDiffOn ℝ ∞ (H e) e.val.target) ∧
      ∀ e z, z ∈ e.val.target →
        (∀ α : ComplexModel n →L[ℝ] ℝ, metricCoefficients w e z (H e z α) = α) ∧
        (∀ u : ComplexModel n, H e z (metricCoefficients w e z u) = u) ∧
        ∀ u v : ComplexModel n, metricCoefficients w e z u v = associatedMetric (w.coeff e z) u v := by
  refine ⟨inverseMetricCoefficients w, inverseMetricCoefficients_smooth w hw, ?_⟩
  intro e z hz
  obtain ⟨hleft, hright⟩ := metric_inverse_identities (hw e z hz).2
  exact ⟨hleft, hright, associatedMetricCLM_apply _⟩

/-- Actual tangent fiber musical equivalence with its original existing dual and topology. -/
def tangentMusicalEquiv (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (x : M) :
    TangentSpace 𝓘(ℝ, ComplexModel n) x ≃L[ℝ]
      (TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ) :=
  metricMusicalEquiv ((hw (complexChartAt x) ((complexChartAt (n := n) x).val x)
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))).2)

/-- Literal actual smooth Riemannian tangent metric readback of the musical map. -/
theorem tangentMusicalEquiv_toCLM (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (x : M) :
    (tangentMusicalEquiv w hw x : TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ) =
        (originalHermitianRiemannianMetric w hw).inner x := metricMusicalEquiv_toCLM _

/-- Original Hermitian data internally produces the genuine tangent-cotangent equivalences. -/
theorem exists_original_tangent_musical_equivalences (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ b : ∀ x : M, TangentSpace 𝓘(ℝ, ComplexModel n) x ≃L[ℝ]
        (TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ),
      (∀ x (u v : TangentSpace 𝓘(ℝ, ComplexModel n) x),
        b x u v = (originalHermitianRiemannianMetric w hw).inner x u v) ∧
      (∀ x (u : TangentSpace 𝓘(ℝ, ComplexModel n) x), (b x).symm (b x u) = u) ∧
      (∀ x (α : TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ), b x ((b x).symm α) = α) ∧
      ∀ x e, x ∈ e.val.source → ∀ u v : ComplexModel n,
        b x (chartTransitionDerivative e (complexChartAt x) (e.val x) u)
          (chartTransitionDerivative e (complexChartAt x) (e.val x) v) =
            associatedMetric (w.coeff e (e.val x)) u v := by
  refine ⟨tangentMusicalEquiv w hw, ?_, ?_, ?_, ?_⟩
  · intro x u v
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ => L u v)
      (tangentMusicalEquiv_toCLM w hw x)
  · intro x u
    exact (tangentMusicalEquiv w hw x).symm_apply_apply u
  · intro x α
    exact (tangentMusicalEquiv w hw x).apply_symm_apply α
  · intro x e hx u v
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ]
        TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ =>
      L (chartTransitionDerivative e (complexChartAt x) (e.val x) u)
        (chartTransitionDerivative e (complexChartAt x) (e.val x) v))
      (tangentMusicalEquiv_toCLM w hw x)
    exact h.trans (metricFiber_chart_readback w hw x e hx u v)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianMusicalInverse
