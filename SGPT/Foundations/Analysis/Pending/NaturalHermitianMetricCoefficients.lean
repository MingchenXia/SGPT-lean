import SGPT.Foundations.Analysis.FirstPass.HermitianGeometry
import SGPT.Foundations.Analysis.FirstPass.ExteriorDerivative
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact

/-! # Genuine smooth positive Hermitian metric coefficients

The original fundamental form supplies its actual continuous symmetric
bilinear metric and a proved finite-dimensional coercivity bound.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients

open FirstPass

variable {n : ℕ}

/-- The original complex structure is an actual continuous real linear map. -/
def complexStructureCLM : ComplexModel n →L[ℝ] ComplexModel n :=
  (Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ

/-- Full continuous real linear conversion from alternating coefficients to bilinear metric coefficients. -/
def associatedMetricCLM : ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
    (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) := by
  let single : ((ComplexModel n) [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n →L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexModel n)
      (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let preJ : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ComplexModel n) (ComplexModel n) ℝ).flip
      complexStructureCLM
  exact (ContinuousLinearMap.compL ℝ (ComplexModel n)
      (ComplexModel n →L[ℝ] ℝ) (ComplexModel n →L[ℝ] ℝ) preJ).comp
    ((ContinuousLinearMap.compL ℝ (ComplexModel n)
      ((ComplexModel n) [⋀^Fin 1]→L[ℝ] ℝ) (ComplexModel n →L[ℝ] ℝ) single).comp
      ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)

/-- Literal full original associated metric readback. -/
theorem associatedMetricCLM_apply (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u v : ComplexModel n) : associatedMetricCLM a u v = associatedMetric a u v := by
  change a (Matrix.vecCons u (fun _ : Fin 1 => Complex.I • v)) = a ![u, Complex.I • v]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The actual type (1,1) alternating law gives symmetry of the original associated metric. -/
theorem associatedMetric_symm {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsOneOne a) (u v : ComplexModel n) : associatedMetric a u v = associatedMetric a v u := by
  have hJ : Complex.I • (Complex.I • u) = -u := by
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  have htype := ha (Complex.I • u) v
  rw [hJ] at htype
  have hneg : a ![-u, Complex.I • v] = -a ![u, Complex.I • v] := by
    change a.toAlternatingMap ![-u, Complex.I • v] = -a.toAlternatingMap ![u, Complex.I • v]
    simpa only [neg_one_smul] using
      a.toAlternatingMap.map_vecCons_smul ![Complex.I • v] (-1 : ℝ) u
  have hswap : a ![Complex.I • u, v] = -a ![v, Complex.I • u] := by
    have heq : (![v, Complex.I • u] : Fin 2 → ComplexModel n) ∘ Equiv.swap 0 1 =
        ![Complex.I • u, v] := by
      funext i
      fin_cases i <;> simp
    rw [← heq]
    exact a.toAlternatingMap.map_swap _ (by decide : (0 : Fin 2) ≠ 1)
  rw [hneg, hswap] at htype
  exact neg_injective htype

/-- The constructed associated metric has the original complex structure as an isometry. -/
theorem associatedMetric_J_isometry {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsOneOne a) (u v : ComplexModel n) :
    associatedMetric a (Complex.I • u) (Complex.I • v) = associatedMetric a u v :=
  ha u (Complex.I • v)

/-- Actual internally constructed positive definite real inner product core. -/
@[instance_reducible]
def associatedMetricCore (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : IsOneOne a) (hp : IsStrictlyPositive a) : InnerProductSpace.Core ℝ (ComplexModel n) where
  inner u v := associatedMetricCLM a u v
  conj_inner_symm u v := by
    change associatedMetricCLM a v u = associatedMetricCLM a u v
    simp only [associatedMetricCLM_apply]
    exact associatedMetric_symm ha v u
  re_inner_nonneg u := by
    change 0 ≤ associatedMetricCLM a u u
    by_cases hu : u = 0
    · subst u
      simp
    · rw [associatedMetricCLM_apply]
      exact (hp u hu).le
  add_left u v w := by simp
  smul_left u v r := by simp
  definite u h := by
    change associatedMetricCLM a u u = 0 at h
    rw [associatedMetricCLM_apply] at h
    by_contra hu
    exact (hp u hu).ne' h

/-- Strict positivity internally produces coercivity in the original finite-dimensional model norm. -/
theorem associatedMetric_coercive {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) : ∃ c : ℝ, 0 < c ∧
      ∀ u : ComplexModel n, c * ‖u‖ ^ 2 ≤ associatedMetric a u u := by
  classical
  rcases subsingleton_or_nontrivial (ComplexModel n) with hs | hn
  · let _ := hs
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    rw [← associatedMetricCLM_apply]
    simp
  · let _ := hn
    have hc : Continuous (fun u : ComplexModel n => associatedMetricCLM a u u) := by fun_prop
    obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : ComplexModel n) (1 : ℝ)).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
    have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
    have hvne : v ≠ 0 := fun h => by simp [h] at hvnorm
    refine ⟨associatedMetricCLM a v v, ?_, ?_⟩
    · rw [associatedMetricCLM_apply]
      exact ha v hvne
    · intro u
      by_cases hu : u = 0
      · subst u
        rw [← associatedMetricCLM_apply]
        simp
      · have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
        have hunit : ‖u‖⁻¹ • u ∈ sphere (0 : ComplexModel n) (1 : ℝ) :=
          mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hu)
        have hm := hmin hunit
        change associatedMetricCLM a v v ≤
          associatedMetricCLM a (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) at hm
        simp only [map_smul, smul_apply, smul_eq_mul] at hm
        have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖u‖)
        have hcancel : (‖u‖⁻¹ * (‖u‖⁻¹ * associatedMetricCLM a u u)) * ‖u‖ ^ 2 =
            associatedMetricCLM a u u := by
          field_simp
        rw [hcancel] at hmul
        simpa only [associatedMetricCLM_apply] using hmul

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The full actual metric coefficient map determined by the original fundamental form. -/
def metricCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  associatedMetricCLM (w.coeff e z)

/-- Original Hermitian geometry alone constructs all smooth positive compatible metric coefficients. -/
theorem exists_smooth_compatible_positive_metric (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ G : ComplexChart n M → ComplexModel n →
        (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ),
      (∀ e z u v, G e z u v = associatedMetric (w.coeff e z) u v) ∧
      (∀ e, ContDiffOn ℝ ∞ (G e) e.val.target) ∧
      (∀ e z, z ∈ e.val.target →
        (∀ u v, G e z u v = G e z v u) ∧
        (∀ u, u ≠ 0 → 0 < G e z u u) ∧
        (∀ u v, G e z (Complex.I • u) (Complex.I • v) = G e z u v) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ G e z u u) ∧
      ∀ e f z, z ∈ (chartTransition e f).source → ∀ u v,
        G e z u v = G f (chartTransition e f z)
          (chartTransitionDerivative e f z u) (chartTransitionDerivative e f z v) := by
  refine ⟨metricCoefficients w, ?_, ?_, ?_, ?_⟩
  · intro e z u v
    exact associatedMetricCLM_apply _ _ _
  · intro e
    apply ContDiff.comp_contDiffOn ?_ (w.smooth e)
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
      (F := ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
      (by exact associatedMetricCLM (n := n))
  · intro e z hz
    have ht := (hw e z hz).1
    have hp := (hw e z hz).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u v
      simp only [metricCoefficients, associatedMetricCLM_apply]
      exact associatedMetric_symm ht u v
    · intro u hu
      simpa only [metricCoefficients, associatedMetricCLM_apply, associatedMetric] using hp u hu
    · intro u v
      simp only [metricCoefficients, associatedMetricCLM_apply]
      exact associatedMetric_J_isometry ht u v
    · simpa only [metricCoefficients, associatedMetricCLM_apply] using associatedMetric_coercive hp
  · intro e f z hz u v
    simp only [metricCoefficients, associatedMetricCLM_apply]
    unfold associatedMetric
    have h := w.compatible e f z hz ![u, Complex.I • v]
    have hvec : (fun i => chartTransitionDerivative e f z (![u, Complex.I • v] i)) =
        ![chartTransitionDerivative e f z u, Complex.I • chartTransitionDerivative e f z v] := by
      funext i
      fin_cases i
      · rfl
      · exact chartTransitionDerivative_complex_smul e f z hz Complex.I v
    rw [hvec] at h
    exact h

end SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
