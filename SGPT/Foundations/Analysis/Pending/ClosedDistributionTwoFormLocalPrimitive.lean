import SGPT.Foundations.Analysis.Pending.DistributionFormHomotopy
import SGPT.Foundations.Analysis.Pending.LocalTwoFormPoincare
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.SmoothDistribution

set_option autoImplicit false

/-! Genuine local distribution primitives. Full BP statements and ENTIRE
proofs precede this source. Scalar ddC potentials and global BC gluing remain
separate obligations, not assumptions of these local constructions. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology
open SGPT.Foundations.Analysis.LocalCurrents
namespace SGPT.Foundations.Analysis.Pending.ClosedDistributionTwoFormLocalPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

private theorem regularFormDistribution_coefficient {k : ℕ}
    (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (v : Fin k → E)
    (hv : LocallyIntegrableOn (fun z => a z v) Ω μ) :
    regularFormDistribution μ a (ha.continuous.locallyIntegrable.locallyIntegrableOn Ω) v =
      regularDistribution μ (fun z => a z v) hv := by
  ext φ
  rw [regularFormDistribution_apply, regularDistribution_apply]
  have hi : Integrable (fun z => φ z • a z) μ :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (ha.continuous.locallyIntegrable.locallyIntegrableOn Ω)
  change (formEvaluationCLM v) (∫ z, φ z • a z ∂μ) = _
  rw [← (formEvaluationCLM v).integral_comp_comm hi]
  simp only [map_smul, formEvaluationCLM_apply, smul_eq_mul]

/-- All original compact tests identify the actual exterior derivative of a
smooth form distribution with its genuine classical density. -/
theorem exteriorDerivative_regularFormDistribution_apply {k : ℕ}
    (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (v : Fin (k+1) → E) (φ : 𝓓(Ω, ℝ)) :
    exteriorDerivative
      (regularFormDistribution μ a (ha.continuous.locallyIntegrable.locallyIntegrableOn Ω)) v φ =
      ∫ z, φ z * extDeriv a z v ∂μ := by
  have hs (i : Fin (k+1)) (r : ℝ) : (-1 : ℤ)^i.val • r = (-1 : ℝ)^i.val * r := by
    simp [zsmul_eq_mul]
  have hscalar (i : Fin (k+1)) : ContDiff ℝ 1 (fun z => a z (i.removeNth v)) :=
    ((formEvaluationCLM (i.removeNth v)).contDiff.comp ha).of_le (by simp)
  have hd (i : Fin (k+1)) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v i)
        (regularFormDistribution μ a
          (ha.continuous.locallyIntegrable.locallyIntegrableOn Ω) (i.removeNth v)) φ =
        ∫ z, φ z * fderiv ℝ (fun y => a y (i.removeNth v)) z (v i) ∂μ := by
    rw [regularFormDistribution_coefficient a ha (i.removeNth v)
      ((hscalar i).continuous.locallyIntegrable.locallyIntegrableOn Ω),
      lineDerivCLM_regularDistribution (hscalar i), regularDistribution_apply]
  rw [exteriorDerivative_apply]
  simp only [sum_apply, _root_.smul_apply]
  simp_rw [hd, hs, ← integral_const_mul]
  have hI (i : Fin (k+1)) : Integrable (fun z => (-1 : ℝ)^i.val *
      (φ z * fderiv ℝ (fun y => a y (i.removeNth v)) z (v i))) μ :=
    (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrableOn_fderiv_of_contDiff (hscalar i) (v i))).const_mul _
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [extDeriv_apply ((ha.differentiable (by simp)) z) v]
  simp_rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exteriorDerivative_sub {k : ℕ} (A B : DistributionForm Ω k) :
    exteriorDerivative (A - B) = exteriorDerivative A - exteriorDerivative B := by
  ext v φ
  simp [exteriorDerivative_apply, AlternatingMap.sub_apply, map_sub, smul_sub,
    Finset.sum_sub_distrib]

section Complex
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
open LelongPoincareDivisor DistributionFormRegularization DistributionFormHomotopy

/-- Natural closedness internally produces a complete local distribution
one-form primitive. No potential, exactness or target continuity premise. -/
theorem exists_local_primitive (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : DistributionForm Ω 2) (hA : IsClosed A)
    (x : E) (hx : x ∈ Ω) :
    ∃ (W : Opens E) (hW : W ≤ Ω) (C : DistributionForm W 1),
      x ∈ W ∧ exteriorDerivative C = restrictForm A hW := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have := hE
    have hAz : A = 0 := by
      apply AlternatingMap.ext
      intro v
      exact A.map_eq_zero_of_eq v (Subsingleton.elim _ _) Fin.zero_ne_one
    refine ⟨Ω, le_rfl, 0, hx, ?_⟩
    rw [hAz]
    ext v φ
    simp [exteriorDerivative_apply, restrictForm_apply]
  · have := hE
    let D : AdaptedRadialKernelData μ Ω x :=
      Classical.choice (exists_adaptedRadialKernelData μ hx)
    let a := regularizedForm D 0 A
    have ha : ContDiff ℝ (⊤ : ℕ∞) a := contDiff_regularizedForm D 0 A
    have hclosed : ∀ z ∈ D.inner, extDeriv a z = 0 := by
      intro z hz
      rw [show extDeriv a z = regularizedForm D 0 (exteriorDerivative A) z from
        extDeriv_regularizedForm_eq D 0 A (subset_closure hz), hA]
      ext v
      change D.distributionRegularizedValue (0 : 𝓓'(Ω, ℝ)) 0 z = 0
      rfl
    obtain ⟨r, hr, hU, S, hS, hSe⟩ :=
      LocalPotentials.exists_smooth_local_twoForm_primitive D.inner.isOpen a ha.contDiffOn
        hclosed D.center_mem
    let W : Opens E := ⟨Metric.ball x r, Metric.isOpen_ball⟩
    have hWU : W ≤ D.inner := hU
    let C : DistributionForm W 1 :=
      regularFormDistribution μ S (hS.continuous.locallyIntegrable.locallyIntegrableOn W) -
        restrictForm (primitive D 0 A) hWU
    refine ⟨W, hWU.trans D.inner_le, C, Metric.mem_ball_self hr, ?_⟩
    ext v φ
    rw [show C = _ from rfl, exteriorDerivative_sub,
      AlternatingMap.sub_apply, _root_.sub_apply,
      exteriorDerivative_regularFormDistribution_apply S hS,
      ← restrictForm_exteriorDerivative]
    rw [restrictForm_apply, exteriorDerivative_primitive_eq_pairing D 0 A hA]
    have hmono (z : E) : (TestFunction.monoCLM ℝ φ : 𝓓(D.inner, ℝ)) z = φ z :=
      congrFun (testFunction_inclusion_coe hWU φ) z
    have hint : (∫ z, φ z * extDeriv S z v ∂μ) =
        ∫ z, (TestFunction.monoCLM ℝ φ : 𝓓(D.inner, ℝ)) z * a z v ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hmono]
      by_cases hz : z ∈ W
      · rw [hSe z hz]
      · have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hz (φ.tsupport_subset ht))
        rw [hz0, zero_mul, zero_mul]
    rw [hint]
    change _ = A v (TestFunction.monoCLM ℝ φ)
    have hinc : (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ : 𝓓(D.inner, ℝ)) :
        𝓓(Ω, ℝ)) = TestFunction.monoCLM ℝ φ := by
      ext z
      rw [congrFun (testFunction_inclusion_coe D.inner_le
        (TestFunction.monoCLM ℝ φ : 𝓓(D.inner, ℝ))) z,
        congrFun (testFunction_inclusion_coe hWU φ) z,
        congrFun (testFunction_inclusion_coe (hWU.trans D.inner_le) φ) z]
    rw [hinc]
    ring

end Complex
end SGPT.Foundations.Analysis.Pending.ClosedDistributionTwoFormLocalPrimitive
