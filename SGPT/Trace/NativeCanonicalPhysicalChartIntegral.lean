import SGPT.Trace.NativeCanonicalPhysicalDensity
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Complex.Module

/-! Actual original Jacobians and genuine physical canonical coordinate integrals.
Every map is the literal transition between the original native charts. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem nativeCanonicalPhysicalTransition_fderiv (e f : ComplexChart n X) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    (fderiv ℂ (coordinateMap id f e) (f.val x)).toLinearMap =
      (nativeOriginalChartTangentEquiv e x he).toLinearMap.comp
        (nativeOriginalChartTangentEquiv f x hf).symm.toLinearMap := by
  let g : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) X X ∞ := ⟨id, contMDiff_id⟩
  apply LinearMap.ext
  intro v
  have h := coordinateMap_fderiv_fixed_native_charts_apply g f e x hf he v
  change fderiv ℂ (coordinateMap id f e) (f.val x) v =
    nativeOriginalChartTangentEquiv e x he
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) id x
        ((nativeOriginalChartTangentEquiv f x hf).symm v)) at h
  rw [mfderiv_id] at h
  exact h

theorem nativeCanonicalPhysicalTransition_realJacobian (e f : ComplexChart n X) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    |(fderiv ℝ (coordinateMap id f e) (f.val x)).det| =
      ‖LinearMap.det ((nativeOriginalChartTangentEquiv e x he).toLinearMap.comp
        (nativeOriginalChartTangentEquiv f x hf).symm.toLinearMap)‖ ^ 2 := by
  have hF : DifferentiableAt ℂ (coordinateMap id f e) (f.val x) :=
    (coordinateMap_contDiffAt contMDiff_id f e (mem_coordinateDomain hf he)).differentiableAt (by simp)
  rw [hF.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ (coordinateMap id f e) (f.val x)).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
    nativeCanonicalPhysicalTransition_fderiv e f x he hf]

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle n X)
  (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)

def nativeCanonicalPhysicalCoordinateDensity (e : ComplexChart n X) (z : ComplexModel n) : ℝ≥0∞ := by
  classical
  exact if hz : z ∈ e.val.target then nativeCanonicalPhysicalChartDensity L e
    (e.val.symm z) (e.val.map_target hz) (S (e.val.symm z)) (w (e.val.symm z)) else 0

private theorem actualCanonicalPhysicalDensity_point_eq (e : ComplexChart n X)
    (a b : X) (ha : a ∈ e.val.source) (hb : b ∈ e.val.source) (hab : a = b) :
    nativeCanonicalPhysicalChartDensity L e a ha (S a) (w a) =
      nativeCanonicalPhysicalChartDensity L e b hb (S b) (w b) := by
  subst b
  rfl

theorem nativeCanonicalPhysicalCoordinateDensity_change (e f : ComplexChart n X)
    (z : ComplexModel n) (hz : z ∈ coordinateDomain id f e) :
    nativeCanonicalPhysicalCoordinateDensity L S w f z =
      ENNReal.ofReal |(fderiv ℝ (coordinateMap id f e) z).det| *
        nativeCanonicalPhysicalCoordinateDensity L S w e (coordinateMap id f e z) := by
  classical
  let x := f.val.symm z
  have hf : x ∈ f.val.source := f.val.map_target hz.1
  have he : x ∈ e.val.source := hz.2
  have hfx : f.val x = z := f.val.right_inv hz.1
  have het : coordinateMap id f e z ∈ e.val.target := e.val.map_source he
  have hxe : e.val.symm (coordinateMap id f e z) = x := e.val.left_inv he
  unfold nativeCanonicalPhysicalCoordinateDensity
  rw [dif_pos hz.1, dif_pos het]
  have hDe : nativeCanonicalPhysicalChartDensity L e
      (e.val.symm (coordinateMap id f e z)) (e.val.map_target het)
      (S (e.val.symm (coordinateMap id f e z))) (w (e.val.symm (coordinateMap id f e z))) =
      nativeCanonicalPhysicalChartDensity L e x he (S x) (w x) := by
    exact actualCanonicalPhysicalDensity_point_eq L S w e _ _ _ _ hxe
  rw [hDe]
  have h := nativeCanonicalPhysicalChartDensity_change L e f x he hf (S x) (w x)
  rw [← nativeCanonicalPhysicalTransition_realJacobian e f x he hf, hfx] at h
  exact h

theorem nativeCanonicalPhysicalCoordinateIntegral_change (e f : ComplexChart n X)
    (A : Set (ComplexModel n)) (hA : MeasurableSet A)
    (hsub : A ⊆ coordinateDomain id f e) :
    (∫⁻ z in (coordinateMap id f e) '' A,
      nativeCanonicalPhysicalCoordinateDensity L S w e z ∂volume) =
    ∫⁻ z in A, nativeCanonicalPhysicalCoordinateDensity L S w f z ∂volume := by
  let F := coordinateMap id f e
  have hderiv : ∀ z ∈ A, HasFDerivWithinAt F (fderiv ℝ F z) A z := by
    intro z hz
    have hc : DifferentiableAt ℂ F z :=
      (coordinateMap_contDiffAt contMDiff_id f e (hsub hz)).differentiableAt (by simp)
    have hr : DifferentiableAt ℝ F z := hc.restrictScalars ℝ
    exact hr.hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn F A := by
    intro z hz t ht hzt
    have hx := e.val.injOn (hsub hz).2 (hsub ht).2 hzt
    calc
      z = f.val (f.val.symm z) := (f.val.right_inv (hsub hz).1).symm
      _ = f.val (f.val.symm t) := congrArg f.val hx
      _ = t := f.val.right_inv (hsub ht).1
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv hinj
    (nativeCanonicalPhysicalCoordinateDensity L S w e)
  apply h.trans
  apply setLIntegral_congr_fun hA
  intro z hz
  exact (nativeCanonicalPhysicalCoordinateDensity_change L S w e f z (hsub hz)).symm

end SGPT.Trace.Bertini
