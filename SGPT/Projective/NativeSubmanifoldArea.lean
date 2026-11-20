import SGPT.Foundations.Analysis.Pending.HausdorffAreaFormula
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Intrinsic native submanifold chart densities as actual Hausdorff area
densities, with the volume Jacobian proved and cancelled internally.
Blueprint: `native-submanifold-area.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
open TopDegreeDensity

/-- Actual Hausdorff reading of a parameter density under a smooth
immersion with its genuine inverse. No integration equality is an input. -/
theorem integral_image_density_div_normDet {k n : ℕ}
    (G : ComplexModel k → ComplexModel n) {U : Set (ComplexModel k)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hD : ∀ z ∈ U, Function.Injective (fderiv ℝ G z))
    (A : ComplexModel n → ComplexModel k) (hA : ContinuousOn A (G '' U))
    (hAG : ∀ z ∈ U, A (G z) = z)
    (r : ComplexModel k → ℝ) (hr : ContinuousOn r U)
    {K : Set (ComplexModel k)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∫ y in G '' K,
        r (A y) / (fderiv ℝ G (A y) : ComplexModel k →ₗ[ℝ] ComplexModel n).normDet
          ∂(μHE[2 * k] : Measure (ComplexModel n)) =
      ∫ z in K, r z := by
  have hnz : ∀ z ∈ U,
      (fderiv ℝ G z : ComplexModel k →ₗ[ℝ] ComplexModel n).normDet ≠ 0 := by
    intro z hz
    exact ((LinearMap.normDet_ne_zero_tfae _).out 0 4).mpr (hD z hz)
  have hJac : ContinuousOn
      (fun z => (fderiv ℝ G z : ComplexModel k →ₗ[ℝ] ComplexModel n).normDet) U :=
    HausdorffAreaFormula.continuous_normDet.comp_continuousOn
      (hG.continuousOn_fderiv_of_isOpen hU (by simp))
  have hAmaps : MapsTo A (G '' U) U := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [hAG z hz]
  have hden : ContinuousOn
      (fun y => r (A y) /
        (fderiv ℝ G (A y) : ComplexModel k →ₗ[ℝ] ComplexModel n).normDet) (G '' U) :=
    (hr.div hJac hnz).comp hA hAmaps
  have hGK : IsCompact (G '' K) := hK.image_of_continuousOn (hG.continuousOn.mono hKU)
  have hmeas : AEStronglyMeasurable
      (fun y => r (A y) /
        (fderiv ℝ G (A y) : ComplexModel k →ₗ[ℝ] ComplexModel n).normDet)
      ((μHE[Module.finrank ℝ (ComplexModel k)] : Measure (ComplexModel n)).restrict (G '' K)) :=
    (hden.mono (image_mono hKU)).aestronglyMeasurable hGK.measurableSet
  have hGi : InjOn G K := by
    intro z hz w hw hzw
    have h := congrArg A hzw
    simpa only [hAG z (hKU hz), hAG w (hKU hw)] using h
  rw [show 2 * k = Module.finrank ℝ (ComplexModel k) by
    rw [finrank_real_of_complex]
    simp [ComplexModel]]
  rw [HausdorffAreaFormula.integral_image_eq_integral hU (hG.of_le (by simp))
    hK.measurableSet hKU hGi (fun z hz => hD z (hKU hz)) hmeas]
  apply setIntegral_congr_fun hK.measurableSet
  intro z hz
  dsimp only
  rw [hAG z (hKU hz)]
  exact mul_div_cancel₀ _ (hnz z (hKU hz))

section Native

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

/-- The actual native inclusion manufactures its original coordinate
inverse on the WHOLE local image, without an inverse certificate. -/
theorem exists_native_chart_inverse :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    ∀ (e : ComplexChart k W) (a : ComplexChart n X),
      ∃ A : ComplexModel n → ComplexModel k,
        ContinuousOn A
          (coordinateMap (Subtype.val : W → X) e a ''
            coordinateDomain (Subtype.val : W → X) e a) ∧
        ∀ z ∈ coordinateDomain (Subtype.val : W → X) e a,
          A (coordinateMap (Subtype.val : W → X) e a z) = z := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  intro e a
  obtain ⟨F, hF⟩ := e.property
  let G := coordinateMap (Subtype.val : W → X) e a
  let U := coordinateDomain (Subtype.val : W → X) e a
  let A : ComplexModel n → ComplexModel k := fun y =>
    coordinateProjection n k (F.flat (F.amb.val (a.val.symm y)))
  have hcoords : ∀ y ∈ G '' U,
      y ∈ a.val.target ∧ a.val.symm y ∈ F.ambSource := by
    rintro _ ⟨z, hz, rfl⟩
    have hsrc : e.val.symm z ∈ (F.chart hk).source := by
      rw [← hF]
      exact e.val.map_target hz.1
    refine ⟨coordinateMap_mem_target hz, ?_⟩
    change a.val.symm (a.val ((e.val.symm z : W) : X)) ∈ F.ambSource
    rw [a.val.left_inv hz.2]
    exact hsrc
  have hA : ContinuousOn A (G '' U) := by
    have hInv : ContinuousOn a.val.symm (G '' U) :=
      a.val.continuousOn_symm.mono (fun y hy => (hcoords y hy).1)
    have hAmb : ContinuousOn (fun y => F.amb.val (a.val.symm y)) (G '' U) :=
      F.amb.val.continuousOn.comp hInv (fun y hy => (hcoords y hy).2.1)
    have hFlat : ContinuousOn (fun y => F.flat (F.amb.val (a.val.symm y))) (G '' U) :=
      F.flat.continuousOn.comp hAmb (fun y hy => (hcoords y hy).2.2)
    exact (coordinateProjection n k).continuous.comp_continuousOn hFlat
  refine ⟨A, hA, ?_⟩
  intro z hz
  change coordinateProjection n k
    (F.flat (F.amb.val (a.val.symm (a.val ((e.val.symm z : W) : X))))) = z
  rw [a.val.left_inv hz.2]
  change (F.chart hk) (e.val.symm z) = z
  rw [← hF]
  exact e.val.right_inv hz.1

/-- Actual native pulled-back top-form integration in a whole member chart
equals its actual Hausdorff reading with the SAME chart inverse and Jacobian.
The inverse and all smoothness/measurability facts are produced internally. -/
theorem exists_native_chart_area_reading :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (e : ComplexChart k W) (a : ComplexChart n X),
      ∃ A : ComplexModel n → ComplexModel k,
        ∀ (γ : SmoothRealForm n X (2 * k))
          (K : Set (ComplexModel k)) (_hK : IsCompact K)
          (_hKU : K ⊆ coordinateDomain (Subtype.val : W → X) e a),
          ∫ y in coordinateMap (Subtype.val : W → X) e a '' K,
              topDensity ((SmoothRealForm.pullback hι γ).coeff e (A y)) /
                (fderiv ℝ (coordinateMap (Subtype.val : W → X) e a) (A y) :
                  ComplexModel k →ₗ[ℝ] ComplexModel n).normDet
                ∂(μHE[2 * k] : Measure (ComplexModel n)) =
            ∫ z in K, topDensity ((SmoothRealForm.pullback hι γ).coeff e z) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro e a
  obtain ⟨A, hA, hAG⟩ := exists_native_chart_inverse hk hW e a
  refine ⟨A, fun γ K hK hKU => ?_⟩
  apply integral_image_density_div_normDet _ (coordinateDomain_isOpen hι e a)
    (coordinateMap_contDiffOn_real hι e a)
    (SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val hk hW e a)
    A hA hAG (fun z => topDensity ((SmoothRealForm.pullback hι γ).coeff e z)) ?_ hK hKU
  exact (continuous_topDensity.comp_continuousOn
    ((SmoothRealForm.pullback hι γ).smooth e).continuousOn).mono (fun _ hz => hz.1)

end Native

end SGPT.Projective.NumEq.CompleteIntersections
