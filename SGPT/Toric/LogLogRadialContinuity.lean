import SGPT.Toric.LogLogAngularTests
import SGPT.Convex.FiniteAlexandrovContinuity
import SGPT.Convex.SmoothFiniteApproximation

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Convex
open scoped Topology ENNReal CompactlySupported

/-- The actual radial window proves integrability with only genuine local finiteness. -/
theorem integrable_logLogRadial_test_of_locallyFinite {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    Integrable (fun p : ℝ × ℝ => η (logLogRadialPoint p))
      (μ.prod logLogAngularMeasure) := by
  obtain ⟨a, b, hwindow⟩ := exists_logLogRadial_test_window hK hzero
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuous hη
  have hfinite : (μ.prod logLogAngularMeasure) (Icc a b ×ˢ (univ : Set ℝ)) < ⊤ := by
    rw [Measure.prod_prod, logLogAngularMeasure_univ, mul_one]
    exact isCompact_Icc.measure_lt_top
  have hi : IntegrableOn (fun p : ℝ × ℝ => η (logLogRadialPoint p))
      (Icc a b ×ˢ (univ : Set ℝ)) (μ.prod logLogAngularMeasure) := by
    apply IntegrableOn.of_bound hfinite
      (hη.comp continuous_logLogRadialPoint).aestronglyMeasurable C
    exact Eventually.of_forall fun p => hC (logLogRadialPoint p)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro p hp
  by_contra hn
  exact hp ⟨hwindow p.1 p.2 hn, mem_univ p.2⟩

/-- Full signed-test Fubini needs only the actually produced compact radial support. -/
theorem integral_map_logLogRadialPoint_of_locallyFinite {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (∫ z, η z ∂Measure.map logLogRadialPoint (μ.prod logLogAngularMeasure)) =
      ∫ x, logLogAngularAverage η x ∂μ := by
  rw [integral_map_of_stronglyMeasurable continuous_logLogRadialPoint.measurable
    hη.stronglyMeasurable,
    integral_prod _ (integrable_logLogRadial_test_of_locallyFinite hη hK hzero μ)]
  rfl

/-- The actual angular integral is a genuine original real compact-test map. -/
def logLogAngularCompactTest {η : ℂ → ℝ} (hη : Continuous η)
    (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) : C_c(ℝ, ℝ) :=
  ⟨⟨logLogAngularAverage η, continuous_logLogAngularAverage hη hK⟩,
    hasCompactSupport_logLogAngularAverage hK hzero⟩

/-- Actual real compact-test continuity yields true signed tests of the punctured radial maps. -/
theorem tendsto_integral_radialMap_of_convex_compact_convergence
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ j, ConvexOn ℝ univ (F j))
    (hF : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn F f atTop K)
    {η : ℂ → ℝ} (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) :
    Tendsto (fun j => ∫ z, η z ∂Measure.map logLogRadialPoint
      ((alexandrovMeasure scalarPairing volume (fun x => (F j x : EReal))).prod
        logLogAngularMeasure)) atTop
      (𝓝 (∫ z, η z ∂Measure.map logLogRadialPoint
        ((alexandrovMeasure scalarPairing volume (fun x => (f x : EReal))).prod
          logLogAngularMeasure))) := by
  have hlocal (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g) :
      IsLocallyFiniteMeasure (alexandrovMeasure scalarPairing volume
        (fun x => (g x : EReal))) :=
    isLocallyFiniteMeasure_alexandrovMeasure_coe scalarPairing hg
  have hleft (j : ℕ) :
      (∫ z, η z ∂Measure.map logLogRadialPoint
        ((alexandrovMeasure scalarPairing volume (fun x => (F j x : EReal))).prod
          logLogAngularMeasure)) =
        ∫ x, logLogAngularAverage η x ∂alexandrovMeasure scalarPairing volume
          (fun x => (F j x : EReal)) := by
    let := hlocal (F j) (hFcv j)
    exact integral_map_logLogRadialPoint_of_locallyFinite hη hK hzero _
  have hright :
      (∫ z, η z ∂Measure.map logLogRadialPoint
        ((alexandrovMeasure scalarPairing volume (fun x => (f x : EReal))).prod
          logLogAngularMeasure)) =
        ∫ x, logLogAngularAverage η x ∂alexandrovMeasure scalarPairing volume
          (fun x => (f x : EReal)) := by
    let := hlocal f hf
    exact integral_map_logLogRadialPoint_of_locallyFinite hη hK hzero _
  simp_rw [hleft, hright]
  exact tendsto_integral_alexandrovMeasure_of_finite_convex_compact_convergence
    (ν := volume) scalarPairing hf hFcv hF (logLogAngularCompactTest hη hK hzero)

/-- Genuine smooth bumps and original real convex convergence retain the whole circle measure. -/
theorem tendsto_integral_radialMap_smooth_logLog {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) :
    Tendsto (fun j => ∫ z, η z ∂Measure.map logLogRadialPoint
      ((alexandrovMeasure scalarPairing volume
        (fun x => (finiteConvexSmoothApprox volume logLogProfile j x : EReal))).prod
        logLogAngularMeasure)) atTop (𝓝 (∫ z, η z ∂logLogRadialMeasure)) := by
  exact tendsto_integral_radialMap_of_convex_compact_convergence convexOn_logLogProfile
    (convexOn_finiteConvexSmoothApprox volume convexOn_logLogProfile)
    (fun _ hcomp => tendstoUniformlyOn_finiteConvexSmoothApprox volume
      convexOn_logLogProfile hcomp) hη hK hzero

end SGPT.Toric
