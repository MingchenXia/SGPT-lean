import SGPT.PSH.SourceTestCurveLegendreCorrespondence
import SGPT.PSH.SourceIModelTestCurves

/-! # Original maximal geodesic rays

The original inverse Legendre test curve defines maximality of a genuine
model-origin ray. The actual Ross--Witt Nyström correspondence restricts to
I-model test curves and these maximal rays without changing either transform.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- Original `def:maximalgeoray`: the SAME actual inverse Legendre test curve
belongs to the original based I-model collection. -/
def SourceRayIsMaximal (omega : KahlerBackground n M) {ℓ : SourceRayFamily M}
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) : Prop :=
  sourceRayLegendreTestCurve omega hℓ ∈ SourceIModelTestCurves θ φ hφ

/-- The original maximal-ray collection retains genuine geodesic-ray
membership and the prescribed initial value from the original ray class. -/
def sourceMaximalGeodesicRays (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) : Set (SourceRayFamily M) :=
  {ℓ | ∃ hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ, SourceRayIsMaximal omega hℓ}

/-- Inverse basedness is produced by the actual Legendre construction;
maximality is exactly I-modelness of all its genuine open slices. -/
theorem sourceRayIsMaximal_iff_slices (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    SourceRayIsMaximal omega hℓ ↔
      SourceTestCurveIsIModel (sourceRayLegendreTestCurve omega hℓ) := by
  constructor
  · exact And.right
  · intro hI
    exact ⟨(source_ray_legendre_test_curve_whole omega hℓ).1, hI⟩

/-- The original forward transform is maximal exactly for original I-model
test curves. Exact object inversion retains its real cutoff and every pole. -/
theorem sourceTestCurveLegendreRay_isMaximal_iff (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    SourceRayIsMaximal omega
        (source_test_curve_legendre_geodesic_whole omega Γ hbased).1 ↔
      SourceTestCurveIsIModel Γ := by
  rw [sourceRayIsMaximal_iff_slices,
    sourceTestCurveLegendre_left_inverse omega Γ hbased]

/-- The unchanged original Legendre maps restrict to the based I-model
test curves and the genuine maximal rays, including the original time zero. -/
def sourceIModelTestCurveLegendreEquiv (omega : KahlerBackground n M)
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) :
    {Γ : SourceTestCurve θ // Γ ∈ SourceIModelTestCurves θ φ hφ} ≃
      {ℓ : SourceRayFamily M // ℓ ∈ sourceMaximalGeodesicRays omega θ φ hφ} where
  toFun Γ := ⟨sourceTestCurveLegendreRay Γ.1.toSourceTestCurvePredata,
    (source_test_curve_legendre_geodesic_whole omega Γ.1 Γ.2.1).1,
    (sourceTestCurveLegendreRay_isMaximal_iff omega Γ.1 Γ.2.1).mpr Γ.2.2⟩
  invFun ℓ := ⟨sourceRayLegendreTestCurve omega ℓ.2.choose, ℓ.2.choose_spec⟩
  left_inv Γ := Subtype.ext (sourceTestCurveLegendre_left_inverse omega Γ.1 Γ.2.1)
  right_inv ℓ := Subtype.ext (sourceRayLegendre_right_inverse omega ℓ.2.choose)

end SGPT.PSH.VariableComplexAtlas
