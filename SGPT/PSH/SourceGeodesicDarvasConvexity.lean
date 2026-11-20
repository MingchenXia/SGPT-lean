import SGPT.PSH.SourceGeodesicEnergyAffinity
import SGPT.PSH.SourceDarvasMetric
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicDarvasConvexity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ} {omega : KahlerBackground n M}
  {curve other : ℝ → M → EReal}

/-- The literal original Darvas distance on the source's CLOSED unit
interval. Actual slice E1 memberships are manufactured from the endpoints.
Zero extension is only a real-domain representation of that interval
function; no off-interval potential is given an E1/PSH premise or readback. -/
def sourceGeodesicDarvasDistance
    (hg : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (hk : SourceGeodesicClosedInterval omega θ 0 1 other)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve 0) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve 1) hφ)
    (k₀ : SourceRelativeFiniteEnergy θ φ (other 0) hφ)
    (k₁ : SourceRelativeFiniteEnergy θ φ (other 1) hφ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ Icc (0 : ℝ) 1 then sourceDarvasDistance θ φ hφ
    ⟨curve t, sourceRelativeFiniteEnergy_sourceGeodesic_on hg h₀ h₁ ht⟩
    ⟨other t, sourceRelativeFiniteEnergy_sourceGeodesic_on hk k₀ k₁ ht⟩ else 0

/-- At EVERY original closed time this function is precisely the actual
source E1 distance of the SAME original potentials, including endpoints. -/
theorem sourceGeodesicDarvasDistance_eq_distance
    (hg : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (hk : SourceGeodesicClosedInterval omega θ 0 1 other)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve 0) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve 1) hφ)
    (k₀ : SourceRelativeFiniteEnergy θ φ (other 0) hφ)
    (k₁ : SourceRelativeFiniteEnergy θ φ (other 1) hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceGeodesicDarvasDistance hg hk h₀ h₁ k₀ k₁ t = sourceDarvasDistance θ φ hφ
      ⟨curve t, sourceRelativeFiniteEnergy_sourceGeodesic_on hg h₀ h₁ ht⟩
      ⟨other t, sourceRelativeFiniteEnergy_sourceGeodesic_on hk k₀ k₁ ht⟩ := by
  simp only [sourceGeodesicDarvasDistance, dif_pos ht]

/-- The complete genuine source/native distance dictionary on the ENTIRE
original closed interval, for EVERY prescribed pair of source geodesics. -/
theorem sourceGeodesicDarvasDistance_eq_native_on
    (hg : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (hk : SourceGeodesicClosedInterval omega θ 0 1 other)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve 0) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve 1) hφ)
    (k₀ : SourceRelativeFiniteEnergy θ φ (other 0) hφ)
    (k₁ : SourceRelativeFiniteEnergy θ φ (other 1) hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceGeodesicDarvasDistance hg hk h₀ h₁ k₀ k₁ t =
      RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative
        (closedSubgeodesicSlice
          (finiteGeodesic (atlasClosedFormToNative θ).val (curve 0) (curve 1)) (curve 0) (curve 1) t)
        (closedSubgeodesicSlice
          (finiteGeodesic (atlasClosedFormToNative θ).val (other 0) (other 1)) (other 0) (other 1) t) := by
  rw [sourceGeodesicDarvasDistance_eq_distance hg hk h₀ h₁ k₀ k₁ ht,
    sourceDarvasDistance_eq_native omega]
  have hcurve := hg.eq_sourcePerronClosedSlice_reparam ht
  have hother := hk.eq_sourcePerronClosedSlice_reparam ht
  simp only [mul_one, mul_zero, add_zero] at hcurve hother
  change RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative
    (curve t) (other t) = _
  rw [hcurve, hother]
  simp only [sourcePerronClosedSlice_eq_native]

/-- WHOLE original prop:d1convex: full actual ConvexOn on the entire
CLOSED interval for EVERY pair of original geodesics with original E1
endpoints. Actual rooftop/energy/restriction producers manufacture the
whole three-time bound; no bounded reference or convexity certificate. -/
theorem sourceGeodesicDarvasDistance_convexOn
    (hg : SourceGeodesicClosedInterval omega θ 0 1 curve)
    (hk : SourceGeodesicClosedInterval omega θ 0 1 other)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve 0) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve 1) hφ)
    (k₀ : SourceRelativeFiniteEnergy θ φ (other 0) hφ)
    (k₁ : SourceRelativeFiniteEnergy θ φ (other 1) hφ) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (sourceGeodesicDarvasDistance hg hk h₀ h₁ k₀ k₁) := by
  have hn := SingularModelGeodesicDarvasConvexity.convexOn_relativeD1_closedGeodesics omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₁)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp k₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp k₁)
  apply hn.congr
  intro t ht
  exact (sourceGeodesicDarvasDistance_eq_native_on hg hk h₀ h₁ k₀ k₁ ht).symm

end SGPT.PSH.VariableComplexAtlas
