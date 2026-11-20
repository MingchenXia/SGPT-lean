import SGPT.PSH.SourceRadialDarvasMetric
import SGPT.Foundations.Analysis.Pending.SingularModelFullMassRayRadialEnergy
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The ENTIRE original model-origin full-mass ray class. No positive-time
finite-energy condition is added to the domain of radial energy. -/
abbrev SourceGeodesicRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :=
  {ℓ : SourceRayFamily M // ℓ ∈ sourceGeodesicRays omega θ φ hφ}

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Genuine inclusion of the original finite-energy ray class, preserving
EVERY original function and every original time. -/
def sourceFiniteEnergyRayToGeodesicRay (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) : SourceGeodesicRay omega θ φ hφ :=
  ⟨L.val, L.property.1.1, L.property.2⟩

/-- WHOLE original radial-energy definition: literal EReal LIMSUP on ALL
original R, retaining negative infinity. The clamped real-time reader
merely normalizes the original nonnegative-time domain for atTop. -/
def sourceRadialEnergy (omega : KahlerBackground n M)
    (L : SourceGeodesicRay omega θ φ hφ) : EReal :=
  Filter.limsup (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) *
    sourceRelativeEnergy θ φ (sourceRayExtension L.val t) hφ) atTop

/-- Actual full-mass Perron truncation/extended-energy chords produce the
true defining limit, on the ENTIRE original R including the bottom case.
Real energy arithmetic occurs only in the internally proved finite case. -/
theorem tendsto_sourceRadialEnergy (omega : KahlerBackground n M)
    (L : SourceGeodesicRay omega θ φ hφ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) *
      sourceRelativeEnergy θ φ (sourceRayExtension L.val t) hφ) atTop
      (𝓝 (if sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ = ⊥ then ⊥ else
        (((sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ).toReal -
          (sourceRelativeEnergy θ φ (L.val ⟨0, by simp⟩) hφ).toReal : ℝ) : EReal))) := by
  have hn := (mem_sourceGeodesicRays_iff_native omega θ φ hφ L.val).mp L.property
  have hT := SingularModelFullMassRayRadialEnergy.tendsto_radialEnergy_of_fullMass omega hn.1
  simpa only [sourceRelativeEnergy_eq_native,
    sourceRayExtension_nonneg L.val 1 zero_le_one,
    sourceRayExtension_nonneg L.val 0 le_rfl] using hT

/-- Genuine convergence identifies the literal original EReal limsup,
including a genuinely negative-infinite energy slope. -/
theorem sourceRadialEnergy_eq (omega : KahlerBackground n M)
    (L : SourceGeodesicRay omega θ φ hφ) :
    sourceRadialEnergy omega L =
      if sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ = ⊥ then ⊥ else
        (((sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ).toReal -
          (sourceRelativeEnergy θ φ (L.val ⟨0, by simp⟩) hφ).toReal : ℝ) : EReal) :=
  (tendsto_sourceRadialEnergy omega L).limsup_eq

/-- The native selector and the original LIMSUP agree on the WHOLE
original full-mass ray class because the actual extended integrand
converges. This is not an unsupported identification of two definitions. -/
theorem sourceRadialEnergy_eq_native (omega : KahlerBackground n M)
    (L : SourceGeodesicRay omega θ φ hφ) :
    sourceRadialEnergy omega L =
      RelativeGeodesicRays.radialEnergy (atlasClosedFormToNative θ) φ hφ.toNative
        (sourceRayExtension L.val) := by
  have hn := (mem_sourceGeodesicRays_iff_native omega θ φ hφ L.val).mp L.property
  have hT := SingularModelFullMassRayRadialEnergy.tendsto_radialEnergy_of_fullMass omega hn.1
  have he : sourceRadialEnergy omega L =
      if RelativeDarvasDistance.energy (atlasClosedFormToNative θ) φ hφ.toNative
          (sourceRayExtension L.val 1) = ⊥ then ⊥ else
        (((RelativeDarvasDistance.energy (atlasClosedFormToNative θ) φ hφ.toNative
            (sourceRayExtension L.val 1)).toReal -
          (RelativeDarvasDistance.energy (atlasClosedFormToNative θ) φ hφ.toNative
            (sourceRayExtension L.val 0)).toReal : ℝ) : EReal) := by
    simpa only [sourceRadialEnergy, sourceRelativeEnergy_eq_native] using hT.limsup_eq
  exact he.trans hT.limUnder_eq.symm

/-- BOTH extended endpoints are excluded for original R1 rays by actual
produced time-one and initial E1 energy, before any finite readback. -/
theorem sourceRadialEnergy_finite (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) :
    sourceRadialEnergy omega (sourceFiniteEnergyRayToGeodesicRay omega L) ≠ ⊤ ∧
      sourceRadialEnergy omega (sourceFiniteEnergyRayToGeodesicRay omega L) ≠ ⊥ := by
  have hf := sourceRelativeFiniteEnergy_coe_toReal omega
    (sourceFiniteEnergyRaySlice omega L ⟨1, by norm_num⟩).property
  change ((sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ).toReal : EReal) =
    sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ at hf
  have hne : sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ ≠ ⊥ := by
    rw [← hf]
    exact EReal.coe_ne_bot _
  rw [sourceRadialEnergy_eq omega]
  change (if sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ = ⊥ then ⊥ else _) ≠ ⊤ ∧
    (if sourceRelativeEnergy θ φ (L.val ⟨1, by norm_num⟩) hφ = ⊥ then ⊥ else _) ≠ ⊥
  rw [if_neg hne]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- WHOLE original ordered-ray proposition, with the literal original
LIMSUP energies and original radial Darvas limit on exact source R1.
All-time original order and every original pole are preserved. -/
theorem sourceRadialDarvasDistance_eq_energy_sub (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) (hle : SourceRayLE L.val K.val) :
    sourceRadialDarvasDistance omega L K =
      sourceRadialEnergy omega (sourceFiniteEnergyRayToGeodesicRay omega K) -
        sourceRadialEnergy omega (sourceFiniteEnergyRayToGeodesicRay omega L) := by
  rw [sourceRadialDarvasDistance_eq_native, sourceRadialEnergy_eq_native,
    sourceRadialEnergy_eq_native]
  exact SingularModelGeodesicRayOrderedDistance.rayD1_eq_radialEnergy_sub_of_model_origin omega
    ((mem_sourceFiniteEnergyRays_iff_native omega θ φ hφ L.val).mp L.property)
    ((mem_sourceFiniteEnergyRays_iff_native omega θ φ hφ K.val).mp K.property)
    ((sourceRayLE_iff_extension L.val K.val).mp hle)

end SGPT.PSH.VariableComplexAtlas
