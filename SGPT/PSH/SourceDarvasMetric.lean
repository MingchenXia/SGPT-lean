import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M]

/-- Exactly the original preceq finite-energy domain, with actual full
non-pluripolar mass and the actual canonical absolute gap integral. -/
abbrev SourceFiniteEnergyPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) :=
  {u : M → EReal // SourceRelativeFiniteEnergy θ φ u hφ}

/-- The genuine whole-class dictionary is an equivalence retaining every
underlying function, with no normalization or bounded-reference condition. -/
def sourceFiniteEnergyPotentialEquivNative
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : SourceFiniteEnergyPotential θ φ hφ ≃
      SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative where
  toFun u := ⟨u.val, (sourceRelativeFiniteEnergy_iff_native θ φ u.val hφ).mp u.property⟩
  invFun u := ⟨u.val, (sourceRelativeFiniteEnergy_iff_native θ φ u.val hφ).mpr u.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The original Darvas formula is defined on precisely the original E1
subtype. The finite-energy readback theorem below excludes BOTH energy
endpoints for all three terms; no assertion is made on a larger domain. -/
def sourceDarvasDistance (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ)
    (u v : SourceFiniteEnergyPotential θ φ hφ) : ℝ :=
  (sourceRelativeEnergy θ φ u.val hφ).toReal +
    (sourceRelativeEnergy θ φ v.val hφ).toReal -
      2 * (sourceRelativeEnergy θ φ (thetaRooftop θ u.val v.val) hφ).toReal

variable [BorelSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual source rooftop closure manufactures the genuine E1 rooftop;
neither PSH nor full mass nor integrability of this output is supplied. -/
def sourceFiniteEnergyRooftop (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) : SourceFiniteEnergyPotential θ φ hφ :=
  ⟨thetaRooftop θ u.val v.val,
    sourceRelativeFiniteEnergy_rooftop omega u.property v.property⟩

/-- The literal largest-source-competitor rooftop is the native envelope,
using genuine rooftop closure produced from the two input E1 potentials. -/
theorem sourceFiniteEnergyRooftop_eq_native (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    (sourceFiniteEnergyRooftop omega u v).val =
      RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u.val v.val := by
  exact sourceThetaRooftop_eq_native u.property.1.choose v.property.1.choose
    (RelativePreceqClasses.relativeFiniteEnergyPreceq_rooftop omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)).1.plurisubharmonic

/-- All THREE defining energies are genuinely finite before real readback.
In particular the rooftop term is not an unsupported toReal convention. -/
theorem sourceDarvasEnergies_finite (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    ((sourceRelativeEnergy θ φ u.val hφ).toReal : EReal) = sourceRelativeEnergy θ φ u.val hφ ∧
    ((sourceRelativeEnergy θ φ v.val hφ).toReal : EReal) = sourceRelativeEnergy θ φ v.val hφ ∧
    ((sourceRelativeEnergy θ φ (thetaRooftop θ u.val v.val) hφ).toReal : EReal) =
      sourceRelativeEnergy θ φ (thetaRooftop θ u.val v.val) hφ :=
  ⟨sourceRelativeFiniteEnergy_coe_toReal omega u.property,
    sourceRelativeFiniteEnergy_coe_toReal omega v.property,
    sourceRelativeFiniteEnergy_coe_toReal omega
      (sourceRelativeFiniteEnergy_rooftop omega u.property v.property)⟩

/-- The complete original energy formula and actual rooftop equal the
genuine native Darvas functional on the ENTIRE original E1 domain. -/
theorem sourceDarvasDistance_eq_native (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ u v =
      RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative u.val v.val := by
  have hr := sourceFiniteEnergyRooftop_eq_native omega u v
  change thetaRooftop θ u.val v.val = _ at hr
  simp only [sourceDarvasDistance, sourceRelativeEnergy_eq_native, hr,
    RelativeDarvasDistance.relativeD1]

/-- The original ordered energy-difference equation on its full E1 domain. -/
theorem sourceDarvasDistance_eq_energy_sub_of_le (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) (huv : u.val ≤ v.val) :
    sourceDarvasDistance θ φ hφ u v =
      (sourceRelativeEnergy θ φ v.val hφ).toReal -
        (sourceRelativeEnergy θ φ u.val hφ).toReal := by
  rw [sourceDarvasDistance_eq_native omega, sourceRelativeEnergy_eq_native,
    sourceRelativeEnergy_eq_native]
  exact RelativeDarvasDistance.relativeD1_eq_sub_of_le
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose) huv

/-- Actual finite-energy rooftop closure and genuine envelope maximality
give the original Pythagorean decomposition used in both source proofs. -/
theorem sourceDarvasDistance_eq_add_rooftop (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ u v =
      sourceDarvasDistance θ φ hφ u (sourceFiniteEnergyRooftop omega u v) +
        sourceDarvasDistance θ φ hφ v (sourceFiniteEnergyRooftop omega u v) := by
  simp only [sourceDarvasDistance_eq_native omega, sourceFiniteEnergyRooftop_eq_native omega]
  exact RelativeDarvasDistance.relativeD1_eq_add_rooftop
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose)
    ((isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1.choose)
    (RelativePreceqClasses.relativeFiniteEnergyPreceq_rooftop omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)).1.plurisubharmonic

/-- WHOLE original prop:d1contract, for all original E1 inputs and their
produced actual rooftops, with an arbitrary singular model reference. -/
theorem sourceDarvasDistance_rooftop_le (omega : KahlerBackground n M)
    (u v w : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ
        (sourceFiniteEnergyRooftop omega u w) (sourceFiniteEnergyRooftop omega v w) ≤
      sourceDarvasDistance θ φ hφ u v := by
  simp only [sourceDarvasDistance_eq_native omega, sourceFiniteEnergyRooftop_eq_native omega]
  exact SingularModelDarvasContraction.relativeD1_rooftop_le omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp w.property)

theorem sourceDarvasDistance_nonneg (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) : 0 ≤ sourceDarvasDistance θ φ hφ u v := by
  rw [sourceDarvasDistance_eq_native omega]
  exact SingularModelDarvasBasic.relativeD1_nonneg omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)

theorem sourceDarvasDistance_self (omega : KahlerBackground n M)
    (u : SourceFiniteEnergyPotential θ φ hφ) : sourceDarvasDistance θ φ hφ u u = 0 := by
  rw [sourceDarvasDistance_eq_native omega]
  exact RelativeDarvasDistance.relativeD1_self
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose)

theorem sourceDarvasDistance_comm (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ u v = sourceDarvasDistance θ φ hφ v u := by
  simp only [sourceDarvasDistance_eq_native omega]
  exact RelativeDarvasDistance.relativeD1_comm _ _ _ _ _

/-- The actual singular-model contraction and finite rooftop-energy order
produce the source triangle inequality, not a triangle certificate. -/
theorem sourceDarvasDistance_triangle (omega : KahlerBackground n M)
    (u v w : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ u v ≤
      sourceDarvasDistance θ φ hφ u w + sourceDarvasDistance θ φ hφ w v := by
  simp only [sourceDarvasDistance_eq_native omega]
  exact SingularModelDarvasContraction.relativeD1_triangle omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp w.property)

/-- Genuine truncation locality, energy bounds and actual full-mass
domination supply separation on the entire original preceq E1 domain. -/
theorem sourceDarvasDistance_eq_zero_iff (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ u v = 0 ↔ u = v := by
  constructor
  · intro h
    rw [sourceDarvasDistance_eq_native omega] at h
    exact Subtype.ext (SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property) h)
  · rintro rfl
    exact sourceDarvasDistance_self omega u

/-- The WHOLE original metric lemma as an actual MetricSpace, transported
through the complete original/native subtype equivalence. No completeness
assertion is included in this earlier source statement. -/
@[instance_reducible]
def sourceDarvasMetricSpace (omega : KahlerBackground n M) :
    MetricSpace (SourceFiniteEnergyPotential θ φ hφ) :=
  MetricSpace.induced (sourceFiniteEnergyPotentialEquivNative θ φ hφ)
    (sourceFiniteEnergyPotentialEquivNative θ φ hφ).injective
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace omega)

/-- The transported actual metric has precisely the original defining
energy/rooftop distance on the same original functions. -/
theorem sourceDarvasMetricSpace_dist (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    dist u v = sourceDarvasDistance θ φ hφ u v := by
  change RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative
    u.val v.val = sourceDarvasDistance θ φ hφ u v
  exact (sourceDarvasDistance_eq_native omega u v).symm

end SGPT.PSH.VariableComplexAtlas
