import SGPT.NAPotential.DHMeasure
import SGPT.PSH.SourceTestCurveModificationPullback
import SGPT.Envelopes.SourcePositiveMassCurrents

/-! # Duistermaat--Heckman measures on supplied modifications

For an original positive I-model test curve on `X`, pull it
back through a genuine analytic modification from a compact Kähler manifold
with a smooth flag. Its flag DH measure is independent of that supplied
modification and flag: both measures have the same original slice-mass tails.
No existence of a flag-carrying modification is assumed to have been proved
here. The existing flag measure is in successor dimension.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DH

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {π : Y → X}

/-- Pull back the actual positive I-model curve along the given modification. -/
def positiveCurveModificationPullback (hπ : IsAnalyticModification (n := n) π)
    (omegaY : KahlerBackground n Y) (Γ : SourcePositiveIModelTestCurve θ) :
    SourcePositiveIModelTestCurve (θ.nativeHolomorphicPullback hπ.1) := by
  refine ⟨Γ.val.modificationPullback hπ, ?_⟩
  apply (sourceIModelTestCurvesPositive_iff_slices omegaY _).mpr
  apply (Γ.val.modificationPullback_isIModel_iff hπ).mpr
  obtain ⟨φ, hφ, hΓ⟩ := Γ.property
  exact hΓ.2

/-- The actual original cutoff survives pointwise modification pullback. -/
theorem positiveCurveModificationPullback_max (hπ : IsAnalyticModification (n := n) π)
    (omegaY : KahlerBackground n Y) (Γ : SourcePositiveIModelTestCurve θ) :
    (positiveCurveModificationPullback hπ omegaY Γ).val.max = Γ.val.max := rfl

/-- Every strict pulled-back slice has the same total mass as the same original
slice, without a nonempty exceptional-locus or finite-value hypothesis. -/
theorem positiveCurveModificationPullback_slice_mass
    (hπ : IsAnalyticModification (n := n) π) (omegaY : KahlerBackground n Y)
    (Γ : SourcePositiveIModelTestCurve θ) (t : ℝ) (ht : t < Γ.val.max) :
    sourcePotentialNonPluripolarMeasure (θ.nativeHolomorphicPullback hπ.1)
      ((positiveCurveModificationPullback hπ omegaY Γ).val.potential ⟨t, ht⟩)
      ((positiveCurveModificationPullback hπ omegaY Γ).val.thetaPSH ⟨t, ht⟩) univ =
    sourcePotentialNonPluripolarMeasure θ (Γ.val.potential ⟨t, ht⟩)
      (Γ.val.thetaPSH ⟨t, ht⟩) univ := by
  exact sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ
    (Γ.val.thetaPSH ⟨t, ht⟩)
    ((positiveCurveModificationPullback hπ omegaY Γ).val.thetaPSH ⟨t, ht⟩)

section SuppliedFlags

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)} {π : F.carrier → X}

/-- The positive limit mass of the actual pullback manufactures the big
background needed by the existing flag measure. -/
theorem positiveCurveModificationPullback_isBig
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1))) := by
  let G := positiveCurveModificationPullback hπ F.omega Γ
  exact sourcePositiveMass_isBig F.omega G.val.limit_thetaPSH G.val.positiveLimitMass

/-- The actual flag measure on the supplied modified manifold. -/
def naDuistermaatHeckmanOnModification
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ) :
    Measure ℝ :=
  naDuistermaatHeckman (F := F) (positiveCurveModificationPullback_isBig hπ Γ)
    (positiveCurveModificationPullback hπ F.omega Γ)

instance naDuistermaatHeckmanOnModification_finite
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ) :
    IsFiniteMeasure (naDuistermaatHeckmanOnModification (F := F) hπ Γ) := by
  unfold naDuistermaatHeckmanOnModification
  infer_instance

/-- A supplied modification reads the original strict slice mass as its
entire upper tail. -/
theorem naDuistermaatHeckmanOnModification_Ici
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ)
    (t : ℝ) (ht : t < Γ.val.max) :
    naDuistermaatHeckmanOnModification (F := F) hπ Γ (Ici t) =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential ⟨t, ht⟩)
        (Γ.val.thetaPSH ⟨t, ht⟩) univ := by
  unfold naDuistermaatHeckmanOnModification
  rw [naDuistermaatHeckman_Ici (F := F) (positiveCurveModificationPullback_isBig hπ Γ)
    (positiveCurveModificationPullback hπ F.omega Γ) ⟨t, ht⟩]
  exact positiveCurveModificationPullback_slice_mass hπ F.omega Γ t ht

/-- The actual modification measure vanishes above the unchanged cutoff. -/
theorem naDuistermaatHeckmanOnModification_Ioi_max
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanOnModification (F := F) hπ Γ (Ioi Γ.val.max) = 0 := by
  unfold naDuistermaatHeckmanOnModification
  exact naDuistermaatHeckman_Ioi_max _ _

/-- The two genuine flag measures on two supplied modifications coincide.
Neither a common refinement nor equality of their measures is supplied. -/
theorem naDuistermaatHeckmanOnModification_independent
    {F₁ F₂ : OriginalFlagGeometry.{u} (m + 1)}
    [MeasurableSpace F₁.carrier] [BorelSpace F₁.carrier]
    [MeasurableSpace F₂.carrier] [BorelSpace F₂.carrier]
    {π₁ : F₁.carrier → X} {π₂ : F₂.carrier → X}
    (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    (hπ₂ : IsAnalyticModification (n := m + 1) π₂)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanOnModification (F := F₁) hπ₁ Γ =
      naDuistermaatHeckmanOnModification (F := F₂) hπ₂ Γ := by
  apply measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact naDuistermaatHeckmanOnModification_Ioi_max (F := F₁) hπ₁ Γ
  · exact naDuistermaatHeckmanOnModification_Ioi_max (F := F₂) hπ₂ Γ
  · intro t ht
    rw [naDuistermaatHeckmanOnModification_Ici (F := F₁) hπ₁ Γ t ht,
      naDuistermaatHeckmanOnModification_Ici (F := F₂) hπ₂ Γ t ht]

end SuppliedFlags
end SGPT.NAPotential.DH
