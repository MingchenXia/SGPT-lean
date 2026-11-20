import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.PSH.SourceEnvelopeRooftop
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original all-chart competitors produce exactly the native minimal envelope. -/
theorem sourceMinimalEnvelope_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    sourceMinimalEnvelope θ = thetaPshSupremum (atlasClosedFormToNative θ).val := by
  funext x
  rw [thetaPshSupremum_apply]
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup_of_le v.1 (le_iSup_of_le
      ⟨(isThetaPSH_iff_nativeThetaPotential θ v.1).mp v.2.1, v.2.2⟩ le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    exact le_iSup (fun w : {w : M → EReal //
      (ofFixedModel n M).IsThetaPSH θ w ∧ w ≤ 0} ↦ w.1 x)
      ⟨v, (isThetaPSH_iff_nativeThetaPotential θ v).mpr hv.1, hv.2⟩

/-- Finite translation is reversible at both original infinite endpoints. -/
theorem sub_one_le_iff_le_add_one (a b : EReal) :
    a - 1 ≤ b ↔ a ≤ b + 1 :=
  EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot 1)) (Or.inl (EReal.coe_ne_top 1))

variable [MeasurableSpace M] [CompactSpace M]

/-- The actual diagonal non-pluripolar measure of an original universal theta-PSH input.
The unchanged background and the genuine native potential are internally recovered. -/
def sourcePotentialNonPluripolarMeasure
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : Measure M :=
  diagonalPotentialMeasure (atlasClosedFormToNative θ) u
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- Original `def:cap`: the literal printed all-source-competitor supremum.
On Borel sets these are the original integrals. The same measure outer values
extend the construction to arbitrary sets, without a measurability premise. -/
def sourceThetaCapacity (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (E : Set M) : ℝ≥0∞ :=
  ⨆ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (_ : (fun x ↦ sourceMinimalEnvelope θ x - 1) ≤ u)
    (_ : u ≤ sourceMinimalEnvelope θ), sourcePotentialNonPluripolarMeasure θ u hu E

/-- The source-facing Borel-set formula retains the actual printed inequalities. -/
theorem sourceThetaCapacity_borel
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (E : Set M)
    (_hE : MeasurableSet E) :
    sourceThetaCapacity θ E =
      ⨆ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
        (_ : (fun x ↦ sourceMinimalEnvelope θ x - 1) ≤ u)
        (_ : u ≤ sourceMinimalEnvelope θ), sourcePotentialNonPluripolarMeasure θ u hu E := rfl

/-- Exact equality with the genuine native theta-capacity, by actual competitor
reindexing. No mass, reference boundedness, or capacity certificate is supplied. -/
theorem sourceThetaCapacity_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (E : Set M) :
    sourceThetaCapacity θ E = ThetaCapacity.thetaCapacityV (atlasClosedFormToNative θ) E := by
  unfold sourceThetaCapacity ThetaCapacity.thetaCapacityV ThetaCapacity.thetaCapacity
  rw [sourceMinimalEnvelope_eq_native]
  apply le_antisymm
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply iSup_le
    intro hlo
    apply iSup_le
    intro hup
    exact le_iSup_of_le u (le_iSup_of_le
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      (le_iSup_of_le hup (le_iSup_of_le
        (fun x ↦ (sub_one_le_iff_le_add_one _ _).mp (hlo x)) le_rfl)))
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply iSup_le
    intro hup
    apply iSup_le
    intro hlo
    exact le_iSup_of_le u (le_iSup_of_le
      ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hu)
      (le_iSup_of_le
        (fun x ↦ (sub_one_le_iff_le_add_one _ _).mpr (hlo x))
        (le_iSup_of_le hup le_rfl)))

@[simp] theorem sourceThetaCapacity_empty
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    sourceThetaCapacity θ (∅ : Set M) = 0 := by
  rw [sourceThetaCapacity_eq_native]
  exact ThetaCapacity.thetaCapacity_empty _ _

theorem sourceThetaCapacity_mono
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {E F : Set M} (hEF : E ⊆ F) :
    sourceThetaCapacity θ E ≤ sourceThetaCapacity θ F := by
  rw [sourceThetaCapacity_eq_native, sourceThetaCapacity_eq_native]
  exact ThetaCapacity.thetaCapacity_mono hEF

theorem sourceThetaCapacity_union_le
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (E F : Set M) :
    sourceThetaCapacity θ (E ∪ F) ≤ sourceThetaCapacity θ E + sourceThetaCapacity θ F := by
  simp only [sourceThetaCapacity_eq_native, ThetaCapacity.thetaCapacityV]
  exact ThetaCapacity.thetaCapacity_union_le _ _ _ _

end SGPT.PSH.VariableComplexAtlas
