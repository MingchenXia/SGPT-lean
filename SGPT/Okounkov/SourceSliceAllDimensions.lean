import SGPT.Okounkov.SourceSliceKahlerTrace
import SGPT.Okounkov.SourceSliceZeroTail

/-! Whole source lma:slicepob, every n>0 including the genuine zero-dimensional
first-flag target: Kähler-current existence and identity, then the source's
printed general positive-current/defined-trace clause, with unchanged objects. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Filter
open scoped Topology Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.PSH SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN

/-- The printed general positive-current clause for positive-dimensional
targets, obtained by the same potential's actual positive perturbations.
The trace and its representative are exactly the original source inputs. -/
theorem slice_zero_generalPartialBody_eq_of_defined_sourceTrace
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ)
    {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential (firstFlagRestriction F θ).val ψ)
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m + 1) ψ τ) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ) ψ := by
  rw [generalPartialBody_eq_iInter_general_add_kahler F hφ F.omega,
    firstCoordinateSlice_iInter,
    generalPartialBody_eq_iInter_general_add_kahler F.tail hψ
      (TranscendentalSlice.restrictedKahlerForm (F := F) F.omega)]
  congr 1
  funext j
  have he : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  have hK := isKahlerCurrentPotential_add_smul hφ F.omega he
  have hψε : IsThetaPshPotential
      (firstFlagRestriction F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form)).val ψ := by
    have h := isThetaPshPotential_of_isKahlerCurrentPotential
      (isKahlerCurrentPotential_add_smul hψ
        (TranscendentalSlice.restrictedKahlerForm (F := F) F.omega) he)
    simpa only [Valuative.firstFlagRestriction_add_smul,
      TranscendentalSlice.restrictedKahlerForm_form] using h
  have h := slice_zero_generalPartialBody_eq_of_kahler F hK hτ hψε hP
  simpa only [Valuative.firstFlagRestriction_add_smul,
    TranscendentalSlice.restrictedKahlerForm_form] using h

/-- The genuine original generic-zero reader gives first valuation zero,
without requiring pointwise finiteness on the first flag component. -/
theorem flagValuation_first_zero_of_source_generic_zero
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.tail.carrier → F.carrier) φ = 0) :
    flagValuation F φ 0 = 0 := by
  have h0 : (potentialFlagValuation F hφ 0 : ℝ≥0∞) = 0 :=
    (potentialFlagValuation_first F hφ).trans hz
  have hNN : potentialFlagValuation F hφ 0 = 0 := by exact_mod_cast h0
  rw [flagValuation_eq hφ]
  change ((potentialFlagValuation F hφ 0 : NNReal) : ℝ) = 0
  rw [hNN, NNReal.coe_zero]

/-- The whole original source general positive-current/defined-trace clause
of lma:slicepob, for every positive source dimension n=m+1. The target is
literally the actual source body, including its genuine n=0 construction. -/
theorem slice_zero_generalBody_eq_of_defined_sourceTrace
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.tail.carrier → F.carrier) φ = 0)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ)
    {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential (firstFlagRestriction F θ).val ψ)
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m) ψ τ) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      SourceTestCurveAllDimensions.generalBody F.tail (firstFlagRestriction F θ) ⟨ψ, hψ⟩ := by
  cases m with
  | zero =>
      exact Valuative.slice_zero_generalBody_eq_of_dim_one F hφ
        (flagValuation_first_zero_of_source_generic_zero F hφ hz) hψ
  | succ k =>
      exact slice_zero_generalPartialBody_eq_of_defined_sourceTrace F hφ hτ hψ hP

/-- The original Kähler-current hypotheses themselves manufacture the source
trace's representative in the literal restricted original class, in every
source dimension. This proves the existence implicit in the first clause. -/
theorem exists_source_trace_representative_of_kahler_zero
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    (hz : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.tail.carrier → F.carrier) φ = 0) :
    ∃ (τ ψ : F.tail.carrier → EReal),
      IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ ∧
      ∃ hψ : IsThetaPshPotential (firstFlagRestriction F θ).val ψ,
        (letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
        haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
        SourcePEquivalent (n := m) ψ τ) ∧
        firstCoordinateSlice (generalPartialBody F θ φ) 0 =
          SourceTestCurveAllDimensions.generalBody F.tail (firstFlagRestriction F θ) ⟨ψ, hψ⟩ := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hι := contMDiff_firstFlagInclusion F
  have hg := nativeGeneric_zero_of_source_zero F φ hz
  obtain ⟨κ, ψ, hT, hψ, hpos⟩ := exists_positive_native_first_trace_of_kahler_zero F hK hg
  have hu : IsGlobalQuasiPshPotential (n := m + 1) φ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background
      F.omega φ).mpr ⟨θ, hφ⟩
  obtain ⟨τ, hτ⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential
    (Nat.le_succ m) F.omega F.tail.omega hu hι hz
  have hnat := (isSourceTraceRepresentativeAlong_iff_native (Nat.succ_ne_zero m)
    F.omega F.tail.omega hι φ τ).mp hτ
  have hP := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    F.tail.omega F.tail.omega hι hT hnat
  have hτ' : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ := hτ
  exact ⟨τ, ψ, hτ', hψ, hP,
    slice_zero_generalBody_eq_of_defined_sourceTrace F hφ hz hτ' hψ hP⟩
end SGPT.Okounkov.SourceSlice
