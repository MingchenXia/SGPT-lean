import SGPT.Okounkov.SourceSliceRestrictedLimit
import SGPT.Okounkov.SourceTraceOperations
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

/-! Complete original Kähler-current slice: actual current margin produces
the positive original-class trace reader, and exact QEA body intersections
produce the slice without incoming approximation or convergence data. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Filter
open scoped Topology Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.Okounkov.TranscendentalPartial
open SGPT.PSH SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN

/-- The actual current's Kähler margin, with actual zero generic Lelong
number, produces a positive trace reader in the literal original restricted
class. This includes the genuine zero-dimensional target. -/
theorem exists_positive_native_first_trace_of_kahler_zero
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    [MeasurableSpace F.tail.carrier] [BorelSpace F.tail.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    (hz : (⨅ y : F.tail.carrier, lelongNumber (n := m + 1) φ y.val) = 0) :
    ∃ (κ : KahlerBackground (m + 1) F.carrier) (ρ : F.tail.carrier → EReal),
      IsTraceRepresentativeAlong κ F.tail.omega (contMDiff_firstFlagInclusion F) φ ρ ∧
      ∃ hρ : IsThetaPshPotential (firstFlagRestriction F θ).val ρ,
        HasPositivePotentialMass (firstFlagRestriction F θ) ρ hρ := by
  obtain ⟨κ, hκ⟩ := hK
  have hκ' : IsThetaPshPotential (θ - (1 : ℝ) • κ.form).val φ := by
    simpa only [one_smul] using hκ
  have hpull : (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F)
      κ.form).val.IsKahler := (TranscendentalSlice.restrictedKahlerForm (F := F) κ).isKahler
  obtain ⟨ρ, hT, hρ, hpos⟩ :=
    PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin
      κ F.tail.omega (contMDiff_firstFlagInclusion F) hpull zero_lt_one hκ' hz
  exact ⟨κ, ρ, hT, hρ, hpos⟩

/-- The actual original Kähler QEA and genuine positive trace reader give
precisely the source body slice. All stage restrictions and their native
convergence are constructed by the preceding producer. -/
theorem slice_zero_kahler_of_positive_native_trace
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    [MeasurableSpace F.tail.carrier] [BorelSpace F.tail.carrier]
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    {κ : KahlerBackground (m + 2) F.carrier} {ρ : F.tail.carrier → EReal}
    (hT : IsTraceRepresentativeAlong κ F.tail.omega (contMDiff_firstFlagInclusion F) φ ρ)
    (hρ : IsThetaPshPotential (firstFlagRestriction F θ).val ρ)
    (hpos : HasPositivePotentialMass (firstFlagRestriction F θ) ρ hρ) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ) ρ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hK
  have hbig := BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
    (Nat.succ_pos m) F.tail.omega (firstFlagRestriction F θ) hρ hpos
  obtain ⟨hr, hlim⟩ := restricted_kahlerQEA_native_limit F hU hT hρ hbig
  have hstage (j : ℕ) : generalPartialBody F θ (U j) = partialOkounkovBody F θ (U j) :=
    (generalPartialBody_eq_analyticPartialBody (hU.2 j).1 (hU.2 j).2).trans
      (TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody (hU.2 j).1 (hU.2 j).2)
  have hinter : generalPartialBody F θ φ = ⋂ j, generalPartialBody F θ (U j) :=
    (generalPartialBody_eq_kahlerPartialBody hK).trans
      ((kahlerPartialBody_eq_iInter hU).trans (iInter_congr fun j => (hstage j).symm))
  rw [hinter, firstCoordinateSlice_iInter]
  have hslice (j : ℕ) : firstCoordinateSlice (generalPartialBody F θ (U j)) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ)
        (fun y : F.tail.carrier => U j y.val) :=
    slice_zero_of_globalAnalytic_of_restriction_psh F (hU.2 j).1 (hr j)
  simp_rw [hslice]
  apply iInter_generalPartialBody_eq_of_antitone_native_limit F.tail F.tail.omega
    (firstFlagRestriction F θ) hbig
    (fun j => ⟨fun y : F.tail.carrier => U j y.val, hr j⟩) ⟨ρ, hρ⟩ hpos ?_ hlim
  obtain ⟨ω, ε, hfull⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  intro i j hij y
  exact hfull.term_antitone y.val hij

/-- Full positive-dimensional-target Kähler clause of source `lma:slicepob`:
the internally produced positive reader is compared with every original
source trace representative. No positive-mass premise is imposed on ψ. -/
theorem slice_zero_generalPartialBody_eq_of_kahler
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ)
    {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential (firstFlagRestriction F θ).val ψ)
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m + 1) ψ τ) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ) ψ := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have htr : IsSourceTraceRepresentativeAlong F.omega F.tail.omega
      (contMDiff_firstFlagInclusion F) φ τ := hτ
  have hnative := (isSourceTraceRepresentativeAlong_iff_native (by omega)
    F.omega F.tail.omega (contMDiff_firstFlagInclusion F) φ τ).mp htr
  obtain ⟨κ, ρ, hT, hρ, hpos⟩ :=
    exists_positive_native_first_trace_of_kahler_zero F hK hnative.1
  rw [slice_zero_kahler_of_positive_native_trace F hK hT hρ hpos]
  have hρτ := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    F.tail.omega F.tail.omega (contMDiff_firstFlagInclusion F) hT hnative
  apply Subset.antisymm
  · exact Valuative.generalPartialBody_mono_of_iOrder hρ hψ
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans F.tail.omega hρτ.1 hP.2))
  · exact Valuative.generalPartialBody_mono_of_iOrder hψ hρ
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans F.tail.omega hP.1 hρτ.2))
end SGPT.Okounkov.SourceSlice
