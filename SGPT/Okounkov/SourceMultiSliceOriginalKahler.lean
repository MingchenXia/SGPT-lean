import SGPT.Okounkov.SourceMultiSliceTargetApproximation
import SGPT.Okounkov.SourceMultiSliceBodyAllDimensions
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance

/-! Actual all-k Kähler-current source slice: same original approximation,
actual current-margin trace reader and genuine original zero target. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody

/-- Every SAME original analytic Kähler-QEA stage internally gets its
actual original target PSH witness and its entire first-k-zero source slice.
The finite target point is derived from original generic zero. -/
theorem original_kahlerQEA_stage_zero_slices (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    (hg : (⨅ y, lelongNumber (n := m + k) φ (originalInclusion m k F y)) = 0)
    (j : ℕ) :
    ∃ hr : IsThetaPshPotential (originalRestriction m k F θ).val
        (fun y => U j (originalInclusion m k F y)),
      zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨U j,(hU.2 j).1.1⟩) =
        SourceTestCurveAllDimensions.generalBody (originalTail m k F)
          (originalRestriction m k F θ) ⟨fun y => U j (originalInclusion m k F y),hr⟩ := by
  obtain ⟨omegaRef, ε, hfull⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  have hι := originalInclusion_contMDiff m k F
  have hdirect : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => U j (originalInclusion m k F y)) := by
    apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hU.2 j).1.1.1
    · intro x _
      exact hfull.term_hasAnalyticSingularityType j (complexChartAt (n := m + k) x)
        ((complexChartAt (n := m + k) x).val x)
        ((complexChartAt (n := m + k) x).val.map_source (mem_complexChartAt_source x))
    · exact AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero
        hfull (originalInclusion m k F) hg j
  obtain ⟨y, _, hy⟩ := hdirect.2 (Classical.choice inferInstance) Set.univ isOpen_univ (mem_univ _)
  exact analytic_zeroSlice_eq_of_original_target_finite m k F (hU.2 j).1 ⟨y,hy⟩

/-- The actual original current margin produces a positive genuine trace
reader in the SAME original restricted class, including target dimension zero. -/
theorem exists_positive_native_original_target_trace (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    [MeasurableSpace (originalTail m k F).carrier] [BorelSpace (originalTail m k F).carrier]
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    (hg : (⨅ y, lelongNumber (n := m + k) φ (originalInclusion m k F y)) = 0) :
    ∃ (κ : KahlerBackground (m + k) F.carrier) (ρ : (originalTail m k F).carrier → EReal),
      IsTraceRepresentativeAlong κ (originalTail m k F).omega
        (originalInclusion_contMDiff m k F) φ ρ ∧
      ∃ hρ : IsThetaPshPotential (originalRestriction m k F θ).val ρ,
        HasPositivePotentialMass (originalRestriction m k F θ) ρ hρ := by
  obtain ⟨κ,hκ⟩ := hK
  have hκ' : IsThetaPshPotential (θ - (1 : ℝ) • κ.form).val φ := by
    simpa only [one_smul] using hκ
  obtain ⟨ρ,hT,hρP,hposP⟩ :=
    PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin
      κ (originalTail m k F).omega (originalInclusion_contMDiff m k F)
      (originalInclusion_pullback_isKahler m k F κ) zero_lt_one hκ' hg
  have hρR := ((originalRestriction_geometricallyEq m k F θ).thetaPshPotential_iff ρ).mpr hρP
  have hmass := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq
    (originalRestriction_geometricallyEq m k F θ) hρR hρP
  refine ⟨κ,ρ,hT,hρR,?_⟩
  rw [HasPositivePotentialMass, hmass]
  exact hposP

/-- Exact original all-k Kähler body slice, using internally constructed
ordinary stage restrictions/native limit and the actual zero-source carrier. -/
theorem original_zeroSlice_kahler_of_positive_native_trace (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    [MeasurableSpace (originalTail m k F).carrier] [BorelSpace (originalTail m k F).carrier]
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    {κ : KahlerBackground (m + k) F.carrier} {ρ : (originalTail m k F).carrier → EReal}
    (hT : IsTraceRepresentativeAlong κ (originalTail m k F).omega
      (originalInclusion_contMDiff m k F) φ ρ)
    (hρ : IsThetaPshPotential (originalRestriction m k F θ).val ρ)
    (hpos : HasPositivePotentialMass (originalRestriction m k F θ) ρ hρ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ
      ⟨φ,isThetaPshPotential_of_isKahlerCurrentPotential hK⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ) ⟨ρ,hρ⟩ := by
  obtain ⟨U,hU⟩ := exists_isKahlerQEA hK
  have hstages := original_kahlerQEA_stage_zero_slices m k F hU hT.1
  choose hRstage hStage using hstages
  rw [sourceBody_eq_iInter_kahlerQEA F hK hU, zeroSlice_iInter]
  simp_rw [hStage]
  cases m with
  | zero => simp only [sourceBody_zero_eq_univ, iInter_univ]
  | succ r =>
      have hbig := BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
        (Nat.succ_pos r) (originalTail (r + 1) k F).omega
        (originalRestriction (r + 1) k F θ) hρ hpos
      obtain ⟨hr,hlim⟩ := original_target_kahlerQEA_native_limit (r + 1) k F hU hT hρ hbig
      apply SourceSlice.iInter_generalPartialBody_eq_of_antitone_native_limit
        (originalTail (r + 1) k F) (originalTail (r + 1) k F).omega
        (originalRestriction (r + 1) k F θ) hbig
        (fun j => ⟨fun y => U j (originalInclusion (r + 1) k F y),hr j⟩)
        ⟨ρ,hρ⟩ hpos ?_ hlim
      obtain ⟨omegaRef,ε,hfull⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
      intro i j hij y
      exact hfull.term_antitone (originalInclusion (r + 1) k F y) hij

/-- All-k original Kähler-current source clause for every actual original
trace representative; no positive mass is assumed for that representative. -/
theorem original_zeroSlice_kahler_of_defined_sourceTrace (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (hn : 0 < m + k)
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ)
    {κSource : KahlerBackground (m + k) F.carrier}
    {τ : (originalTail m k F).carrier → EReal}
    (hτ : letI : MeasurableSpace (originalTail m k F).carrier := borel _
      haveI : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
      IsSourceTraceRepresentativeAlong κSource (originalTail m k F).omega
        (originalInclusion_contMDiff m k F) φ τ)
    {ψ : (originalTail m k F).carrier → EReal}
    (hψ : IsThetaPshPotential (originalRestriction m k F θ).val ψ)
    (hP : letI : MeasurableSpace (originalTail m k F).carrier := borel _
      haveI : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
      SourcePEquivalent (n := m) ψ τ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ
      ⟨φ,isThetaPshPotential_of_isKahlerCurrentPotential hK⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ) ⟨ψ,hψ⟩ := by
  let _ : MeasurableSpace (originalTail m k F).carrier := borel _
  have _ : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
  have hnat := (isSourceTraceRepresentativeAlong_iff_native hn.ne'
    κSource (originalTail m k F).omega (originalInclusion_contMDiff m k F) φ τ).mp hτ
  obtain ⟨κ,ρ,hT,hρ,hpos⟩ := exists_positive_native_original_target_trace m k F hK hnat.1
  rw [original_zeroSlice_kahler_of_positive_native_trace m k F hK hT hρ hpos]
  have hρτ := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    (originalTail m k F).omega (originalTail m k F).omega
    (originalInclusion_contMDiff m k F) hT hnat
  apply Subset.antisymm
  · exact sourceBody_mono_of_iOrder (originalTail m k F) hρ hψ
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans (originalTail m k F).omega hρτ.1 hP.2))
  · exact sourceBody_mono_of_iOrder (originalTail m k F) hψ hρ
      (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
        (SourcePOrder.trans (originalTail m k F).omega hP.1 hρτ.2))
end SGPT.Okounkov.SourceMultiSlice
