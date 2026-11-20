import SGPT.Okounkov.SourceMultiSliceOriginalInverse
import SGPT.Okounkov.SourceMultiSliceOriginalRestriction
import SGPT.Okounkov.SourceTraceModification
import SGPT.PSH.SourceModificationOrders

/-! Direct ORIGINAL Y_k traces and potentials are pulled to the actual
original iterated tail by its internally constructed canonical biholomorphism.
No trace, chart, body or carrier transport certificate is supplied. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- The SAME direct original Y_k has its original closed/connected regularity. -/
theorem directCarrier_isClosedConnectedSubmanifold (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) :
    IsClosedConnectedSubmanifold (m + k) (F.flag (originalIndex m k)) m :=
  ⟨(F.smooth.2.2 (originalIndex m k)).1,
    (F.smooth.2.2 (originalIndex m k)).2.1,directCarrier_regular m k F⟩

section Direct
variable (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k))
local instance directCharts : ChartedSpace (ComplexModel m) (F.flag (originalIndex m k)) :=
  directCarrierCharts m k F
local instance directComplex : IsComplexManifold m (F.flag (originalIndex m k)) :=
  directCarrierComplex m k F
local instance directCompact : CompactSpace (F.flag (originalIndex m k)) :=
  isCompact_iff_compactSpace.mp (directCarrier_isClosedConnectedSubmanifold m k F).1.isCompact
local instance directConnected : ConnectedSpace (F.flag (originalIndex m k)) :=
  isConnected_iff_connectedSpace.mp (directCarrier_isClosedConnectedSubmanifold m k F).2.1
local instance directMeasurable : MeasurableSpace (F.flag (originalIndex m k)) := borel _
local instance directBorel : BorelSpace (F.flag (originalIndex m k)) := ⟨rfl⟩
local instance targetMeasurable : MeasurableSpace (originalTail m k F).carrier := borel _
local instance targetBorel : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
local instance ambientMeasurable : MeasurableSpace F.carrier := borel _
local instance ambientBorel : BorelSpace F.carrier := ⟨rfl⟩

/-- The actual original direct inclusion, in its genuine inherited atlas. -/
theorem directCarrierInclusion_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + k)) ∞
      (Subtype.val : F.flag (originalIndex m k) → F.carrier) :=
  SubmanifoldChartedSpace.contMDiff_val (by omega) (directCarrier_regular m k F)

/-- Literal original smooth form restricted DIRECTLY to original Y_k. -/
def directRestriction (θ : ClosedRealOneOneForm (m + k) F.carrier) :
    ClosedRealOneOneForm m (F.flag (originalIndex m k)) :=
  ClosedRealOneOneForm.pullback (directCarrierInclusion_contMDiff m k F) θ

/-- Actual original ambient Kahler form restricted DIRECTLY to original Y_k. -/
def directCarrierKahler (omegaAmbient : KahlerBackground (m + k) F.carrier) :
    KahlerBackground m (F.flag (originalIndex m k)) :=
  SubmanifoldKahlerRestriction.kahlerBackground (by omega)
    (directCarrier_regular m k F) omegaAmbient

/-- The canonical actual carrier map is a true analytic modification, with
its real global holomorphic inverse and compactness supplying properness. -/
theorem originalCarrierHomeomorph_isAnalyticModification :
    IsAnalyticModification (n := m) (originalCarrierHomeomorph m k F) := by
  exact isAnalyticModification_biholomorphic_transport
    (Homeomorph.refl (F.flag (originalIndex m k))) (originalCarrierHomeomorph m k F)
    contMDiff_id contMDiff_id
    (originalCarrierHomeomorph_contMDiff m k F)
    (originalCarrierHomeomorph_symm_contMDiff m k F) isAnalyticModification_identity

/-- The actual generic reader is unchanged on the whole original Y_k carrier. -/
theorem sourceGeneric_original_eq_direct (φ : F.carrier → EReal) :
    sourceGenericLelongNumber (n := m + k) (originalInclusion m k F) φ =
      sourceGenericLelongNumber (n := m + k)
        (Subtype.val : F.flag (originalIndex m k) → F.carrier) φ := by
  unfold sourceGenericLelongNumber
  apply le_antisymm
  · apply le_iInf
    intro x
    obtain ⟨y,rfl⟩ := (originalCarrierHomeomorph m k F).surjective x
    exact iInf_le _ y
  · apply le_iInf
    intro y
    exact iInf_le _ (originalCarrierHomeomorph m k F y)

/-- Direct and iterated source-class pullback agree GEOMETRICALLY on the
same original points; literal stored pullback-functoriality is not assumed. -/
theorem originalRestriction_geometricallyEq_directPullback
    (θ : ClosedRealOneOneForm (m + k) F.carrier) :
    (originalRestriction m k F θ).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (originalCarrierHomeomorph_contMDiff m k F)
        (directRestriction m k F θ)).val := by
  have h := TranscendentalVolId.pullback_comp_geometricallyEq'
    (directCarrierInclusion_contMDiff m k F)
    (originalCarrierHomeomorph_contMDiff m k F) θ.val
  exact (originalRestriction_geometricallyEq m k F θ).trans h

/-- A given DIRECT original source representative acquires its actual
iterated original-class PSH witness internally. -/
theorem original_psh_pullback_of_direct {θ : ClosedRealOneOneForm (m + k) F.carrier}
    {ψ : F.flag (originalIndex m k) → EReal}
    (hψ : IsThetaPshPotential (directRestriction m k F θ).val ψ) :
    IsThetaPshPotential (originalRestriction m k F θ).val
      (ψ ∘ originalCarrierHomeomorph m k F) := by
  have hp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    (originalCarrierHomeomorph_isAnalyticModification m k F) (directRestriction m k F θ) hψ
  exact ((originalRestriction_geometricallyEq_directPullback m k F θ).thetaPshPotential_iff _).mpr hp

/-- Genuine original direct-Y_k trace data internally manufacture the literal
pulled trace on the actual original tail; no intermediate trace tower or
trace-equivalence certificate is an input. -/
theorem exists_original_trace_of_direct_sourceTrace
    (omegaAmbient : KahlerBackground (m + k) F.carrier)
    (omegaDirect : KahlerBackground m (F.flag (originalIndex m k)))
    {φ : F.carrier → EReal} {τ : F.flag (originalIndex m k) → EReal}
    (hτ : IsSourceTraceRepresentativeAlong omegaAmbient omegaDirect
      (directCarrierInclusion_contMDiff m k F) φ τ) :
    ∃ κ : KahlerBackground (m + k) F.carrier,
      IsSourceTraceRepresentativeAlong κ (originalTail m k F).omega
        (originalInclusion_contMDiff m k F) φ
        (τ ∘ originalCarrierHomeomorph m k F) := by
  have hz : sourceGenericLelongNumber (n := m + k) (originalInclusion m k F) φ = 0 :=
    (sourceGeneric_original_eq_direct m k F φ).trans hτ.1
  exact exists_sourceTraceRepresentative_modification_of_commuting
    (π := id) isAnalyticModification_identity
    (originalCarrierHomeomorph_isAnalyticModification m k F)
    omegaAmbient F.omega omegaDirect (originalTail m k F).omega
    (directCarrierInclusion_contMDiff m k F) (originalInclusion_contMDiff m k F)
    (fun y => (originalCarrierHomeomorph_val m k F y).symm) hτ hz

/-- The actual original direct-source P-equivalence is preserved by the
manufactured carrier modification, including true zero-dimensional targets. -/
theorem original_pequivalent_pullback_of_direct
    (omegaDirect : KahlerBackground m (F.flag (originalIndex m k)))
    {ψ τ : F.flag (originalIndex m k) → EReal}
    (hP : SourcePEquivalent (n := m) ψ τ) :
    SourcePEquivalent (n := m) (ψ ∘ originalCarrierHomeomorph m k F)
      (τ ∘ originalCarrierHomeomorph m k F) := by
  obtain ⟨σ,hψσ,hτσ,hposψ,hposτ,horder⟩ := hP.1
  have lift {v : F.flag (originalIndex m k) → EReal}
      (hv : IsThetaPshPotential σ.val v) :
      (ofFixedModel m (F.flag (originalIndex m k))).IsQPSH v := by
    refine ⟨nativeClosedFormToAtlas σ,?_⟩
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using hv
  exact (SGPT.PSH.ModificationOrders.sourcePEquivalent_modification_pullback_iff
    omegaDirect (originalTail m k F).omega
    (originalCarrierHomeomorph_isAnalyticModification m k F) (lift hψσ) (lift hτσ)).mp hP
end Direct
end SGPT.Okounkov.SourceMultiSlice
