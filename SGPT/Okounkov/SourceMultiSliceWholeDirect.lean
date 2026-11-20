import SGPT.Okounkov.SourceMultiSliceDirectTrace
import SGPT.Okounkov.SourceMultiSliceWholeOriginal
import SGPT.Okounkov.SourceMultiSliceRemainingFlag

/-! Entire original rmk:slicepob with a DIRECT ORIGINAL Y_k source trace
and DIRECT ORIGINAL restricted-class representative, internally transported
to the actual remaining original flag. No transport certificate is supplied. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

section Direct
variable (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k))
local instance : ChartedSpace (ComplexModel m) (F.flag (originalIndex m k)) :=
  directCarrierCharts m k F
local instance : IsComplexManifold m (F.flag (originalIndex m k)) := directCarrierComplex m k F
local instance : CompactSpace (F.flag (originalIndex m k)) :=
  isCompact_iff_compactSpace.mp (directCarrier_isClosedConnectedSubmanifold m k F).1.isCompact
local instance : ConnectedSpace (F.flag (originalIndex m k)) :=
  isConnected_iff_connectedSpace.mp (directCarrier_isClosedConnectedSubmanifold m k F).2.1
local instance : MeasurableSpace (F.flag (originalIndex m k)) := borel _
local instance : BorelSpace (F.flag (originalIndex m k)) := ⟨rfl⟩
local instance : MeasurableSpace (originalTail m k F).carrier := borel _
local instance : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
local instance : MeasurableSpace F.carrier := borel _
local instance : BorelSpace F.carrier := ⟨rfl⟩

/-- Original DIRECT trace/current inputs imply the whole all-k source slice.
The actual canonical biholomorphism, trace and P-equivalence pullbacks, and
restricted-class PSH witness are all constructed internally. -/
theorem original_zeroSlice_eq_of_direct_defined_sourceTrace
    (hn : 0 < m + k)
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + k)
      (Subtype.val : F.flag (originalIndex m k) → F.carrier) φ = 0)
    {omegaAmbient : KahlerBackground (m + k) F.carrier}
    {omegaDirect : KahlerBackground m (F.flag (originalIndex m k))}
    {τ ψ : F.flag (originalIndex m k) → EReal}
    (hτ : IsSourceTraceRepresentativeAlong omegaAmbient omegaDirect
      (directCarrierInclusion_contMDiff m k F) φ τ)
    (hψ : IsThetaPshPotential (directRestriction m k F θ).val ψ)
    (hP : SourcePEquivalent (n := m) ψ τ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ)
        ⟨ψ ∘ originalCarrierHomeomorph m k F, original_psh_pullback_of_direct m k F hψ⟩ := by
  obtain ⟨κ,hT⟩ := exists_original_trace_of_direct_sourceTrace m k F omegaAmbient omegaDirect hτ
  have hzN := (sourceGeneric_original_eq_direct m k F φ).trans hz
  have hPN := original_pequivalent_pullback_of_direct m k F omegaDirect hP
  exact original_zeroSlice_eq_of_defined_sourceTrace m k F hn hφ hzN hT
    (original_psh_pullback_of_direct m k F hψ) hPN

/-- WHOLE original rmk:slicepob with exactly its natural DIRECT Y_k trace,
the SAME original current/flag/class and every actual DIRECT representative.
All n=m+k>0, k=0..n, and true zero-dimensional target are covered. -/
theorem original_zeroSlice_eq_of_natural_direct_sourceTrace
    (hn : 0 < m + k)
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + k)
      (Subtype.val : F.flag (originalIndex m k) → F.carrier) φ = 0)
    {τ ψ : F.flag (originalIndex m k) → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega
      (directCarrier_isClosedConnectedSubmanifold m k F) φ τ)
    (hψ : IsThetaPshPotential (directRestriction m k F θ).val ψ)
    (hP : SourcePEquivalent (n := m) ψ τ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ)
        ⟨ψ ∘ originalCarrierHomeomorph m k F, original_psh_pullback_of_direct m k F hψ⟩ := by
  have hT : IsSourceTraceRepresentativeAlong F.omega (directCarrierKahler m k F F.omega)
      (directCarrierInclusion_contMDiff m k F) φ τ := hτ
  exact original_zeroSlice_eq_of_direct_defined_sourceTrace m k F hn hφ hz hT hψ hP
/-- The same actual source formula also includes ambient dimension zero:
its genuine source bodies on both sides are the previously proved true zero
construction, rather than an assumed singleton replacement. -/
theorem original_zeroSlice_eq_of_natural_direct_sourceTrace_all_dimensions
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + k)
      (Subtype.val : F.flag (originalIndex m k) → F.carrier) φ = 0)
    {τ ψ : F.flag (originalIndex m k) → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega
      (directCarrier_isClosedConnectedSubmanifold m k F) φ τ)
    (hψ : IsThetaPshPotential (directRestriction m k F θ).val ψ)
    (hP : SourcePEquivalent (n := m) ψ τ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ)
        ⟨ψ ∘ originalCarrierHomeomorph m k F, original_psh_pullback_of_direct m k F hψ⟩ := by
  by_cases hn : 0 < m + k
  · exact original_zeroSlice_eq_of_natural_direct_sourceTrace m k F hn hφ hz hτ hψ hP
  · have hm : m = 0 := by omega
    have hk : k = 0 := by omega
    subst m
    subst k
    simp only [sourceBody_zero_eq_univ,zeroSlice,Set.preimage_univ]
end Direct
end SGPT.Okounkov.SourceMultiSlice
