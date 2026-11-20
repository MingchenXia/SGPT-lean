import SGPT.Okounkov.FlagSourceBodyGeometry
import SGPT.Okounkov.SourceMultiSliceWholeOriginal
import SGPT.Trace.ModificationTrace
import SGPT.Trace.TraceMass
import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceModificationOrders
import SGPT.Foundations.Analysis.Pending.FormPullbackCompMixed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.SourceMultiSlice
open scoped Topology Manifold ContDiff

section Slice
variable (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) (W : OriginalFlagGeometry.{u} m)
local instance sliceAmbientMeasurable : MeasurableSpace F.carrier := borel _
local instance sliceAmbientBorel : BorelSpace F.carrier := ⟨rfl⟩
local instance sliceTargetMeasurable : MeasurableSpace W.carrier := borel _
local instance sliceTargetBorel : BorelSpace W.carrier := ⟨rfl⟩
local instance sliceTailMeasurable : MeasurableSpace (originalTail m k F).carrier := borel _
local instance sliceTailBorel : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩

/-- ACTUAL original normalized-trace body slice under a genuine realization
of the SAME original tail. The trace representative, all P-equivalences,
restricted-class PSH and body transport are produced internally. Inputs are
actual geometry, original theta-PSH and its original defined trace domain;
there is no body/matrix/trace-presentation or target mass certificate. -/
theorem normalizedTrace_zeroSlice_of_originalTail_biholomorphic
    (e : (originalTail m k F).carrier ≃ₜ W.carrier)
    (he : ∀ i, e '' (originalTail m k F).flag i = W.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e.symm)
    {ι : W.carrier → F.carrier}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + k)) ∞ ι)
    (hcomm : ∀ y, ι (e y) = originalInclusion m k F y)
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong F.omega W.omega hι θ φ) :
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody W (ClosedRealOneOneForm.pullback hι θ)
        ⟨SGPT.Trace.sourceTraceEnvelope F.omega W.omega hι θ φ hdefined,
          SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope F.omega W.omega hι θ φ hdefined⟩ := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ψ := SGPT.Trace.sourceTraceEnvelope F.omega W.omega hι θ φ hdefined
  let τ := Classical.choose hdefined
  obtain ⟨htrace, hτ, hposτ⟩ := Classical.choose_spec hdefined
  have hψ : IsThetaPshPotential η.val ψ :=
    SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope F.omega W.omega hι θ φ hdefined
  have hmod := (isFlagLifting_of_biholomorphic e he hf hg).1
  have hψpull : IsThetaPshPotential (ClosedRealOneOneForm.pullback hf η).val (ψ ∘ e) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hmod η hψ
  have hfun : ι ∘ e = originalInclusion m k F := funext hcomm
  have hgeo0 := (FormPullbackCompMixed.pullback_comp_geometricallyEq hι hf θ.val).symm
  rw [FormPullbackCompMixed.pullback_congr (hι.comp hf) (originalInclusion_contMDiff m k F) hfun θ.val] at hgeo0
  have hgeo : (ClosedRealOneOneForm.pullback hf η).val.GeometricallyEq
      (originalRestriction m k F θ).val :=
    hgeo0.trans (originalRestriction_geometricallyEq m k F θ).symm
  have hψtail : IsThetaPshPotential (originalRestriction m k F θ).val (ψ ∘ e) :=
    (hgeo.thetaPshPotential_iff _).mp hψpull
  have hP : SourcePEquivalent (n := m) ψ τ :=
    (SGPT.PSH.GlobalPComparison.sourcePEquivalent_singularityEnvelope W.omega η hτ hposτ).symm
  have hPtail := (SGPT.PSH.ModificationOrders.sourcePEquivalent_modification_pullback_iff
    W.omega (originalTail m k F).omega hmod
    (sourceQPSH_of_native_thetaPsh W hψ) (sourceQPSH_of_native_thetaPsh W hτ)).mp hP
  have hT := SGPT.Trace.sourceTrace_modification_of_commuting (by omega : m ≤ m + k)
    (show IsAnalyticModification (n := m + k) (id : F.carrier → F.carrier) from
      isAnalyticModification_identity)
    hmod F.omega F.omega W.omega (originalTail m k F).omega hι (originalInclusion_contMDiff m k F)
    (fun y => (hcomm y).symm) htrace
  obtain ⟨κ, hτtail⟩ := hT.2.1
  have hslice : zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ) ⟨ψ ∘ e,hψtail⟩ := by
    by_cases hn : 0 < m + k
    · exact original_zeroSlice_eq_of_defined_sourceTrace m k F hn hφ
        (by simpa only [Function.comp_id] using hT.1)
        (by simpa only [Function.comp_id] using hτtail) hψtail hPtail
    · have hm : m = 0 := by omega
      have hk : k = 0 := by omega
      subst m
      subst k
      rw [sourceGeneralBody_zero_eq_univ F hφ,
        sourceGeneralBody_zero_eq_univ (originalTail 0 0 F) hψtail]
      simp only [zeroSlice, Set.preimage_univ]
  have hbodyGeo := sourceGeneralBody_geometricallyEq (originalTail m k F) hgeo hψtail
  have hbodyMap := sourceGeneralBody_biholomorphic e he hf hg hψ
  exact hslice.trans (hbodyGeo.symm.trans hbodyMap)

end Slice
end SGPT.Okounkov.ToricTransport
