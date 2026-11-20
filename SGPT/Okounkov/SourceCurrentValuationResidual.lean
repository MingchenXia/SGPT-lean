import SGPT.Okounkov.SourceSliceAllDimensions
import SGPT.Okounkov.TranscendentalCoreValuationBounded

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceCurrentValuation
open Set Filter
open scoped Topology Manifold NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open SingularGlobalPOrder
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody

/-- Removing the actual generic divisor coefficient preserves the actual
Kähler margin. All residual positivity, generic zero and recomposition are
produced from the original current, not assumed. -/
theorem exists_kahler_normalized_first_residual {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.tail.carrier → F.carrier) φ).toNNReal
    ∃ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
      TranscendentalMain.IsFirstDivisorUnitMetric F E ∧
      IsKahlerCurrentPotential (θ - (c : ℝ) • E.curvature)
        (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ)) ∧
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : F.tail.carrier → F.carrier)
        (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ)) = 0 ∧
      (fun x => extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ) x +
        ((c : ℝ) : EReal) * E.weight x) = φ := by
  let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.tail.carrier → F.carrier) φ).toNNReal
  have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
  obtain ⟨κ, hκ⟩ := hK
  obtain ⟨D, hDI, E, hEW, hmetric, hv, hz⟩ :=
    exists_normalized_smooth_divisor_residual_generic_zero hκ F.firstDivisor
  have hKv : IsKahlerCurrentPotential (θ - (c : ℝ) • E.curvature)
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ)) := by
    refine ⟨κ, ?_⟩
    have heq : θ - (c : ℝ) • E.curvature - κ.form =
        (θ - κ.form) - (c : ℝ) • E.curvature := by abel
    rw [heq]
    exact hv
  have hv' := isThetaPshPotential_of_isKahlerCurrentPotential hKv
  exact ⟨E, ⟨D, hDI, hEW, hmetric⟩, hKv, hz,
    smooth_divisor_residual_recompose hφ F.firstDivisor E hEW c hv'⟩

/-- Every original source trace and every genuinely P-equivalent
restricted-class reader give the exact tail of the original valuation. -/
theorem flagValuation_eq_cons_of_residual_sourceTrace {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E)
    {τ : F.tail.carrier → EReal}
    (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.tail.carrier → F.carrier) φ).toNNReal φ)) τ)
    {β : ClosedRealOneOneForm m F.tail.carrier} {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential β.val ψ)
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m) ψ τ) :
    flagValuation F φ = Fin.cons
      ((sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.tail.carrier → F.carrier) φ).toNNReal : ℝ)
      (flagValuation F.tail ψ) := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  obtain ⟨D, hDI, hEW, hmetric⟩ := hE
  have hstep : OriginalFlagStep F φ τ := ⟨θ, hφ, D, hDI, E, hEW, hmetric, hτ⟩
  have hτ' := hτ
  unfold IsNaturalSourceTraceRepresentative at hτ'
  obtain ⟨_hg, _θ, _ε, _seq, _hqea, γ, _hadm, hγτ, _hterms, _hlim⟩ := hτ'
  have htail := potentialFlagValuation_tail_of_originalFlagStep F hφ hstep hγτ
  have hI := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP
  have heq := flagValuation_eq_of_iEquivalent (F := F.tail) hψ hγτ hI
  have htail' : (fun i => flagValuation F φ i.succ) = flagValuation F.tail ψ := by
    rw [heq, flagValuation_eq (F := F.tail) hγτ, ← htail, flagValuation_eq (F := F) hφ]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero, flagValuation_eq hφ]
    change ((potentialFlagValuation F hφ 0 : ℝ≥0) : ℝ) = _
    rw [(potentialFlagValuation_spec F hφ).1]
  · rw [Fin.cons_succ]
    exact congrFun htail' j

end SGPT.Okounkov.SourceCurrentValuation
