import SGPT.Okounkov.SourceMultiSliceOriginalKahler

/-! Entire original rmk:slicepob: every k=0..n, n>0, general original
positive current and the source's exact defined-trace condition. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Okounkov.PartialBody

/-- Same actual source body under a proved equality of its stored original
forms. Potential values are identical and PSH proof fields are irrelevant. -/
theorem sourceBody_congr_form {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ η : ClosedRealOneOneForm n F.carrier} (heq : θ = η)
    {φ : F.carrier → EReal} (hθ : IsThetaPshPotential θ.val φ)
    (hη : IsThetaPshPotential η.val φ) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hθ⟩ =
      SourceTestCurveAllDimensions.generalBody F η ⟨φ,hη⟩ := by
  subst η
  rfl

/-- WHOLE original higher-codimension source slice, all n=m+k>0 and every
k=0..n. The actual given original current, flag, target inclusion, restricted
class and prescribed trace representative are unchanged throughout.
No approximation, model, resolution, mass or convergence certificate is input. -/
theorem original_zeroSlice_eq_of_defined_sourceTrace (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (hn : 0 < m + k)
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hz : sourceGenericLelongNumber (n := m + k) (originalInclusion m k F) φ = 0)
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
    zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩) =
      SourceTestCurveAllDimensions.generalBody (originalTail m k F)
        (originalRestriction m k F θ) ⟨ψ,hψ⟩ := by
  let _ : MeasurableSpace (originalTail m k F).carrier := borel _
  have _ : BorelSpace (originalTail m k F).carrier := ⟨rfl⟩
  have hτzero : IsSourceTraceRepresentativeAlong κSource (originalTail m k F).omega
      (originalInclusion_contMDiff m k F) φ τ := ⟨hz,hτ.2⟩
  rw [sourceBody_eq_iInter_general_add_kahler F hφ F.omega, zeroSlice_iInter,
    sourceBody_eq_iInter_general_add_kahler (originalTail m k F) hψ
      (originalKahler m k F F.omega)]
  congr 1
  funext j
  have he : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  have hK := isKahlerCurrentPotential_add_smul hφ F.omega he
  have hform : originalRestriction m k F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) =
      originalRestriction m k F θ + ((j : ℝ) + 1)⁻¹ • (originalKahler m k F F.omega).form := by
    rw [originalRestriction_add_smul, originalKahler_form]
  have hψε : IsThetaPshPotential
      (originalRestriction m k F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form)).val ψ := by
    rw [hform]
    exact isThetaPshPotential_of_isKahlerCurrentPotential
      (isKahlerCurrentPotential_add_smul hψ (originalKahler m k F F.omega) he)
  have h := original_zeroSlice_kahler_of_defined_sourceTrace m k F hn hK hτzero hψε hP
  exact h.trans (sourceBody_congr_form (originalTail m k F) hform hψε
    (isThetaPshPotential_of_isKahlerCurrentPotential
      (isKahlerCurrentPotential_add_smul hψ (originalKahler m k F F.omega) he)))
end SGPT.Okounkov.SourceMultiSlice
