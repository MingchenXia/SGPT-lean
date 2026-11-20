import SGPT.PSH.SourceGlobalAnalyticType
import SGPT.PSH.LogResolution

/-! # Native log resolution from the original local analytic input

The global coherent ideal is now produced internally from the original local
rational bounded analytic singularities. Existing Hironaka and log-resolution
proofs are reused unchanged. Arbitrary fixed native dimensions, including0,
remain covered; mixed-dimensional component geometry remains separate.
Blueprint NATIVE-LOG/blueprint.tex preceded this wrapper.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open VariableComplexAtlas

universe u

/-- Original local analytic data on a compact native complex manifold
produce ONE actual native coherent ideal and ONE positive rational type. -/
theorem exists_nativeCoherentRationalAnalyticType_of_compact
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {φ : X → EReal} (ha : (ofFixedModel n X).HasRationalAnalyticType φ) :
    ∃ (c : ℚ) (I : GermIdeal n X),
      (ofFixedModel n X).HasCoherentRationalAnalyticType φ c I := by
  obtain ⟨c, I, ht⟩ := GlobalAnalyticType.exists_atlasCoherentRationalAnalyticType_of_compact ha
  exact ⟨c, I.toNative, hasAtlasCoherentRationalAnalyticType_iff_native.mp ht⟩

/-- The native source log-resolution conclusion from the ACTUAL original
local analytic hypothesis, with no supplied global ideal or type certificate.
No positive dimension, Kähler, connectedness, mass or smooth neat remainder
assumption is added. Mixed-dimensional component geometry is separate. -/
theorem exists_isLogResolution_of_hasRationalAnalyticType
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsQPSH φ)
    (ha : (ofFixedModel n X).HasRationalAnalyticType φ) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X), CompactSpace Y ∧ IsLogResolution n φ π := by
  obtain ⟨c, I, ht⟩ := exists_nativeCoherentRationalAnalyticType_of_compact ha
  exact exists_isLogResolution_of_hasCoherentRationalAnalyticType hφ ht

end SGPT.PSH
