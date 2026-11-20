import SGPT.PSH.SourcePerronGeodesic
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicAdmissible

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The entire original arbitrary-family supremum proposition: arbitrary
nonempty indexing, separately uniformly bounded-above endpoint families,
the actual spatial USC supremum, full original joint product theta-PSH,
and both original GLOBAL Kähler-volume L1 endpoint limits. -/
theorem sourceSubgeodesic_uscSup {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, SourceSubgeodesicFrom omega θ (curve i) (u₀ i) (u₁ i))
    (h₀ : ∃ C : ℝ, ∀ i x, u₀ i x ≤ (C : EReal))
    (h₁ : ∃ C : ℝ, ∀ i x, u₁ i x ≤ (C : EReal)) :
    SourceSubgeodesicFrom omega θ (fun t ↦ uscSup (fun i ↦ curve i t))
      (uscSup u₀) (uscSup u₁) := by
  apply (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
  exact SubgeodesicPerronStability.isSubgeodesicFrom_uscRegularization_iSup_of_bounded_endpoints
    omega (atlasClosedFormToNative θ)
    (fun i ↦ (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp (h i)) h₀ h₁

/-- An actual original joining subgeodesic produces endpoint recovery for
the ENTIRE original Perron family. No relative full-mass assumption or
Perron output certificate is supplied; both actual original global L1
limits and the whole actual product PSH condition are conclusions. -/
theorem SourceSubgeodesicFrom.sourcePerron_isSubgeodesicFrom
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    SourceSubgeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ := by
  apply (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
  have heq : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun t ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ t
  rw [heq]
  exact FiniteGeodesicAdmissible.isSubgeodesicFrom_finiteGeodesic
    omega (atlasClosedFormToNative θ)
    ((sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp h)

/-- The whole original `lma:geodsubgeod`, retaining exactly its existence
hypothesis and the original all-competitor envelope with the same endpoints.
The genuine endpoint theta-PSH hypotheses already follow from the witness. -/
theorem sourcePerron_isSubgeodesicFrom_of_exists (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (h : ∃ curve : ℝ → M → EReal, SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    SourceSubgeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ := by
  obtain ⟨curve, hcurve⟩ := h
  exact hcurve.sourcePerron_isSubgeodesicFrom

end SGPT.PSH.VariableComplexAtlas
