import SGPT.Projective.OriginalModificationPullbackValues

/-! Valuation-free genuine native-modification multiplier dimensions and their actual limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalModification
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Okounkov SGPT.LineBundle SGPT.IGood.DXMain SGPT.AlmostSemigroup
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
local instance : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z] {π : Z → SchemeComplexPoint f}
  (hπ : IsAnalyticModification (n := m+1) π)
  {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)

omit [IsIntegral X] in
/-- Actual multiplier descent gives the original whole-subspace dimension bound in every degree. -/
theorem pullbackMultiplierH0_le_multiplierH0 (k : ℕ) :
    OkoTower.pullbackMultiplierH0 a H hπ hφ k ≤
      multiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic L k := by
  let : FiniteDimensional ℂ (SectionSpace f L k) := SectionSpace.finiteDimensional f E a k
  apply Submodule.finrank_mono
  intro s hs
  exact OkoTower.isMultiplierSection_of_isPullbackMultiplierSection f E hπ
    hφ.1.quasiPlurisubharmonic hs

/-- Actual native-modification Riemann--Roch and actual descent give the SAME original scalar limit. -/
theorem tendsto_normalized_pullbackMultiplierH0
    [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
    [Nonempty (SchemeComplexPoint f)]
    (Y : Fin (m+1+1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (omegaZ : KahlerBackground (m+1) Z) :
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ (m+1) *
      (OkoTower.pullbackMultiplierH0 a H hπ hφ k : ℝ)) atTop
      (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY) (H.curvature a) φ))) := by
  let V := volume.real (PartialBody.generalPartialBody
    (schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY) (H.curvature a) φ)
  obtain ⟨C₀, _, hC⟩ := AlgPOB.exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsubX, _⟩ := hC C₀ le_rfl φ hφ
  have hsub := (OkoTower.pullbackMultiplierSectionSet_subset f E Y hY a hπ
    hφ.1.quasiPlurisubharmonic).trans hsubX
  let S := OkoTower.pullbackConeSubset f E Y hY a π φ hsub
  have hcard (k : ℕ) : S.normalizedCardinality k =
      (k : ℝ)⁻¹ ^ (m+1) * (OkoTower.pullbackMultiplierH0 a H hπ hφ k : ℝ) := by
    have h := Nat.card_eq_card_finite_toFinset (S.finite_slice k)
    rw [ConeSubset.normalizedCardinality, OkoTower.pullbackMultiplierH0,
      ← OkoTower.card_slice_pullbackMultiplierSectionSet f E Y hY a hπ.1.continuous
        (OkoTower.quasiPsh_comp a H hπ hφ) k]
    rw [show (S.slices k).card = Nat.card
      (slice (OkoTower.pullbackMultiplierSectionSet f E Y hY a π φ) (k : ℤ)) from h.symm]
  have hlow (ε : ℝ) (hε : 0 < ε) :=
    OkoTower.pullbackConeSubset_lower f E Y hY a H hπ omegaZ hφ hsub hε
  have hup := ValGen.tendsto_normalized_multiplierH0 f E Y hY a H hφ
  apply tendsto_order.mpr
  constructor
  · intro z hz
    change z < V at hz
    filter_upwards [hlow ((V - z) / 2) (by linarith)] with k hk
    rw [hcard] at hk
    change V - (V - z) / 2 ≤ (k : ℝ)⁻¹ ^ (m+1) *
      (OkoTower.pullbackMultiplierH0 a H hπ hφ k : ℝ) at hk
    linarith
  · intro z hz
    filter_upwards [(tendsto_order.mp hup).2 z hz] with k hk
    have hdim : (OkoTower.pullbackMultiplierH0 a H hπ hφ k : ℝ) ≤
        (multiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic L k : ℝ) := by
      exact_mod_cast pullbackMultiplierH0_le_multiplierH0 f E a H hπ hφ k
    exact (mul_le_mul_of_nonneg_left hdim (by positivity)).trans_lt hk

end SGPT.Okounkov.OriginalModification
