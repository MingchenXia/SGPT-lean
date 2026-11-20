import SGPT.PSH.SourceSubgeodesic
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointQuasiEverywhere

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal original left endpoint limsup on the actual one-sided
filter, retaining every extended-real pole. It is an actual limit below. -/
def sourceSubgeodesicLeftLimit (curve : ℝ → M → EReal) (x : M) : EReal :=
  limsup (fun t ↦ curve t x) (𝓝[>] (0 : ℝ))

/-- The literal original right endpoint limsup, without silently replacing
the original filter by a time-reversed selector. -/
def sourceSubgeodesicRightLimit (curve : ℝ → M → EReal) (x : M) : EReal :=
  limsup (fun t ↦ curve t x) (𝓝[<] (1 : ℝ))

omit [TopologicalSpace M] in
/-- The actual native left limit has exactly the literal original formula. -/
theorem sourceSubgeodesicLeftLimit_eq_native (curve : ℝ → M → EReal) :
    sourceSubgeodesicLeftLimit curve = SubgeodesicEndpointLimits.leftLimit curve := rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : KahlerBackground n M}
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}

/-- The genuine existing actual right limit identifies its time-reversed
native definition with the literal original right limsup. -/
theorem sourceSubgeodesicRightLimit_eq_native
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    sourceSubgeodesicRightLimit curve = SubgeodesicEndpointLimits.rightLimit curve := by
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h
  funext x
  exact (SubgeodesicEndpointLimits.tendsto_rightLimit hn.interior x).limsup_eq

/-- An ACTUAL one-sided limit at every original point, including bottom
vertical traces; no pointwise endpoint equality is assumed. -/
theorem tendsto_sourceSubgeodesicLeftLimit
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (x : M) :
    Tendsto (fun t ↦ curve t x) (𝓝[>] (0 : ℝ))
      (𝓝 (sourceSubgeodesicLeftLimit curve x)) := by
  rw [sourceSubgeodesicLeftLimit_eq_native]
  exact SubgeodesicEndpointLimits.tendsto_leftLimit
    ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h).interior x

/-- An ACTUAL left-sided limit at one, with the literal original filter. -/
theorem tendsto_sourceSubgeodesicRightLimit
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (x : M) :
    Tendsto (fun t ↦ curve t x) (𝓝[<] (1 : ℝ))
      (𝓝 (sourceSubgeodesicRightLimit curve x)) := by
  rw [sourceSubgeodesicRightLimit_eq_native h]
  exact SubgeodesicEndpointLimits.tendsto_rightLimit
    ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h).interior x

/-- The literal left limit is below its assigned endpoint EVERYWHERE,
with the pole branch retained before any finite real arithmetic. -/
theorem sourceSubgeodesicLeftLimit_le
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    sourceSubgeodesicLeftLimit curve ≤ u₀ := by
  rw [sourceSubgeodesicLeftLimit_eq_native]
  exact SubgeodesicEndpointLimits.leftLimit_le
    ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h)

/-- The literal right limit is below its assigned endpoint EVERYWHERE. -/
theorem sourceSubgeodesicRightLimit_le
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    sourceSubgeodesicRightLimit curve ≤ u₁ := by
  rw [sourceSubgeodesicRightLimit_eq_native h]
  exact SubgeodesicEndpointLimits.rightLimit_le
    ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h)

variable [ConnectedSpace M]

/-- Actual ORIGINAL neighborhood PSH pole witnesses for the left failure
set, through the already accepted full source/native QE dictionary. -/
theorem sourceSubgeodesicLeftLimit_quasiEverywhere
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    SourceQuasiEverywhere (n := n) (fun x ↦ sourceSubgeodesicLeftLimit curve x = u₀ x) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  rw [sourceSubgeodesicLeftLimit_eq_native]
  exact SubgeodesicEndpointQuasiEverywhere.leftLimit_quasiEverywhereEq omega
    (atlasClosedFormToNative θ) ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h)

/-- Actual ORIGINAL neighborhood PSH pole witnesses for the right failure
set; no arbitrary-null-to-pluripolar inference is used. -/
theorem sourceSubgeodesicRightLimit_quasiEverywhere
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    SourceQuasiEverywhere (n := n) (fun x ↦ sourceSubgeodesicRightLimit curve x = u₁ x) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  rw [sourceSubgeodesicRightLimit_eq_native h]
  exact SubgeodesicEndpointQuasiEverywhere.rightLimit_quasiEverywhereEq omega
    (atlasClosedFormToNative θ) ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h)

/-- WHOLE original cor:subgeodboundary: both actual EVERY-point limits,
both everywhere inequalities, and both genuine ORIGINAL QE equalities. -/
theorem source_subgeodesic_endpoints_whole
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    (∀ x, Tendsto (fun t ↦ curve t x) (𝓝[>] (0 : ℝ))
      (𝓝 (sourceSubgeodesicLeftLimit curve x))) ∧
    (∀ x, Tendsto (fun t ↦ curve t x) (𝓝[<] (1 : ℝ))
      (𝓝 (sourceSubgeodesicRightLimit curve x))) ∧
    sourceSubgeodesicLeftLimit curve ≤ u₀ ∧
    sourceSubgeodesicRightLimit curve ≤ u₁ ∧
    SourceQuasiEverywhere (n := n) (fun x ↦ sourceSubgeodesicLeftLimit curve x = u₀ x) ∧
    SourceQuasiEverywhere (n := n) (fun x ↦ sourceSubgeodesicRightLimit curve x = u₁ x) :=
  ⟨tendsto_sourceSubgeodesicLeftLimit h, tendsto_sourceSubgeodesicRightLimit h,
    sourceSubgeodesicLeftLimit_le h, sourceSubgeodesicRightLimit_le h,
    sourceSubgeodesicLeftLimit_quasiEverywhere h, sourceSubgeodesicRightLimit_quasiEverywhere h⟩

end SGPT.PSH.VariableComplexAtlas
