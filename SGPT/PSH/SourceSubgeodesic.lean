import SGPT.PSH.SourceRayL1
import SGPT.PSH.SourceRayProduct
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicAffineTranslation

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The entire original normalized definition: actual source endpoints and
interior slices, full actual product theta-PSH, and both one-sided GLOBAL L1
limits for the genuine Kähler volume. No off-interval condition is imposed. -/
def SourceSubgeodesicFrom (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH θ u₀ ∧
    (ofFixedModel n M).IsThetaPSH θ u₁ ∧
      SourceSubgeodesicInterior θ curve ∧
        Tendsto (fun t ↦ sourceGlobalL1Distance omega (curve t) u₀) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
          Tendsto (fun t ↦ sourceGlobalL1Distance omega (curve t) u₁) (𝓝[<] (1 : ℝ)) (𝓝 0)

/-- Exact original/native dictionary with the same whole original background,
functions, endpoints, strip and actual global L1 topology. -/
theorem sourceSubgeodesicFrom_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) :
    SourceSubgeodesicFrom omega θ curve u₀ u₁ ↔
      IsSubgeodesicFrom (atlasClosedFormToNative θ).val curve u₀ u₁ := by
  constructor
  · rintro ⟨h₀, h₁, hi, hleft, hright⟩
    exact ⟨(isThetaPSH_iff_nativeThetaPotential θ u₀).mp h₀,
      (isThetaPSH_iff_nativeThetaPotential θ u₁).mp h₁,
      (sourceInterior_iff_native θ curve).mp hi,
      (sourceRayL1_iff_global omega hi.1 h₀ sourceRay_endpoint_filters.1).mpr hleft,
      (sourceRayL1_iff_global omega hi.1 h₁ sourceRay_endpoint_filters.2).mpr hright⟩
  · intro h
    have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mpr h.left_endpoint
    have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mpr h.right_endpoint
    have hi := (sourceInterior_iff_native θ curve).mpr h.interior
    exact ⟨h₀, h₁, hi,
      (sourceRayL1_iff_global omega hi.1 h₀ sourceRay_endpoint_filters.1).mp h.tendsto_left,
      (sourceRayL1_iff_global omega hi.1 h₁ sourceRay_endpoint_filters.2).mp h.tendsto_right⟩

/-- The original constant subgeodesic for every genuine theta-PSH potential,
including unbounded potentials with their literal original poles. -/
theorem sourceSubgeodesic_const (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceSubgeodesicFrom omega θ (fun _ : ℝ ↦ u) u u := by
  apply (sourceSubgeodesicFrom_iff_native omega θ _ u u).mpr
  exact isSubgeodesicFrom_const ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- The full general clause of the original affine example, for EVERY source
subgeodesic and both correctly shifted endpoints. -/
theorem SourceSubgeodesicFrom.affineTranslated {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (A B : ℝ) :
    SourceSubgeodesicFrom omega θ (affineTranslatedCurve curve A B)
      (fun x ↦ u₀ x + (B : EReal)) (fun x ↦ u₁ x + ((A + B : ℝ) : EReal)) := by
  apply (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
  exact ((sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h).affineTranslated A B

/-- The displayed original affine family, with arbitrary genuine base
potential and arbitrary real slope, as part of the entire affine example. -/
theorem sourceSubgeodesic_affine (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (C : ℝ) :
    SourceSubgeodesicFrom omega θ (fun t x ↦ u x + ((t * C : ℝ) : EReal))
      u (fun x ↦ u x + (C : EReal)) := by
  have h := (sourceSubgeodesic_const omega hu).affineTranslated C 0
  change SourceSubgeodesicFrom omega θ (fun t x ↦ u x + ((C * t + 0 : ℝ) : EReal))
    (fun x ↦ u x + ((0 : ℝ) : EReal)) (fun x ↦ u x + ((C + 0 : ℝ) : EReal)) at h
  simpa only [add_zero, EReal.coe_zero, mul_comm] using h

/-- The original general CLOSED-interval convention retains a≤b, including
the actual single-value family when a=b. -/
def SourceSubgeodesicClosedInterval (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (a b : ℝ)
    (curve : ℝ → M → EReal) : Prop :=
  a ≤ b ∧ SourceSubgeodesicFrom omega θ (fun s ↦ curve (s * b + (1 - s) * a))
    (curve a) (curve b)

/-- The printed closed degenerate convention is exactly the genuine
theta-PSH condition on its single original value. -/
theorem sourceSubgeodesicClosedInterval_self_iff (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (a : ℝ)
    (curve : ℝ → M → EReal) :
    SourceSubgeodesicClosedInterval omega θ a a curve ↔
      (ofFixedModel n M).IsThetaPSH θ (curve a) := by
  constructor
  · intro h
    exact h.2.1
  · intro hu
    refine ⟨le_rfl, ?_⟩
    have heq : (fun s : ℝ ↦ curve (s * a + (1 - s) * a)) = (fun _ : ℝ ↦ curve a) := by
      funext s
      congr 1
      ring
    rw [heq]
    exact sourceSubgeodesic_const omega hu

end SGPT.PSH.VariableComplexAtlas
