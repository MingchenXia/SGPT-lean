import SGPT.NAPotential.DHSourceBounds

/-! # Continuity from the order-theoretic source limits

The source assumption that the
positive limit is a greatest lower bound or least upper bound is expressed
using the actual NA order and quantifies over every NA potential in the
original background. A genuine common order bound yields the cutoff bound;
the existing source operations' universal properties then identify them with
the given limit. No operation equality or cutoff bound is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DH
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The original order-theoretic greatest lower bound is the actual
decreasing-infimum operation. -/
theorem toNA_eq_decreasingInf_of_greatest_lower_bound (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ)) :
    sourcePositiveTestCurveToNA Γ = SourceNAPotential.decreasingInf omega
      (fun i => sourcePositiveTestCurveToNA (Γs i)) ha
      (cutoff_bddBelow_of_positive_lower_bound omega Γs Γ hbound) := by
  apply SourceNAPOrder.antisymm
  · exact SourceNAPotential.le_decreasingInf omega (fun i => sourcePositiveTestCurveToNA (Γs i))
      ha (cutoff_bddBelow_of_positive_lower_bound omega Γs Γ hbound)
      (sourcePositiveTestCurveToNA Γ) hbound
  · apply hgreatest
    intro i
    exact SourceNAPotential.decreasingInf_le omega (fun i => sourcePositiveTestCurveToNA (Γs i))
      ha (cutoff_bddBelow_of_positive_lower_bound omega Γs Γ hbound) i

/-- The original order-theoretic least upper bound is the actual usc-supremum
operation. -/
theorem toNA_eq_uscSup_of_least_upper_bound (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    sourcePositiveTestCurveToNA Γ = SourceNAPotential.uscSup omega
      (fun i => sourcePositiveTestCurveToNA (Γs i))
      (cutoff_bddAbove_of_positive_upper_bound omega Γs Γ hbound) := by
  apply SourceNAPOrder.antisymm
  · apply hleast
    intro i
    exact SourceNAPotential.le_uscSup omega (fun i => sourcePositiveTestCurveToNA (Γs i))
      (cutoff_bddAbove_of_positive_upper_bound omega Γs Γ hbound) i
  · exact SourceNAPotential.uscSup_le omega (fun i => sourcePositiveTestCurveToNA (Γs i))
      (cutoff_bddAbove_of_positive_upper_bound omega Γs Γ hbound)
      (sourcePositiveTestCurveToNA Γ) hbound

/-- Intrinsic DH continuity from a genuine order-theoretic decreasing
infimum and the source volume convergence. -/
theorem naIntrinsicDuistermaatHeckman_tendsto_of_order_infimum
    (omega : KahlerBackground n M) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naIntrinsicFiniteDuistermaatHeckman omega (Γs i)) atTop
      (𝓝 (naIntrinsicFiniteDuistermaatHeckman omega Γ)) :=
  naIntrinsicDuistermaatHeckman_tendsto_of_decreasingInf omega Γs Γ ha
    (cutoff_bddBelow_of_positive_lower_bound omega Γs Γ hbound)
    (toNA_eq_decreasingInf_of_greatest_lower_bound omega Γs Γ ha hbound hgreatest) hvol

/-- Intrinsic DH continuity from a genuine order-theoretic increasing
usc supremum. -/
theorem naIntrinsicDuistermaatHeckman_tendsto_of_order_supremum
    (omega : KahlerBackground n M) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naIntrinsicFiniteDuistermaatHeckman omega (Γs i)) atTop
      (𝓝 (naIntrinsicFiniteDuistermaatHeckman omega Γ)) :=
  naIntrinsicDuistermaatHeckman_tendsto_of_uscSup omega Γs Γ hmono
    (cutoff_bddAbove_of_positive_upper_bound omega Γs Γ hbound)
    (toNA_eq_uscSup_of_least_upper_bound omega Γs Γ hbound hleast)

section Flag

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}
  (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))

/-- The same order-theoretic decreasing statement for the actual source flag
measure in positive dimension. -/
theorem naDuistermaatHeckman_tendsto_of_order_infimum
    (omega : KahlerBackground (m + 1) F.carrier) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig Γ)) :=
  naDuistermaatHeckman_tendsto_of_decreasingInf hbig omega Γs Γ ha
    (cutoff_bddBelow_of_positive_lower_bound omega Γs Γ hbound)
    (toNA_eq_decreasingInf_of_greatest_lower_bound omega Γs Γ ha hbound hgreatest) hvol

/-- The same order-theoretic increasing statement for the actual source flag
measure in positive dimension. -/
theorem naDuistermaatHeckman_tendsto_of_order_supremum
    (omega : KahlerBackground (m + 1) F.carrier) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig Γ)) :=
  naDuistermaatHeckman_tendsto_of_uscSup hbig omega Γs Γ hmono
    (cutoff_bddAbove_of_positive_upper_bound omega Γs Γ hbound)
    (toNA_eq_uscSup_of_least_upper_bound omega Γs Γ hbound hleast)

end Flag
end SGPT.NAPotential.DH
