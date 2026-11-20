import SGPT.Checks.Comparison.TraceNativeDivisorReader

/-! Literal native prime composition by an ACTUAL analytic modification.
The SAME model/divisor is retained, and the ORIGINAL single-common-resolution
relation is respected. Blueprint: trace-resolution-divisor-transport.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff ENNReal

variable {k : ℕ} {V W : Type u} [TopologicalSpace V] [TopologicalSpace W]
  [ChartedSpace (ComplexModel k) V] [ChartedSpace (ComplexModel k) W]
  [IsComplexManifold k V] [IsComplexManifold k W]
  {π : W → V} (hπ : IsAnalyticModification (n := k) π)

/-- The literal composed original prime, on the SAME model and divisor. -/
def primePush (p : PrimePresentation k W) : PrimePresentation k V where
  model := p.model
  projection := π ∘ p.projection
  modification := AnalyticModificationComposition.isAnalyticModification_comp hπ p.modification
  divisor := p.divisor
  divisorDimension := p.divisorDimension
  smooth := p.smooth
  codimension_one := p.codimension_one

/-- Actual common geometry composes over the base, without altering its
strict transform or requiring an extra reader/equivalence certificate. -/
theorem primePush_commonResolution {p q : PrimePresentation k W}
    (h : commonResolutionRelation p q) :
    commonResolutionRelation (primePush hπ p) (primePush hπ q) := by
  obtain ⟨h⟩ := h
  refine ⟨⟨h.model,h.left,h.right,h.left_modification,h.right_modification,?_,h.strict_equal⟩⟩
  funext x
  exact congrArg π (congrFun h.over_base x)

/-- Literal unchanged source reader, including infinite values. -/
theorem presentationReader_primePush (φ : V → EReal) (p : PrimePresentation k W) :
    presentationReader φ (primePush hπ p) = presentationReader (φ ∘ π) p := rfl

variable [CompactSpace V] [ConnectedSpace V] [CompactSpace W] [ConnectedSpace W]

/-- Actual induced map on the original direct prime quotients. -/
def directPrimePush : DirectPrimeOver k W → DirectPrimeOver k V :=
  Quot.map (primePush hπ) (fun _ _ h => primePush_commonResolution hπ h)

theorem directPrimePush_mk (p : PrimePresentation k W) :
    directPrimePush hπ (Quot.mk commonResolutionRelation p) =
      Quot.mk commonResolutionRelation (primePush hπ p) := rfl

/-- Native weighted prime transport keeps the same REAL weight and fixes
the actual trivial point; no dimension-positive hypothesis is imposed. -/
def nativeDivisorialPush : NativeDivisorialPoint k W → NativeDivisorialPoint k V
  | none => none
  | some cp => some (cp.1,directPrimePush hπ cp.2)

theorem nativeDivisorialPush_trivial : nativeDivisorialPush hπ none = none := rfl

theorem nativeDivisorialPush_prime_mk (p : PrimePresentation k W) (c : ℝ) (hc : 0 < c) :
    nativeDivisorialPush hπ (some (⟨c,hc⟩,Quot.mk commonResolutionRelation p)) =
      some (⟨c,hc⟩,Quot.mk commonResolutionRelation (primePush hπ p)) := rfl

end SGPT.NAPotential.TraceComparison
