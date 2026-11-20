import SGPT.Unibranch.OriginalNativeHSGlobalResolution
import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductRegularGraph
import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductProperProjections

/-! Resolve the actual noncompact inverse graph using the existing global resolution.
No graph, common model, resolution or projection-properness certificate is an input.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.PrimeNov16ResolvedGraph
open Set CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SourceReducedComplexSpace
open scoped Topology Manifold ContDiff ProductComplexManifold

variable {n : ℕ} {X Y₀ Y₁ : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- The SAME actual graph closure acquires a genuine smooth native resolution,
with both proper composed coordinate projections and the actual over-base square.
This is a producer for the noncompact common-model construction, not its manifold bridge. -/
theorem exists_actual_resolved_graph {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (B : Set X), IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
        V.dim = n ∧
        V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
        (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
          RegularAtDim (n := n + n) V.carrier p n) ∧
        ∃ (Z : SourceReducedComplexSpace)
          (ρ : Z ⟶ ofClosedAnalytic V.carrier V.analytic),
          IsResolution ρ ∧
          IsIsoOver ρ (HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicRegularLocus
            (ofClosedAnalytic V.carrier V.analytic).obj) ∧
          IsProperMap ρ.hom.left.base ∧
          Function.Surjective ρ.hom.left.base ∧
          IsProperMap (fun z : Z.obj.left => (ρ.hom.left.base z).val.1) ∧
          IsProperMap (fun z : Z.obj.left => (ρ.hom.left.base z).val.2) ∧
          (∀ z : Z.obj.left, c₀ (ρ.hom.left.base z).val.1 =
            c₁ (ρ.hom.left.base z).val.2) := by
  obtain ⟨B, s₀, s₁, hBc, hBa, hBi, _hs₀, _hs₁, _hr₀, _hr₁,
    _hl₀, _hl₁, V, hVdim, _hVcomp, hVclosure, hVF, hGreg, _hGimage⟩ :=
    AnalyticFibreProductRegularGraph.exists_actual_mainComponent_regular_graph hc₀ hc₁
  let A := ofClosedAnalytic V.carrier V.analytic
  let Z := OriginalNativeHSGlobalResolution.source A
  let ρ : Z ⟶ A := OriginalNativeHSGlobalResolution.projection A
  have hρ : IsProperMap ρ.hom.left.base := OriginalNativeHSGlobalResolution.proper A
  have hp₀ : IsProperMap (fun p : V.carrier => p.val.1) :=
    AnalyticFibreProductProperProjections.isProperMap_fst_of_closed_fibreProduct
      hc₀.1.continuous hc₁.2.1 V.isClosed_carrier hVF
  have hp₁ : IsProperMap (fun p : V.carrier => p.val.2) :=
    AnalyticFibreProductProperProjections.isProperMap_snd_of_closed_fibreProduct
      hc₀.2.1 hc₁.1.continuous V.isClosed_carrier hVF
  exact ⟨B, hBc, hBa, hBi, V, hVdim, hVclosure, hGreg, Z, ρ,
    OriginalNativeHSGlobalResolution.resolution A,
    OriginalNativeHSGlobalResolution.originalReg A, hρ,
    OriginalNativeHSGlobalResolution.surjective A, hp₀.comp hρ, hp₁.comp hρ,
    fun z => hVF (ρ.hom.left.base z).property⟩

end SGPT.PSH.PrimeNov16ResolvedGraph
