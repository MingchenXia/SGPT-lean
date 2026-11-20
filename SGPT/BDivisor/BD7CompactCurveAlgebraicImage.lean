import SGPT.Okounkov.OF12AmbientProjectiveTrace
import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem

/-! The image on complex points of a compact holomorphic curve in a smooth
projective target is the exact trace of a closed algebraic carrier. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.BDivisor.GM
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

local instance curveImageTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance curveImageCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g d
local instance curveImageManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

/-- Remmert gives the closed analytic image in the ambient projective space;
Chow reads its inverse image as the trace of a closed set on the original scheme. -/
theorem exists_closedAlgebraicTrace_eq_image_of_compactCurve_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    ∃ Z : Set X, IsClosed Z ∧ range g = schemeNativeAlgebraicTrace f Z := by
  let F := projectivePoint f E n ∘ g
  have hEmbed := isHolomorphicEmbedding_projectivePoint f E n
  have hF := (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hEmbed).comp hg
  have hproper : AnalyticDimensionBasics.ProperOn F univ := by
    intro K hK
    rw [univ_inter]
    exact (hK.isClosed.preimage hF.continuous).isCompact
  have hAnalytic := ProperMappingTheorem.isComplexAnalyticSubset_image
    hF (isComplexAnalyticSubset_univ (n := 1) (M := T)) hproper
  obtain ⟨Z, hZ, htrace⟩ := SGPT.Okounkov.OF12.exists_closed_trace_of_ambient_analyticSubset E hAnalytic
  refine ⟨Z, hZ, ?_⟩
  ext q
  change q ∈ range g ↔ schemeComplexPointImage f q ∈ Z
  rw [htrace, ambientPoint_eq_projectivePoint E n]
  change q ∈ range g ↔ projectivePoint f E n q ∈ F '' univ
  rw [image_univ]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, hEmbed.injective ht⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
