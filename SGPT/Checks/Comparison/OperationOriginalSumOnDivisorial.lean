import SGPT.Checks.Comparison.OperationNASumDivisorial
import SGPT.NAPotential.AlgebraicPrimeDictionaryMain
import SGPT.Checks.Comparison.SourceZeroModels

/-! Actual original sum formula on ENTIRE augmented source X^Div.
Dictionary geometry is internally produced; n=0/trivial retained.
Blueprint: operation-original-sum-divisorial.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProper f] [IsIntegral X]
local instance originalSumDivPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalSumDivPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalSumDivPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

omit [IsIntegral X] in
/-- The actual original sum cutoffs at the SAME prescribed geometric index. -/
theorem sourceNA_component_max_sum (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    ((Γ.sum Δ).component ω).val.max = (Γ.component ω).val.max + (Δ.component ω).val.max := by
  change (Γ.sumComponent Δ ω).val.max = _
  rw [SourceNAPotential.sumComponent_max (sourceKahlerFormRepresentative ω),
    sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative ω) Γ ω,
    sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative ω) Δ ω]

/-- ALL original source divisorial points, including actual trivial,
obey the literal original sum formula. Geometry/realization are INTERNAL;
ALL n including zero, no rational Chern or approximation assumption. -/
theorem naPotentialAnAt_sum_on_sourceDivisorialSet
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (v : BerkovichPoint f) (hv : v ∈ sourceDivisorialSet f) :
    naPotentialAnAt n E (Γ.sum Δ) ω v =
      naPotentialAnAt n E Γ ω v + naPotentialAnAt n E Δ ω v := by
  cases n with
  | zero =>
    simp only [SGPT.NAPotential.BJ.SourceZeroModels.naPotentialAnAt_eq_of_dim_zero,
      sourceNA_component_max_sum f 0, EReal.coe_add]
  | succ k =>
    rcases (mem_sourceDivisorialSet_iff f v).mp hv with hv0 | hvD
    · subst v
      rw [DivDict2.naPotentialAnAt_trivial (E := E),
        DivDict2.naPotentialAnAt_trivial (E := E),
        DivDict2.naPotentialAnAt_trivial (E := E),
        sourceNA_component_max_sum f (k+1),EReal.coe_add]
    · rcases hvD with ⟨D,t,ht,rfl⟩
      obtain ⟨p,hp⟩ := AlgebraicPrimeDictionary.algebraicPrimesRealized (m := k) E D
      rw [DivDict2.naPotentialAnAt_ordVal hp (Γ.sum Δ) ω t ht,
        DivDict2.naPotentialAnAt_ordVal hp Γ ω t ht,
        DivDict2.naPotentialAnAt_ordVal hp Δ ω t ht,
        naDivisorialTransform_sum Γ Δ ω p ht]

end SGPT.NAPotential.OperationComparison
