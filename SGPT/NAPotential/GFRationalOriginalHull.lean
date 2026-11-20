import SGPT.NAPotential.GFRationalVertexSectionFamily
import SGPT.NAPotential.WholePiecewiseLinearHull

/-! # The ORIGINAL regularized rational concave hull is an ACTUAL common-degree section maximum
Source: `lma:gfinimage`, closing paragraph before `eq:gf-rational-hull`.
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Convex.CutSimplex
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open scoped BigOperators Classical

variable {X : Scheme.{0}} {L : X.Modules} {f : X ⟶ Spec (.of ℂ)} [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance hullPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance hullPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance hullPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable (H : SchemeLineBundleMetric f n E L)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- **At every rational parameter the ORIGINAL regularized hull is an actual scaled maximum of
genuine products of the ORIGINAL generating sections**, all in ONE original tensor degree.
Only the nodal sections and their stated normalization are inputs; the hull identity and the
common-degree family are manufactured internally, including at every polar point. -/
theorem exists_originalHull_sectionMaximum [IsIntegral X] (b : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K) (D : PiecewiseLinearData θ)
    (hτ : ∀ i, ∃ q : ℚ, D.τ i = q) (I : Fin (D.N + 1) → Type)
    [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : Fin (D.N + 1)) → I i → bundlePowerGlobalSections L N)
    (ht : ∀ i j, t i j ≠ 0)
    (hA : ∀ i, D.A i = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p)
    (s : ℚ) (hs : (s : ℝ) ≤ D.τ 0) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ F : ActualSectionFamily L (N * Q),
      (∀ j, F.sections j ≠ 0) ∧
      uscRegularization (D.pointwiseUpperConcaveEnvelope (s : ℝ)) =
        fun p => ((((K * Q : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          finiteMaximum (fun j => H.sectionLogNormSq b (N * Q) (F.sections j)) p := by
  obtain ⟨Q, hQ, a, hmass, ha⟩ := exists_integer_vertexWeights_real D.τ hτ s
  let V := VertexIndex D.τ (s : ℝ)
  let : Fintype V := Fintype.ofFinite V
  let : Nonempty V := ⟨Sum.inl ⟨0, hs⟩⟩
  let F := vertexSectionFamily b N Q a hmass I t
  refine ⟨Q, hQ, F, vertexSectionFamily_ne_zero (f := f) b N Q a hmass I t ht, ?_⟩
  rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
  funext p
  rw [simplexValue_eq_vertex_iSup]
  change (⨆ v : V, weightedValue D (vertexVector D.τ (s : ℝ) v) p) = _
  dsimp only [F]
  rw [vertexSectionFamily_finiteMaximum,
    scale_iSup_finite _ _ (by positivity)]
  apply iSup_congr
  intro v
  rw [normalized_integer_sum K Q hK hQ]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA i, ha v i]

end SGPT.NAPotential.BJ.GfIm.RationalHull
