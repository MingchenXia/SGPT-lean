import SGPT.Checks.Comparison.TraceGermIdealPullback
import SGPT.Checks.Comparison.TraceGFSectionPullback

/-! Actual ideal analytification commutes with the actual original scheme morphism.
Source `thm:comp_traceop`; blueprint `trace-na-ideal-functoriality.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.GfIm
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
  [IsSeparated f] [QuasiCompact f] [IsSeparated (i ≫ f)] [QuasiCompact (i ≫ f)]

local instance traceFunSourceTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticPointTopology (i ≫ f)
local instance traceFunTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceFunSourceCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceFunTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceFunSourceManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (i ≫ f) k
local instance traceFunTargetManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The ENTIRE original inverse-image ideal has precisely the actual image
of the ENTIRE original analytic germ ideal. The full stalk square is
derived from the actual original scheme morphism, not supplied. -/
theorem analyticIdeal_comap_germ_eq (J : X.IdealSheafData) (p : SchemeComplexPoint (i ≫ f)) :
    anGerms (i ≫ f) k EY (J.comap i) p =
      (anGerms f n EX J (schemeComplexPointMap (i ≫ f) f i rfl p)).map
        (schemeMorphismNativeGermPullback f i k n p) := by
  rw [analyticIdeal_germ_eq_map_stalk, SGPT.NAPotential.BJ.stalkIdeal_comap, Ideal.map_map,
    schemeNativeStalkGerm_naturality_hom f i k n p, ← Ideal.map_map]
  apply congrArg (Ideal.map (schemeMorphismNativeGermPullback f i k n p))
  change (SGPT.NAPotential.Berkovich.stalkIdeal J
      (schemeComplexPointImage f (schemeComplexPointMap (i ≫ f) f i rfl p))).map
        (schemeNativeStalkGerm f n (schemeComplexPointMap (i ≫ f) f i rfl p)) = _
  exact (analyticIdeal_germ_eq_map_stalk f n EX J
    (schemeComplexPointMap (i ≫ f) f i rfl p)).symm

/-- **The actual original inverse-image ideal analytifies to its actual
holomorphic pullback**, as the whole original germ ideal, in every source
and target dimension. No flatness, coefficient, ideal or germ certificate input. -/
theorem analytificationIdeal_comap (J : X.IdealSheafData) :
    analytificationIdeal (i ≫ f) k EY (J.comap i) =
      GermIdeal.pullback (m := k) (schemeComplexPointMap (i ≫ f) f i rfl)
        (analytificationIdeal f n EX J) := by
  let F := schemeComplexPointMap (i ≫ f) f i rfl
  let hF := schemeComplexPointMap_contMDiff f i k n ∞
  apply GermIdeal.ext
  funext p g
  apply propext
  by_cases hg : HolomorphicAt k g p
  · rw [mem_analytificationIdeal_iff_mk (i ≫ f) k EY (J.comap i) p hg,
      pullback_mem_iff_mk_mem_map hF (analytificationIdeal f n EX J) p
        (fun a ha => ha.1) hg,
      spanGerms_analytificationIdeal_eq f n EX J (F p),
      analyticIdeal_comap_germ_eq f i n k EX EY J p]
    rfl
  · exact ⟨fun h => (hg h.1).elim, fun h => (hg h.1).elim⟩

end SGPT.NAPotential.TraceComparison
