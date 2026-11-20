import SGPT.Checks.Comparison.GfImSections
import SGPT.Okounkov.SchemeNativeStalkNaturality

/-! Entire original algebraic ideal stalks and actual native analytic germ ideals.
Source `thm:comp_traceop`; blueprint `trace-na-ideal-functoriality.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult
open SGPT.NAPotential.BJ.GfIm
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance traceGermsPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceGermsPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceGermsPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The ENTIRE original analytic ideal germ is the actual extension of the
ENTIRE original algebraic stalk ideal; every generator and every sum is retained. -/
theorem analyticIdeal_germ_eq_map_stalk (J : X.IdealSheafData) (p : SchemeComplexPoint f) :
    anGerms f n E J p =
      (SGPT.NAPotential.Berkovich.stalkIdeal J (schemeComplexPointImage f p)).map
        (schemeNativeStalkGerm f n p) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g, hg, ⟨U, hpU, r, hr, rfl⟩, rfl⟩
    rw [← regularGermHom_apply f n E (U : X.Opens) p hpU r]
    exact Ideal.mem_map_of_mem (schemeNativeStalkGerm f n p)
      (germ_mem_stalkIdeal J U hpU hr)
  · rw [SGPT.NAPotential.Berkovich.stalkIdeal, Ideal.map_iSup]
    apply iSup_le
    intro U
    rw [Ideal.map_iSup]
    apply iSup_le
    intro hpU
    rw [Ideal.map_map]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change regularGermHom f n E (U : X.Opens) p hpU r ∈ anGerms f n E J p
    rw [regularGermHom_apply]
    exact mk_mem_spanGerms (schemeOpenRegularFunction_holomorphicAt f n E
      (U : X.Opens) r p hpU) ⟨U, hpU, r, hr, rfl⟩

end SGPT.NAPotential.TraceComparison
