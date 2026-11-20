import SGPT.BDivisor.BD6Cycle
import SGPT.BDivisor.ClassPullback
import SGPT.Projective.OriginalPhysicalMetricOverBase

/-! Chern pullback for original scheme lines and their finite real combinations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

local instance pullbackPointTopology {Z : Scheme.{0}} (g : Z ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance pullbackPointCharts {Z : Scheme.{0}} (g : Z ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance pullbackPointManifold {Z : Scheme.{0}} (g : Z ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

variable {X Y : Scheme.{0}}

/-- The actual sheaf pullback with its pulled-back original rank-one atlas. -/
def pullbackIntrinsicLineBundle (h : X ⟶ Y) (A : IntrinsicLineBundle Y) : IntrinsicLineBundle X :=
  ⟨(Scheme.Modules.pullback h).obj A.sheaf, matePullbackAtlas h A.atlas⟩

variable (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (h : X ⟶ Y) (hh : h ≫ fY = fX) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) fX] [SmoothOfRelativeDimension (m + 1) fY]
  [IsSeparated fX] [QuasiCompact fX] [IsSeparated fY] [QuasiCompact fY]
  (EX : ClosedProjectiveEmbedding fX) (EY : ClosedProjectiveEmbedding fY)

/-- The first Chern class of an original scheme line commutes with pullback along
the complex-point map of the actual morphism over the complex numbers. -/
theorem algChern_pullback (A : IntrinsicLineBundle Y) :
    algChern fX EX m (pullbackIntrinsicLineBundle h A) =
      classPullback
        (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fX fY h hh (m + 1) (m + 1) ∞)
        (algChern fY EY m A) := by
  let B := pullbackIntrinsicLineBundle h A
  let K := schemeLineBundleMetric fX (m + 1) EX B.atlas
  let H := schemeLineBundleMetric fY (m + 1) EY A.atlas
  let HP := originalPhysicalPullbackMetricOver fX fY h hh (m + 1) (m + 1) EX EY A.atlas H
  have hmetric : algChern fX EX m B = RealBottChern.ofRepresentative (HP.curvature B.atlas) :=
    K.chernClass_independent HP B.atlas B.atlas
  change algChern fX EX m B = _
  rw [hmetric, classPullback_ofRepresentative]
  apply (RealBottChern.ofRepresentative_eq_iff _ _).mpr
  exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
    (originalPhysicalPullbackMetricOver_curvature fX fY h hh (m + 1) (m + 1) EX EY A.atlas H)

/-- Chern pullback on finite real combinations of original scheme lines. -/
theorem algChern_linearCombination_pullback (v : IntrinsicLineBundle Y →₀ ℝ) :
    Finsupp.linearCombination ℝ (algChern fX EX m)
        (Finsupp.lmapDomain ℝ ℝ (pullbackIntrinsicLineBundle h) v) =
      classPullback
        (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fX fY h hh (m + 1) (m + 1) ∞)
        (Finsupp.linearCombination ℝ (algChern fY EY m) v) := by
  have hlinear :
      (Finsupp.linearCombination ℝ (algChern fX EX m)).comp
          (Finsupp.lmapDomain ℝ ℝ (pullbackIntrinsicLineBundle h)) =
        (classPullback
          (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fX fY h hh (m + 1) (m + 1) ∞)).comp
          (Finsupp.linearCombination ℝ (algChern fY EY m)) := by
    apply Finsupp.lhom_ext
    intro A r
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.linearCombination_single, map_smul, algChern_pullback fX fY h hh m EX EY]
  exact LinearMap.congr_fun hlinear v

end SGPT.BDivisor.BD6
