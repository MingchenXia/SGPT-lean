import SGPT.Projective.OkounkovOriginalPerturbGeometry

/-! The two literal original tensor/positive-perturbation models have actual coefficient-equal curvatures.
Blueprint: okounkov-original-tensor-perturb-curvature.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance tensorPerturbCurvTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorPerturbCurvCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance tensorPerturbCurvManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_tensorPerturb_curvatures_geometricallyEq {L N A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f n E N)
    (r : LineBundleAtlas A) (G : SchemeLineBundleMetric f n E A)
    (d : LineBundleAtlas (bundleTensor L N)) (q p : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    let aP := OkoNS.perturbAtlas a r q p
    let bP := OkoNS.perturbAtlas b r q p
    let HP := originalPerturbMetric f n E a H r G q p
    let KP := originalPerturbMetric f n E b K r G q p
    (((HP.tensorProduct KP aP bP).curvature (pairwiseTensorAtlas aP bP))).val.GeometricallyEq
      ((originalPerturbMetric f n E d (H.tensorProduct K a b) r G q (p+p)).curvature
        (OkoNS.perturbAtlas d r q (p+p))).val := by
  let := E.isSeparated
  let := E.quasiCompact
  let aP := OkoNS.perturbAtlas a r q p
  let bP := OkoNS.perturbAtlas b r q p
  let HP := originalPerturbMetric f n E a H r G q p
  let KP := originalPerturbMetric f n E b K r G q p
  dsimp only
  intro c z hz
  have ha := originalPerturbMetric_curvature f n E a H r G q p c hz
  have hb := originalPerturbMetric_curvature f n E b K r G q p c hz
  have hd := originalPerturbMetric_curvature f n E d (H.tensorProduct K a b) r G q (p+p) c hz
  have hprod := HP.curvature_tensorProduct KP aP bP (pairwiseTensorAtlas aP bP) c hz
  have hbase := H.curvature_tensorProduct K a b d c hz
  rw [hprod,ClosedRealOneOneForm.coeff_add,ha,hb,hd]
  simp only [ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_smul,Nat.cast_add]
  rw [hbase,ClosedRealOneOneForm.coeff_add]
  module
end SGPT.Okounkov.OriginalBook
