import SGPT.Projective.OriginalPositiveTensorTwist
import SGPT.Bergman.SiuNativePositiveNS

/-! Forward actual ORIGINAL scheme line Chern classes in the actual native
Cartier span. Blueprint: original-scheme-chern-neronseveri.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.BDivisor.NSKodaira
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance originalNSTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalNSCharts (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance originalNSManifold (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

/-- Genuine actual positive original physical line produces its SAME Chern class in actual native NS. -/
theorem originalPositiveLine_chern_mem_neronSeveri (P : OriginalPositiveLine f n E) :
    RealBottChern.ofRepresentative P.curvature ∈ SGPT.BDivisor.DFAlg.neronSeveri n (SchemeComplexPoint f) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact positive_native_chern_mem_neronSeveri P.native.bundle P.native.smooth
    P.curvature P.native.own P.positive

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (A : OriginalPositiveLine f n E)

include A in
/-- ANY actual original physical line class lands in existing actual native NS by genuine original positive twist. -/
theorem originalSchemeLine_chern_mem_neronSeveri :
    RealBottChern.ofRepresentative (H.curvature a) ∈ SGPT.BDivisor.DFAlg.neronSeveri n (SchemeComplexPoint f) := by
  obtain ⟨M, _, hpos⟩ := exists_positive_originalTensorTwist f n E a H A
  let Q : OriginalPositiveLine f n E :=
    { sheaf := bundleTensor L (bundleTensorPower A.sheaf M)
      atlas := pairwiseTensorAtlas a (A.atlas.tensorPower M)
      metric := H.tensorProduct (A.metric.tensorPower A.atlas M) a (A.atlas.tensorPower M)
      positive := hpos }
  have hQ := originalPositiveLine_chern_mem_neronSeveri f n E Q
  have hA := originalPositiveLine_chern_mem_neronSeveri f n E A
  have hclass : RealBottChern.ofRepresentative Q.curvature =
      RealBottChern.ofRepresentative (H.curvature a) +
        (M : ℝ) • RealBottChern.ofRepresentative A.curvature := by
    have h := RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (originalTensorTwist_curvature f n E a H A M)
    exact h.trans (by rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul])
  have hmem := (SGPT.BDivisor.DFAlg.neronSeveri n (SchemeComplexPoint f)).sub_mem hQ
    ((SGPT.BDivisor.DFAlg.neronSeveri n (SchemeComplexPoint f)).smul_mem (M : ℝ) hA)
  simpa only [hclass, add_sub_cancel_right] using hmem

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
