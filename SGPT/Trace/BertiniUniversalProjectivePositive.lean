import SGPT.Bergman.SiuNativeProjectiveEquivalence
import SGPT.Bergman.SourceNativeFirstChernForm

/-! The EXACT original book projective embedding produces an actual
smooth positive native auxiliary bundle. Frozen class/potential/native
metric producers are reused; no arbitrary chosen O1 metric positivity. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.BDivisor.NSKodaira
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

theorem exists_actual_positive_native_bundle_of_book_projective
    (hproj : SGPT.Trace.Bertini.IsProjectiveManifold n X) :
    ∃ (G : HermitianHolomorphicLineBundle.{0,0} n X) (hG : IsSourceSmoothHermitianMetric G),
      (sourceNativeFirstChernForm G hG).val.IsKahler := by
  obtain ⟨omega,hK,hNS⟩ := isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hproj
  obtain ⟨G,hG,theta,hOwn,hPos⟩ := exists_positive_native_bundle_of_kahler_mem_neronSeveri omega hK hNS
  refine ⟨G,hG,?_,(sourceNativeFirstChernForm G hG).property.1⟩
  intro c z hz
  rw [sourceNativeFirstChernForm_geometricallyEq G hG hOwn c hz]
  exact hPos.1 c z hz

end SGPT.Trace.BertiniUniversal
