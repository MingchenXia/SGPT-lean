import SGPT.Bergman.SourceSmoothWeightedMeasureBound
import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

omit [ConnectedSpace X] in
/-- Actual original positive-degree beta is finite by the PRODUCED smooth
point bound against the SAME finite raw Kahler volume. No probability,
BM, rank/basis or finite-measure certificate enters. -/
theorem sourceBergmanMeasure_isFinite
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (k : ℕ) (hk : 0 < k) (phi : X → EReal) :
    IsFiniteMeasure (sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
      ((IntegrationCurrent.kahlerVolume omega).comap
        (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi) := by
  obtain ⟨D, hD, hbound⟩ := exists_source_smooth_weighted_measure_bound L T hL hT v hv
    (IntegrationCurrent.kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
  let : IsFiniteMeasure (ENNReal.ofReal D • IntegrationCurrent.kahlerVolume omega) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  exact isFiniteMeasure_of_le _ (hbound k hk phi)

omit [ConnectedSpace X] in
/-- The TRUE original raw-volume beta, as an actual finite measure with
the library's weak topology. Finiteness is manufactured internally. -/
def sourceBergmanFiniteMeasure
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (k : ℕ) (hk : 0 < k) (phi : X → EReal) :
    FiniteMeasure X :=
  ⟨sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
    ((IntegrationCurrent.kahlerVolume omega).comap
      (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi,
    sourceBergmanMeasure_isFinite omega L T hL hT v hv k hk phi⟩

omit [ConnectedSpace X] in
/-- Exact both-type readback: no rescaling/replacement of the source beta. -/
theorem sourceBergmanFiniteMeasure_toMeasure
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (k : ℕ) (hk : 0 < k) (phi : X → EReal) :
    (sourceBergmanFiniteMeasure omega L T hL hT v hv k hk phi : Measure X) =
      sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
        ((IntegrationCurrent.kahlerVolume omega).comap
          (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi := rfl

end SGPT.Bergman.ContactConcentration
