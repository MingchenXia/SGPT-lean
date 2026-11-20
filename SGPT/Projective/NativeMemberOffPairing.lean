import SGPT.Projective.NativeMemberGlobalSums
import SGPT.Projective.NativeSectionWeightedCurrentArea

/-! Actual off-member finite-partition terms vanish against the SAME
complete original native section divisor current. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle
open scoped Topology Distributions Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira LelongPoincareDivisor CanonicalCurrentFrame
open ProductTestForms ActualCompactGlobalPairingCalibration

namespace NativeMemberPartition
variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
  {L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X}
  {s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber}
  {hgen : ∀ x : X, ∃ j, s j x ≠ 0} {l : HyperplaneSpace N}
  {hl : IsSmoothHypersurfaceMember (m + 1) (sourceNativeFiniteSectionProjectiveMap L s hgen) l}
  (Q : NativeMemberPartition L s hgen l hl)

/-- Every actual off-member weight vanishes against the SAME full original
section divisor current, with its retained genuine frame/chart. -/
theorem pairing_eq_zero_of_off (hL : IsSourceSmoothHermitianMetric L) (i : Fin Q.size)
    (hoff : Disjoint ((Q.patch i).domain : Set X)
      (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l))
    (G : SmoothRealForm (m + 1) X (2 * m)) :
    pairingLM (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (nativeSectionDivisorMetric L hL (linearSection L s l)
        (linearSection_dense_nonzero (Nat.succ_pos m) L s hgen l
          (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl)))
      (smulFun (Q.weight i) (Q.smooth i) (divisorPeriodComplement m ▸ G)) = 0 := by
  apply nativeSection_weighted_pairing_eq_zero_of_nonzero L hL (linearSection L s l)
    (linearSection_dense_nonzero (Nat.succ_pos m) L s hgen l
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl)
    (Q.patch i).frame (Q.patch i).chart (Q.weight i) (Q.smooth i) (Q.compact i)
    (fun _ hx => (Q.patch i).subset_frame_chart (Q.support i hx)) _ (divisorPeriodComplement m ▸ G)
  intro x hx hs
  exact (disjoint_left.mp hoff) (Q.support i hx) ((linearSection_zero_iff L s hgen l x).mp hs)

end NativeMemberPartition
end SGPT.Projective.NumEq.CompleteIntersections
