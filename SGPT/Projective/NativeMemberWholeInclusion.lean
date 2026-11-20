import SGPT.Projective.NativeMemberOffPairing
import SGPT.Projective.NativeMemberLocalInclusion

/-! The actual global whole native member current/inclusion identity,
manufacturing its true finite partition and consuming proved local geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle MeasureTheory
open scoped Topology Distributions Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira LelongPoincareDivisor CanonicalCurrentFrame
open ProductTestForms ActualCompactGlobalPairingCalibration IntegrationCurrent TopDegreeDensity

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 2)) X] [IsComplexManifold (d + 2) X] [CompactSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 2) X)
  (hL : IsSourceSmoothHermitianMetric L)
  (s : Fin (N + 1) → HolomorphicSections (n := d + 2) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hl : IsSmoothHypersurfaceMember (d + 2)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- The entire original native section current equals the intrinsic
integral on the SAME entire member. All true local geometry and the SAME
finite smooth weights are manufactured internally, before the test form. -/
theorem native_member_pairing_eq_integral
    (G : SmoothRealForm (d + 2) X (2 * (d + 1))) :
    let := nativeMemberChartedSpace L s hgen l hl
    let := nativeMemberComplex L s hgen l hl
    let : MeasurableSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := borel _
    let : BorelSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := ⟨rfl⟩
    let : CompactSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :=
      wholeMember_compact _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
    ∀ κW : KahlerBackground (d + 1) (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l),
    pairingLM (integrationCurrent (canonicalBasis (d + 2)) (Nat.succ_pos (d + 1))
      (nativeSectionDivisorMetric L hL (linearSection L s l)
        (linearSection_dense_nonzero (Nat.succ_pos (d + 1)) L s hgen l
          (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl)))
      (divisorPeriodComplement (d + 1) ▸ G) =
      ∫ y, topRatio κW.form.val (SmoothRealForm.pullback
        (nativeMemberInclusion L s hgen l hl).contMDiff G) y ∂kahlerVolume κW := by
  let := nativeMemberChartedSpace L s hgen l hl
  let := nativeMemberComplex L s hgen l hl
  let W := member (sourceNativeFiniteSectionProjectiveMap L s hgen) l
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : CompactSpace W := wholeMember_compact _
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
  dsimp only
  intro κW
  obtain ⟨Q⟩ := exists_nativeMemberPartition L s hgen l hl
  rw [Q.pairing_eq_sum_weightedCast, Q.intrinsic_integral_eq_sum G κW]
  apply Finset.sum_congr rfl
  intro i _
  rcases (Q.patch i).window_or_off with hon | hoff
  · obtain ⟨x, hx, hxO, P, e, hPm, hmem, _hlocus⟩ := hon
    exact native_member_weighted_pairing_eq_integral L s hgen l hL hl
      (Q.patch i).frame (Q.patch i).chart _ P hPm e
      (Q.weight i) (Q.smooth i) (Q.compact i)
      (fun y hy => (Q.patch i).subset_frame_chart (Q.support i hy))
      (fun y hy => hmem y (Q.support i hy)) G κW
  · rw [Q.pairing_eq_zero_of_off hL i hoff G,
      Q.intrinsic_integral_eq_zero_of_off i hoff G κW]

end SGPT.Projective.NumEq.CompleteIntersections
