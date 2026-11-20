import SGPT.Projective.NativeMemberPartition
import SGPT.Projective.NumEqDivisorGlobalPairing
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent
import SGPT.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure

/-! Unconditional actual full-current and intrinsic weighted sum identities
for the SAME manufactured finite whole-member partition. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open StronglyPositiveForms ProductTestForms ActualCompactGlobalPairingCalibration
open IntegrationCurrent TopDegreeDensity

variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hl : IsSmoothHypersurfaceMember (m + 1)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- The SAME literal holomorphic inclusion used by every original member
window; no independently chosen chart structure or inverse occurs. -/
def nativeMemberInclusion :
    let := nativeMemberChartedSpace L s hgen l hl
    let := nativeMemberComplex L s hgen l hl
    ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1))
      (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) X ∞ :=
  ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) (fun _ hx =>
    regularAtDim_member _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl hx)⟩

private theorem member_cast_sum {a b r : ℕ} (h : a = b)
    (A : Fin r → SmoothRealForm (m + 1) X a) :
    (h ▸ ∑ i, A i : SmoothRealForm (m + 1) X b) = ∑ i, (h ▸ A i) := by
  cases h
  rfl

private theorem member_cast_smulFun {a b : ℕ} (h : a = b)
    (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ) (G : SmoothRealForm (m + 1) X a) :
    (h ▸ smulFun χ hχ G : SmoothRealForm (m + 1) X b) = smulFun χ hχ (h ▸ G) := by
  cases h
  rfl

namespace NativeMemberPartition
variable {L s hgen l hl} (Q : NativeMemberPartition L s hgen l hl)

/-- The SAME weighted original global forms sum literally coefficientwise
at every original chart point, including their total extensions. -/
theorem weighted_forms_sum {q : ℕ} (G : SmoothRealForm (m + 1) X q) :
    (∑ i, smulFun (Q.weight i) (Q.smooth i) G) = G := by
  apply smoothRealForm_ext
  intro c z
  let ev : SmoothRealForm (m + 1) X q →+ RealForm (m + 1) q :=
    { toFun := fun H => H.coeff c z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show (∑ i, smulFun (Q.weight i) (Q.smooth i) G).coeff c z =
      ∑ i, (smulFun (Q.weight i) (Q.smooth i) G).coeff c z from map_sum ev _ _]
  simp only [smulFun_coeff, ← Finset.sum_smul, Q.sum_one, one_smul]

variable [CompactSpace X]

/-- The actual native full-current pairing is the sum on the SAME genuine
manufactured partition weights. This assumes no desired local equality. -/
theorem pairing_eq_sum
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (G : SmoothRealForm (m + 1) X (2 * m)) :
    pairingLM T (divisorPeriodComplement m ▸ G) =
      ∑ i, pairingLM T (divisorPeriodComplement m ▸ smulFun (Q.weight i) (Q.smooth i) G) := by
  calc
    _ = pairingLM T (divisorPeriodComplement m ▸ ∑ i, smulFun (Q.weight i) (Q.smooth i) G) :=
      congrArg (fun H => pairingLM T (divisorPeriodComplement m ▸ H)) (Q.weighted_forms_sum G).symm
    _ = _ := by rw [member_cast_sum, map_sum]

/-- The SAME actual sum in the precise degree-cast/weight order used by
the genuine local geometric current theorem. Commutation is proved
internally as literal global tensor equality, never supplied as a premise. -/
theorem pairing_eq_sum_weightedCast
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (G : SmoothRealForm (m + 1) X (2 * m)) :
    pairingLM T (divisorPeriodComplement m ▸ G) =
      ∑ i, pairingLM T (smulFun (Q.weight i) (Q.smooth i) (divisorPeriodComplement m ▸ G)) := by
  rw [Q.pairing_eq_sum T G]
  exact Finset.sum_congr rfl (fun i _ => congrArg (pairingLM T) (member_cast_smulFun _ _ _ _))

/-- The actual intrinsic whole-member integral is the sum of the SAME
ambient weighted pullback integrals, for ANY actual native member Kahler
background and ANY original smooth complementary form. -/
theorem intrinsic_integral_eq_sum (G : SmoothRealForm (m + 1) X (2 * m)) :
    let := nativeMemberChartedSpace L s hgen l hl
    let := nativeMemberComplex L s hgen l hl
    let : MeasurableSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := borel _
    let : BorelSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := ⟨rfl⟩
    let : CompactSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :=
      wholeMember_compact _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
    ∀ κW : KahlerBackground m (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l),
    (∫ y, topRatio κW.form.val (SmoothRealForm.pullback
      (nativeMemberInclusion L s hgen l hl).contMDiff G) y ∂kahlerVolume κW) =
      ∑ i, ∫ y, topRatio κW.form.val (SmoothRealForm.pullback
        (nativeMemberInclusion L s hgen l hl).contMDiff (smulFun (Q.weight i) (Q.smooth i) G)) y
          ∂kahlerVolume κW := by
  let := nativeMemberChartedSpace L s hgen l hl
  let := nativeMemberComplex L s hgen l hl
  let W := member (sourceNativeFiniteSectionProjectiveMap L s hgen) l
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : CompactSpace W := wholeMember_compact _
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
  dsimp only
  intro κW
  let hi := (nativeMemberInclusion L s hgen l hl).contMDiff
  have hpoint (y : W) :
      (∑ i, topRatio κW.form.val (SmoothRealForm.pullback hi
        (smulFun (Q.weight i) (Q.smooth i) G)) y) =
      topRatio κW.form.val (SmoothRealForm.pullback hi G) y := by
    simp_rw [pullback_smulFun hi, SmoothCurrentTraceMeasure.topRatio_smulFun]
    rw [← Finset.sum_mul, Q.sum_one, one_mul]
  calc
    _ = ∫ y, ∑ i, topRatio κW.form.val (SmoothRealForm.pullback hi
        (smulFun (Q.weight i) (Q.smooth i) G)) y ∂kahlerVolume κW :=
      integral_congr_ae (Eventually.of_forall fun y => (hpoint y).symm)
    _ = _ := integral_finsetSum _ (fun i _ => IntegrationCurrent.integrable_topRatio κW _)

/-- An off-member partition patch has identically zero intrinsic weighted
pullback integral on the ENTIRE member, without a component selection. -/
theorem intrinsic_integral_eq_zero_of_off (i : Fin Q.size)
    (hoff : Disjoint ((Q.patch i).domain : Set X)
      (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l))
    (G : SmoothRealForm (m + 1) X (2 * m)) :
    let := nativeMemberChartedSpace L s hgen l hl
    let := nativeMemberComplex L s hgen l hl
    let : MeasurableSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := borel _
    let : BorelSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) := ⟨rfl⟩
    let : CompactSpace (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :=
      wholeMember_compact _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
    ∀ κW : KahlerBackground m (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l),
    (∫ y, topRatio κW.form.val (SmoothRealForm.pullback
      (nativeMemberInclusion L s hgen l hl).contMDiff (smulFun (Q.weight i) (Q.smooth i) G)) y
        ∂kahlerVolume κW) = 0 := by
  let := nativeMemberChartedSpace L s hgen l hl
  let := nativeMemberComplex L s hgen l hl
  let W := member (sourceNativeFiniteSectionProjectiveMap L s hgen) l
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : CompactSpace W := wholeMember_compact _
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
  dsimp only
  intro κW
  have hz (y : W) : Q.weight i y = 0 := by
    by_contra h
    exact (disjoint_left.mp hoff) (Q.support i (subset_tsupport _ h)) y.property
  have hpoint (y : W) : topRatio κW.form.val (SmoothRealForm.pullback
      (nativeMemberInclusion L s hgen l hl).contMDiff (smulFun (Q.weight i) (Q.smooth i) G)) y = 0 := by
    rw [pullback_smulFun, SmoothCurrentTraceMeasure.topRatio_smulFun]
    change Q.weight i (y : X) * _ = 0
    rw [hz y, zero_mul]
  simp_rw [hpoint]
  exact integral_zero _ _

end NativeMemberPartition
end SGPT.Projective.NumEq.CompleteIntersections
