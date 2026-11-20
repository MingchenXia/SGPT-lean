import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeAdditionConcavity
import SGPT.Foundations.Analysis.Pending.OrderedConvexNativeContinuity
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze

set_option autoImplicit false

/-! # Actual I-envelope limits along naturally ordered convex paths -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeOrderedConvexNativeLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  ThetaPshConvexCombination ThetaPshL1Topology EndpointMixedMassConvexCombination
  ActualIEnvelopeAdditionConcavity ActualIEnvelopeOrderInfimum
  OrderedConvexNativeContinuity SingularCanonicalOrderSqueeze SingularGlobalPOrder
  SingularCanonicalSingularityDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Concavity and actual global ordered distance squeeze internally produce
the original-background native I-envelope limit along the ordered convex path. -/
theorem tendsto_native_iEnvelope_ordered_convex (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hp : IsThetaPshPotential θ.val p) (hpu : p ≤ u) {I : Type*}
    (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i => (t i).val) F (𝓝 0)) :
    ∃ (hB : ∀ i, IsThetaPshPotential θ.val
        (iSingularityEnvelope θ.val (convexComb (1 - (t i).val) u p)))
      (hP : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u)),
      Tendsto (fun i => (⟨iSingularityEnvelope θ.val
        (convexComb (1 - (t i).val) u p), hB i⟩ : ThetaPshL1 θ.val)) F
        (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
          ⟨iSingularityEnvelope θ.val u, hP⟩) := by
  let P := iSingularityEnvelope θ.val u
  let Q := iSingularityEnvelope θ.val p
  have hP : IsThetaPshPotential θ.val P :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hQ : IsThetaPshPotential θ.val Q :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hp.1.hasSmoothLocalPotentials p hp
  have hQP : Q ≤ P := iSingularityEnvelope_le_of_iOrderOnManifold θ hu
    (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic hpu)
  let U : I → M → EReal := fun i => convexComb (1 - (t i).val) u p
  have hU (i : I) : IsThetaPshPotential θ.val (U i) :=
    isThetaPshPotential_convexComb_closed hu hp
      (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)
  let B : I → M → EReal := fun i => iSingularityEnvelope θ.val (U i)
  have hB (i : I) : IsThetaPshPotential θ.val (B i) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (hU i).1.hasSmoothLocalPotentials (U i) (hU i)
  let A : I → M → EReal := fun i => convexComb (1 - (t i).val) P Q
  have hA (i : I) : IsThetaPshPotential θ.val (A i) :=
    isThetaPshPotential_convexComb_closed hP hQ
      (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)
  have hAB (i : I) : A i ≤ B i := by
    intro x
    change ((1 - (t i).val : ℝ) : EReal) * P x +
      ((1 - (1 - (t i).val) : ℝ) : EReal) * Q x ≤
        iSingularityEnvelope θ.val (U i) x
    have hUi : U i = fun y => ((1 - (t i).val : ℝ) : EReal) * u y +
        ((t i).val : EReal) * p y := by
      funext y
      simp only [U, convexComb, sub_sub_cancel]
    rw [hUi, sub_sub_cancel]
    exact iSingularityEnvelope_convexCombination_le hu hp
      (t i).property.1 (t i).property.2 x
  have hBP (i : I) : B i ≤ P := by
    have hUu := convexComb_mono (sub_nonneg.mpr (t i).property.2.le)
      (sub_le_self 1 (t i).property.1.le) (a := u) (b := p) (c := u) (d := u) le_rfl hpu
    rw [ThetaCapacity.convexComb_self (sub_pos.mpr (t i).property.2)
      (by linarith [(t i).property.1]) u] at hUu
    exact iSingularityEnvelope_le_of_iOrderOnManifold θ hu
      (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic hUu)
  let AT : I → ThetaPshL1 θ.val := fun i => ⟨A i, hA i⟩
  let BT : I → ThetaPshL1 θ.val := fun i => ⟨B i, hB i⟩
  let PT : ThetaPshL1 θ.val := ⟨P, hP⟩
  have hlimA : Tendsto AT F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace PT) :=
    tendsto_native_ordered_convex omega θ hbig hP hQ hQP F t ht
  let _nativeMetric : PseudoMetricSpace (ThetaPshL1 θ.val) :=
    singularityPseudoMetricSpace omega θ hbig
  let _nativeTopology : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hdistA : Tendsto (fun i => dist (AT i) PT) F (𝓝 (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hlimA
  have hrealA : Tendsto (fun i => (singularityDistance omega θ hbig (A i) P).toReal)
      F (𝓝 (0 : ℝ)) := hdistA.congr' (Eventually.of_forall fun i =>
        dist_eq_singularityDistance_toReal omega θ hbig (AT i) PT)
  have hvalue (i : I) :
      (((singularityDistance omega θ hbig (A i) P).toReal : ℝ) : EReal) =
        singularityDistance omega θ hbig (A i) P := by
    obtain ⟨r, _, _, _, hr⟩ := exists_tendsto_singularityDistance omega θ hbig (hA i) hP
    rw [hr, EReal.toReal_coe]
  have hextA : Tendsto (fun i => singularityDistance omega θ hbig (A i) P)
      F (𝓝 (0 : EReal)) := by
    simpa only [hvalue, EReal.coe_zero] using EReal.tendsto_coe.mpr hrealA
  have hABP (i : I) : SourcePOrder (n := n) (A i) (B i) :=
    sourcePOrder_of_moreSingularOn omega θ θ (hA i) (hB i)
      (MoreSingularOn.of_le fun x _ => hAB i x)
  have hBPP (i : I) : SourcePOrder (n := n) (B i) P :=
    sourcePOrder_of_moreSingularOn omega θ θ (hB i) hP
      (MoreSingularOn.of_le fun x _ => hBP i x)
  have hextB := (tendsto_singularityDistance_zero_of_sourcePOrder omega θ hbig F
    hA hB (fun _ => hP) hABP hBPP hextA).2
  have hrealB : Tendsto (fun i => (singularityDistance omega θ hbig (B i) P).toReal)
      F (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, EReal.toReal_zero] using
      (EReal.tendsto_toReal (by simp : (0 : EReal) ≠ ⊤)
        (by simp : (0 : EReal) ≠ ⊥)).comp hextB
  have hdistB : Tendsto (fun i => dist (BT i) PT) F (𝓝 (0 : ℝ)) :=
    hrealB.congr' (Eventually.of_forall fun i =>
      (dist_eq_singularityDistance_toReal omega θ hbig (BT i) PT).symm)
  refine ⟨hB, hP, ?_⟩
  change Tendsto BT F (𝓝 PT)
  exact (tendsto_iff_dist_tendsto_zero (α := ThetaPshL1 θ.val)
    (f := BT) (a := PT)).mpr hdistB

end

end SGPT.Foundations.Analysis.Pending.IEnvelopeOrderedConvexNativeLimit
