import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze

set_option autoImplicit false

/-! # Actual native order-sandwich convergence

SGPT PDF0239 Corollary 6.2.11. True canonical finiteness and the proved
global ordered distance squeeze give native middle convergence for all
original masses. No positive-mass/model or target-limit certificate.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularNativeOrderSandwich

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  ThetaPshL1Topology SingularGlobalPOrder SingularGlobalPEnvelopeBridge
  SingularCanonicalSingularityDistance SingularCanonicalOrderSqueeze

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem singularityDistance_eq_coe_dist
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    singularityDistance omega θ hbig u.val v.val = (dist u v : EReal) := by
  let := singularityPseudoMetricSpace omega θ hbig
  obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omega θ hbig
    u.property v.property
  have hd : dist u v = m := by
    simpa only [hD, EReal.toReal_coe] using
      dist_eq_singularityDistance_toReal omega θ hbig u v
  rw [hd]
  exact hD

/-- The true global order squeeze and actual finite defining distances
internally produce middle native convergence from the two outer limits. -/
theorem tendsto_native_of_sourcePOrder_sandwich
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I)
    (a b c : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hab : ∀ i, SourcePOrder (n := n) (a i).val (b i).val)
    (hbc : ∀ i, SourcePOrder (n := n) (b i).val (c i).val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (hc : Tendsto c F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto b F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have houterReal : Tendsto (fun i => dist (a i) (c i)) F (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using ha.dist hc
  have houterExtended : Tendsto (fun i => singularityDistance omega θ hbig
      (a i).val (c i).val) F (𝓝 (0 : EReal)) := by
    simpa only [← singularityDistance_eq_coe_dist omega θ hbig, EReal.coe_zero] using
      EReal.tendsto_coe.mpr houterReal
  have hmiddleExtended := (tendsto_singularityDistance_zero_of_sourcePOrder omega θ hbig
    F (fun i => (a i).property) (fun i => (b i).property) (fun i => (c i).property)
    hab hbc houterExtended).1
  have hmiddleReal : Tendsto (fun i => (singularityDistance omega θ hbig
      (a i).val (b i).val).toReal) F (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, EReal.toReal_zero] using
      (EReal.tendsto_toReal (show (0 : EReal) ≠ ⊤ by simp)
        (show (0 : EReal) ≠ ⊥ by simp)).comp hmiddleExtended
  have hmiddleDist : Tendsto (fun i => dist (b i) (a i)) F (𝓝 (0 : ℝ)) := by
    have he : (fun i => (singularityDistance omega θ hbig (a i).val (b i).val).toReal) =
        fun i => dist (b i) (a i) := by
      funext i
      rw [singularityDistance_eq_coe_dist omega θ hbig, EReal.toReal_coe, dist_comm]
    exact he ▸ hmiddleReal
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsum := hmiddleDist.add (tendsto_iff_dist_tendsto_zero.mp ha)
  apply squeeze_zero (fun _ => dist_nonneg) (fun i => dist_triangle (b i) (a i) v)
  simpa only [zero_add] using hsum

/-- Literal original-background envelope comparisons suffice, via the
proved forward transport to global order, including two zero masses. -/
theorem tendsto_native_of_fixedPOrder_sandwich
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I)
    (a b c : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hab : ∀ i, POrderWith θ (a i).val (b i).val)
    (hbc : ∀ i, POrderWith θ (b i).val (c i).val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (hc : Tendsto c F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto b F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v) :=
  tendsto_native_of_sourcePOrder_sandwich omega θ hbig F a b c v
    (fun i => sourcePOrder_of_pOrderWith omega θ (a i).property (b i).property (hab i))
    (fun i => sourcePOrder_of_pOrderWith omega θ (b i).property (c i).property (hbc i)) ha hc

end
end SGPT.Foundations.Analysis.Pending.SingularNativeOrderSandwich
