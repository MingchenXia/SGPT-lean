import SGPT.Foundations.Analysis.Pending.SingularNativeMaximumContinuity
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

set_option autoImplicit false

/-! # Actual global P-order passes to genuine native limits -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SingularGlobalPOrder SingularGlobalPMaximum ThetaPshL1Topology
  SingularCanonicalSingularityDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual maximum continuity and genuine canonical zero distance
internally pass the global source P-order through every nontrivial native limit. -/
theorem sourcePOrder_of_native_limits
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) [F.NeBot]
    (a b : I → ThetaPshL1 θ.val) (p q : ThetaPshL1 θ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace p))
    (hb : Tendsto b F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace q))
    (horder : ∀ᶠ i in F, SourcePOrder (n := n) (a i).val (b i).val) :
    SourcePOrder (n := n) p.val q.val := by
  let W : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩
  let P : ThetaPshL1 θ.val :=
    ⟨fun x => max (p.val x) (q.val x), IsThetaPshPotential.max p.property q.property⟩
  have hW : Tendsto W F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace P) :=
    SingularNativeMaximumContinuity.tendsto_native_max omega θ hbig F a b p q ha hb
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hzero : ∀ᶠ i in F, dist (W i) (b i) = 0 := by
    filter_upwards [horder] with i hi
    have hpeq := (sourcePOrder_iff_sourcePEquivalent_max omega
      (a i).property (b i).property).mp hi
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        omega θ hbig (W i).property (b i).property).mpr hpeq
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hd, EReal.toReal_zero]
  have hd₀ : Tendsto (fun i => dist (W i) (b i)) F (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ hi => hi.symm)
  have hz : dist P q = 0 := tendsto_nhds_unique (hW.dist hb) hd₀
  rw [dist_eq_singularityDistance_toReal omega θ hbig] at hz
  obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omega θ hbig
    P.property q.property
  have hm : m = 0 := by simpa only [hD, EReal.toReal_coe] using hz
  have hdist : singularityDistance omega θ hbig P.val q.val = 0 := by
    simpa only [hm, EReal.coe_zero] using hD
  exact (sourcePOrder_iff_sourcePEquivalent_max omega p.property q.property).mpr
    ((SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omega θ hbig P.property q.property).mp hdist)

end

end SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed
