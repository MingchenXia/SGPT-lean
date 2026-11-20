import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # The complete actual maximum-and-mass native convergence criterion

SGPT PDF0237 Corollary 6.2.8 conditions (1) and (2). Actual native mass
convergence applied twice, and the actual double maximum subtype identity,
produce the full remaining source equivalence for arbitrary filters.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual native mass convergence applied to the original and genuine maximum
families produces both directions of source Corollary 6.2.8 condition (2). -/
theorem tendsto_native_iff_max_and_endpointMixedMass (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ι : Type*} (F : Filter ι) (w : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    let Z : ι → ThetaPshL1 θ.val := fun i =>
      ⟨fun x => max ((w i).val x) (v.val x),
        IsThetaPshPotential.max (w i).property v.property⟩
    Tendsto w F (𝓝 v) ↔
      Tendsto Z F (𝓝 v) ∧
      ∀ k : Fin (n + 1),
        Tendsto (fun i => endpointMixedMass θ (thetaPshSupremum θ.val) (w i).val
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (w i).property k)
          F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v.val
            (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property k)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let Z : ι → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((w i).val x) (v.val x), IsThetaPshPotential.max (w i).property v.property⟩
  let ZZ : ι → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((Z i).val x) (v.val x), IsThetaPshPotential.max (Z i).property v.property⟩
  let mass : Fin (n + 1) → ThetaPshL1 θ.val → ℝ≥0∞ := fun k a =>
    endpointMixedMass θ (thetaPshSupremum θ.val) a.val
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic a.property k
  have hz : ZZ = Z := by
    funext i
    apply Subtype.ext
    funext x
    change max (max ((w i).val x) (v.val x)) (v.val x) = max ((w i).val x) (v.val x)
    rw [max_assoc, max_self]
  have hw := tendsto_native_iff_endpointMixedMass omega θ hbig F w v
  change Tendsto w F (𝓝 v) ↔ ∀ k,
    Tendsto (fun i => mass k (w i)) F (𝓝 (mass k v)) ∧
      Tendsto (fun i => mass k (Z i)) F (𝓝 (mass k v)) at hw
  have hZ := tendsto_native_iff_endpointMixedMass omega θ hbig F Z v
  change Tendsto Z F (𝓝 v) ↔ ∀ k,
    Tendsto (fun i => mass k (Z i)) F (𝓝 (mass k v)) ∧
      Tendsto (fun i => mass k (ZZ i)) F (𝓝 (mass k v)) at hZ
  rw [hz] at hZ
  simp only [and_self] at hZ
  constructor
  · intro h
    have hm := hw.mp h
    exact ⟨hZ.mpr (fun k => (hm k).2), fun k => (hm k).1⟩
  · intro h
    have hm := hZ.mp h.1
    exact hw.mpr (fun k => ⟨h.2 k, hm k⟩)

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion
