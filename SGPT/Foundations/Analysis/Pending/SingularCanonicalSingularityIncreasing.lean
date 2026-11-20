import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets

set_option autoImplicit false

/-! # Increasing directed nets converge in the actual singularity pseudometric

SGPT PDF0226 Corollary 6.2.4, first assertion. Genuine regularized supremum
and actual endpoint mass limits are produced internally from the uniform
upper bound and directed monotonicity. The source's additional model-potential
closure clause remains a separate envelope result.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  GlobalNonPluripolar IncreasingMixedDirectedNets SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual directed endpoint mixed mass continuity produces both genuine
regularized supremum and defining real singularity-distance convergence. -/
theorem tendsto_singularityDistance_of_monotone_uniformlyBounded
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → M → EReal} (hu : ∀ i, IsThetaPshPotential θ.val (u i))
    (hmono : Monotone u) {C : ℝ} (hC : ∀ i x, u i x ≤ (C : EReal)) :
    let U := uscRegularization (⨆ i, u i)
    IsThetaPshPotential θ.val U ∧
      Tendsto (fun i => (singularityDistance omega θ hbig (u i) U).toReal)
        atTop (𝓝 0) := by
  classical
  let U := uscRegularization (⨆ i, u i)
  let V := thetaPshSupremum θ.val
  have hU : IsThetaPshPotential θ.val U :=
    isThetaPshPotential_regularized_of_uniformlyBounded hu hC
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  refine ⟨hU, (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass
    omega θ hbig atTop hu hU).mpr ?_⟩
  intro k
  let T : I → Fin n → M → EReal := fun i => endpointMixedPotential k (u i) V
  have hT : ∀ i a, IsThetaPshPotential θ.val (T i a) := by
    intro i a
    by_cases ha : a.val < k.val
    · simpa only [T, endpointMixedPotential, if_pos ha] using hu i
    · simpa only [T, endpointMixedPotential, if_neg ha] using hV
  have hTm : ∀ a, Monotone fun i => T i a := by
    intro a i j hij
    by_cases ha : a.val < k.val
    · simpa only [T, endpointMixedPotential, if_pos ha] using hmono hij
    · simp only [T, endpointMixedPotential, if_neg ha, le_refl]
  have hTC : ∀ a i x, T i a x ≤ (max C 0 : ℝ) := by
    intro a i x
    by_cases ha : a.val < k.val
    · simp only [T, endpointMixedPotential, if_pos ha]
      exact (hC i x).trans (EReal.coe_le_coe_iff.mpr (le_max_left C 0))
    · simp only [T, endpointMixedPotential, if_neg ha]
      exact (thetaPshSupremum_le_zero θ.val x).trans
        (EReal.coe_le_coe_iff.mpr (le_max_right C 0))
  have hS : (fun a => uscRegularization (⨆ i, T i a)) = endpointMixedPotential k U V := by
    funext a
    by_cases ha : a.val < k.val
    · simp only [T, endpointMixedPotential, if_pos ha]
      rfl
    · simp only [T, endpointMixedPotential, if_neg ha, iSup_const]
      exact uscRegularization_eq hV.1.quasiPlurisubharmonic.upperSemicontinuous
  have hm := tendsto_mixed_mass_of_directed_monotone_uniformlyBounded
    omega hT hTm hTC
  have hmeas := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple hS
    (fun a => (isThetaPshPotential_regularized_of_uniformlyBounded
      (fun i => hT i a) (hTC a)).1)
    (endpointMixedPotential_thetaPlurisubharmonic θ k U V hU hV)
  rw [hmeas] at hm
  have hmass : Tendsto (fun i => (endpointMixedMass θ V (u i) hV (hu i) k).toReal)
      atTop (𝓝 (endpointMixedMass θ V U hV hU k).toReal) := by
    simpa only [endpointMixedMass, endpointMixedMeasure, Measure.real] using hm
  have hmax (i : I) : (fun x => max (u i x) (U x)) = U := by
    funext x
    exact max_eq_right ((le_iSup u i x).trans (le_uscRegularization _ x))
  have hmaxmass (i : I) :
      endpointMixedMass θ V (fun x => max (u i x) (U x)) hV
        (IsThetaPshPotential.max (hu i) hU) k = endpointMixedMass θ V U hV hU k := by
    have ht := congrArg (fun w => endpointMixedPotential k w V) (hmax i)
    have he := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
      (endpointMixedPotential_thetaPlurisubharmonic θ k _ V
        (IsThetaPshPotential.max (hu i) hU) hV)
      (endpointMixedPotential_thetaPlurisubharmonic θ k U V hU hV)
    exact congrArg (fun μ : Measure M => μ univ) he
  refine ⟨hmass, ?_⟩
  change Tendsto (fun i => (endpointMixedMass θ V (fun x => max (u i x) (U x)) hV
    (IsThetaPshPotential.max (hu i) hU) k).toReal) atTop
    (𝓝 (endpointMixedMass θ V U hV hU k).toReal)
  simpa only [hmaxmass] using
    (tendsto_const_nhds : Tendsto (fun _ : I => (endpointMixedMass θ V U hV hU k).toReal)
      atTop (𝓝 (endpointMixedMass θ V U hV hU k).toReal))

/-- The original directed net converges to its internally produced genuine
regularized supremum in the explicitly chosen actual native dS topology. -/
theorem tendsto_native_of_monotone_uniformlyBounded
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (w : I → ThetaPshL1 θ.val) (hmono : Monotone fun i => (w i).val)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) :
    let U : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ i, (w i).val),
      isThetaPshPotential_regularized_of_uniformlyBounded (fun i => (w i).property) hC⟩
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w atTop (𝓝 U) := by
  let U : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ i, (w i).val),
    isThetaPshPotential_regularized_of_uniformlyBounded (fun i => (w i).property) hC⟩
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Tendsto w atTop (𝓝 U)
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig]
  exact (tendsto_singularityDistance_of_monotone_uniformlyBounded omega θ hbig
    (fun i => (w i).property) hmono hC).2

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
