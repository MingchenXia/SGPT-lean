import SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false

/-! # Natural ordered convex paths converge in the original native singularity topology -/

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.OrderedConvexNativeContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeEnergy ThetaPshConvexCombination ThetaPshL1Topology MixedMass
  ActualIndependentConvexMassPolynomial SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  EndpointMixedMassConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

private theorem tendsto_endpoint_convex_one (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u p V : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (hV : IsThetaPshPotential θ.val V) {I : Type*} (F : Filter I)
    (t : I → Ioo (0 : ℝ) 1) (ht : Tendsto (fun i => (t i).val) F (𝓝 0))
    (j : Fin (n + 1)) :
    Tendsto (fun i => (endpointMixedMass θ V (convexComb (1 - (t i).val) u p)
      hV (isThetaPshPotential_convexComb_closed hu hp
        (sub_nonneg.mpr (t i).property.2.le)
        (sub_le_self 1 (t i).property.1.le)) j).toReal) F
      (𝓝 (endpointMixedMass θ V u hV hu j).toReal) := by
  classical
  let U : Fin n → M → EReal := endpointMixedPotential j u V
  let P : Fin n → M → EReal := endpointMixedPotential j p V
  have hU (k : Fin n) : IsThetaPshPotential θ.val (U k) := by
    dsimp only [U, endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hV
  have hP (k : Fin n) : IsThetaPshPotential θ.val (P k) := by
    dsimp only [P, endpointMixedPotential]
    split_ifs <;> first | exact hp | exact hV
  let Q := convexMixedMassPolynomial (fun _ : Fin n => θ) U P hU hP
  have hpoly := Q.continuous.tendsto (1 : ℝ) |>.comp
    (show Tendsto (fun i => 1 - (t i).val) F (𝓝 1) from
      by simpa only [sub_zero] using tendsto_const_nhds.sub ht)
  have heq (i : I) :
      (endpointMixedMass θ V (convexComb (1 - (t i).val) u p) hV
        (isThetaPshPotential_convexComb_closed hu hp
          (sub_nonneg.mpr (t i).property.2.le)
          (sub_le_self 1 (t i).property.1.le)) j).toReal = Q.eval (1 - (t i).val) := by
    have htuple : (fun k => convexComb (1 - (t i).val) (U k) (P k)) =
        endpointMixedPotential j (convexComb (1 - (t i).val) u p) V := by
      funext k
      dsimp only [U, P, endpointMixedPotential]
      split_ifs
      · rfl
      · exact ThetaCapacity.convexComb_self (sub_pos.mpr (t i).property.2)
          (by linarith [(t i).property.1]) V
    have h := globalMixedMass_convexComb_toReal_eq_eval omega hU hP
      (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)
    have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
      (fun k => (isThetaPshPotential_convexComb_closed (hU k) (hP k)
        (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)).1)
      (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
        (isThetaPshPotential_convexComb_closed hu hp
          (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)) hV)
    have he := congrArg (fun μ : Measure M => (μ univ).toReal) hm
    exact he.symm.trans h
  have h1 : Q.eval 1 = (endpointMixedMass θ V u hV hu j).toReal := by
    have htuple : (fun k => convexComb 1 (U k) (P k)) = U := by
      funext k x
      simp only [convexComb, EReal.coe_one, one_mul, sub_self,
        EReal.coe_zero, zero_mul, add_zero]
    have h := globalMixedMass_convexComb_toReal_eq_eval omega hU hP
      (a := 1) zero_le_one le_rfl
    have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
      (fun k => (isThetaPshPotential_convexComb_closed (hU k) (hP k)
        zero_le_one le_rfl).1) (fun k => (hU k).1)
    have he := congrArg (fun μ : Measure M => (μ univ).toReal) hm
    exact h.symm.trans he
  simpa only [Function.comp_def, ← heq, h1] using hpoly

variable [ConnectedSpace M]

/-- The actual finite slot polynomial produces every endpoint limit;
natural pointwise order makes the maximum tuple exactly the target tuple. -/
theorem tendsto_native_ordered_convex (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hp : IsThetaPshPotential θ.val p) (hpu : p ≤ u) {I : Type*}
    (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i => (t i).val) F (𝓝 0)) :
    let W : I → ThetaPshL1 θ.val := fun i =>
      ⟨convexComb (1 - (t i).val) u p,
        isThetaPshPotential_convexComb_closed hu hp
          (sub_nonneg.mpr (t i).property.2.le)
          (sub_le_self 1 (t i).property.1.le)⟩
    Tendsto W F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
      ⟨u, hu⟩) := by
  let W : I → ThetaPshL1 θ.val := fun i =>
    ⟨convexComb (1 - (t i).val) u p,
      isThetaPshPotential_convexComb_closed hu hp
        (sub_nonneg.mpr (t i).property.2.le)
        (sub_le_self 1 (t i).property.1.le)⟩
  let _nativeMetric : PseudoMetricSpace (ThetaPshL1 θ.val) :=
    singularityPseudoMetricSpace omega θ hbig
  let _nativeTopology : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hreal : Tendsto (fun i =>
      (singularityDistance omega θ hbig (W i).val u).toReal) F (𝓝 (0 : ℝ)) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig F
      (fun i => (W i).property) hu).mpr
    let V := thetaPshSupremum θ.val
    have hV : IsThetaPshPotential θ.val V :=
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
    have hmax (i : I) : (fun x => max ((W i).val x) (u x)) = u := by
      have hle := convexComb_mono (sub_nonneg.mpr (t i).property.2.le)
        (sub_le_self 1 (t i).property.1.le) (a := u) (b := p) (c := u) (d := u) le_rfl hpu
      rw [ThetaCapacity.convexComb_self (sub_pos.mpr (t i).property.2)
        (by linarith [(t i).property.1]) u] at hle
      exact funext fun x => max_eq_right (hle x)
    intro j
    refine ⟨tendsto_endpoint_convex_one omega hu hp hV F t ht j, ?_⟩
    simpa only [hmax] using (tendsto_const_nhds :
      Tendsto (fun _ : I => (endpointMixedMass θ V u hV hu j).toReal) F
        (𝓝 (endpointMixedMass θ V u hV hu j).toReal))
  have hdist : Tendsto (fun i => dist (W i) (⟨u, hu⟩ : ThetaPshL1 θ.val)) F
      (𝓝 (0 : ℝ)) := hreal.congr' (Eventually.of_forall fun i =>
        (dist_eq_singularityDistance_toReal omega θ hbig (W i) ⟨u, hu⟩).symm)
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

end

end SGPT.Foundations.Analysis.Pending.OrderedConvexNativeContinuity
