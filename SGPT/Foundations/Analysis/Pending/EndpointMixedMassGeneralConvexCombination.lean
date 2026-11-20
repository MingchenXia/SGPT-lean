import SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false

/-! # Actual endpoint mixed masses for two independent potentials

SGPT `cor:lineardsconv`: the actual independent-slot mass polynomial is
specialized to the endpoint tuples for two arbitrary potentials and a third
reference. It supplies the mass limits, and the literal maximum identity
then supplies general interpolation convergence in the native dS topology.
No mass limit or distance estimate is an input.
-/

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeEnergy ThetaPshConvexCombination ThetaPshL1Topology
  EndpointMixedMassConvexCombination ActualIndependentConvexMassPolynomial
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison SingularCanonicalSingularityInterpolation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem endpoint_genuine {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (j : Fin (n + 1)) (k : Fin n) :
    IsThetaPshPotential θ.val (endpointMixedPotential j u p k) := by
  dsimp only [endpointMixedPotential]
  split_ifs <;> first | exact hu | exact hp

/-- The actual independent-slot finite selector polynomial with endpoint
tuples (u,p) and (v,p). Its coefficients are genuine finite mixed masses. -/
def endpointConvexMassPolynomial {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) (j : Fin (n + 1)) : ℝ[X] :=
  convexMixedMassPolynomial (fun _ : Fin n => θ)
    (endpointMixedPotential j u p) (endpointMixedPotential j v p)
    (endpoint_genuine hu hp j) (endpoint_genuine hv hp j)

private theorem convexComb_self_closed {N : Type*} (p : N → EReal)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : convexComb a p p = p := by
  by_cases h0 : a = 0
  · subst a
    funext x
    simp only [convexComb, EReal.coe_zero, zero_mul, sub_zero,
      EReal.coe_one, one_mul, zero_add]
  by_cases h1 : a = 1
  · subst a
    funext x
    simp only [convexComb, EReal.coe_one, one_mul, sub_self,
      EReal.coe_zero, zero_mul, add_zero]
  exact ThetaCapacity.convexComb_self
    (lt_of_le_of_ne ha0 (Ne.symm h0)) (lt_of_le_of_ne ha1 h1) p

/-- Genuine mixed multilinearity identifies the actual endpoint mass with
the same finite polynomial at every closed coefficient, including poles. -/
theorem endpointMixedMass_general_convexComb_eq_eval (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (j : Fin (n + 1)) :
    (endpointMixedMass θ p (convexComb a u v) hp
      (isThetaPshPotential_convexComb_closed hu hv ha0 ha1) j).toReal =
      (endpointConvexMassPolynomial hu hv hp j).eval a := by
  have htuple : (fun k => convexComb a (endpointMixedPotential j u p k)
      (endpointMixedPotential j v p k)) =
      endpointMixedPotential j (convexComb a u v) p := by
    funext k
    dsimp only [endpointMixedPotential]
    split_ifs
    · rfl
    · exact convexComb_self_closed p ha0 ha1
  have h := globalMixedMass_convexComb_toReal_eq_eval omega
    (endpoint_genuine hu hp j) (endpoint_genuine hv hp j) ha0 ha1
  have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
    (fun k => (isThetaPshPotential_convexComb_closed
      (endpoint_genuine hu hp j k) (endpoint_genuine hv hp j k) ha0 ha1).1)
    (endpointMixedPotential_thetaPlurisubharmonic θ j _ p
      (isThetaPshPotential_convexComb_closed hu hv ha0 ha1) hp)
  have he := congrArg (fun μ : Measure M => (μ univ).toReal) hm
  exact he.symm.trans h

/-- Every endpoint mixed mass is continuous on the entire closed parameter
interval, with two independent endpoints and the same third reference. -/
theorem continuous_toReal_endpointMixedMass_general_convexComb
    (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) (j : Fin (n + 1)) :
    Continuous (fun a : Icc (0 : ℝ) 1 =>
      (endpointMixedMass θ p (convexComb a.val u v) hp
        (isThetaPshPotential_convexComb_closed hu hv a.property.1 a.property.2) j).toReal) := by
  have heq (a : Icc (0 : ℝ) 1) :=
    endpointMixedMass_general_convexComb_eq_eval omega hu hv hp
      a.property.1 a.property.2 j
  simp_rw [heq]
  exact (endpointConvexMassPolynomial hu hv hp j).continuous.comp continuous_subtype_val

/-- Coefficients tending to zero give the literal original right endpoint
mass, without positive-mass or minimal-singularity hypotheses. -/
theorem tendsto_toReal_endpointMixedMass_general_convexComb_zero
    (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) {I : Type*} (F : Filter I)
    (t : I → Ioo (0 : ℝ) 1) (ht : Tendsto (fun i => (t i).val) F (𝓝 0))
    (j : Fin (n + 1)) :
    Tendsto (fun i => (endpointMixedMass θ p (convexComb (t i).val u v) hp
      (isThetaPshPotential_convexComb_closed hu hv
        (t i).property.1.le (t i).property.2.le) j).toReal) F
      (𝓝 (endpointMixedMass θ p v hp hv j).toReal) := by
  let a : I → Icc (0 : ℝ) 1 := fun i =>
    ⟨(t i).val, (t i).property.1.le, (t i).property.2.le⟩
  have ha : Tendsto a F (𝓝 (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1)) := by
    exact tendsto_subtype_rng.mpr ht
  have hzero : convexComb 0 u v = v := by
    funext x
    simp only [convexComb, EReal.coe_zero, zero_mul, sub_zero,
      EReal.coe_one, one_mul, zero_add]
  simpa only [Function.comp_def, hzero] using
    ((continuous_toReal_endpointMixedMass_general_convexComb omega hu hv hp j).tendsto
      (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1)).comp ha

variable [ConnectedSpace M]

/-- Whole original two-potential interpolation in the actual native dS
topology. Finite mixed-mass polynomials supply both original limit families;
the exact maximum identity retains all poles and zero original masses. -/
theorem tendsto_native_general_convex_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) {I : Type*} (F : Filter I)
    (t : I → Ioo (0 : ℝ) 1) (ht : Tendsto (fun i => (t i).val) F (𝓝 0)) :
    let W : I → ThetaPshL1 θ.val := fun i =>
      ⟨convexComb (t i).val u v,
        isThetaPshPotential_convexComb_closed hu hv
          (t i).property.1.le (t i).property.2.le⟩
    Tendsto W F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
      ⟨v, hv⟩) := by
  let W : I → ThetaPshL1 θ.val := fun i =>
    ⟨convexComb (t i).val u v,
      isThetaPshPotential_convexComb_closed hu hv
        (t i).property.1.le (t i).property.2.le⟩
  let _nativeMetric : PseudoMetricSpace (ThetaPshL1 θ.val) :=
    singularityPseudoMetricSpace omega θ hbig
  let _nativeTopology : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hmax (i : I) : (fun x => max ((W i).val x) (v x)) =
      convexComb (t i).val (fun x => max (u x) (v x)) v := by
    change (fun x => max (convexComb (t i).val u v x) (v x)) = _
    have hs := ThetaCapacity.convexComb_self (t i).property.1 (t i).property.2 v
    calc
      _ = (fun x => max (convexComb (t i).val u v x)
        (convexComb (t i).val v v x)) := by rw [hs]
      _ = _ := convexComb_max_common u v v (t i).property.1.le
  have hreal : Tendsto (fun i =>
      (singularityDistance omega θ hbig (W i).val v).toReal) F (𝓝 (0 : ℝ)) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig
      F (fun i => (W i).property) hv).mpr
    intro j
    refine ⟨tendsto_toReal_endpointMixedMass_general_convexComb_zero
      omega hu hv hV F t ht j, ?_⟩
    simpa only [hmax] using
      tendsto_toReal_endpointMixedMass_general_convexComb_zero
        omega (IsThetaPshPotential.max hu hv) hv hV F t ht j
  have hdist : Tendsto (fun i => dist (W i) (⟨v, hv⟩ : ThetaPshL1 θ.val)) F
      (𝓝 (0 : ℝ)) := hreal.congr' (Eventually.of_forall fun i =>
        (dist_eq_singularityDistance_toReal omega θ hbig (W i) ⟨v, hv⟩).symm)
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

end

end SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination
