import SGPT.Foundations.Analysis.Pending.ActualPositiveMixedMassNativeContinuity
import SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial
import SGPT.Foundations.Analysis.Pending.FinitePolynomialEvaluationContinuity
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
import SGPT.Foundations.Analysis.Pending.SingularPositiveConvexMixedMass
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Pi

set_option autoImplicit false

/-! # Full actual independent native mixed-mass continuity

SGPT PDF0234--0237 Theorem 6.2.1. Actual positive interpolation, finite
Lagrange recovery, and finite native product sequential continuity
produce the full mixed-mass limit. No mixed limit certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualNativeMixedMassContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy MixedMass DiagonalMass
  ThetaPshL1Topology ThetaPshConvexCombination EndpointMixedMassConvexCombination
  SingularCanonicalSingularityDistance SingularMinimalCanonicalRay
  SingularCanonicalSingularityInterpolation SingularPositiveConvexMixedMass
  ActualPositiveMixedMassNativeContinuity ActualIndependentConvexMassPolynomial
  FinitePolynomialEvaluationContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual positive interpolation and finite Lagrange recovery produce the
full independent mixed-mass limit, including zero diagonal target masses. -/
theorem tendsto_globalMixedMass_of_native_sequence
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (θ a).val (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, hu j a⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j) (fun a => (hu j a).1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  let V : Fin n → M → EReal := fun a => thetaPshSupremum (θ a).val
  have hVmodel (a : Fin n) : IsModelPotential (θ a) (V a) :=
    isModelPotential_thetaPshSupremum omega (θ a) (hbig a)
  have hV (a : Fin n) : IsThetaPshPotential (θ a).val (V a) := (hVmodel a).plurisubharmonic
  have hinter (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      Tendsto (fun j => (convexMixedMassPolynomial θ (u j) V (hu j) hV).eval r) atTop
        (𝓝 ((convexMixedMassPolynomial θ v V hv hV).eval r)) := by
    have hw (j : ℕ) (a : Fin n) : IsThetaPshPotential (θ a).val
        (convexComb r (u j a) (V a)) :=
      isThetaPshPotential_convexComb_closed (hu j a) (hV a) hr0.le hr1.le
    have hz (a : Fin n) : IsThetaPshPotential (θ a).val (convexComb r (v a) (V a)) :=
      isThetaPshPotential_convexComb_closed (hv a) (hV a) hr0.le hr1.le
    have hzpos (a : Fin n) : 0 < diagonalPotentialMass (θ a)
        (convexComb r (v a) (V a)) (hz a) :=
      hasPositivePotentialMass_convexComb_of_right (hv a) (hV a) (hVmodel a).positive_mass hr0 hr1
    have hwlim (a : Fin n) : Tendsto
        (fun j => (⟨convexComb r (u j a) (V a), hw j a⟩ : ThetaPshL1 (θ a).val)) atTop
        (@nhds (ThetaPshL1 (θ a).val)
          (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
          ⟨convexComb r (v a) (V a), hz a⟩) := by
      let := singularityPseudoMetricSpace omega (θ a) (hbig a)
      let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
      exact ((continuous_native_convexComb_minimal omega (θ a) (hbig a) hr0.le hr1.le).tendsto
        (⟨v a, hv a⟩ : ThetaPshL1 (θ a).val)).comp (hlim a)
    have hm := tendsto_globalMixedMass_of_native_positive omega hbig hw hz hzpos hwlim
    have hf : globalMixedMass θ (fun a => convexComb r (v a) (V a))
        (fun a => (hz a).1) ≠ ⊤ := (globalMixedMass_lt_top omega (fun a => (hz a).1)).ne
    have hr := (ENNReal.tendsto_toReal hf).comp hm
    have hfun : (fun j => (convexMixedMassPolynomial θ (u j) V (hu j) hV).eval r) =
        fun j => (globalMixedMass θ (fun a => convexComb r (u j a) (V a))
          (fun a => (hw j a).1)).toReal :=
      funext fun j => (globalMixedMass_convexComb_toReal_eq_eval omega (hu j) hV hr0.le hr1.le).symm
    rw [hfun, ← globalMixedMass_convexComb_toReal_eq_eval omega hv hV hr0.le hr1.le]
    exact hr
  let nodes : Fin (n + 1) → ℝ := fun k => ((k.val : ℝ) + 1) / ((n : ℝ) + 2)
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hnodes0 (k : Fin (n + 1)) : 0 < nodes k := by dsimp [nodes]; positivity
  have hnodes1 (k : Fin (n + 1)) : nodes k < 1 := by
    apply (div_lt_one hden).mpr
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hnodes : Function.Injective nodes := by
    have hm : StrictMono nodes := by
      intro i j hij
      apply (div_lt_div_iff_of_pos_right hden).mpr
      have hijreal : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
      linarith
    exact hm.injective
  have ht := tendsto_eval_of_finite_evaluations atTop nodes hnodes
    (fun j => convexMixedMassPolynomial θ (u j) V (hu j) hV)
    (convexMixedMassPolynomial θ v V hv hV)
    (fun j => natDegree_convexMixedMassPolynomial_le θ (u j) V (hu j) hV)
    (natDegree_convexMixedMassPolynomial_le θ v V hv hV)
    (fun k => hinter (nodes k) (hnodes0 k) (hnodes1 k)) 1
  have heval (U : Fin n → M → EReal)
      (hU : ∀ a, IsThetaPshPotential (θ a).val (U a)) :
      (convexMixedMassPolynomial θ U V hU hV).eval 1 =
        (globalMixedMass θ U (fun a => (hU a).1)).toReal := by
    have h := (globalMixedMass_convexComb_toReal_eq_eval omega hU hV
      (a := 1) zero_le_one le_rfl).symm
    have hQ : (fun a => convexComb 1 (U a) (V a)) = U := by
      funext a x
      simp only [convexComb, EReal.coe_one, one_mul, sub_self, EReal.coe_zero,
        zero_mul, add_zero]
    simpa only [hQ] using h
  have hfun : (fun j => (convexMixedMassPolynomial θ (u j) V (hu j) hV).eval 1) =
      fun j => (globalMixedMass θ (u j) (fun a => (hu j a).1)).toReal :=
    funext fun j => heval (u j) (hu j)
  rw [hfun, heval v hv] at ht
  have he := ENNReal.continuous_ofReal.tendsto
    (globalMixedMass θ v (fun a => (hv a).1)).toReal |>.comp ht
  simpa only [Function.comp_def,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega (fun a => (hu _ a).1)).ne,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega (fun a => (hv a).1)).ne] using he

private theorem continuous_native_mass
    (omega : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a))) :
    letI _nativeMetric (a : Fin n) : PseudoMetricSpace (ThetaPshL1 (θ a).val) :=
      singularityPseudoMetricSpace omega (θ a) (hbig a)
    letI _nativeTopology (a : Fin n) : TopologicalSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
    Continuous (fun w : (a : Fin n) → ThetaPshL1 (θ a).val =>
      globalMixedMass θ (fun a => (w a).val) (fun a => (w a).property.1)) := by
  let _nativeMetric (a : Fin n) : PseudoMetricSpace (ThetaPshL1 (θ a).val) :=
    singularityPseudoMetricSpace omega (θ a) (hbig a)
  let _nativeTopology (a : Fin n) : TopologicalSpace (ThetaPshL1 (θ a).val) :=
    (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
  apply continuous_iff_seqContinuous.mpr
  intro seq q hseq
  exact tendsto_globalMixedMass_of_native_sequence omega hbig
    (fun j a => (seq j a).property) (fun a => (q a).property)
    (fun a => (tendsto_pi_nhds.mp hseq) a)

/-- The genuine finite native product mass map is actually continuous, so
slotwise native convergence along every original incoming filter produces
full independent mixed-mass convergence, including zero masses. -/
theorem tendsto_globalMixedMass_of_native
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {I : Type*} (F : Filter I)
    {u : I → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (θ a).val (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, hu j a⟩ : ThetaPshL1 (θ a).val)) F
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j) (fun a => (hu j a).1)) F
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  let _nativeMetric (a : Fin n) : PseudoMetricSpace (ThetaPshL1 (θ a).val) :=
    singularityPseudoMetricSpace omega (θ a) (hbig a)
  let _nativeTopology (a : Fin n) : TopologicalSpace (ThetaPshL1 (θ a).val) :=
    (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
  let D := (a : Fin n) → ThetaPshL1 (θ a).val
  let mass : D → ℝ≥0∞ := fun w => globalMixedMass θ (fun a => (w a).val)
    (fun a => (w a).property.1)
  have hc : Continuous mass := continuous_native_mass omega θ hbig
  let uT : I → D := fun j a => ⟨u j a, hu j a⟩
  let vT : D := fun a => ⟨v a, hv a⟩
  have ht : Tendsto uT F (𝓝 vT) := tendsto_pi_nhds.mpr hlim
  have hmass : Tendsto (mass ∘ uT) F (𝓝 (mass vT)) := (hc.tendsto vT).comp ht
  change Tendsto (mass ∘ uT) F (𝓝 (mass vT))
  exact hmass

end
end SGPT.Foundations.Analysis.Pending.ActualNativeMixedMassContinuity
