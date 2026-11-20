import SGPT.Foundations.Analysis.Pending.ActualPotentialSumMassPolynomial
import SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityScalarEquivalence
import SGPT.Foundations.Analysis.Pending.FinitePolynomialEvaluationContinuity

set_option autoImplicit false

/-! # Actual endpoint mass recovery from a native summand and native sum

SGPT PDF0242 (6.26). Positive scaling and actual addition produce the
positive-node mass limits; actual Lagrange recovery produces the original
constant term. No scaled-sum limit or mass-recovery certificate is an input.
-/

open Set Filter MeasureTheory Polynomial
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualAdditionEndpointMassRecovery

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  MixedMass GlobalNonPluripolar GlobalDiagonalScaling GlobalMultilinearExpansion
  MixedSummandCapacityDomination ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularNativeAdditionContinuity
  SingularCanonicalSingularityScalarEquivalence ActualPositiveClassScaling
  ActualNativeMixedMassContinuity ActualPotentialSumMassPolynomial
  FinitePolynomialEvaluationContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem genuineAdd {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem bigAdd {θ σ : ClosedRealOneOneForm n M} {v : M → EReal}
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hv : IsThetaPshPotential σ.val v) :
    IsBigClass (RealBottChern.ofRepresentative (θ + σ)) := by
  obtain ⟨T⟩ := hθ
  refine ⟨{
    representative := T.representative + σ
    represents := by simp only [RealBottChern.ofRepresentative_add, T.represents]
    potential := fun x => T.potential x + v x
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have h := genuineAdd T.strictlyPsh hv
  have heq : (T.representative - T.lowerBound.form) + σ =
      (T.representative + σ) - T.lowerBound.form := by abel
  simpa only [heq] using h

private theorem nativeCongr (omega : KahlerBackground n M)
    {α β : ClosedRealOneOneForm n M} (hform : α = β)
    (hα : IsBigClass (RealBottChern.ofRepresentative α))
    (hβ : IsBigClass (RealBottChern.ofRepresentative β)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 α.val) (b : I → ThetaPshL1 β.val)
    (p : ThetaPshL1 α.val) (q : ThetaPshL1 β.val)
    (hfamily : ∀ i, (a i).val = (b i).val) (htarget : p.val = q.val)
    (hlim : Tendsto a F (@nhds (ThetaPshL1 α.val)
      (singularityPseudoMetricSpace omega α hα).toUniformSpace.toTopologicalSpace p)) :
    Tendsto b F (@nhds (ThetaPshL1 β.val)
      (singularityPseudoMetricSpace omega β hβ).toUniformSpace.toTopologicalSpace q) := by
  subst β
  have eab : a = b := _root_.funext fun i => Subtype.ext (hfamily i)
  have epq : p = q := Subtype.ext htarget
  simpa only [eab, epq] using hlim

private theorem scaledSumNative (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 θ.val) (b : I → ThetaPshL1 σ.val)
    (p : ThetaPshL1 θ.val) (q : ThetaPshL1 σ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p))
    (hsum : Tendsto (fun i => (⟨fun x => (a i).val x + (b i).val x,
        genuineAdd (a i).property (b i).property⟩ : ThetaPshL1 (θ + σ).val)) F
      (@nhds (ThetaPshL1 (θ + σ).val)
        (singularityPseudoMetricSpace omega (θ + σ) (bigAdd hθ q.property)).toUniformSpace.toTopologicalSpace
        ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩))
    {c : ℝ} (hc : 1 < c) :
    let hcθ : IsBigClass (RealBottChern.ofRepresentative (c • θ)) := by
      simpa only [RealBottChern.ofRepresentative_smul] using
        isBigClass_positive_smul hθ (zero_lt_one.trans hc)
    let Csum : I → ThetaPshL1 (c • θ + σ).val := fun i =>
      ⟨fun x => (c : EReal) * (a i).val x + (b i).val x,
        genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul
          (a i).property (zero_lt_one.trans hc)) (b i).property⟩
    Tendsto Csum F (@nhds (ThetaPshL1 (c • θ + σ).val)
      (singularityPseudoMetricSpace omega (c • θ + σ) (bigAdd hcθ q.property)).toUniformSpace.toTopologicalSpace
      ⟨fun x => (c : EReal) * p.val x + q.val x,
        genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul
          p.property (zero_lt_one.trans hc)) q.property⟩) := by
  let d := c - 1
  have hd : 0 < d := sub_pos.mpr hc
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hD : IsBigClass (RealBottChern.ofRepresentative (d • θ)) := by
    simpa only [RealBottChern.ofRepresentative_smul] using isBigClass_positive_smul hθ hd
  have hC : IsBigClass (RealBottChern.ofRepresentative (c • θ)) := by
    simpa only [RealBottChern.ofRepresentative_smul] using isBigClass_positive_smul hθ hc0
  let A : I → ThetaPshL1 (d • θ).val := fun i =>
    ⟨fun x => (d : EReal) * (a i).val x,
      RestrictedApproximantComparison.isThetaPshPotential_smul (a i).property hd⟩
  let P : ThetaPshL1 (d • θ).val :=
    ⟨fun x => (d : EReal) * p.val x,
      RestrictedApproximantComparison.isThetaPshPotential_smul p.property hd⟩
  let S : I → ThetaPshL1 (θ + σ).val := fun i =>
    ⟨fun x => (a i).val x + (b i).val x, genuineAdd (a i).property (b i).property⟩
  let T : ThetaPshL1 (θ + σ).val :=
    ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩
  have hA : Tendsto A F (@nhds (ThetaPshL1 (d • θ).val)
      (singularityPseudoMetricSpace omega (d • θ) hD).toUniformSpace.toTopologicalSpace P) :=
    (tendsto_native_positive_smul_iff omega θ hθ hd F a p).mpr ha
  have h := tendsto_native_add omega (d • θ) (θ + σ) hD (bigAdd hθ q.property)
    F A S P T hA hsum
  have heq : d • θ + (θ + σ) = c • θ + σ := by
    dsimp only [d]
    module
  have hpot (u v : EReal) : (d : EReal) * u + (u + v) = (c : EReal) * u + v := by
    have hd1 : d + 1 = c := by dsimp only [d]; ring
    calc
      _ = ((d : EReal) * u + (1 : EReal) * u) + v := by simp only [one_mul, add_assoc]
      _ = ((d : EReal) + (1 : EReal)) * u + v :=
        congrArg (fun z => z + v) (EReal.right_distrib_of_nonneg
          (EReal.coe_nonneg.mpr hd.le) zero_le_one).symm
      _ = _ := by rw [← EReal.coe_one, ← EReal.coe_add, hd1]
  exact nativeCongr omega heq (bigAdd hD T.property) (bigAdd hC q.property) F
    (fun i => ⟨fun x => (A i).val x + (S i).val x, genuineAdd (A i).property (S i).property⟩)
    (fun i => ⟨fun x => (c : EReal) * (a i).val x + (b i).val x,
      genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul (a i).property hc0)
        (b i).property⟩)
    ⟨fun x => P.val x + T.val x, genuineAdd P.property T.property⟩
    ⟨fun x => (c : EReal) * p.val x + q.val x,
      genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul p.property hc0) q.property⟩
    (fun i => _root_.funext fun x => hpot ((a i).val x) ((b i).val x))
    (_root_.funext fun x => hpot (p.val x) (q.val x)) h

/-- Actual native convergence of one summand and the sum produces every
original endpoint mixed-mass limit of the other summand. -/
theorem tendsto_endpointMixedMass_of_native_and_native_add
    (omega : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 θ.val) (b : I → ThetaPshL1 σ.val)
    (p : ThetaPshL1 θ.val) (q : ThetaPshL1 σ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p))
    (hsum : Tendsto (fun i => (⟨fun x => (a i).val x + (b i).val x,
        genuineAdd (a i).property (b i).property⟩ : ThetaPshL1 (θ + σ).val)) F
      (@nhds (ThetaPshL1 (θ + σ).val)
        (singularityPseudoMetricSpace omega (θ + σ) (bigAdd hθ q.property)).toUniformSpace.toTopologicalSpace
        ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩))
    {R : M → EReal} (hR : IsThetaPshPotential σ.val R) (j : Fin (n + 1)) :
    Tendsto (fun i => endpointMixedMass σ R (b i).val hR (b i).property j) F
      (𝓝 (endpointMixedMass σ R q.val hR q.property j)) := by
  classical
  let poly : I → ℝ[X] := fun i => potentialSumEndpointMassPolynomial θ σ
    (a i).val (b i).val R (a i).property (b i).property hR j
  let target := potentialSumEndpointMassPolynomial θ σ p.val q.val R p.property q.property hR j
  have hpositive (c : ℝ) (hc : 1 < c) : Tendsto (fun i => (poly i).eval c) F
      (𝓝 (target.eval c)) := by
    have hc0 : 0 < c := zero_lt_one.trans hc
    have hcθ : IsBigClass (RealBottChern.ofRepresentative (c • θ)) := by
      simpa only [RealBottChern.ofRepresentative_smul] using isBigClass_positive_smul hθ hc0
    have hcγ : IsBigClass (RealBottChern.ofRepresentative (c • θ + σ)) :=
      bigAdd hcθ q.property
    let η : Fin n → ClosedRealOneOneForm n M := fun k =>
      if k.val < j.val then c • θ + σ else σ
    let U : I → Fin n → M → EReal := fun i k =>
      if k.val < j.val then (fun x => (c : EReal) * (a i).val x + (b i).val x) else R
    let T : Fin n → M → EReal := fun k =>
      if k.val < j.val then (fun x => (c : EReal) * p.val x + q.val x) else R
    have hη (k : Fin n) : IsBigClass (RealBottChern.ofRepresentative (η k)) := by
      dsimp only [η]
      split_ifs <;> first | exact hcγ | exact hσ
    have hU (i : I) (k : Fin n) : IsThetaPshPotential (η k).val (U i k) := by
      dsimp only [η, U]
      split_ifs
      · exact genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul (a i).property hc0)
          (b i).property
      · exact hR
    have hT (k : Fin n) : IsThetaPshPotential (η k).val (T k) := by
      dsimp only [η, T]
      split_ifs
      · exact genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul p.property hc0)
          q.property
      · exact hR
    have hC := scaledSumNative omega θ σ hθ F a b p q ha hsum hc
    have hconst : Tendsto (fun _ : I => (⟨R, hR⟩ : ThetaPshL1 σ.val)) F
        (@nhds (ThetaPshL1 σ.val)
          (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace ⟨R, hR⟩) :=
      @tendsto_const_nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace
        I ⟨R, hR⟩ F
    have hslots (k : Fin n) : Tendsto
        (fun i => (⟨U i k, hU i k⟩ : ThetaPshL1 (η k).val)) F
        (@nhds (ThetaPshL1 (η k).val)
          (singularityPseudoMetricSpace omega (η k) (hη k)).toUniformSpace.toTopologicalSpace
          ⟨T k, hT k⟩) := by
      by_cases hk : k.val < j.val
      · have heq : c • θ + σ = η k := by simp only [η, hk, ↓reduceIte]
        exact nativeCongr omega heq hcγ (hη k) F
          (fun i => ⟨fun x => (c : EReal) * (a i).val x + (b i).val x,
            genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul
              (a i).property hc0) (b i).property⟩)
          (fun i => ⟨U i k, hU i k⟩)
          ⟨fun x => (c : EReal) * p.val x + q.val x,
            genuineAdd (RestrictedApproximantComparison.isThetaPshPotential_smul p.property hc0)
              q.property⟩
          ⟨T k, hT k⟩ (fun _ => by simp only [U, hk, ↓reduceIte])
          (by simp only [T, hk, ↓reduceIte]) hC
      · have heq : σ = η k := by simp only [η, hk, ↓reduceIte]
        exact nativeCongr omega heq hσ (hη k) F (fun _ => ⟨R, hR⟩)
          (fun i => ⟨U i k, hU i k⟩) ⟨R, hR⟩ ⟨T k, hT k⟩
          (fun _ => by simp only [U, hk, ↓reduceIte])
          (by simp only [T, hk, ↓reduceIte]) hconst
    have hm := tendsto_globalMixedMass_of_native omega hη F hU hT hslots
    have hmreal := (ENNReal.tendsto_toReal (globalMixedMass_lt_top omega (fun k => (hT k).1)).ne).comp hm
    have hfun : (fun i => (poly i).eval c) =
        fun i => (globalMixedMass η (U i) (fun k => (hU i k).1)).toReal := by
      funext i
      exact (globalMixedMass_potential_sum_toReal_eq_eval omega (a i).property
        (b i).property hR j hc0.le).symm
    have htarget : target.eval c = (globalMixedMass η T (fun k => (hT k).1)).toReal :=
      (globalMixedMass_potential_sum_toReal_eq_eval omega p.property q.property hR j hc0.le).symm
    rw [hfun, htarget]
    exact hmreal
  let nodes : Fin (n + 1) → ℝ := fun k => (k.val : ℝ) + 2
  have hnodes : Function.Injective nodes := by
    intro k l h
    apply Fin.ext
    have he : (k.val : ℝ) = (l.val : ℝ) := add_right_cancel h
    exact_mod_cast he
  have hnode (k : Fin (n + 1)) : 1 < nodes k := by
    dsimp only [nodes]
    have hk : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
    linarith
  have hzero := tendsto_eval_of_finite_evaluations F nodes hnodes poly target
    (fun i => natDegree_potentialSumEndpointMassPolynomial_le θ σ (a i).val (b i).val R
      (a i).property (b i).property hR j)
    (natDegree_potentialSumEndpointMassPolynomial_le θ σ p.val q.val R p.property q.property hR j)
    (fun k => hpositive (nodes k) (hnode k)) 0
  have hreal : Tendsto (fun i => (endpointMixedMass σ R (b i).val hR (b i).property j).toReal) F
      (𝓝 ((endpointMixedMass σ R q.val hR q.property j).toReal)) := by
    simpa only [poly, target, eval_zero_potentialSumEndpointMassPolynomial omega] using hzero
  have hfin (w : ThetaPshL1 σ.val) : endpointMixedMass σ R w.val hR w.property j ≠ ⊤ :=
    (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic σ j w.val R w.property hR)).ne
  have h := (ENNReal.continuous_ofReal.tendsto
    (endpointMixedMass σ R q.val hR q.property j).toReal).comp hreal
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (hfin _)] using h

end
end SGPT.Foundations.Analysis.Pending.ActualAdditionEndpointMassRecovery
