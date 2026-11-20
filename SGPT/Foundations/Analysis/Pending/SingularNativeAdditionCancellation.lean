import SGPT.Foundations.Analysis.Pending.ActualAdditionEndpointMassRecovery
import SGPT.Foundations.Analysis.Pending.SingularNativeMaximumContinuity

set_option autoImplicit false

/-! # Actual native cancellation of either genuine potential summand

SGPT PDF0242, the two cancellation directions of Theorem 6.2.2.
The actual endpoint recovery, full mass criterion, and genuine maximum
continuity retain all original zero-mass cases, with no positivity input.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularNativeAdditionCancellation

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  MixedMass GlobalNonPluripolar GlobalMultilinearExpansion
  MixedSummandCapacityDomination ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularNativeAdditionContinuity
  ActualAdditionEndpointMassRecovery SingularNativeMaximumContinuity
  SingularCanonicalSingularityMassComparison SingularCanonicalSingularityMaximumCriterion
  SingularMinimalCanonicalRay

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
  have eab : a = b := funext fun i => Subtype.ext (hfamily i)
  have epq : p = q := Subtype.ext htarget
  simpa only [eab, epq] using hlim

/-- Ordered cancellation uses the full original endpoint and maximum mass
criterion, so zero target mass is allowed. -/
theorem tendsto_native_of_native_and_native_add_of_le
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
    (hle : ∀ i, q.val ≤ (b i).val) :
    Tendsto b F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q) := by
  apply (tendsto_native_iff_endpointMixedMass omega σ hσ F b q).mpr
  intro j
  have hR := (isModelPotential_thetaPshSupremum omega σ hσ).plurisubharmonic
  have h := tendsto_endpointMixedMass_of_native_and_native_add omega θ σ hθ hσ F
    a b p q ha hsum hR j
  refine ⟨h, ?_⟩
  have heq (i : I) : (fun x => max ((b i).val x) (q.val x)) = (b i).val := by
    funext x
    exact max_eq_left (hle i x)
  convert h using 1
  funext i
  simp only [heq i]

/-- General cancellation of the second summand. All its original target
masses may be zero; the maximum family is produced by genuine continuity. -/
theorem tendsto_native_of_native_and_native_add
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
        ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩)) :
    Tendsto b F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q) := by
  let γ := θ + σ
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := bigAdd hθ q.property
  let S : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => (a i).val x + (b i).val x, genuineAdd (a i).property (b i).property⟩
  let C : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => (a i).val x + q.val x, genuineAdd (a i).property q.property⟩
  let T : ThetaPshL1 γ.val :=
    ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩
  let B : I → ThetaPshL1 σ.val := fun i =>
    ⟨fun x => max ((b i).val x) (q.val x), IsThetaPshPotential.max (b i).property q.property⟩
  have hconst : Tendsto (fun _ : I => q) F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q) :=
    @tendsto_const_nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace I q F
  have hC : Tendsto C F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace T) :=
    tendsto_native_add omega θ σ hθ hσ F a (fun _ => q) p q ha hconst
  have hmax := tendsto_native_max omega γ hγ F S C T T hsum hC
  have hmaxSum : Tendsto (fun i => (⟨fun x => (a i).val x + (B i).val x,
      genuineAdd (a i).property (B i).property⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace T) := by
    exact nativeCongr omega rfl hγ hγ F
      (fun i => ⟨fun x => max ((S i).val x) ((C i).val x),
        IsThetaPshPotential.max (S i).property (C i).property⟩)
      (fun i => ⟨fun x => (a i).val x + (B i).val x,
        genuineAdd (a i).property (B i).property⟩)
      ⟨fun x => max (T.val x) (T.val x), IsThetaPshPotential.max T.property T.property⟩ T
      (fun i => funext fun x => (add_max ((a i).val x) ((b i).val x) (q.val x)).symm)
      (funext fun _ => max_self _) hmax
  have hB := tendsto_native_of_native_and_native_add_of_le omega θ σ hθ hσ F
    a B p q ha hmaxSum (fun i x => le_max_right ((b i).val x) (q.val x))
  apply (tendsto_native_iff_max_and_endpointMixedMass omega σ hσ F b q).mpr
  refine ⟨hB, ?_⟩
  intro j
  exact tendsto_endpointMixedMass_of_native_and_native_add omega θ σ hθ hσ F
    a b p q ha hsum (isModelPotential_thetaPshSupremum omega σ hσ).plurisubharmonic j

/-- General cancellation of the first summand, with exact original sum
background and potential transport after interchanging the summands. -/
theorem tendsto_native_of_native_right_and_native_add
    (omega : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 θ.val) (b : I → ThetaPshL1 σ.val)
    (p : ThetaPshL1 θ.val) (q : ThetaPshL1 σ.val)
    (hb : Tendsto b F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q))
    (hsum : Tendsto (fun i => (⟨fun x => (a i).val x + (b i).val x,
        genuineAdd (a i).property (b i).property⟩ : ThetaPshL1 (θ + σ).val)) F
      (@nhds (ThetaPshL1 (θ + σ).val)
        (singularityPseudoMetricSpace omega (θ + σ) (bigAdd hθ q.property)).toUniformSpace.toTopologicalSpace
        ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩)) :
    Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p) := by
  have hswap : Tendsto (fun i => (⟨fun x => (b i).val x + (a i).val x,
      genuineAdd (b i).property (a i).property⟩ : ThetaPshL1 (σ + θ).val)) F
      (@nhds (ThetaPshL1 (σ + θ).val)
        (singularityPseudoMetricSpace omega (σ + θ) (bigAdd hσ p.property)).toUniformSpace.toTopologicalSpace
        ⟨fun x => q.val x + p.val x, genuineAdd q.property p.property⟩) :=
    nativeCongr omega (add_comm θ σ) (bigAdd hθ q.property) (bigAdd hσ p.property) F
      (fun i => ⟨fun x => (a i).val x + (b i).val x, genuineAdd (a i).property (b i).property⟩)
      (fun i => ⟨fun x => (b i).val x + (a i).val x, genuineAdd (b i).property (a i).property⟩)
      ⟨fun x => p.val x + q.val x, genuineAdd p.property q.property⟩
      ⟨fun x => q.val x + p.val x, genuineAdd q.property p.property⟩
      (fun i => funext fun x => add_comm ((a i).val x) ((b i).val x))
      (funext fun x => add_comm (p.val x) (q.val x)) hsum
  exact tendsto_native_of_native_and_native_add omega σ θ hσ hθ F b a q p hb hswap

end
end SGPT.Foundations.Analysis.Pending.SingularNativeAdditionCancellation
