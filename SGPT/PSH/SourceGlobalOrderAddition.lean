import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceIEnvelope
import SGPT.PSH.AtlasQPSHAddition
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
import SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition

set_option autoImplicit false

/-! # Addition for the original global singularity orders

The full genuine QPSH domain is retained.  Actual native addition continuity
and the actual all-level multiplier addition theorem supply the two clauses
of the original `prop:Ppartialsum`, including zero original masses.
-/

open Set Filter
open scoped Topology

namespace SGPT.PSH.GlobalOrderAddition

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
  SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
  SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
  VariableComplexAtlas GlobalPComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem native_of_source {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem genuine_add {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
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
  simpa only [sumForm, Fintype.sum_bool, α, Bool.true_eq_false,
    Bool.false_eq_true, ↓reduceIte, one_smul] using h

private theorem native_const_iff (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (p q : ThetaPshL1 θ.val) :
    Tendsto (fun _ : ℕ => p) atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace q) ↔
      sourcePEquivalent (n := n) p.val q.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Tendsto (fun _ : ℕ => p) atTop (𝓝 q) ↔ _
  rw [tendsto_iff_dist_tendsto_zero]
  constructor
  · intro h
    have hz : dist p q = 0 := tendsto_nhds_unique tendsto_const_nhds h
    obtain ⟨m, _, _, _, hm⟩ :=
      exists_tendsto_singularityDistance omega θ hbig p.property q.property
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hm, EReal.toReal_coe] at hz
    have hD : singularityDistance omega θ hbig p.val q.val = 0 := by
      simpa only [hz, EReal.coe_zero] using hm
    exact (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      p.property q.property).mp hD
  · intro h
    have hD := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      p.property q.property).mpr h
    have hd : dist p q = 0 := by
      rw [dist_eq_singularityDistance_toReal omega θ hbig, hD, EReal.toReal_zero]
    simpa only [hd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Actual global P-equivalence is preserved by literal extended addition on
the entire genuine source QPSH domain. Positive common backgrounds are produced. -/
theorem sourcePEquivalent_add (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b)
    (hua : sourcePEquivalent (n := n) u a) (hvb : sourcePEquivalent (n := n) v b) :
    sourcePEquivalent (n := n) (fun x => u x + v x) (fun x => a x + b x) := by
  obtain ⟨C, hC, huC, haC, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (native_of_source hu) (native_of_source ha)
  obtain ⟨D, hD, hvD, hbD, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (native_of_source hv) (native_of_source hb)
  let θ : ClosedRealOneOneForm n M := C • omega.form
  let σ : ClosedRealOneOneForm n M := D • omega.form
  have hθ : IsBigClass (RealBottChern.ofRepresentative θ) :=
    PluripolarCapacityDichotomy.isBigClass_kahler (KahlerBackground.smul hC omega)
  have hσ : IsBigClass (RealBottChern.ofRepresentative σ) :=
    PluripolarCapacityDichotomy.isBigClass_kahler (KahlerBackground.smul hD omega)
  have hγ : IsBigClass (RealBottChern.ofRepresentative (θ + σ)) :=
    PluripolarCapacityDichotomy.isBigClass_kahler
      ((KahlerBackground.smul hC omega).add (KahlerBackground.smul hD omega))
  let p : ThetaPshL1 θ.val := ⟨u, huC⟩
  let q : ThetaPshL1 σ.val := ⟨v, hvD⟩
  let r : ThetaPshL1 θ.val := ⟨a, haC⟩
  let s : ThetaPshL1 σ.val := ⟨b, hbD⟩
  have hp := (native_const_iff omega θ hθ p r).mpr hua
  have hq := (native_const_iff omega σ hσ q s).mpr hvb
  have hsum := SingularNativeAdditionContinuity.tendsto_native_add omega θ σ hθ hσ
    (atTop : Filter ℕ) (fun _ => p) (fun _ => q) r s hp hq
  exact (native_const_iff omega (θ + σ) hγ
    ⟨fun x => u x + v x, genuine_add huC hvD⟩
    ⟨fun x => a x + b x, genuine_add haC hbD⟩).mp hsum

/-- The original GLOBAL P-order respects addition for four genuine QPSH inputs. -/
theorem sourcePOrder_add (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b)
    (hua : sourcePOrder (n := n) u a) (hvb : sourcePOrder (n := n) v b) :
    sourcePOrder (n := n) (fun x => u x + v x) (fun x => a x + b x) := by
  have hU := hu.max_compactKahler omega ha
  have hV := hv.max_compactKahler omega hb
  have hUa := (GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    omega (native_of_source hu) (native_of_source ha)).mp hua
  have hVb := (GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    omega (native_of_source hv) (native_of_source hb)).mp hvb
  have hsum := sourcePEquivalent_add omega hU hV ha hb hUa hVb
  have hmore : MoreSingularOn (fun x => u x + v x)
      (fun x => max (u x) (a x) + max (v x) (b x)) univ :=
    MoreSingularOn.of_le fun x _ =>
      add_le_add (le_max_left (u x) (a x)) (le_max_left (v x) (b x))
  have hstep := GlobalQuasiPshPositivePDomain.sourcePOrder_of_moreSingularOn_globalQuasiPsh
    omega (native_of_source (hu.add hv)) (native_of_source (hU.add hV)) hmore
  exact SingularGlobalPOrder.SourcePOrder.trans omega hstep hsum.1

/-- Actual all-level source multiplier order respects addition, retaining both
genuine QPSH sum domains and the exact all-chart Haar/germ inclusions. -/
theorem sourceIOrder_add (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b)
    (hua : sourceIOrder (ofFixedModel n M) u a)
    (hvb : sourceIOrder (ofFixedModel n M) v b) :
    sourceIOrder (ofFixedModel n M) (fun x => u x + v x) (fun x => a x + b x) := by
  obtain ⟨C, _, huC, haC, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (native_of_source hu) (native_of_source ha)
  obtain ⟨D, _, hvD, hbD, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      (native_of_source hv) (native_of_source hb)
  exact (sourceIOrder_iff_native (hu.add hv) (ha.add hb)).mpr
    (ActualMultiplierOrderAddition.iOrderOnManifold_add huC hvD haC hbD
      ((sourceIOrder_iff_native hu ha).mp hua) ((sourceIOrder_iff_native hv hb).mp hvb))

/-- The complete original `prop:Ppartialsum`: both GLOBAL P-order and actual
source I-order are preserved under addition of four genuine QPSH potentials. -/
theorem sourceGlobalOrder_addition (omega : KahlerBackground n M)
    {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) (hv : (ofFixedModel n M).IsQPSH v)
    (ha : (ofFixedModel n M).IsQPSH a) (hb : (ofFixedModel n M).IsQPSH b) :
    (sourcePOrder (n := n) u a → sourcePOrder (n := n) v b →
      sourcePOrder (n := n) (fun x => u x + v x) (fun x => a x + b x)) ∧
    (sourceIOrder (ofFixedModel n M) u a → sourceIOrder (ofFixedModel n M) v b →
      sourceIOrder (ofFixedModel n M) (fun x => u x + v x) (fun x => a x + b x)) :=
  ⟨sourcePOrder_add omega hu hv ha hb, sourceIOrder_add omega hu hv ha hb⟩

end
end SGPT.PSH.GlobalOrderAddition
