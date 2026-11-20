import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
import SGPT.Foundations.Analysis.Pending.SingularConvexMixedMassContinuity

set_option autoImplicit false

/-! # Actual native singularity continuity of minimal-potential interpolation

SGPT PDF0233--0234 Lemmas 6.2.4--6.2.5. Actual finite-selector endpoint
mass polynomials and the actual native mass filter criterion produce
interpolation continuity, without general mixed-mass continuity as an input.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  GlobalNonPluripolar MixedMassProductCalculus ThetaPshConvexCombination
  EndpointMixedMassConvexCombination SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology
  SingularConvexMixedMassContinuity

noncomputable section

private theorem convexComb_self {X : Type*} (u : X → EReal)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : convexComb a u u = u := by
  funext x
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  change (a : EReal) * u x + ((1 - a : ℝ) : EReal) * u x = u x
  induction u x using EReal.rec with
  | bot => simp only [EReal.coe_mul_bot_of_pos ha0, EReal.coe_mul_bot_of_pos hb,
      EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos ha0, EReal.coe_mul_top_of_pos hb,
      EReal.top_add_top]
  | coe r =>
    simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring

private theorem convexComb_sub_const_first {X : Type*} (u p : X → EReal)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (C : ℝ) :
    convexComb a (fun x => u x - (C : EReal)) p =
      fun x => convexComb a u p x - ((a * C : ℝ) : EReal) := by
  funext x
  have h := GlobalSlotLinear.ereal_linear_add_coe ha0 (sub_pos.mpr ha1)
    (u x) (p x) (-C) 0
  simpa only [convexComb, sub_eq_add_neg, ← EReal.coe_neg, mul_zero, add_zero,
    EReal.coe_zero, mul_neg] using h.symm

private theorem le_convexComb_of_le {X : Type*} (u p : X → EReal) (h : u ≤ p)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : u ≤ convexComb a u p := by
  calc
    u = convexComb a u u := (convexComb_self u ha0 ha1).symm
    _ ≤ convexComb a u p := convexComb_mono ha0.le ha1.le le_rfl h

/-- Common nonnegative convex interpolation commutes with the actual
pointwise maximum, including poles and coefficient endpoints. -/
theorem convexComb_max_common {X : Type*} (u v p : X → EReal)
    {a : ℝ} (ha0 : 0 ≤ a) :
    (fun x => max (convexComb a u p x) (convexComb a v p x)) =
      convexComb a (fun x => max (u x) (v x)) p := by
  funext x
  simp only [convexComb]
  rcases le_total (u x) (v x) with huv | hvu
  · rw [max_eq_right huv, max_eq_right (add_le_add
      (mul_le_mul_of_nonneg_left huv (EReal.coe_nonneg.mpr ha0)) le_rfl)]
  · rw [max_eq_left hvu, max_eq_left (add_le_add
      (mul_le_mul_of_nonneg_left hvu (EReal.coe_nonneg.mpr ha0)) le_rfl)]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_sub_const_le_minimal {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ C : ℝ, (fun x => u x - (C : EReal)) ≤ thetaPshSupremum θ.val := by
  let C : ℝ := (⨆ x, u x).toReal
  have hf := ModelRaySupremum.iSup_ne_top_ne_bot hu
  have hc : (C : EReal) = ⨆ x, u x := EReal.coe_toReal hf.1 hf.2
  exact ⟨C, le_thetaPshSupremum (hu.sub_const C)
    (sub_const_nonpositive_of_le (fun x => (hc.symm ▸ le_iSup u x)))⟩

private theorem singularityDistance_sub_const (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (C D : ℝ) :
    singularityDistance omega θ hbig (fun x => u x - (C : EReal))
      (fun x => v x - (D : EReal)) = singularityDistance omega θ hbig u v := by
  unfold singularityDistance
  rw [canonicalRay_sub_const_eq θ hu C, canonicalRay_sub_const_eq θ hv D]

omit [ConnectedSpace M] in
private theorem tendsto_endpoint_convex_of_endpoint
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M} {p u : M → EReal}
    {I : Type*} (F : Filter I) {w : I → M → EReal}
    (hw : ∀ i, IsThetaPshPotential θ.val (w i))
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hM : ∀ k : Fin (n + 1),
      Tendsto (fun i => (endpointMixedMass θ p (w i) hp (hw i) k).toReal) F
        (𝓝 (endpointMixedMass θ p u hp hu k).toReal)) (j : Fin (n + 1)) :
    Tendsto (fun i => (endpointMixedMass θ p (convexComb a (w i) p) hp
      (isThetaPshPotential_convexComb_closed (hw i) hp ha0 ha1) j).toReal) F
      (𝓝 (endpointMixedMass θ p (convexComb a u p) hp
        (isThetaPshPotential_convexComb_closed hu hp ha0 ha1) j).toReal) := by
  classical
  let k : (Fin n → Bool) → Fin (n + 1) := fun σ =>
    ⟨Fintype.card {i : Fin n // σ i = true}, Nat.lt_succ_of_le (by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le
        (fun i : Fin n => σ i = true))⟩
  have hb (σ : Fin n → Bool) (v : M → EReal) (hv : IsThetaPshPotential θ.val v) :
      (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then v else p)
        (fun i => by split_ifs <;> first | exact hv.1 | exact hp.1)).toReal =
      (endpointMixedMass θ p v hp hv (k σ)).toReal :=
    congrArg (fun μ : Measure M => (μ univ).toReal)
      (globalMixedMeasure_binary_eq_endpointMixedMeasure hv hp σ (k σ) rfl)
  let weight : (Fin n → Bool) → ℝ := fun σ =>
    ∏ i, if i.val < j.val then (if σ i then a else 1 - a) else (if σ i then 0 else 1)
  have he (v : M → EReal) (hv : IsThetaPshPotential θ.val v) :
      (endpointMixedMass θ p (convexComb a v p) hp
        (isThetaPshPotential_convexComb_closed hv hp ha0 ha1) j).toReal =
      ∑ σ : Fin n → Bool, weight σ * (endpointMixedMass θ p v hp hv (k σ)).toReal := by
    calc
      _ = ∑ σ : Fin n → Bool, weight σ *
          (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then v else p)
            (fun i => by split_ifs <;> first | exact hv.1 | exact hp.1)).toReal :=
        endpointMixedMass_convexComb_eq_sum omega hv hp ha0 ha1 j
      _ = _ := Finset.sum_congr rfl fun σ _ =>
        congrArg (fun r => weight σ * r) (hb σ v hv)
  have hfun : (fun i => (endpointMixedMass θ p (convexComb a (w i) p) hp
      (isThetaPshPotential_convexComb_closed (hw i) hp ha0 ha1) j).toReal) =
      fun i => ∑ σ : Fin n → Bool, weight σ *
        (endpointMixedMass θ p (w i) hp (hw i) (k σ)).toReal :=
    funext fun i => he (w i) (hw i)
  rw [hfun, he u hu]
  exact tendsto_finsetSum Finset.univ fun σ _ => (hM (k σ)).const_mul (weight σ)

/-- Actual endpoint finite polynomials and the actual endpoint/maximum
mass criterion make every fixed minimal interpolation native continuous. -/
theorem continuous_native_convexComb_minimal (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let Q : ThetaPshL1 θ.val → ThetaPshL1 θ.val := fun w =>
      ⟨convexComb a w.val (thetaPshSupremum θ.val),
        isThetaPshPotential_convexComb_closed w.property
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ha0 ha1⟩
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Continuous Q := by
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let Q : ThetaPshL1 θ.val → ThetaPshL1 θ.val := fun w =>
    ⟨convexComb a w.val V, isThetaPshPotential_convexComb_closed w.property hV ha0 ha1⟩
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Continuous Q
  rw [continuous_iff_continuousAt]
  intro v
  change Tendsto Q (𝓝 v) (𝓝 (Q v))
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig]
  apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig
    (𝓝 v) (fun w => (Q w).property) (Q v).property).mpr
  have hD : Tendsto (fun w : ThetaPshL1 θ.val =>
      (singularityDistance omega θ hbig w.val v.val).toReal) (𝓝 v) (𝓝 0) := by
    have h := (tendsto_iff_dist_tendsto_zero.mp
      (tendsto_id : Tendsto (fun w : ThetaPshL1 θ.val => w) (𝓝 v) (𝓝 v)))
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, id] using h
  have hM := (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass
    omega θ hbig (𝓝 v) (fun w : ThetaPshL1 θ.val => w.property) v.property).mp hD
  intro j
  refine ⟨tendsto_endpoint_convex_of_endpoint omega (𝓝 v)
    (fun w : ThetaPshL1 θ.val => w.property) v.property hV ha0 ha1
    (fun k => (hM k).1) j, ?_⟩
  have hm (w : ThetaPshL1 θ.val) :
      endpointMixedMass θ V (fun x => max ((Q w).val x) ((Q v).val x)) hV
        (IsThetaPshPotential.max (Q w).property (Q v).property) j =
      endpointMixedMass θ V (convexComb a (fun x => max (w.val x) (v.val x)) V) hV
        (isThetaPshPotential_convexComb_closed
          (IsThetaPshPotential.max w.property v.property) hV ha0 ha1) j := by
    have ht := congrArg (fun f => endpointMixedPotential j f V)
      (convexComb_max_common w.val v.val V ha0)
    have he := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
      (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
        (IsThetaPshPotential.max (Q w).property (Q v).property) hV)
      (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
        (isThetaPshPotential_convexComb_closed
          (IsThetaPshPotential.max w.property v.property) hV ha0 ha1) hV)
    exact congrArg (fun μ : Measure M => μ univ) he
  have hfun : (fun w : ThetaPshL1 θ.val =>
      (endpointMixedMass θ V (fun x => max ((Q w).val x) ((Q v).val x)) hV
        (IsThetaPshPotential.max (Q w).property (Q v).property) j).toReal) =
      fun w : ThetaPshL1 θ.val =>
        (endpointMixedMass θ V (convexComb a (fun x => max (w.val x) (v.val x)) V) hV
          (isThetaPshPotential_convexComb_closed
            (IsThetaPshPotential.max w.property v.property) hV ha0 ha1) j).toReal :=
    funext fun w => congrArg ENNReal.toReal (hm w)
  change Tendsto (fun w : ThetaPshL1 θ.val =>
    (endpointMixedMass θ V (fun x => max ((Q w).val x) ((Q v).val x)) hV
      (IsThetaPshPotential.max (Q w).property (Q v).property) j).toReal)
    (𝓝 v) (𝓝 (endpointMixedMass θ V (Q v).val hV (Q v).property j).toReal)
  rw [hfun]
  exact tendsto_endpoint_convex_of_endpoint omega (𝓝 v)
    (fun w : ThetaPshL1 θ.val => IsThetaPshPotential.max w.property v.property)
    v.property hV ha0 ha1 (fun k => (hM k).2) j

/-- Every actual minimal interpolation returns to its original genuine
potential in the explicitly selected native singularity topology. -/
theorem tendsto_native_convexComb_minimal_zero (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u : ThetaPshL1 θ.val) {I : Type*} (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i => (t i).val) F (𝓝 0)) :
    let Q : I → ThetaPshL1 θ.val := fun i =>
      ⟨convexComb (1 - (t i).val) u.val (thetaPshSupremum θ.val),
        isThetaPshPotential_convexComb_closed u.property
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
          (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)⟩
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto Q F (𝓝 u) := by
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  obtain ⟨C, hUV⟩ := exists_sub_const_le_minimal u.property
  let U : M → EReal := fun x => u.val x - (C : EReal)
  have hU : IsThetaPshPotential θ.val U := u.property.sub_const C
  let a : I → Icc (0 : ℝ) 1 := fun i =>
    ⟨1 - (t i).val, sub_nonneg.mpr (t i).property.2.le,
      sub_le_self 1 (t i).property.1.le⟩
  have hA : Tendsto a F (𝓝 (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [a, sub_zero] using
      (tendsto_const_nhds.sub ht : Tendsto (fun i => 1 - (t i).val) F (𝓝 (1 - 0)))
  let W : I → M → EReal := fun i => convexComb (a i).val U V
  have hW (i : I) : IsThetaPshPotential θ.val (W i) :=
    isThetaPshPotential_convexComb_closed hU hV (a i).property.1 (a i).property.2
  have hM (j : Fin (n + 1)) :
      Tendsto (fun i => (endpointMixedMass θ V (W i) hV (hW i) j).toReal) F
        (𝓝 (endpointMixedMass θ V U hV hU j).toReal) := by
    simpa only [Function.comp_def] using
      (tendsto_toReal_endpointMixedMass_convexComb_one omega hU hV j).comp hA
  have hlo (i : I) : U ≤ W i :=
    le_convexComb_of_le U V hUV (sub_pos.mpr (t i).property.2)
      (sub_lt_self 1 (t i).property.1)
  have hD : Tendsto (fun i => (singularityDistance omega θ hbig (W i) U).toReal)
      F (𝓝 0) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass
      omega θ hbig F hW hU).mpr
    intro j
    refine ⟨hM j, ?_⟩
    have hm (i : I) :
        endpointMixedMass θ V (fun x => max (W i x) (U x)) hV
          (IsThetaPshPotential.max (hW i) hU) j =
        endpointMixedMass θ V (W i) hV (hW i) j := by
      have htup : endpointMixedPotential j (fun x => max (W i x) (U x)) V =
          endpointMixedPotential j (W i) V :=
        congrArg (fun f => endpointMixedPotential j f V)
          (funext fun x => max_eq_left (hlo i x))
      exact congrArg (fun μ : Measure M => μ univ)
        (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htup
          (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
            (IsThetaPshPotential.max (hW i) hU) hV)
          (endpointMixedPotential_thetaPlurisubharmonic θ j _ V (hW i) hV))
    change Tendsto (fun i => (endpointMixedMass θ V (fun x => max (W i x) (U x)) hV
      (IsThetaPshPotential.max (hW i) hU) j).toReal) F
        (𝓝 (endpointMixedMass θ V U hV hU j).toReal)
    simpa only [hm] using hM j
  let Q : I → ThetaPshL1 θ.val := fun i =>
    ⟨convexComb (1 - (t i).val) u.val V,
      isThetaPshPotential_convexComb_closed u.property hV
        (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)⟩
  have he (i : I) : singularityDistance omega θ hbig (Q i).val u.val =
      singularityDistance omega θ hbig (W i) U := by
    have hshift : W i = fun x => (Q i).val x - (((1 - (t i).val) * C : ℝ) : EReal) :=
      convexComb_sub_const_first u.val V (sub_pos.mpr (t i).property.2)
        (sub_lt_self 1 (t i).property.1) C
    rw [hshift]
    exact (singularityDistance_sub_const omega θ hbig (Q i).property u.property
      ((1 - (t i).val) * C) C).symm
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Tendsto Q F (𝓝 u)
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig, he]
  exact hD

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
