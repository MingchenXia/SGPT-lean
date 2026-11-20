import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundAddition
import SGPT.Foundations.Analysis.Pending.FinitePolynomialEvaluationContinuity

set_option autoImplicit false

/-! # Actual reverse native background transport and convergence equivalence

SGPT PDF0237--0238 Corollary 6.2.9. Actual positive-background native
limits produce finitely many polynomial evaluations, then the original mass.
-/

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy MixedMass
  GlobalNonPluripolar GlobalDiagonalScaling KahlerDomination ThetaPshL1Topology
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison SingularCanonicalSingularityMaximumCriterion
  SingularNativeBackgroundAddition ActualNativeMixedMassContinuity
  ActualPartialBackgroundMassPolynomial FinitePolynomialEvaluationContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_native_change_auxiliary (omega κ : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace v) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hd : Tendsto (fun i => (singularityDistance omega θ hbig (w i).val v.val).toReal)
      F (𝓝 0) := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig] using
      (tendsto_iff_dist_tendsto_zero.mp hlim)
  let := singularityPseudoMetricSpace κ θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_singularityDistance_toReal κ θ hbig, singularityDistance] using hd

private theorem tendsto_original_endpoint_mass_of_enlarged_native
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hγ : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hlim : Tendsto
      (fun i => (⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (w i).property omega.isSemipositive⟩ : ThetaPshL1 (θ + omega.form).val)) F
      (@nhds (ThetaPshL1 (θ + omega.form).val)
        (singularityPseudoMetricSpace omega (θ + omega.form) hγ).toUniformSpace.toTopologicalSpace
        ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive
          v.property omega.isSemipositive⟩)) (j : Fin (n + 1)) :
    Tendsto (fun i => endpointMixedMass θ (thetaPshSupremum θ.val) (w i).val
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (w i).property j) F
      (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v.val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property j)) := by
  classical
  let γ := θ + omega.form
  let φ := thetaPshSupremum θ.val
  have hφ : IsThetaPshPotential θ.val φ :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let S : Finset (Fin n) := Finset.univ.filter fun k => k.val < j.val
  let U : I → Fin n → M → EReal := fun i => endpointMixedPotential j (w i).val φ
  let V : Fin n → M → EReal := endpointMixedPotential j v.val φ
  have hU (i : I) (k : Fin n) : IsThetaPshPotential θ.val (U i k) := by
    dsimp [U, endpointMixedPotential]
    split_ifs <;> first | exact (w i).property | exact hφ
  have hV (k : Fin n) : IsThetaPshPotential θ.val (V k) := by
    dsimp [V, endpointMixedPotential]
    split_ifs <;> first | exact v.property | exact hφ
  let p : I → ℝ[X] := fun i => partialBackgroundMassPolynomial omega (fun _ => θ) (U i) (hU i) S
  let q : ℝ[X] := partialBackgroundMassPolynomial omega (fun _ => θ) V hV S
  have hpositive (c : ℝ) (hc : 1 < c) :
      Tendsto (fun i => (p i).eval c) F (𝓝 (q.eval c)) := by
    let κ := KahlerBackground.smul (sub_pos.mpr hc) omega
    let W0 : I → ThetaPshL1 γ.val := fun i =>
      ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (w i).property omega.isSemipositive⟩
    let V0 : ThetaPshL1 γ.val :=
      ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive⟩
    have h0 : Tendsto W0 F (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace V0) := hlim
    have hκ := tendsto_native_change_auxiliary omega κ γ hγ F W0 V0 h0
    let γ1 := γ + κ.form
    have hγ1 : IsBigClass (RealBottChern.ofRepresentative γ1) := by
      simpa only [one_smul] using
        PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential κ γ V0.property zero_lt_one
    let W1 : I → ThetaPshL1 γ1.val := fun i =>
      ⟨(W0 i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive (W0 i).property κ.isSemipositive⟩
    let V1 : ThetaPshL1 γ1.val :=
      ⟨V0.val, LocalPotentials.isThetaPshPotential_add_of_semipositive V0.property κ.isSemipositive⟩
    have h1 : Tendsto W1 F (@nhds (ThetaPshL1 γ1.val)
        (singularityPseudoMetricSpace κ γ1 hγ1).toUniformSpace.toTopologicalSpace V1) :=
      tendsto_native_add_kahler κ γ hγ F W0 V0 hκ
    let θB : Bool → ClosedRealOneOneForm n M := fun b => if b then γ1 else θ
    let uB : I → Bool → M → EReal := fun i b => if b then (W1 i).val else φ
    let vB : Bool → M → EReal := fun b => if b then V1.val else φ
    have hB (b : Bool) : IsBigClass (RealBottChern.ofRepresentative (θB b)) := by
      cases b <;> first | exact hbig | exact hγ1
    have huB (i : I) (b : Bool) : IsThetaPshPotential (θB b).val (uB i b) := by
      cases b <;> first | exact hφ | exact (W1 i).property
    have hvB (b : Bool) : IsThetaPshPotential (θB b).val (vB b) := by
      cases b <;> first | exact hφ | exact V1.property
    have hconst : Tendsto (fun _ : I => (⟨φ, hφ⟩ : ThetaPshL1 θ.val)) F
        (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace ⟨φ, hφ⟩) := by
      let := singularityPseudoMetricSpace κ θ hbig
      let : TopologicalSpace (ThetaPshL1 θ.val) :=
        (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace
      let z : ThetaPshL1 θ.val := ⟨φ, hφ⟩
      change Tendsto (fun _ : I => z) F (𝓝 z)
      exact tendsto_const_nhds
    have hBlim (b : Bool) : Tendsto
        (fun i => (⟨uB i b, huB i b⟩ : ThetaPshL1 (θB b).val)) F
        (@nhds (ThetaPshL1 (θB b).val)
          (singularityPseudoMetricSpace κ (θB b) (hB b)).toUniformSpace.toTopologicalSpace
          ⟨vB b, hvB b⟩) := by
      cases b
      · exact hconst
      · exact h1
    let η : Fin n → ClosedRealOneOneForm n M := fun k => θB (decide (k.val < j.val))
    let A : I → Fin n → M → EReal := fun i k => uB i (decide (k.val < j.val))
    let B : Fin n → M → EReal := fun k => vB (decide (k.val < j.val))
    have hη (k : Fin n) : IsBigClass (RealBottChern.ofRepresentative (η k)) :=
      hB (decide (k.val < j.val))
    have hA (i : I) (k : Fin n) : IsThetaPshPotential (η k).val (A i k) :=
      huB i (decide (k.val < j.val))
    have hBt (k : Fin n) : IsThetaPshPotential (η k).val (B k) :=
      hvB (decide (k.val < j.val))
    have hslot (k : Fin n) : Tendsto
        (fun i => (⟨A i k, hA i k⟩ : ThetaPshL1 (η k).val)) F
        (@nhds (ThetaPshL1 (η k).val)
          (singularityPseudoMetricSpace κ (η k) (hη k)).toUniformSpace.toTopologicalSpace
          ⟨B k, hBt k⟩) := hBlim (decide (k.val < j.val))
    have hm := tendsto_globalMixedMass_of_native κ hη F hA hBt hslot
    have hr := (ENNReal.tendsto_toReal (globalMixedMass_lt_top κ
      (fun k => (hBt k).1)).ne).comp hm
    have hforms : η = fun k => θ + (if k ∈ S then c else 0) • omega.form := by
      funext k
      by_cases hk : k.val < j.val
      · simp [η, θB, S, hk]
        dsimp [γ1, γ, κ]
        module
      · simp [η, θB, S, hk]
    have hQU (i : I) : A i = U i := by
      funext k
      by_cases hk : k.val < j.val <;> simp [A, U, uB, endpointMixedPotential, hk, W1, W0]
    have hQV : B = V := by
      funext k
      by_cases hk : k.val < j.val <;> simp [B, V, vB, endpointMixedPotential, hk, V1, V0]
    have hevalP (i : I) : (p i).eval c =
        (globalMixedMass η (A i) (fun k => (hA i k).1)).toReal := by
      rw [← globalMixedMass_partial_background_toReal_eq_eval omega (hU i) S (by linarith)]
      unfold globalMixedMass
      exact congrArg (fun μ : Measure M => (μ univ).toReal)
        (globalMixedMeasure_congr hforms (hQU i) _ _).symm
    have hevalQ : q.eval c = (globalMixedMass η B (fun k => (hBt k).1)).toReal := by
      rw [← globalMixedMass_partial_background_toReal_eq_eval omega hV S (by linarith)]
      unfold globalMixedMass
      exact congrArg (fun μ : Measure M => (μ univ).toReal)
        (globalMixedMeasure_congr hforms hQV _ _).symm
    simpa only [hevalP, hevalQ, Function.comp_def] using hr
  let nodes : Fin (n + 1) → ℝ := fun k => (k.val : ℝ) + 2
  have hnodes : Function.Injective nodes := by
    intro k l h
    apply Fin.ext
    have he : (k.val : ℝ) = l.val := by dsimp [nodes] at h; linarith
    exact_mod_cast he
  have hn (k : Fin (n + 1)) : 1 < nodes k := by
    dsimp [nodes]
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    linarith
  have hpdegree (i : I) : (p i).natDegree ≤ n :=
    natDegree_partialBackgroundMassPolynomial_le omega (fun _ => θ) (U i) (hU i) S
  have hqdegree : q.natDegree ≤ n :=
    natDegree_partialBackgroundMassPolynomial_le omega (fun _ => θ) V hV S
  have ht := tendsto_eval_of_finite_evaluations F nodes hnodes p q hpdegree hqdegree
    (fun k => hpositive (nodes k) (hn k)) 0
  have hpzero (i : I) : (p i).eval 0 =
      (endpointMixedMass θ φ (w i).val hφ (w i).property j).toReal := by
    have h := (globalMixedMass_partial_background_toReal_eq_eval omega (hU i) S
      (a := 0) le_rfl).symm
    simpa only [ite_self, zero_smul, add_zero, globalMixedMass,
      endpointMixedMass, endpointMixedMeasure] using h
  have hqzero : q.eval 0 = (endpointMixedMass θ φ v.val hφ v.property j).toReal := by
    have h := (globalMixedMass_partial_background_toReal_eq_eval omega hV S
      (a := 0) le_rfl).symm
    simpa only [ite_self, zero_smul, add_zero, globalMixedMass,
      endpointMixedMass, endpointMixedMeasure] using h
  rw [show (fun i => (p i).eval 0) = fun i =>
    (endpointMixedMass θ φ (w i).val hφ (w i).property j).toReal from _root_.funext hpzero,
    hqzero] at ht
  have hfin (z : ThetaPshL1 θ.val) : endpointMixedMass θ φ z.val hφ z.property j ≠ ⊤ :=
    (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ j z.val φ z.property hφ)).ne
  have he := (ENNReal.continuous_ofReal.tendsto _).comp ht
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (hfin _)] using he

/-- Actual auxiliary metric transport, positive selected-background mixed
limits, and finite polynomial recovery produce the full native equivalence. -/
theorem tendsto_native_iff_add_kahler (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    let γ := θ + omega.form
    let hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
      simpa only [one_smul] using
        PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ v.property zero_lt_one
    let W : I → ThetaPshL1 γ.val := fun i =>
      ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (w i).property omega.isSemipositive⟩
    let V : ThetaPshL1 γ.val :=
      ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive⟩
    Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v) ↔
      Tendsto W F (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace V) := by
  let γ := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ v.property zero_lt_one
  let W : I → ThetaPshL1 γ.val := fun i =>
    ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (w i).property omega.isSemipositive⟩
  let V : ThetaPshL1 γ.val :=
    ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive⟩
  change Tendsto w F (@nhds (ThetaPshL1 θ.val)
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v) ↔
      Tendsto W F (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace V)
  constructor
  · intro h
    exact tendsto_native_add_kahler omega θ hbig F w v h
  · intro h
    let Z : I → ThetaPshL1 θ.val := fun i =>
      ⟨fun x => max ((w i).val x) (v.val x), IsThetaPshPotential.max (w i).property v.property⟩
    let Zγ : I → ThetaPshL1 γ.val := fun i =>
      ⟨(Z i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (Z i).property omega.isSemipositive⟩
    let := singularityPseudoMetricSpace omega γ hγ
    let : TopologicalSpace (ThetaPshL1 γ.val) :=
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
    have hZ : Tendsto Zγ F (𝓝 V) :=
      ((tendsto_native_iff_max_and_endpointMixedMass omega γ hγ F W V).mp h).1
    let := singularityPseudoMetricSpace omega θ hbig
    let : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    apply (tendsto_native_iff_endpointMixedMass omega θ hbig F w v).mpr
    intro j
    exact ⟨tendsto_original_endpoint_mass_of_enlarged_native omega θ hbig hγ F w v h j,
      tendsto_original_endpoint_mass_of_enlarged_native omega θ hbig hγ F Z v hZ j⟩

end
end SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
