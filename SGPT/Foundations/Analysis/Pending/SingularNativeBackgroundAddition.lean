import SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassContinuity
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion
import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly

set_option autoImplicit false

/-! # Actual forward native singularity convergence under Kähler addition

SGPT PDF0237--0238 Corollary 6.2.9, forward direction. Actual original
and fixed smooth mixed slots produce all enlarged endpoint mass limits.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundAddition

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy MixedMass
  GlobalNonPluripolar GlobalDiagonalScaling KahlerDomination ThetaPshL1Topology
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison SingularCanonicalSingularityMaximumCriterion
  ActualPartialBackgroundMassContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem big_add_kahler (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)) := by
  simpa only [one_smul] using
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic zero_lt_one

private theorem tendsto_endpoint_mass_add_kahler (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (j : Fin (n + 1)) :
    let γ := θ + omega.form
    let hγ := big_add_kahler omega θ hbig
    let φ := thetaPshSupremum γ.val
    let hφ := (isModelPotential_thetaPshSupremum omega γ hγ).plurisubharmonic
    Tendsto (fun i => endpointMixedMass γ φ (w i).val hφ
      (LocalPotentials.isThetaPshPotential_add_of_semipositive (w i).property omega.isSemipositive) j) F
      (𝓝 (endpointMixedMass γ φ v.val hφ
        (LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive) j)) := by
  classical
  let γ := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := big_add_kahler omega θ hbig
  let φ := thetaPshSupremum γ.val
  have hφ : IsThetaPshPotential γ.val φ :=
    (isModelPotential_thetaPshSupremum omega γ hγ).plurisubharmonic
  let S : Finset (Fin n) := Finset.univ.filter fun k => k.val < j.val
  let θB : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else γ
  let uB : I → Bool → M → EReal := fun i b => if b then (w i).val else φ
  let vB : Bool → M → EReal := fun b => if b then v.val else φ
  have hB (b : Bool) : IsBigClass (RealBottChern.ofRepresentative (θB b)) := by
    cases b <;> first | exact hγ | exact hbig
  have huB (i : I) (b : Bool) : IsThetaPshPotential (θB b).val (uB i b) := by
    cases b <;> first | exact hφ | exact (w i).property
  have hvB (b : Bool) : IsThetaPshPotential (θB b).val (vB b) := by
    cases b <;> first | exact hφ | exact v.property
  have hconst : Tendsto (fun _ : I => (⟨φ, hφ⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨φ, hφ⟩) := by
    let := singularityPseudoMetricSpace omega γ hγ
    let : TopologicalSpace (ThetaPshL1 γ.val) :=
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
    let z : ThetaPshL1 γ.val := ⟨φ, hφ⟩
    change Tendsto (fun _ : I => z) F (𝓝 z)
    exact tendsto_const_nhds
  have hBlim (b : Bool) : Tendsto
      (fun i => (⟨uB i b, huB i b⟩ : ThetaPshL1 (θB b).val)) F
      (@nhds (ThetaPshL1 (θB b).val)
        (singularityPseudoMetricSpace omega (θB b) (hB b)).toUniformSpace.toTopologicalSpace
        ⟨vB b, hvB b⟩) := by
    cases b
    · exact hconst
    · exact hlim
  let η : Fin n → ClosedRealOneOneForm n M := fun k => θB (decide (k.val < j.val))
  let U : I → Fin n → M → EReal := fun i k => uB i (decide (k.val < j.val))
  let V : Fin n → M → EReal := fun k => vB (decide (k.val < j.val))
  have hη (k : Fin n) : IsBigClass (RealBottChern.ofRepresentative (η k)) :=
    hB (decide (k.val < j.val))
  have hU (i : I) (k : Fin n) : IsThetaPshPotential (η k).val (U i k) :=
    huB i (decide (k.val < j.val))
  have hV (k : Fin n) : IsThetaPshPotential (η k).val (V k) :=
    hvB (decide (k.val < j.val))
  have hslot (k : Fin n) : Tendsto
      (fun i => (⟨U i k, hU i k⟩ : ThetaPshL1 (η k).val)) F
      (@nhds (ThetaPshL1 (η k).val)
        (singularityPseudoMetricSpace omega (η k) (hη k)).toUniformSpace.toTopologicalSpace
        ⟨V k, hV k⟩) := hBlim (decide (k.val < j.val))
  have hm := tendsto_globalMixedMass_partial_background_of_native omega hη F hU hV hslot
    S (a := 1) zero_le_one
  have hforms : (fun k => η k + (if k ∈ S then (1 : ℝ) else 0) • omega.form) =
      fun _ : Fin n => γ := by
    funext k
    by_cases hk : k.val < j.val <;> simp [η, θB, S, hk, γ]
  have hQU (i : I) : U i = endpointMixedPotential j (w i).val φ := by
    funext k
    by_cases hk : k.val < j.val <;> simp [U, uB, endpointMixedPotential, hk]
  have hQV : V = endpointMixedPotential j v.val φ := by
    funext k
    by_cases hk : k.val < j.val <;> simp [V, vB, endpointMixedPotential, hk]
  have hwp (i : I) : IsThetaPshPotential γ.val (w i).val :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive (w i).property omega.isSemipositive
  have hvp : IsThetaPshPotential γ.val v.val :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive
  have heqU (i : I) : globalMixedMass
      (fun k => η k + (if k ∈ S then (1 : ℝ) else 0) • omega.form) (U i)
      (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hU i k)
        (isSemipositive_smul omega.isSemipositive
          (by split_ifs <;> first | exact zero_le_one | exact le_rfl))).1) =
      endpointMixedMass γ φ (w i).val hφ (hwp i) j := by
    unfold globalMixedMass endpointMixedMass endpointMixedMeasure
    exact congrArg (fun μ : Measure M => μ univ) (globalMixedMeasure_congr hforms (hQU i) _ _)
  have heqV : globalMixedMass
      (fun k => η k + (if k ∈ S then (1 : ℝ) else 0) • omega.form) V
      (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hV k)
        (isSemipositive_smul omega.isSemipositive
          (by split_ifs <;> first | exact zero_le_one | exact le_rfl))).1) =
      endpointMixedMass γ φ v.val hφ hvp j := by
    unfold globalMixedMass endpointMixedMass endpointMixedMeasure
    exact congrArg (fun μ : Measure M => μ univ) (globalMixedMeasure_congr hforms hQV _ _)
  simpa only [heqU, heqV] using hm

/-- Actual original-native convergence produces enlarged-native convergence:
the complete maximum/mass criterion and actual mixed slots supply every limit. -/
theorem tendsto_native_add_kahler (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    let γ := θ + omega.form
    let hγ := big_add_kahler omega θ hbig
    let W : I → ThetaPshL1 γ.val := fun i =>
      ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (w i).property omega.isSemipositive⟩
    let V : ThetaPshL1 γ.val :=
      ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive⟩
    Tendsto W F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace V) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let Z : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((w i).val x) (v.val x), IsThetaPshPotential.max (w i).property v.property⟩
  have hZ : Tendsto Z F (𝓝 v) :=
    ((tendsto_native_iff_max_and_endpointMixedMass omega θ hbig F w v).mp hlim).1
  let γ := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := big_add_kahler omega θ hbig
  let W : I → ThetaPshL1 γ.val := fun i =>
    ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (w i).property omega.isSemipositive⟩
  let V : ThetaPshL1 γ.val :=
    ⟨v.val, LocalPotentials.isThetaPshPotential_add_of_semipositive v.property omega.isSemipositive⟩
  let := singularityPseudoMetricSpace omega γ hγ
  let : TopologicalSpace (ThetaPshL1 γ.val) :=
    (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
  change Tendsto W F (𝓝 V)
  apply (tendsto_native_iff_endpointMixedMass omega γ hγ F W V).mpr
  intro j
  exact ⟨tendsto_endpoint_mass_add_kahler omega θ hbig F w v hlim j,
    tendsto_endpoint_mass_add_kahler omega θ hbig F Z v hZ j⟩

end
end SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundAddition
