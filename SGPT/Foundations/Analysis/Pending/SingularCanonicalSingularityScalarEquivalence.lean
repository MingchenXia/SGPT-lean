import SGPT.Foundations.Analysis.Pending.ActualMixedMassPositiveScaling
import SGPT.Foundations.Analysis.Pending.ActualPositiveClassScaling
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # Actual fixed positive scalar convergence equivalence

The endpoint-mass and actual minimal-potential identities give SGPT
PDF0239--0240, Lemma 6.2.6, for arbitrary incoming filters. No scaled
distance identity or mixed-mass convergence is an input assumption.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityScalarEquivalence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  GlobalNonPluripolar AmbientMassBackgroundMonotone MixedMass
  ActualMixedMassPositiveScaling ActualPositiveClassScaling
  SingularMinimalCanonicalRay SingularCanonicalSingularityMassComparison
  SingularCanonicalSingularityDistance ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual endpoint tuple has homogeneous extended total mass. -/
theorem endpointMixedMass_positive_smul
    {θ : ClosedRealOneOneForm n M} {p u : M → EReal}
    (hp : IsThetaPshPotential θ.val p) (hu : IsThetaPshPotential θ.val u)
    {c : ℝ} (hc : 0 < c) (k : Fin (n + 1)) :
    endpointMixedMass (c • θ) (fun x => (c : EReal) * p x)
      (fun x => (c : EReal) * u x)
      (RestrictedApproximantComparison.isThetaPshPotential_smul hp hc)
      (RestrictedApproximantComparison.isThetaPshPotential_smul hu hc) k =
    ENNReal.ofReal (c ^ n) * endpointMixedMass θ p u hp hu k := by
  classical
  have ht : ∀ i : Fin n,
      IsThetaPshPotential θ.val (endpointMixedPotential k u p i) := by
    intro i
    by_cases hi : i.val < k.val
    · simpa only [endpointMixedPotential, hi, if_true] using hu
    · simpa only [endpointMixedPotential, hi, if_false] using hp
  have he : endpointMixedPotential k (fun x => (c : EReal) * u x)
      (fun x => (c : EReal) * p x) =
      fun i x => (c : EReal) * endpointMixedPotential k u p i x := by
    funext i x
    unfold endpointMixedPotential
    split_ifs <;> rfl
  have h := globalMixedMass_positive_smul ht (fun _ => hc)
  unfold endpointMixedMass endpointMixedMeasure
  rw [globalMixedMeasure_congr_tuples rfl he _
    (fun i => (RestrictedApproximantComparison.isThetaPshPotential_smul (ht i) hc).1)]
  simpa only [globalMixedMass, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

variable [ConnectedSpace M]

/-- Actual endpoint/maximum mass profiles give the original fixed-scalar
convergence equivalence in both genuine native distance topologies. -/
theorem tendsto_native_positive_smul_iff (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {c : ℝ} (hc : 0 < c) {ι : Type*} (F : Filter ι)
    (w : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    let hbigc : IsBigClass (RealBottChern.ofRepresentative (c • θ)) := by
      simpa only [RealBottChern.ofRepresentative_smul] using isBigClass_positive_smul hbig hc
    let scale : ThetaPshL1 θ.val → ThetaPshL1 (c • θ).val := fun a =>
      ⟨fun x => (c : EReal) * a.val x,
        RestrictedApproximantComparison.isThetaPshPotential_smul a.property hc⟩
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    letI := singularityPseudoMetricSpace omega (c • θ) hbigc
    letI : TopologicalSpace (ThetaPshL1 (c • θ).val) :=
      (singularityPseudoMetricSpace omega (c • θ) hbigc).toUniformSpace.toTopologicalSpace
    Tendsto (fun i => scale (w i)) F (𝓝 (scale v)) ↔ Tendsto w F (𝓝 v) := by
  dsimp only
  let hbigc : IsBigClass (RealBottChern.ofRepresentative (c • θ)) := by
    simpa only [RealBottChern.ofRepresentative_smul] using isBigClass_positive_smul hbig hc
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let := singularityPseudoMetricSpace omega (c • θ) hbigc
  let : TopologicalSpace (ThetaPshL1 (c • θ).val) :=
    (singularityPseudoMetricSpace omega (c • θ) hbigc).toUniformSpace.toTopologicalSpace
  have hV := thetaPshSupremum_positive_smul omega θ hbig hc
  have hmass {a : M → EReal} (ha : IsThetaPshPotential θ.val a) (k : Fin (n + 1)) :
      endpointMixedMass (c • θ) (thetaPshSupremum (c • θ).val)
        (fun x => (c : EReal) * a x)
        (isModelPotential_thetaPshSupremum omega (c • θ) hbigc).plurisubharmonic
        (RestrictedApproximantComparison.isThetaPshPotential_smul ha hc) k =
      ENNReal.ofReal (c ^ n) * endpointMixedMass θ (thetaPshSupremum θ.val) a
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ha k := by
    simpa only [hV] using endpointMixedMass_positive_smul
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ha hc k
  have hmax (a b : EReal) : max ((c : EReal) * a) ((c : EReal) * b) =
      (c : EReal) * max a b := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab,
        max_eq_right (mul_le_mul_of_nonneg_left hab (EReal.coe_nonneg.mpr hc.le))]
    · rw [max_eq_left hba,
        max_eq_left (mul_le_mul_of_nonneg_left hba (EReal.coe_nonneg.mpr hc.le))]
  have hbridge {f : ι → ℝ≥0∞} {a : ℝ≥0∞} :
      Tendsto (fun i => ENNReal.ofReal (c ^ n) * f i) F
        (𝓝 (ENNReal.ofReal (c ^ n) * a)) ↔ Tendsto f F (𝓝 a) := by
    have hK0 : ENNReal.ofReal (c ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hc n)).ne'
    have hKtop : ENNReal.ofReal (c ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
    constructor
    · intro h
      have h' := (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr hK0)).tendsto
        (ENNReal.ofReal (c ^ n) * a) |>.comp h
      simpa only [Function.comp_def, ENNReal.inv_mul_cancel_left hK0 hKtop] using h'
    · intro h
      exact (ENNReal.continuous_const_mul hKtop).tendsto a |>.comp h
  let scale : ThetaPshL1 θ.val → ThetaPshL1 (c • θ).val := fun a =>
    ⟨fun x => (c : EReal) * a.val x,
      RestrictedApproximantComparison.isThetaPshPotential_smul a.property hc⟩
  have hs := tendsto_native_iff_endpointMixedMass omega (c • θ) hbigc F
    (fun i => scale (w i)) (scale v)
  have ho := tendsto_native_iff_endpointMixedMass omega θ hbig F w v
  refine hs.trans (Iff.trans ?_ ho.symm)
  dsimp only [scale]
  simp_rw [hmax]
  apply forall_congr'
  intro k
  apply and_congr
  · convert hbridge (f := fun i => endpointMixedMass θ (thetaPshSupremum θ.val)
        (w i).val (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
        (w i).property k)
      (a := endpointMixedMass θ (thetaPshSupremum θ.val) v.val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property k)
      using 2
    · funext i
      exact hmass (w i).property k
    · exact congrArg nhds (hmass v.property k)
  · convert hbridge (f := fun i => endpointMixedMass θ (thetaPshSupremum θ.val)
        (fun x => max ((w i).val x) (v.val x))
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
        (IsThetaPshPotential.max (w i).property v.property) k)
      (a := endpointMixedMass θ (thetaPshSupremum θ.val) v.val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property k)
      using 2
    · funext i
      exact hmass (IsThetaPshPotential.max (w i).property v.property) k
    · exact congrArg nhds (hmass v.property k)

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityScalarEquivalence
