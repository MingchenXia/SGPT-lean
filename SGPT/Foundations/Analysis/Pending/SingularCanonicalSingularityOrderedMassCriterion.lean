import SGPT.Foundations.Analysis.Pending.ActualMixedMassOrderedContinuity
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # One ordered actual top-mass limit controls singularity convergence

SGPT PDF0227 Corollary 6.2.6, positive target and actual pointwise order,
with a fixed-weight arbitrary-filter proof. The actual ordered mixed-mass
producer gives every endpoint limit from one actual diagonal limit.
Natural pointwise order then identifies maximum masses and yields the
literal real and native singularity convergence criteria. Global P-order
transport is separate, and no incoming monotonicity is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass MixedMass
  RelativeEnergy ActualMixedMassOrderedContinuity SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem endpointMixedMass_last {θ : ClosedRealOneOneForm n M}
    {p u : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) :
    endpointMixedMass θ p u hp hu (Fin.last n) = diagonalPotentialMass θ u hu := by
  have ht : endpointMixedPotential (Fin.last n) u p = (fun _ : Fin n => u) := by
    funext i
    simp only [endpointMixedPotential, Fin.val_last, if_pos i.isLt]
  have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
    (endpointMixedPotential_thetaPlurisubharmonic θ (Fin.last n) u p hu hp)
    (fun _ : Fin n => hu.1)
  exact congrArg (fun μ : Measure M => μ univ) hm

/-- One actual moving diagonal mass limit supplies every actual endpoint
limit against a genuine positive reference through independent slot tuples. -/
theorem tendsto_endpointMixedMass_of_le_of_diagonal_tendsto
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v p : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) (hle : ∀ i, v ≤ u i)
    (hvpos : 0 < diagonalPotentialMass θ v hv) (hppos : 0 < diagonalPotentialMass θ p hp)
    (hdiag : Tendsto (fun i => diagonalPotentialMass θ (u i) (hu i)) F
      (𝓝 (diagonalPotentialMass θ v hv))) (j : Fin (n + 1)) :
    Tendsto (fun i => endpointMixedMass θ p (u i) hp (hu i) j) F
      (𝓝 (endpointMixedMass θ p v hp hv j)) := by
  classical
  let T : I → Fin n → M → EReal := fun i => endpointMixedPotential j (u i) p
  let P : Fin n → M → EReal := endpointMixedPotential j v p
  have hP : ∀ a, IsThetaPshPotential θ.val (P a) := by
    intro a
    by_cases ha : a.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos ha] using hv
    · simpa only [P, endpointMixedPotential, if_neg ha] using hp
  have hT : ∀ i a, IsThetaPshPotential θ.val (T i a) := by
    intro i a
    by_cases ha : a.val < j.val
    · simpa only [T, endpointMixedPotential, if_pos ha] using hu i
    · simpa only [T, endpointMixedPotential, if_neg ha] using hp
  have horder : ∀ i a, P a ≤ T i a := by
    intro i a
    by_cases ha : a.val < j.val
    · simpa only [P, T, endpointMixedPotential, if_pos ha] using hle i
    · simp only [P, T, endpointMixedPotential, if_neg ha, le_refl]
  have hpos : ∀ a, 0 < diagonalPotentialMass θ (P a) (hP a) := by
    intro a
    by_cases ha : a.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos ha] using hvpos
    · simpa only [P, endpointMixedPotential, if_neg ha] using hppos
  have hdiagT : ∀ a, Tendsto (fun i => diagonalPotentialMass θ (T i a) (hT i a))
      F (𝓝 (diagonalPotentialMass θ (P a) (hP a))) := by
    intro a
    by_cases ha : a.val < j.val
    · simpa only [P, T, endpointMixedPotential, if_pos ha] using hdiag
    · simpa only [P, T, endpointMixedPotential, if_neg ha] using
        (tendsto_const_nhds : Tendsto (fun _ : I => diagonalPotentialMass θ p hp)
          F (𝓝 (diagonalPotentialMass θ p hp)))
  have hm := tendsto_globalMixedMass_of_le_of_diagonal_tendsto
    (θ := fun _ : Fin n => θ) omega F hP hT horder hpos hdiagT
  simpa only [globalMixedMass, endpointMixedMass, endpointMixedMeasure] using hm

/-- Under genuine actual pointwise order and positive target mass, the
defining real singularity distance tends to zero iff the actual top masses converge. -/
theorem tendsto_singularityDistance_iff_diagonalPotentialMass_of_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hle : ∀ i, v ≤ u i) (hvpos : 0 < diagonalPotentialMass θ v hv) :
    Tendsto (fun i => (singularityDistance omega θ hbig (u i) v).toReal) F (𝓝 0) ↔
      Tendsto (fun i => diagonalPotentialMass θ (u i) (hu i)) F
        (𝓝 (diagonalPotentialMass θ v hv)) := by
  let V := thetaPshSupremum θ.val
  have hV : IsModelPotential θ V := isModelPotential_thetaPshSupremum omega θ hbig
  have hfinite {a : M → EReal} (ha : IsThetaPshPotential θ.val a) :
      diagonalPotentialMass θ a ha ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => ha.1)).ne
  constructor
  · intro h
    have hr := ((tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig
      F hu hv).mp h (Fin.last n)).1
    have htop : Tendsto (fun i => (diagonalPotentialMass θ (u i) (hu i)).toReal) F
        (𝓝 (diagonalPotentialMass θ v hv).toReal) := by
      simpa only [endpointMixedMass_last] using hr
    have he := (ENNReal.continuous_ofReal.tendsto
      (diagonalPotentialMass θ v hv).toReal).comp htop
    simpa only [Function.comp_def, ENNReal.ofReal_toReal (hfinite hv),
      ENNReal.ofReal_toReal (hfinite (hu _))] using he
  · intro hdiag
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig F hu hv).mpr
    intro j
    have hm := tendsto_endpointMixedMass_of_le_of_diagonal_tendsto omega F hu hv
      hV.plurisubharmonic hle hvpos hV.positive_mass hdiag j
    have ht : endpointMixedMass θ V v hV.plurisubharmonic hv j ≠ ⊤ :=
      (globalMixedMass_lt_top omega
        (endpointMixedPotential_thetaPlurisubharmonic θ j v V hv hV.plurisubharmonic)).ne
    have hr := (ENNReal.continuousAt_toReal ht).tendsto.comp hm
    have hmax (i : I) : (fun x => max (u i x) (v x)) = u i :=
      funext fun x => max_eq_left (hle i x)
    have hmass (i : I) : endpointMixedMass θ V (fun x => max (u i x) (v x))
        hV.plurisubharmonic (IsThetaPshPotential.max (hu i) hv) j =
        endpointMixedMass θ V (u i) hV.plurisubharmonic (hu i) j := by
      have htup := congrArg (fun w => endpointMixedPotential j w V) (hmax i)
      have he := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htup
        (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
          (IsThetaPshPotential.max (hu i) hv) hV.plurisubharmonic)
        (endpointMixedPotential_thetaPlurisubharmonic θ j (u i) V (hu i) hV.plurisubharmonic)
      exact congrArg (fun μ : Measure M => μ univ) he
    refine ⟨hr, ?_⟩
    change Tendsto (fun i => (endpointMixedMass θ V (fun x => max (u i x) (v x))
      hV.plurisubharmonic (IsThetaPshPotential.max (hu i) hv) j).toReal)
      F (𝓝 (endpointMixedMass θ V v hV.plurisubharmonic hv j).toReal)
    simpa only [hmass, Function.comp_def] using hr

/-- In the explicitly selected actual distance-generated native topology,
ordered convergence is equivalent to the one actual diagonal mass limit. -/
theorem tendsto_native_iff_diagonalPotentialMass_of_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hle : ∀ i, v.val ≤ (w i).val) (hvpos : 0 < diagonalPotentialMass θ v.val v.property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w F (𝓝 v) ↔ Tendsto (fun i => diagonalPotentialMass θ (w i).val (w i).property)
      F (𝓝 (diagonalPotentialMass θ v.val v.property)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig]
  exact tendsto_singularityDistance_iff_diagonalPotentialMass_of_le omega θ hbig
    F (fun i => (w i).property) v.property hle hvpos

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion
