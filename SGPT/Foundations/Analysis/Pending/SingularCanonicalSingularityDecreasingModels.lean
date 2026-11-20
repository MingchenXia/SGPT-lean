import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelPositiveInfimum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # Actual singularity convergence of decreasing model sequences

SGPT PDF0231 Corollary 6.2.7, fixed-background sequence precursor, and
PDF0227's ordered mass criterion. Uniform positive stage masses internally
produce the genuine positive model infimum. Actual endpoint mixed masses
then produce the literal real singularity-distance limit and its native
pseudometric convergence. The full P-type net criterion and general Cauchy
completeness remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass MixedMass
  RelativeEnergy ActualDecreasingModelInfimum ActualDecreasingModelPositiveInfimum
  ActualMixedMassOrderedContinuity SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual endpoint tuples and their positive diagonal limits internally
produce every endpoint mass limit against any genuine positive-mass reference. -/
theorem tendsto_endpointMixedMass_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (u k)
      (hu k).plurisubharmonic) {p : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hpp : 0 < diagonalPotentialMass θ p hp) (j : Fin (n + 1)) :
    Tendsto (fun k => endpointMixedMass θ p (u k) hp (hu k).plurisubharmonic j) atTop
      (𝓝 (endpointMixedMass θ p (⨅ k, u k) hp
        (isThetaPshPotential_iInf_of_antitone_model hu hanti) j)) := by
  classical
  let U := ⨅ k, u k
  have hU : IsThetaPshPotential θ.val U :=
    isThetaPshPotential_iInf_of_antitone_model hu hanti
  have hUpos : 0 < diagonalPotentialMass θ U hU :=
    (isModelPotential_iInf_of_uniform_positive_stage_mass omega hu hanti hδ hbound).positive_mass
  let T : ℕ → Fin n → M → EReal := fun k => endpointMixedPotential j (u k) p
  let P : Fin n → M → EReal := endpointMixedPotential j U p
  have hP : ∀ i, IsThetaPshPotential θ.val (P i) := by
    intro i
    by_cases hi : i.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos hi] using hU
    · simpa only [P, endpointMixedPotential, if_neg hi] using hp
  have hT : ∀ k i, IsThetaPshPotential θ.val (T k i) := by
    intro k i
    by_cases hi : i.val < j.val
    · simpa only [T, endpointMixedPotential, if_pos hi] using (hu k).plurisubharmonic
    · simpa only [T, endpointMixedPotential, if_neg hi] using hp
  have hle : ∀ k i, P i ≤ T k i := by
    intro k i
    by_cases hi : i.val < j.val
    · simpa only [P, T, endpointMixedPotential, if_pos hi] using iInf_le u k
    · simp only [P, T, endpointMixedPotential, if_neg hi, le_refl]
  have hpos : ∀ i, 0 < diagonalPotentialMass θ (P i) (hP i) := by
    intro i
    by_cases hi : i.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos hi] using hUpos
    · simpa only [P, endpointMixedPotential, if_neg hi] using hpp
  have hdiag : ∀ i, Tendsto (fun k => diagonalPotentialMass θ (T k i) (hT k i))
      atTop (𝓝 (diagonalPotentialMass θ (P i) (hP i))) := by
    intro i
    by_cases hi : i.val < j.val
    · simpa only [P, T, endpointMixedPotential, if_pos hi] using
        tendsto_diagonalPotentialMass_iInf_of_uniform_positive_stage_mass omega hu hanti hδ hbound
    · simpa only [P, T, endpointMixedPotential, if_neg hi] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => diagonalPotentialMass θ p hp)
          atTop (𝓝 (diagonalPotentialMass θ p hp)))
  have hm := tendsto_globalMixedMass_of_le_of_diagonal_tendsto
    (θ := fun _ : Fin n => θ) omega atTop hP hT hle hpos hdiag
  simpa only [globalMixedMass, endpointMixedMass, endpointMixedMeasure] using hm

/-- The true positive infimum and all actual endpoint/maximum mass limits
internally yield the finite real defining singularity-distance limit. -/
theorem tendsto_singularityDistance_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (u k)
      (hu k).plurisubharmonic) :
    Tendsto (fun k => (singularityDistance omega θ hbig (u k) (⨅ a, u a)).toReal)
      atTop (𝓝 0) := by
  let U := ⨅ k, u k
  have hU : IsThetaPshPotential θ.val U :=
    isThetaPshPotential_iInf_of_antitone_model hu hanti
  let V := thetaPshSupremum θ.val
  have hV : IsModelPotential θ V := isModelPotential_thetaPshSupremum omega θ hbig
  apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig
    atTop (fun k => (hu k).plurisubharmonic) hU).mpr
  intro j
  have hm := tendsto_endpointMixedMass_iInf_of_uniform_positive_stage_mass
    omega hu hanti hδ hbound hV.plurisubharmonic hV.positive_mass j
  have ht : endpointMixedMass θ V U hV.plurisubharmonic hU j ≠ ⊤ :=
    (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ j U V hU hV.plurisubharmonic)).ne
  have hr := (ENNReal.continuousAt_toReal ht).tendsto.comp hm
  have hmax (k : ℕ) : (fun x => max (u k x) (U x)) = u k := by
    funext x
    exact max_eq_left (iInf_le u k x)
  have hmass (k : ℕ) : endpointMixedMass θ V (fun x => max (u k x) (U x))
      hV.plurisubharmonic (IsThetaPshPotential.max (hu k).plurisubharmonic hU) j =
      endpointMixedMass θ V (u k) hV.plurisubharmonic (hu k).plurisubharmonic j := by
    have htuple := congrArg (fun w => endpointMixedPotential j w V) (hmax k)
    have he := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
      (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
        (IsThetaPshPotential.max (hu k).plurisubharmonic hU) hV.plurisubharmonic)
      (endpointMixedPotential_thetaPlurisubharmonic θ j (u k) V
        (hu k).plurisubharmonic hV.plurisubharmonic)
    exact congrArg (fun μ : Measure M => μ univ) he
  refine ⟨hr, ?_⟩
  change Tendsto (fun k => (endpointMixedMass θ V (fun x => max (u k x) (U x))
    hV.plurisubharmonic (IsThetaPshPotential.max (hu k).plurisubharmonic hU) j).toReal)
    atTop (𝓝 (endpointMixedMass θ V U hV.plurisubharmonic hU j).toReal)
  simpa only [hmass, Function.comp_def] using hr

/-- The native actual distance-generated topology is explicitly selected;
the genuine limit and its distance convergence are both internally produced. -/
theorem tendsto_native_iInf_of_uniform_positive_stage_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (w : ℕ → ThetaPshL1 θ.val) (hu : ∀ k, IsModelPotential θ (w k).val)
    (hanti : Antitone fun k => (w k).val) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (w k).val
      (hu k).plurisubharmonic) :
    let U : ThetaPshL1 θ.val := ⟨⨅ k, (w k).val, isThetaPshPotential_iInf_of_antitone_model hu hanti⟩
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w atTop (𝓝 U) := by
  let U : ThetaPshL1 θ.val := ⟨⨅ k, (w k).val, isThetaPshPotential_iInf_of_antitone_model hu hanti⟩
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  change Tendsto w atTop (𝓝 U)
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig]
  exact tendsto_singularityDistance_iInf_of_uniform_positive_stage_mass omega θ hbig
    hu hanti hδ hbound

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
