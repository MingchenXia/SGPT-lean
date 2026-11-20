import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.Envelopes.SourceRooftopMassCalculus
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich

/-! # Whole original model subsequence sandwich

The lower sequence produced by actual model geometry supplies a genuine
common minorant before each finite raw source roof is identified. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

/-- The literal original finite tail, using the all-source common-minorant roof. -/
def sourceFiniteTailRooftop {X : Type*} [TopologicalSpace X]
    {A : VariableComplexAtlas X} (θ : AtlasClosedRealOneOneForm A)
    (u : ℕ → X → EReal) (i : ℕ) : ℕ → X → EReal
  | 0 => u i
  | k + 1 => thetaRooftop θ (sourceFiniteTailRooftop θ u i k) (u (i + k + 1))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A genuine produced lower barrier makes every finite source tail genuine,
then identifies its entire raw roof with the actual native obstacle roof. -/
theorem sourceFiniteTailRooftop_eq_native_of_lower
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : ℕ → M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSH θ (u j))
    {h : M → EReal} (hh : (ofFixedModel n M).IsThetaPSH θ h) (i : ℕ)
    (hlower : ∀ k, h ≤ SingularModelDarvasFiniteRooftopChains.finiteTailRooftop
      (atlasClosedFormToNative θ) u i k) :
    ∀ k, (ofFixedModel n M).IsThetaPSH θ (sourceFiniteTailRooftop θ u i k) ∧
      sourceFiniteTailRooftop θ u i k =
        SingularModelDarvasFiniteRooftopChains.finiteTailRooftop
          (atlasClosedFormToNative θ) u i k := by
  intro k
  induction k with
  | zero => exact ⟨hu i, rfl⟩
  | succ k ih =>
    have hn := (isThetaPSH_iff_nativeThetaPotential θ _).mp ih.1
    have hb := (isThetaPSH_iff_nativeThetaPotential θ _).mp (hu (i + k + 1))
    have hleft : h ≤ sourceFiniteTailRooftop θ u i k := by
      rw [ih.2]
      exact hlower k
    have hright : h ≤ u (i + k + 1) := by
      apply (hlower (k + 1)).trans
      change RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ)
        (SingularModelDarvasFiniteRooftopChains.finiteTailRooftop
          (atlasClosedFormToNative θ) u i k) (u (i + k + 1)) ≤ _
      rw [← ih.2]
      exact RelativeDarvasDistance.rooftop_le_right hn hb
    have hroof := isThetaPSH_thetaRooftop_of_nonempty ih.1 (hu (i + k + 1))
      ⟨⟨h, hh, hleft, hright⟩⟩
    refine ⟨hroof, ?_⟩
    change thetaRooftop θ (sourceFiniteTailRooftop θ u i k) (u (i + k + 1)) = _
    rw [sourceThetaRooftop_eq_native ih.1 (hu (i + k + 1))
      (sourceThetaRooftop_native_genuine ih.1 (hu (i + k + 1)) hroof), ih.2]
    rfl

variable [MeasurableSpace M] [BorelSpace M]

/-- Whole original `prop:incanddec`: original models, strict subsequence,
both literal source tail formulas, actual monotonicity and both actual dS limits.
The target is only genuine PSH, and no limiting certificate is an input. -/
theorem sourceSingularityModelSandwich
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (ui : ℕ → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hmodels : ∀ i, SourceModelPotential θ (ui i).val) {δ : ℝ}
    (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ)
    (hlim : Tendsto ui atTop (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology ω θ hbig) u)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ η ψ : ℕ → SourceThetaPotentialL1 θ,
      (∀ i, (η i).val = ⨅ k, sourceFiniteTailRooftop θ (fun j ↦ (ui (f j)).val) i k) ∧
      (∀ i, (ψ i).val = uscRegularization (⨆ j, (ui (f (i + j))).val)) ∧
      (∀ i, SourceModelPotential θ (η i).val) ∧ Monotone (fun i ↦ (η i).val) ∧
      (∀ x, Antitone fun i ↦ (ψ i).val x) ∧
      (∀ i, (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ψ i).val) ∧
      Tendsto η atTop (@nhds (SourceThetaPotentialL1 θ)
        (sourceSingularityTopology ω θ hbig) u) ∧
      Tendsto ψ atTop (@nhds (SourceThetaPotentialL1 θ)
        (sourceSingularityTopology ω θ hbig) u) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (a : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
  have hnlim := hmap.tendsto_nhds_iff.mp hlim
  obtain ⟨f, hf, η, ψ, hηeq, hψeq, hηmodel, hηmono, hψanti, hbetween, hηlim, hψlim⟩ :=
    SingularCanonicalSingularityModelSandwich.exists_strictMono_monotone_sandwich_of_tendsto
      ω (atlasClosedFormToNative θ) hbig
      (fun i ↦ sourceThetaPotentialL1EquivNative θ (ui i))
      (sourceThetaPotentialL1EquivNative θ u)
      (fun i ↦ (sourceModelPotential_iff_native θ _).mp (hmodels i)) hδ hstage hnlim
  let ηs : ℕ → SourceThetaPotentialL1 θ :=
    fun i ↦ (sourceThetaPotentialL1EquivNative θ).symm (η i)
  let ψs : ℕ → SourceThetaPotentialL1 θ :=
    fun i ↦ (sourceThetaPotentialL1EquivNative θ).symm (ψ i)
  have hfinite (i k : ℕ) :
      sourceFiniteTailRooftop θ (fun j ↦ (ui (f j)).val) i k =
        SingularModelDarvasFiniteRooftopChains.finiteTailRooftop
          (atlasClosedFormToNative θ) (fun j ↦ (ui (f j)).val) i k := by
    apply (sourceFiniteTailRooftop_eq_native_of_lower (fun j ↦ (ui (f j)).property)
      (ηs i).property i ?_ k).2
    intro a
    change (η i).val ≤ _
    rw [hηeq i]
    exact iInf_le _ a
  refine ⟨f, hf, ηs, ψs, ?_, ?_, ?_, hηmono, hψanti, hbetween, ?_, ?_⟩
  · intro i
    change (η i).val = _
    rw [hηeq i]
    exact iInf_congr fun k ↦ (hfinite i k).symm
  · exact hψeq
  · intro i
    exact (sourceModelPotential_iff_native θ _).mpr (hηmodel i)
  · apply hmap.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, ηs, Equiv.apply_symm_apply] using hηlim
  · apply hmap.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, ψs, Equiv.apply_symm_apply] using hψlim

end SGPT.PSH.VariableComplexAtlas
