import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # Actual positive I-good model limits of decreasing analytic stages -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticAntitoneIGoodLimit

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus
  DiagonalMass RelativeEnergy ThetaPshL1Topology PluripolarCapacityDichotomy
  SingularCanonicalSingularityDistance ActualDecreasingModelPositiveInfimum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual analytic stages internally produce a positive ordinary model,
its I-goodness, and the original stages' genuine native convergence. -/
theorem exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
    (omega β : KahlerBackground n M) {v : ℕ → M → EReal}
    (hv : ∀ j, IsThetaPshPotential β.form.val (v j))
    (hA : ∀ j, HasManifoldAnalyticSingularityType (n := n) (v j))
    (hanti : Antitone v) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ j, ENNReal.ofReal δ ≤ diagonalPotentialMass β.form (v j) (hv j)) :
    ∃ hτ : IsModelPotential β.form (⨅ j, singularityEnvelope β.form.val (v j)),
      IGoodWith β.form (⨅ j, singularityEnvelope β.form.val (v j)) hτ.plurisubharmonic ∧
      Tendsto (fun j => (⟨v j, hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omega β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
          ⟨⨅ j, singularityEnvelope β.form.val (v j), hτ.plurisubharmonic⟩) := by
  let P : ℕ → M → EReal := fun j => singularityEnvelope β.form.val (v j)
  have hpos (j : ℕ) : HasPositivePotentialMass β.form (v j) (hv j) :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le (hbound j)
  have hP (j : ℕ) : IsModelPotential β.form (P j) := by
    have hp := singularityEnvelope_isThetaPshPotential β.form.val β.form.property.1
      β.form.property.2 (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
    exact ⟨hp, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega β.form (v j) (hv j) (hpos j)).symm,
      (singularityEnvelopeMassPreserving omega β.form (v j) (hv j) hp).symm ▸ hpos j⟩
  have hPanti : Antitone P := fun i j hij =>
    singularityEnvelope_mono (θ := β.form.val)
      (MoreSingularOn.of_le fun x _ => hanti hij x)
  have hPbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass β.form (P j) (hP j).plurisubharmonic :=
    (hbound j).trans_eq
      (singularityEnvelopeMassPreserving omega β.form (v j) (hv j)
        (hP j).plurisubharmonic).symm
  have hτ := isModelPotential_iInf_of_uniform_positive_stage_mass omega hP hPanti hδ hPbound
  have hPI (j : ℕ) : IsIModelPotential β.form.val (P j) := by
    have he := (AnalyticPotentialsIGood.iGoodWith_of_analytic_type_of_positive_mass
      omega (hv j) (hA j) (hpos j)).envelope_eq
    change IsIModelPotential β.form.val (singularityEnvelope β.form.val (v j))
    rw [he]
    exact iSingularityEnvelope_isIModelPotential β.form.val β.form.property.1 β.form.property.2
      (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
  have hτI := ActualIEnvelopeOrderInfimum.isIModelPotential_iInf_of_isThetaPshPotential
    β.form hPI hτ.plurisubharmonic
  refine ⟨hτ, ⟨hτ.positive_mass, hτ.envelope_eq.symm.trans hτI.envelope_eq⟩, ?_⟩
  let := singularityPseudoMetricSpace omega β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omega β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  let x : ℕ → ThetaPshL1 β.form.val := fun j => ⟨v j, hv j⟩
  let w : ℕ → ThetaPshL1 β.form.val := fun j => ⟨P j, (hP j).plurisubharmonic⟩
  let τ : ThetaPshL1 β.form.val := ⟨⨅ j, P j, hτ.plurisubharmonic⟩
  have hwlim : Tendsto w atTop (𝓝 τ) :=
    SingularCanonicalSingularityDecreasingModels.tendsto_native_iInf_of_uniform_positive_stage_mass
      omega β.form (isBigClass_kahler β) w hP hPanti hδ hPbound
  have hzero (j : ℕ) : dist (x j) (w j) = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        omega β.form (isBigClass_kahler β) (hv j) (hP j).plurisubharmonic).mpr
        (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
          omega β.form (hv j))
    change (singularityDistance omega β.form (isBigClass_kahler β) (v j) (P j)).toReal = 0
    rw [hd, EReal.toReal_zero]
  have hdist (j : ℕ) : dist (x j) τ = dist (w j) τ := by
    apply le_antisymm
    · simpa only [hzero j, zero_add] using dist_triangle (x j) (w j) τ
    · have hh := dist_triangle (w j) (x j) τ
      rw [dist_comm (w j) (x j), hzero j, zero_add] at hh
      exact hh
  change Tendsto x atTop (𝓝 τ)
  rw [tendsto_iff_dist_tendsto_zero] at hwlim ⊢
  simpa only [hdist] using hwlim

end

end SGPT.Foundations.Analysis.Pending.AnalyticAntitoneIGoodLimit
