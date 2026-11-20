import SGPT.Foundations.Analysis.Pending.AnalyticAntitoneIGoodLimit

set_option autoImplicit false

/-! # Actual positive I-good model limits in arbitrary big backgrounds -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticAntitoneBigIGoodLimit

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus
  DiagonalMass RelativeEnergy ThetaPshL1Topology
  SingularCanonicalSingularityDistance ActualDecreasingModelPositiveInfimum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual analytic stages internally produce a positive ordinary model,
its I-goodness, and the original stages' genuine native convergence. -/
theorem exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {v : ℕ → M → EReal}
    (hv : ∀ j, IsThetaPshPotential θ.val (v j))
    (hA : ∀ j, HasManifoldAnalyticSingularityType (n := n) (v j))
    (hanti : Antitone v) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ j, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (v j) (hv j)) :
    ∃ hτ : IsModelPotential θ (⨅ j, singularityEnvelope θ.val (v j)),
      IGoodWith θ (⨅ j, singularityEnvelope θ.val (v j)) hτ.plurisubharmonic ∧
      Tendsto (fun j => (⟨v j, hv j⟩ : ThetaPshL1 θ.val))
        atTop (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace omega θ
            (hbig)).toUniformSpace.toTopologicalSpace
          ⟨⨅ j, singularityEnvelope θ.val (v j), hτ.plurisubharmonic⟩) := by
  let P : ℕ → M → EReal := fun j => singularityEnvelope θ.val (v j)
  have hpos (j : ℕ) : HasPositivePotentialMass θ (v j) (hv j) :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le (hbound j)
  have hP (j : ℕ) : IsModelPotential θ (P j) := by
    have hp := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
      θ.property.2 (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
    exact ⟨hp, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (v j) (hv j) (hpos j)).symm,
      (singularityEnvelopeMassPreserving omega θ (v j) (hv j) hp).symm ▸ hpos j⟩
  have hPanti : Antitone P := fun i j hij =>
    singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hanti hij x)
  have hPbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (P j) (hP j).plurisubharmonic :=
    (hbound j).trans_eq
      (singularityEnvelopeMassPreserving omega θ (v j) (hv j)
        (hP j).plurisubharmonic).symm
  have hτ := isModelPotential_iInf_of_uniform_positive_stage_mass omega hP hPanti hδ hPbound
  have hPI (j : ℕ) : IsIModelPotential θ.val (P j) := by
    have he := (AnalyticPotentialsIGood.iGoodWith_of_analytic_type_of_positive_mass
      omega (hv j) (hA j) (hpos j)).envelope_eq
    change IsIModelPotential θ.val (singularityEnvelope θ.val (v j))
    rw [he]
    exact iSingularityEnvelope_isIModelPotential θ.val θ.property.1 θ.property.2
      (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
  have hτI := ActualIEnvelopeOrderInfimum.isIModelPotential_iInf_of_isThetaPshPotential
    θ hPI hτ.plurisubharmonic
  refine ⟨hτ, ⟨hτ.positive_mass, hτ.envelope_eq.symm.trans hτI.envelope_eq⟩, ?_⟩
  let := singularityPseudoMetricSpace omega θ (hbig)
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ
      (hbig)).toUniformSpace.toTopologicalSpace
  let x : ℕ → ThetaPshL1 θ.val := fun j => ⟨v j, hv j⟩
  let w : ℕ → ThetaPshL1 θ.val := fun j => ⟨P j, (hP j).plurisubharmonic⟩
  let τ : ThetaPshL1 θ.val := ⟨⨅ j, P j, hτ.plurisubharmonic⟩
  have hwlim : Tendsto w atTop (𝓝 τ) :=
    SingularCanonicalSingularityDecreasingModels.tendsto_native_iInf_of_uniform_positive_stage_mass
      omega θ (hbig) w hP hPanti hδ hPbound
  have hzero (j : ℕ) : dist (x j) (w j) = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        omega θ (hbig) (hv j) (hP j).plurisubharmonic).mpr
        (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
          omega θ (hv j))
    change (singularityDistance omega θ (hbig) (v j) (P j)).toReal = 0
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

end SGPT.Foundations.Analysis.Pending.AnalyticAntitoneBigIGoodLimit
