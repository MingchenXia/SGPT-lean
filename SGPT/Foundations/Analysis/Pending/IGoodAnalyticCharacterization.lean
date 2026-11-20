import SGPT.Foundations.Analysis.Pending.PositiveNativeIGoodSequenceClosure
import SGPT.Foundations.Analysis.Pending.PositiveMassAnalyticCurrentSequences
import SGPT.Foundations.Analysis.Pending.BigClassIGoodMassCriterion
import SGPT.Foundations.Analysis.Pending.FullQEANativeIGoodCriterion

set_option autoImplicit false

/-! # Actual analytic, mass-volume, and literal envelope characterizations -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IGoodAnalyticCharacterization

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  PositiveNativeIGoodSequenceClosure PositiveMassAnalyticCurrentSequences
  BigClassIGoodMassCriterion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The original positive-mass source's three equivalent conditions,
including the internally produced analytic-current strengthening. -/
theorem analytic_native_mass_envelope_current_equivalences
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    let A : Prop := ∃ v : ℕ → ThetaPshL1 θ.val,
      (∀ j, HasManifoldAnalyticSingularityType (n := n) (v j).val) ∧
      Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨u, hu⟩)
    let K : Prop := ∃ v : ℕ → ThetaPshL1 θ.val,
      (∀ j, HasManifoldAnalyticSingularityType (n := n) (v j).val ∧
        ∃ δ : ℝ, 0 < δ ∧ IsThetaPshPotential (θ - δ • omega.form).val (v j).val) ∧
      Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨u, hu⟩)
    (A ↔ diagonalPotentialMass θ u hu = iVolume θ hu.1.hasSmoothLocalPotentials u hu) ∧
      (A ↔ singularityEnvelope θ.val u = iSingularityEnvelope θ.val u) ∧ (A ↔ K) := by
  dsimp only
  let U : ThetaPshL1 θ.val := ⟨u, hu⟩
  let A : Prop := ∃ v : ℕ → ThetaPshL1 θ.val,
    (∀ j, HasManifoldAnalyticSingularityType (n := n) (v j).val) ∧
    Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace U)
  let K : Prop := ∃ v : ℕ → ThetaPshL1 θ.val,
    (∀ j, HasManifoldAnalyticSingularityType (n := n) (v j).val ∧
      ∃ δ : ℝ, 0 < δ ∧ IsThetaPshPotential (θ - δ • omega.form).val (v j).val) ∧
    Tendsto v atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace U)
  have hAK : K → A := by
    rintro ⟨v, hv, hlim⟩
    exact ⟨v, fun j => (hv j).1, hlim⟩
  have hAI : A → IGoodWith θ u hu := by
    rintro ⟨v, hv, hlim⟩
    exact iGoodWith_of_analytic_native_sequence_positive_limit
      omega θ hbig v U hpos hv hlim
  have hIK : IGoodWith θ u hu → K := fun hgood =>
    exists_analytic_current_sequence_native_of_iGoodWith omega θ hbig hu hgood
  have hiff : A ↔ IGoodWith θ u hu := ⟨hAI, fun hgood => hAK (hIK hgood)⟩
  have hgoodEq : IGoodWith θ u hu ↔
      singularityEnvelope θ.val u = iSingularityEnvelope θ.val u :=
    ⟨fun hgood => hgood.envelope_eq, fun he => ⟨hpos, he⟩⟩
  exact ⟨hiff.trans (iGoodWith_iff_actual_mass_eq_iVolume omega θ hbig hu hpos),
    hiff.trans hgoodEq, ⟨fun ha => hIK (hAI ha), hAK⟩⟩

end

end SGPT.Foundations.Analysis.Pending.IGoodAnalyticCharacterization
