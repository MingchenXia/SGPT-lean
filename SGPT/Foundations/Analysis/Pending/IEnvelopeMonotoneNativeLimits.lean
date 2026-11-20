import SGPT.Foundations.Analysis.Pending.IEnvelopeDecreasingModelInfimum
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels

set_option autoImplicit false

/-! # Actual typed I-envelopes and their two monotone positive native limit branches -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeMonotoneNativeLimits

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  DiagonalMass MixedMass ActualDecreasingModelInfimum
  IEnvelopeIncreasingRegularizedSupremum IEnvelopeDecreasingModelInfimum
  ActualIEnvelopeOrderInfimum SingularCanonicalSingularityIncreasing
  SingularCanonicalSingularityDecreasingModels IncreasingMixedDirectedNets

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The literal I-envelope as a genuine strong-PSH reader; the witness is
independently produced, with no mass or continuity certificate. -/
def iEnvelopeReader (θ : ClosedRealOneOneForm n M) (u : ThetaPshL1 θ.val) :
    ThetaPshL1 θ.val :=
  ⟨iSingularityEnvelope θ.val u.val,
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      u.property.1.hasSmoothLocalPotentials u.val u.property⟩

/-- The genuine positive regularized supremum is internally produced and
the literal increasing I-envelope identity transports its native limit. -/
theorem tendsto_iEnvelope_of_monotone_uniformlyBounded
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (w : ℕ → ThetaPshL1 θ.val) (hmono : Monotone fun j => (w j).val)
    {C : ℝ} (hC : ∀ j x, (w j).val x ≤ (C : EReal))
    (hpos : HasPositivePotentialMass θ (uscRegularization (⨆ j, (w j).val))
      (isThetaPshPotential_regularized_of_uniformlyBounded (fun j => (w j).property) hC)) :
    let U : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ j, (w j).val),
      isThetaPshPotential_regularized_of_uniformlyBounded (fun j => (w j).property) hC⟩
    Tendsto (fun j => iEnvelopeReader θ (w j)) atTop
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        (iEnvelopeReader θ U)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let U : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ j, (w j).val),
    isThetaPshPotential_regularized_of_uniformlyBounded (fun j => (w j).property) hC⟩
  let B : ℕ → ThetaPshL1 θ.val := fun j => iEnvelopeReader θ (w j)
  have hBmono : Monotone fun j => (B j).val := by
    intro i j hij
    exact iSingularityEnvelope_le_of_iOrderOnManifold θ (w j).property
      (iOrderOnManifold_of_le (w j).property.1.quasiPlurisubharmonic (hmono hij))
  have hB0 (j : ℕ) (x : M) : (B j).val x ≤ (0 : EReal) :=
    iSingularityEnvelope_le_zero θ.val (w j).val x
  let S : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ j, (B j).val),
    isThetaPshPotential_regularized_of_uniformlyBounded (fun j => (B j).property) hB0⟩
  have hlim : Tendsto B atTop (𝓝 S) :=
    tendsto_native_of_monotone_uniformlyBounded omega θ hbig B hBmono hB0
  have heq : S = iEnvelopeReader θ U := by
    apply Subtype.ext
    exact iSingularityEnvelope_regularized_iSup_eq omega θ hbig
      (fun j => (w j).property) hmono U.property rfl hpos
  simpa only [heq] using hlim

/-- Actual normalized model competitors, true finite mass and the literal
decreasing identity internally produce the decreasing native I-envelope limit. -/
theorem tendsto_iEnvelope_of_antitone_models
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (w : ℕ → ThetaPshL1 θ.val) (hmodel : ∀ j, IsModelPotential θ (w j).val)
    (hanti : Antitone fun j => (w j).val)
    (hpos : HasPositivePotentialMass θ (⨅ j, (w j).val)
      (isThetaPshPotential_iInf_of_antitone_model hmodel hanti)) :
    let U : ThetaPshL1 θ.val := ⟨⨅ j, (w j).val,
      isThetaPshPotential_iInf_of_antitone_model hmodel hanti⟩
    Tendsto (fun j => iEnvelopeReader θ (w j)) atTop
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        (iEnvelopeReader θ U)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let U : ThetaPshL1 θ.val := ⟨⨅ j, (w j).val,
    isThetaPshPotential_iInf_of_antitone_model hmodel hanti⟩
  let B : ℕ → ThetaPshL1 θ.val := fun j => iEnvelopeReader θ (w j)
  have hw0 (j : ℕ) : (w j).val ≤ 0 := by
    rw [(hmodel j).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (w j).val
  have hwB (j : ℕ) : (w j).val ≤ (B j).val :=
    le_iSingularityEnvelope (w j).property (hw0 j) (IEquivalentOnManifold.refl (w j).val)
  have hBmodel (j : ℕ) : IsModelPotential θ (B j).val :=
    ⟨(B j).property,
      (singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
        (w j).property.1.hasSmoothLocalPotentials (w j).val (w j).property).symm,
      (hmodel j).positive_mass.trans_le (diagonalPotentialMass_mono_of_kahler
        omega (w j).property (B j).property (MoreSingularOn.of_le fun x _ => hwB j x))⟩
  have hBanti : Antitone fun j => (B j).val := by
    intro i j hij
    exact iSingularityEnvelope_le_of_iOrderOnManifold θ (w i).property
      (iOrderOnManifold_of_le (w i).property.1.quasiPlurisubharmonic (hanti hij))
  let L : ℝ≥0∞ := diagonalPotentialMass θ U.val U.property
  have hL : 0 < L := hpos
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => U.property.1)).ne
  let δ : ℝ := L.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hL.ne' hLtop
  have hδL : ENNReal.ofReal δ = L := ENNReal.ofReal_toReal hLtop
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (B j).val (hBmodel j).plurisubharmonic := by
    rw [hδL]
    exact diagonalPotentialMass_mono_of_kahler omega U.property (B j).property
      (MoreSingularOn.of_le fun x _ => ((iInf_le (fun i => (w i).val) j) x).trans (hwB j x))
  let S : ThetaPshL1 θ.val := ⟨⨅ j, (B j).val,
    isThetaPshPotential_iInf_of_antitone_model hBmodel hBanti⟩
  have hlim : Tendsto B atTop (𝓝 S) :=
    tendsto_native_iInf_of_uniform_positive_stage_mass omega θ hbig
      B hBmodel hBanti hδ hbound
  have heq : S = iEnvelopeReader θ U := by
    apply Subtype.ext
    exact iInf_iSingularityEnvelope_eq omega θ hbig hmodel hanti hpos
  simpa only [heq] using hlim

end

end SGPT.Foundations.Analysis.Pending.IEnvelopeMonotoneNativeLimits
