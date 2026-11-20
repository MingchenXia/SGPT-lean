import SGPT.NPP.MassPushforwardInvariance
import SGPT.BDivisor.VolumeBDivisor
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

/-!
# Volumes of classes under push-forward along modifications

Source `prop:cones_modif2`, item 2 (chapter `chapter_envelopes.tex`): for a proper bimeromorphic
morphism `π : Y → X` from a Kähler manifold `Y` and a big class `β ∈ H^{1,1}(Y, ℝ)`, the class
`π_*β` is big and `vol π_*β ≥ vol β`. (Item 1 is
`SGPT.PSH.VariableComplexAtlas.sourceClassVolume_modification_pullback` and
`SGPT.PSH.VariableComplexAtlas.isBigClass_modification_pullback`.)

The proof is the source's: let `S = θ + ddᶜV_θ` be a current with minimal singularities in `β`.
Then `π_*S` is a closed positive current in `π_*β` (`SGPT.BDivisor.currentPushforward`), hence
`π_*S = θ' + ddᶜu'` for any representative `θ'` of `π_*β`
(`PositiveCurrentPrescribedBottChernRepresentation`). A current with minimal singularities in
`π_*β` is less singular than `π_*S`, so by monotonicity of non-pluripolar masses
`vol π_*β ≥ ∫_X (π_*S)^n`, and `∫_X (π_*S)^n = ∫_Y S^n = vol β` by the push-forward half of
`prop:nppmassinv` (`SGPT.NPP.sourceMixedNonPluripolarMass_modification_pushforward`). The volume
inequality holds for every pseudo-effective `β`. Bigness of `π_*β` follows from
`∫_X (π_*S)^n = vol β > 0` and Boucksom's criterion.

Consequence for b-divisors (`def:volb`): along every domination of models carrying Kähler
forms, `vol (g_* β) ≥ vol β` (`pushforwardVolumeMonotone_of_kahler`), so — when all models are
Kähler, as for the book's models (compositions of blow-ups of the Kähler manifold `X`) — the net
`π ↦ vol 𝔻_π` is decreasing and converges to `vol 𝔻` (`tendsto_vol_of_kahler`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.PSH.VariableComplexAtlas SGPT.NPP

section ClassVolume

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)

include hπ in
/-- **The push-forward of `θ + ddᶜφ` in the push-forward class, with the same mass.** For every
`θ`-psh `φ` on `Y` there are a representative `θ'` of `π_*{θ}` and a `θ'`-psh `u'` with
`π_*(θ + ddᶜφ) = θ' + ddᶜu'` and `∫_X (θ' + ddᶜu')^n = ∫_Y (θ + ddᶜφ)^n`. -/
theorem exists_pushforward_potential_mass (θ : ClosedRealOneOneForm (m + 1) Y) {φ : Y → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    ∃ (θ' : ClosedRealOneOneForm (m + 1) X) (u' : X → EReal)
      (hu' : IsThetaPshPotential θ'.val u'),
      RealBottChern.ofRepresentative θ' =
        classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (RealBottChern.ofRepresentative θ) ∧
      currentPushforward hπ.1 (thetaPotentialCurrent θ.val φ hφ) =
        thetaPotentialCurrent θ'.val u' hu' ∧
      DiagonalMass.diagonalPotentialMass θ' u' hu' = DiagonalMass.diagonalPotentialMass θ φ hφ := by
  let S := ThetaPotentialCurrentBottChernClass.thetaClosedCurrent θ φ hφ
  have hS : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S =
      RealBottChern.ofRepresentative θ :=
    ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ φ hφ
  let c := classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
    (RealBottChern.ofRepresentative θ)
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative θ' = c := ⟨Quotient.out c, Quotient.out_eq c⟩
  have hpush : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S) =
      RealBottChern.ofRepresentative θ' := by
    rw [hθ', bottChernClass_closedCurrentPushforward, hS]
  have hpos : GlobalPositiveCurrentACRestriction.IsFullPositive
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S).val :=
    isFullPositive_currentPushforward hπ.1 fun e α hα =>
      thetaPotentialCurrent_full_positive θ.val φ hφ e α hα
  obtain ⟨u', hu', hread, -⟩ :=
    PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S) θ' hpos hpush
  have heq : currentPushforward hπ.1 (thetaPotentialCurrent θ.val φ hφ) =
      thetaPotentialCurrent θ'.val u' hu' := hread
  refine ⟨θ', u', hu', hθ', heq, ?_⟩
  exact MassPushforward.globalMixedMeasure_univ_pushforward hπ (fun _ => θ) (fun _ => φ)
    (fun _ => hφ) (fun _ => θ') (fun _ => u') (fun _ => hu') (fun _ => heq)

variable [ConnectedSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y] in
include hπ in
/-- A modification of a connected manifold is connected. -/
theorem connectedSpace_of_isAnalyticModification : ConnectedSpace Y := by
  apply connectedSpace_iff_univ.mpr
  have hc := AnalyticModificationConnectedFibres.isConnected_preimage_of_isConnected hπ
    (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens X) isConnected_univ
  change IsConnected (π ⁻¹' (univ : Set X)) at hc
  simpa only [preimage_univ] using hc

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- A big class is pseudo-effective (it contains a Kähler current). -/
theorem classPseudoeffective_of_isBigClass (ωY : KahlerBackground (m + 1) Y)
    {β : RealBottChern (m + 1) Y} (hβ : IsBigClass β) : ClassPseudoeffectiveViaPotentials β := by
  induction β using Quotient.inductionOn with
  | h θN =>
    change IsBigClass (RealBottChern.ofRepresentative θN) at hβ
    obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ :=
      DivisorialDomination.exists_isThetaPshPotential_sub_smul_of_isBigClass ωY _ hβ
    have hu₀' : IsThetaPshPotential θN.val u₀ := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
        (KahlerDomination.isSemipositive_smul ωY.isSemipositive hδ₀.le)
      rwa [sub_add_cancel] at h
    exact (classPseudoeffectiveViaPotentials_ofRepresentative θN).mpr ⟨u₀, hu₀'⟩

include hπ in
/-- Source `prop:cones_modif2`, item 2, volume inequality: for every pseudo-effective (in
particular every big) class `β` on `Y`, `vol π_*β ≥ vol β`. (`Y` is connected as soon as `X`
is, `connectedSpace_of_isAnalyticModification`.) -/
theorem sourceClassVolume_le_classPushforward [ConnectedSpace Y] (ωX : KahlerBackground (m + 1) X)
    (ωY : KahlerBackground (m + 1) Y) {β : RealBottChern (m + 1) Y}
    (hβ : ClassPseudoeffectiveViaPotentials β) :
    sourceClassVolume β ≤
      sourceClassVolume (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) β) := by
  obtain ⟨θ, hθβ, hmin⟩ := exists_minimalSingularities_of_pseudoeffective hβ
  have hV := hmin.1
  have hVn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hV
  obtain ⟨θ', u', hu', hcl, -, hmass⟩ :=
    exists_pushforward_potential_mass hπ (atlasClosedFormToNative θ) hVn
  rw [← hθβ, ← hcl, sourceClassVolume_eq_minimalEnvelope_mass ωY hV]
  have hu'A : (ofFixedModel (m + 1) X).IsThetaPSH (nativeClosedFormToAtlas θ') u' :=
    isThetaPSH_nativeClosedFormToAtlas hu'
  have hrt : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative
      (atlasClosedFormToNative (nativeClosedFormToAtlas θ')) := by
    rw [sourceNativeAtlasForm_roundTrip]
  rw [hrt, sourceClassVolume_eq_minimalEnvelope_mass ωX hu'A]
  have hmono := sourcePotentialNonPluripolarMass_mono ωX hu'A
    (sourceMinimalEnvelope_thetaPSH_of_mem hu'A) (singularityLE_sourceMinimalEnvelope_of_thetaPSH hu'A)
  refine le_trans (le_of_eq ?_) hmono
  have hY : sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
      (sourceMinimalEnvelope_thetaPSH_of_mem hV) univ =
      DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ) (sourceMinimalEnvelope θ)
        hVn := rfl
  have hX : sourcePotentialNonPluripolarMeasure (nativeClosedFormToAtlas θ') u' hu'A univ =
      DiagonalMass.diagonalPotentialMass θ' u' hu' := by
    change DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative (nativeClosedFormToAtlas θ'))
      u' _ = _
    simp only [sourceNativeAtlasForm_roundTrip]
  rw [hY, hX, hmass]

include hπ in
/-- Source `prop:cones_modif2`, item 2, bigness: the push-forward of a big class is big. -/
theorem isBigClass_classPushforward (ωX : KahlerBackground (m + 1) X)
    (ωY : KahlerBackground (m + 1) Y) {β : RealBottChern (m + 1) Y} (hβ : IsBigClass β) :
    IsBigClass (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) β) := by
  have : ConnectedSpace Y := connectedSpace_of_isAnalyticModification hπ
  induction β using Quotient.inductionOn with
  | h θN =>
    change IsBigClass (RealBottChern.ofRepresentative θN) at hβ
    obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ :=
      DivisorialDomination.exists_isThetaPshPotential_sub_smul_of_isBigClass ωY _ hβ
    have hu₀' : IsThetaPshPotential θN.val u₀ := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
        (KahlerDomination.isSemipositive_smul ωY.isSemipositive hδ₀.le)
      rwa [sub_add_cancel] at h
    let θ := nativeClosedFormToAtlas θN
    have hu : (ofFixedModel (m + 1) Y).IsThetaPSH θ u₀ := isThetaPSH_nativeClosedFormToAtlas hu₀'
    have hVA := sourceMinimalEnvelope_thetaPSH_of_mem hu
    have hVn : IsThetaPshPotential θN.val (thetaPshSupremum θN.val) := by
      have h := (isThetaPSH_iff_nativeThetaPotential θ _).mp hVA
      rw [sourceMinimalEnvelope_eq_native] at h
      simpa only [θ, sourceNativeAtlasForm_roundTrip] using h
    have hposY := RestrictedApproximantMass.diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass
      ωY θN hβ hVn
    obtain ⟨θ', u', hu', hcl, -, hmass⟩ := exists_pushforward_potential_mass hπ θN hVn
    change IsBigClass (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (RealBottChern.ofRepresentative θN))
    rw [← hcl]
    exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos (Nat.succ_pos m) ωX θ' hu'
      (hmass ▸ hposY)

include hπ in
/-- Source `prop:cones_modif2`, item 2, as stated: for a big class `β` on `Y`, `π_*β` is big and
`vol π_*β ≥ vol β`. -/
theorem isBigClass_classPushforward_and_le [ConnectedSpace Y] (ωX : KahlerBackground (m + 1) X)
    (ωY : KahlerBackground (m + 1) Y) {β : RealBottChern (m + 1) Y} (hβ : IsBigClass β) :
    IsBigClass (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) β) ∧
      sourceClassVolume β ≤
        sourceClassVolume (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) β) :=
  ⟨isBigClass_classPushforward hπ ωX ωY hβ,
    sourceClassVolume_le_classPushforward hπ ωX ωY (classPseudoeffective_of_isBigClass ωY hβ)⟩

end ClassVolume

/-! ### The volume of a b-divisor as a decreasing limit -/

namespace WeilBDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- `prop:cones_modif2`, item 2, along the dominations of the model system: when every model
carries a Kähler form (as the book's models, compositions of blow-ups of the Kähler `X`, do), the
volume does not decrease under push-forward along dominations. -/
theorem pushforwardVolumeMonotone_of_kahler
    (hK : ∀ π : Modification (m + 1) X, Nonempty (KahlerBackground (m + 1) π.carrier)) :
    PushforwardVolumeMonotone (m + 1) X (Nat.succ_pos m) := by
  intro π π' h β hβ
  let : MeasurableSpace π.carrier := borel π.carrier
  have : BorelSpace π.carrier := ⟨rfl⟩
  let : MeasurableSpace π'.carrier := borel π'.carrier
  have : BorelSpace π'.carrier := ⟨rfl⟩
  obtain ⟨ω⟩ := hK π
  obtain ⟨ω'⟩ := hK π'
  exact sourceClassVolume_le_classPushforward (Modification.Dominates.isAnalyticModification h)
    ω ω' hβ

/-- **`vol 𝔻` is the limit of the decreasing net `π ↦ vol 𝔻_π`** (`def:volb`), when all models
carry Kähler forms. -/
theorem tendsto_vol_of_kahler
    (hK : ∀ π : Modification (m + 1) X, Nonempty (KahlerBackground (m + 1) π.carrier))
    {𝔻 : WeilBDivisor (m + 1) X (Nat.succ_pos m)} (h𝔻 : 𝔻.IsPseudoeffective) :
    Tendsto (fun π => Modification.classVolume π (𝔻.onModel π)) atTop (𝓝 𝔻.vol) :=
  tendsto_vol (pushforwardVolumeMonotone_of_kahler hK) h𝔻

/-- Under the same hypothesis, the net `π ↦ vol 𝔻_π` is decreasing. -/
theorem antitone_classVolume_of_kahler
    (hK : ∀ π : Modification (m + 1) X, Nonempty (KahlerBackground (m + 1) π.carrier))
    {𝔻 : WeilBDivisor (m + 1) X (Nat.succ_pos m)} (h𝔻 : 𝔻.IsPseudoeffective) :
    Antitone fun π => Modification.classVolume π (𝔻.onModel π) :=
  antitone_classVolume (pushforwardVolumeMonotone_of_kahler hK) h𝔻

end WeilBDivisor

end SGPT.BDivisor
