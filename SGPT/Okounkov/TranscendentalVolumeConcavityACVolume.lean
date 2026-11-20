import SGPT.Envelopes.SourceClassVolume
import SGPT.Okounkov.TranscendentalVolumeConcavityStatement
import SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeRightLimit
import SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeBigness
import SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
import SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
import SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentEquivalence
import SGPT.Foundations.Analysis.Pending.Envelopes

/-!
# The volume of a class is Boucksom's absolutely continuous volume

Source: blueprint node `tok:ext-volume-concave` (Boucksom, *On the volume of a line bundle*,
Definition 1.3 and Theorem 1.2 for transcendental classes; the identification of the
non-pluripolar volume of `def:volcohclass` with Boucksom's volume is BEGZ10, and is proved here).

For a class `α` on a connected compact Kähler manifold `X` of dimension `n = m + 1`, the book's
volume `vol α = ∫_X ⟨T_min^n⟩` (`sourceClassVolume`, `def:volcohclass`) equals Boucksom's
volume `v(α) = sup_T ∫_X (T_ac)^n` over all closed positive `(1,1)`-currents `T ∈ α`
(TN's `originalCurrentACVolume`), `sourceClassVolume_eq_originalCurrentACVolume`:

* `≥`: for `T = θ + dd^c v`, `(T_ac)^n ≤ ⟨T^n⟩` (TN `ThetaCurrentGlobalACDomination`) and
  `∫ ⟨T^n⟩ ≤ ∫ ⟨T_min^n⟩` (monotonicity, `thm:mono`);
* `≤`: with Demailly's approximation `v_k ↓ V_θ`, `v_k ∈ PSH(X, θ + δ_k ω)` with analytic
  singularities smooth off their poles, `δ_k → 0`: for `δ_k < ε`,
  `∫ ⟨θ_{V_θ}^n⟩ ≤ ∫ ⟨(θ + εω)_{V_θ}^n⟩ ≤ ∫ ⟨(θ + εω)_{v_k}^n⟩ = ∫ ((θ + εω)_{v_k})_ac^n ≤ v(α + ε{ω})`,
  and `v(α + ε{ω}) → v(α)` as `ε ↓ 0` (TN `OriginalCurrentVolumeRightLimit`: Boucksom's
  calibrated currents, Theorem 4.6, and the semicontinuity Lemma 3.5).

Consequences: `vol α > 0 ⟺ α big` (`prop:nppposimpbig` and its converse, Boucksom Theorem 4.7),
monotonicity under the addition of semipositive forms, and the right limit
`vol(α + ε{ω}) → vol α` for pseudo-effective `α`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedMass
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
open SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas

section Congr

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Congruence of the diagonal non-pluripolar mass in the background and the potential. -/
theorem diagonalPotentialMass_congr {θ θ' : ClosedRealOneOneForm n M} {u u' : M → EReal}
    (hθ : θ = θ') (hu : u = u') (h : IsThetaPshPotential θ.val u)
    (h' : IsThetaPshPotential θ'.val u') :
    diagonalPotentialMass θ u h = diagonalPotentialMass θ' u' h' := by
  subst hθ
  subst hu
  rfl

end Congr

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- Congruence of the global AC top measure in the current. -/
theorem globalACtopMeasure_congr [MeasurableSpace X] [BorelSpace X]
    {T S : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) (hS : IsFullPositive S) (heq : T = S) :
    globalACtopMeasure T hT = globalACtopMeasure S hS := by
  subst S
  rfl

omit [CompactSpace X] in
/-- The sum of two full-positive global currents is full-positive. -/
theorem isFullPositive_add {S T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hT : IsFullPositive T) : IsFullPositive (S + T) := by
  intro e ψ hψ
  exact add_nonneg (hS e ψ hψ) (hT e ψ hψ)

/-- The Bott--Chern class map is additive. -/
theorem bottChernClass_add
    (S T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (S + T) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S +
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T :=
  (bottChernClassLinearMap (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_add S T

variable [ConnectedSpace X]

/-- A class without potentials has volume `0` (`def:volcohclass`). -/
theorem sourceClassVolume_eq_zero_of_not_pseudoeffective [MeasurableSpace X]
    {α : RealBottChern (m + 1) X} (hα : ¬ ClassPseudoeffectiveViaPotentials α) :
    sourceClassVolume α = 0 := by
  classical
  unfold sourceClassVolume
  rw [dif_neg]
  rintro ⟨θ, hθ, φ, hφ⟩
  apply hα
  rw [← hθ, classPseudoeffectiveViaPotentials_ofRepresentative]
  exact ⟨φ, (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.1⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- **`vol {θ} = ∫_X ⟨θ_{V_θ}^n⟩`** in the native language: for a representative `θ` with a
`θ`-psh potential, `V_θ = thetaPshSupremum θ` is `θ`-psh and `vol {θ}` is its non-pluripolar
mass. -/
theorem sourceClassVolume_ofRepresentative (ω : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    ∃ hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val),
      sourceClassVolume (RealBottChern.ofRepresentative θ) =
        diagonalPotentialMass θ (thetaPshSupremum θ.val) hV := by
  have hu' : (ofFixedModel (m + 1) X).IsThetaPSH (nativeClosedFormToAtlas θ) u :=
    (isThetaPSH_iff_nativeThetaPotential _ u).mpr (by rw [sourceNativeAtlasForm_roundTrip]; exact hu)
  have h := sourceClassVolume_eq_minimalEnvelope_mass ω hu'
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu'
  have hV' := (isThetaPSH_iff_nativeThetaPotential _ _).mp hV
  have hVe : sourceMinimalEnvelope (nativeClosedFormToAtlas θ) = thetaPshSupremum θ.val := by
    rw [sourceMinimalEnvelope_eq_native, sourceNativeAtlasForm_roundTrip]
  have hV'' : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) := by
    rw [sourceNativeAtlasForm_roundTrip, hVe] at hV'
    exact hV'
  refine ⟨hV'', ?_⟩
  calc sourceClassVolume (RealBottChern.ofRepresentative θ)
      = sourceClassVolume (RealBottChern.ofRepresentative
          (atlasClosedFormToNative (nativeClosedFormToAtlas θ))) := by
        rw [sourceNativeAtlasForm_roundTrip]
    _ = _ := h
    _ = diagonalPotentialMass θ (thetaPshSupremum θ.val) hV'' :=
        diagonalPotentialMass_congr (sourceNativeAtlasForm_roundTrip θ) hVe _ _

/-- Every potential has mass at most the volume of its class: `∫_X ⟨θ_u^n⟩ ≤ vol {θ}`. -/
theorem diagonalPotentialMass_le_sourceClassVolume (ω : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u) :
    diagonalPotentialMass θ u hu ≤ sourceClassVolume (RealBottChern.ofRepresentative θ) := by
  obtain ⟨hV, hvol⟩ := sourceClassVolume_ofRepresentative ω θ hu
  rw [hvol]
  have hmore : MoreSingularOn u (thetaPshSupremum θ.val) univ :=
    FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2 hu.1.hasSmoothLocalPotentials
      ⟨_, hu⟩ u hu
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω
    (fun _ : Fin (m + 1) => hu) (fun _ => hV) (fun _ => hmore)

/-- Boucksom's volume is at most the non-pluripolar volume. -/
theorem originalCurrentACVolume_le_sourceClassVolume (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) : originalCurrentACVolume α ≤ sourceClassVolume α := by
  unfold originalCurrentACVolume
  refine iSup_le fun T => iSup_le fun hT => iSup_le fun hclass => ?_
  obtain ⟨θ, v, hv, heq, -⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T.val T.property.1 T.property.2 hT
  have hTc : T = thetaClosedCurrent θ v hv := Subtype.ext heq
  have hθ : RealBottChern.ofRepresentative θ = α := by
    rw [← hclass, hTc, bottChernClass_thetaClosedCurrent]
  have hpos : IsFullPositive (thetaPotentialCurrent θ.val v hv) :=
    fun e η hη => thetaPotentialCurrent_full_positive θ.val v hv e η hη
  have hAC : globalACtopMeasure (thetaPotentialCurrent θ.val v hv) hpos ≤
      globalMixedMeasure (fun _ : Fin (m + 1) => θ) (fun _ => v) (fun _ => hv.1) :=
    ThetaCurrentGlobalACDomination.globalACtopMeasure_le_globalMixedMeasure ω θ hv
  rw [globalACtopMeasure_congr hT hpos heq, ← hθ]
  exact (Measure.le_iff'.mp hAC univ).trans (diagonalPotentialMass_le_sourceClassVolume ω θ hv)

/-- The non-pluripolar volume is at most Boucksom's volume. -/
theorem sourceClassVolume_le_originalCurrentACVolume (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) : sourceClassVolume α ≤ originalCurrentACVolume α := by
  by_cases hα : ClassPseudoeffectiveViaPotentials α
  swap
  · rw [sourceClassVolume_eq_zero_of_not_pseudoeffective hα]
    exact bot_le
  induction α using Quotient.inductionOn with
  | h θ =>
  change ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) at hα
  change sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
    originalCurrentACVolume (RealBottChern.ofRepresentative θ)
  obtain ⟨u, hu⟩ := (classPseudoeffectiveViaPotentials_ofRepresentative θ).mp hα
  obtain ⟨hV, hvol⟩ := sourceClassVolume_ofRepresentative ω θ hu
  have hbound : ∀ ε : ℝ, 0 < ε → sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
      originalCurrentACVolume (RealBottChern.ofRepresentative θ +
        ε • RealBottChern.ofRepresentative ω.form) := by
    intro ε hε
    obtain ⟨v, δ, _han, hsmooth, _hanti, hinf, _hδnon, hδlim, hv⟩ :=
      Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation ω θ
        (thetaPshSupremum θ.val) hV
    obtain ⟨k, hk⟩ := (hδlim.eventually (eventually_lt_nhds hε)).exists
    have hve : IsThetaPshPotential (θ + ε • ω.form).val (v k) := by
      have hs := LocalPotentials.isThetaPshPotential_add_of_semipositive (hv k)
        (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr hk.le))
      have he : (θ + δ k • ω.form) + (ε - δ k) • ω.form = θ + ε • ω.form := by module
      simpa only [he] using hs
    have hVe : IsThetaPshPotential (θ + ε • ω.form).val (thetaPshSupremum θ.val) :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hV
        (KahlerDomination.isSemipositive_smul ω.isSemipositive hε.le)
    have hbg := AmbientMassBackgroundMonotone.globalMixedMeasure_diagonal_le_add_smul
      ω.isSemipositive hε hV hVe.1
    have horder : MoreSingularOn (thetaPshSupremum θ.val) (v k) univ :=
      MoreSingularOn.of_le fun x _ => by
        rw [← hinf x]
        exact iInf_le _ k
    have hmass := GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω
      (fun _ : Fin (m + 1) => hVe) (fun _ => hve) (fun _ => horder)
    have heqAC := congrArg (fun μ : Measure X => μ univ)
      (OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
        (θ + ε • ω.form) hve (hsmooth k))
    have hle := ac_top_mass_le_volume (thetaClosedCurrent (θ + ε • ω.form) (v k) hve)
      (fun e η hη => thetaPotentialCurrent_full_positive (θ + ε • ω.form).val (v k) hve e η hη)
      (bottChernClass_thetaClosedCurrent (θ + ε • ω.form) (v k) hve)
    rw [hvol]
    calc diagonalPotentialMass θ (thetaPshSupremum θ.val) hV
        ≤ globalMixedMeasure (fun _ : Fin (m + 1) => θ + ε • ω.form)
            (fun _ => thetaPshSupremum θ.val) (fun _ => hVe.1) univ :=
          Measure.le_iff'.mp hbg univ
      _ ≤ globalMixedMass (fun _ : Fin (m + 1) => θ + ε • ω.form) (fun _ => v k)
            (fun _ => hve.1) := hmass
      _ = _ := heqAC.symm
      _ ≤ originalCurrentACVolume (RealBottChern.ofRepresentative (θ + ε • ω.form)) := hle
      _ = originalCurrentACVolume (RealBottChern.ofRepresentative θ +
            ε • RealBottChern.ofRepresentative ω.form) := by
          rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  have hlim := OriginalCurrentVolumeRightLimit.tendsto_originalCurrentACVolume_add_smul_right ω
    (RealBottChern.ofRepresentative θ) hα
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)

/-- **The non-pluripolar volume (`def:volcohclass`) is Boucksom's volume** (Boucksom
Definition 1.3, `sup_T ∫_X (T_ac)^n`), for every class. -/
theorem sourceClassVolume_eq_originalCurrentACVolume (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) : sourceClassVolume α = originalCurrentACVolume α :=
  le_antisymm (sourceClassVolume_le_originalCurrentACVolume ω α)
    (originalCurrentACVolume_le_sourceClassVolume ω α)

/-- The volume is finite. -/
theorem sourceClassVolume_lt_top (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) : sourceClassVolume α < ⊤ := by
  rw [sourceClassVolume_eq_originalCurrentACVolume ω]
  exact originalCurrentACVolume_lt_top ω α

/-- **`vol(α) > 0 ⟺ α` big** (Boucksom Theorem 4.7; `prop:nppposimpbig` and its converse),
with TN's bigness. -/
theorem sourceClassVolume_pos_iff_isBigClass (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) : 0 < sourceClassVolume α ↔ IsBigClass α := by
  rw [sourceClassVolume_eq_originalCurrentACVolume ω]
  exact (OriginalCurrentVolumeBigness.isBigClass_iff_originalCurrentACVolume_pos ω α).symm

/-- **`vol(α) > 0 ⟺ α` big**, with the source bigness `def:psefclass`. -/
theorem volumePositiveIffBig (ω : KahlerBackground (m + 1) X) :
    VolumePositiveIffBigStatement (m := m) X := fun α => by
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass]
  exact sourceClassVolume_pos_iff_isBigClass ω α

/-- The volume does not decrease when a semipositive form is added to the class. -/
theorem sourceClassVolume_le_add_semipositive (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) (η : ClosedRealOneOneForm (m + 1) X)
    (hη : η.val.IsSemipositive) :
    sourceClassVolume α ≤ sourceClassVolume (α + RealBottChern.ofRepresentative η) := by
  rw [sourceClassVolume_eq_originalCurrentACVolume ω, sourceClassVolume_eq_originalCurrentACVolume ω]
  exact OriginalCurrentVolumeRightLimit.originalCurrentACVolume_le_add_semipositive α η hη

/-- **`vol(α + ε{ω}) → vol(α)` as `ε ↓ 0`** for a pseudo-effective class `α`. -/
theorem tendsto_sourceClassVolume_add_smul_right (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) (hα : ClassPseudoeffectiveViaPotentials α) :
    Tendsto (fun ε : ℝ => sourceClassVolume (α + ε • RealBottChern.ofRepresentative ω.form))
      (𝓝[>] 0) (𝓝 (sourceClassVolume α)) := by
  simp only [sourceClassVolume_eq_originalCurrentACVolume ω]
  exact OriginalCurrentVolumeRightLimit.tendsto_originalCurrentACVolume_add_smul_right ω α hα

end SGPT.Okounkov.TranscendentalVolumeConcavity
