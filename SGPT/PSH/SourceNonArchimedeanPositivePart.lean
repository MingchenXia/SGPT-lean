import SGPT.PSH.SourceNonArchimedeanVolume
import SGPT.PSH.SourceTestCurveMassContinuity
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

/-! # The original positive-volume non-Archimedean part

All actual varying-background models, their masses, and the original curve
are manufactured along the complete `source-non-archimedean-volume.tex` route.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass
open MixedMass MixedMassBoundedDifference CanonicalBackgroundPolynomial

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual mixed-measure selector polynomial makes the original mass
drop no larger than its value after a genuine Kähler enlargement, in every dimension. -/
theorem nativeMassDrop_le_add_background (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential α.val u) (hv : IsThetaPshPotential α.val v)
    (hvu : v ≤ u) {N : ℝ} (hN : 0 < N) :
    (diagonalPotentialMass α u hu).toReal - (diagonalPotentialMass α v hv).toReal ≤
      (diagonalPotentialMass (α + N • omega.form) u
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hu
          (KahlerDomination.isSemipositive_smul omega.isSemipositive hN.le))).toReal -
      (diagonalPotentialMass (α + N • omega.form) v
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hv
          (KahlerDomination.isSemipositive_smul omega.isSemipositive hN.le))).toReal := by
  classical
  let Θ : Fin n → ClosedRealOneOneForm n M := fun _ => α
  let U : Fin n → M → EReal := fun _ => u
  let V : Fin n → M → EReal := fun _ => v
  let cu (g : Fin n → Option (Fin n)) : ℝ :=
    (globalMixedMass (fun i => optForm omega Θ (g i))
      (fun i => optPot U (g i)) (fun i => optPot_psh omega (fun _ => hu) (g i))).toReal
  let cv (g : Fin n → Option (Fin n)) : ℝ :=
    (globalMixedMass (fun i => optForm omega Θ (g i))
      (fun i => optPot V (g i)) (fun i => optPot_psh omega (fun _ => hv) (g i))).toReal
  have hcoeff (g : Fin n → Option (Fin n)) : cv g ≤ cu g := by
    have hgu (i : Fin n) : IsThetaPshPotential (optForm omega Θ (g i)).val (optPot U (g i)) :=
      ⟨optPot_psh omega (fun _ => hu) (g i),
        (optPot_quasiPsh (fun _ => hu) (g i)).2⟩
    have hgv (i : Fin n) : IsThetaPshPotential (optForm omega Θ (g i)).val (optPot V (g i)) :=
      ⟨optPot_psh omega (fun _ => hv) (g i),
        (optPot_quasiPsh (fun _ => hv) (g i)).2⟩
    apply ENNReal.toReal_mono (globalMixedMass_lt_top omega (fun i => (hgu i).1)).ne
    apply GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega hgv hgu
    intro i
    apply MoreSingularOn.of_le
    intro x _
    cases g i with
    | none => exact le_rfl
    | some j => exact hvu x
  let d (g : Fin n → Option (Fin n)) := N ^ backgroundDegree g * (cu g - cv g)
  have hnonneg (g : Fin n → Option (Fin n)) : 0 ≤ d g :=
    mul_nonneg (pow_nonneg hN.le _) (sub_nonneg.mpr (hcoeff g))
  have hup := LocalPotentials.isThetaPshPotential_add_of_semipositive hu
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hN.le)
  have hvp := LocalPotentials.isThetaPshPotential_add_of_semipositive hv
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hN.le)
  have hpoly :
      (diagonalPotentialMass (α + N • omega.form) u hup).toReal -
        (diagonalPotentialMass (α + N • omega.form) v hvp).toReal =
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)), d g := by
    have hpu := SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum
      omega (fun _ : Fin n => hu) hN
    have hpv := SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum
      omega (fun _ : Fin n => hv) hN
    change (globalMixedMass (fun _ : Fin n => α + N • omega.form) U _).toReal -
      (globalMixedMass (fun _ : Fin n => α + N • omega.form) V _).toReal = _
    rw [hpu, hpv]
    simp only [d, cu, cv, Θ, U, V, mul_sub, Finset.sum_sub_distrib]
  have hmem : (fun i : Fin n => some i) ∈ Fintype.piFinset (backgroundChoices (n := n)) := by
    simp [backgroundChoices]
  have hkeep := Finset.single_le_sum (fun g _ => hnonneg g) hmem
  have hconstant : d (fun i => some i) =
      (diagonalPotentialMass α u hu).toReal - (diagonalPotentialMass α v hv).toReal := by
    simp [d, cu, cv, backgroundDegree, optForm, optPot, Θ, U, V,
      diagonalPotentialMass, diagonalPotentialMeasure, globalMixedMass]
  rw [hconstant] at hkeep
  rw [hpoly]
  exact hkeep

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Finite real encoding of the original actual component-limit mass. -/
def sourceNALimitMassReal (Γ : SourceNAPotential θ) (ω : KahlerBackground n M) : ℝ :=
  (sourceNAComponentMass Γ (sourceKahlerFormOfBackground ω)).toReal

theorem sourceNALimitMassReal_eq (Γ : SourceNAPotential θ) (ω : KahlerBackground n M) :
    sourceNALimitMassReal Γ ω =
      (sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ω θ)
        (sourceTestCurveLimit (Γ.realizedComponent ω).val.toSourceTestCurvePredata)
        (Γ.realizedComponent ω).val.limit_thetaPSH univ).toReal :=
  congrArg ENNReal.toReal (sourceNAComponentMass_realized Γ ω)

/-- Finite real encoding of the same original actual open-slice mass. -/
def sourceNASliceMassReal (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (ω : KahlerBackground n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) : ℝ :=
  (sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ω θ)
    (sourceNACommonSlice omega Γ ω τ) (sourceNACommonSlice_thetaPSH omega Γ ω τ) univ).toReal

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem kahler_eq_of_form_eq {ω η : KahlerBackground n M} (h : ω.form = η.form) :
    ω = η := by
  cases ω
  cases η
  cases h
  rfl

/-- Whole original lma:NA_mass_drop_transition, with finite real masses
of the actual unchanged inverse-system curves and every 0<t≤1. -/
theorem sourceNAMassDrop_le (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceNALimitMassReal Γ (KahlerBackground.smul ht0 omega) -
        sourceNASliceMassReal omega Γ (KahlerBackground.smul ht0 omega) τ ≤
      sourceNALimitMassReal Γ omega - sourceNASliceMassReal omega Γ omega τ := by
  rcases ht1.eq_or_lt with ht | ht
  · subst t
    have he : KahlerBackground.smul ht0 omega = omega :=
      kahler_eq_of_form_eq (by simp only [KahlerBackground.smul_form, one_smul])
    rw [he]
  let ωt := KahlerBackground.smul ht0 omega
  let α := sourceTestCurveEnlargedBackground ωt θ
  let β := sourceTestCurveEnlargedBackground omega θ
  have hdiff : (omega.form - ωt.form).val.IsSemipositive := by
    have he : omega.form - ωt.form = (1-t) • omega.form := by
      dsimp only [ωt]
      rw [KahlerBackground.smul_form]
      module
    rw [he]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr ht.le)
  have hab : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive := by
    have he : atlasClosedFormToNative β - atlasClosedFormToNative α =
        omega.form - ωt.form := by
      dsimp only [α, β]
      rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native]
      abel
    rw [he]
    exact hdiff
  let u := sourceTestCurveLimit (Γ.realizedComponent ωt).val.toSourceTestCurvePredata
  let v := sourceNACommonSlice omega Γ ωt τ
  have hu := (Γ.realizedComponent ωt).val.limit_thetaPSH
  have hv := sourceNACommonSlice_thetaPSH omega Γ ωt τ
  have hi := (Γ.realizedComponent ωt).val.limit_iModel omega
    ((sourceIModelTestCurvesPositive_iff_slices omega _).mp (Γ.realizedComponent ωt).property)
  have hIv := sourceNACommonSlice_iModel omega Γ ωt τ
  have hpv := (sourceNACommonSlice_model omega Γ ωt τ).choose_spec.2
  have huβ := sourceThetaPSH_of_semipositive_difference hab hu
  have hvβ := sourceThetaPSH_of_semipositive_difference hab hv
  have hmu := (sourceIModel_transition_envelope_and_mass omega hab hi
    (Γ.realizedComponent ωt).val.positiveLimitMass).2
  have hmv := (sourceIModel_transition_envelope_and_mass omega hab hIv hpv).2
  have hLM : sourceNALimitMassReal Γ omega =
      (diagonalPotentialMass (atlasClosedFormToNative β) u
        ((isThetaPSH_iff_nativeThetaPotential β u).mp huβ)).toReal := by
    have h := (sourcePotentialMass_congr (Γ.realizedComponent_limit_transition hdiff)
      (Γ.realizedComponent omega).val.limit_thetaPSH _).trans hmu
    exact (sourceNALimitMassReal_eq Γ omega).trans (congrArg ENNReal.toReal h)
  have hSM : sourceNASliceMassReal omega Γ omega τ =
      (diagonalPotentialMass (atlasClosedFormToNative β) v
        ((isThetaPSH_iff_nativeThetaPotential β v).mp hvβ)).toReal := by
    exact congrArg ENNReal.toReal
      ((sourcePotentialMass_congr (sourceNACommonSlice_transition omega Γ hdiff τ) _ _).trans hmv)
  have hvu : v ≤ u := by
    intro x
    let r : Iio (Γ.realizedComponent ωt).val.max := ⟨τ.val, by
      rw [Γ.realizedComponent_max_eq_cutoff omega ωt]
      exact τ.property⟩
    change (Γ.realizedComponent ωt).val.potential r x ≤
      uscRegularization (fun y => ⨆ r, (Γ.realizedComponent ωt).val.potential r y) x
    exact (le_iSup (fun s => (Γ.realizedComponent ωt).val.potential s x) r).trans
      (le_uscRegularization
        (fun y => ⨆ s, (Γ.realizedComponent ωt).val.potential s y) x)
  have hn := nativeMassDrop_le_add_background omega
    ((isThetaPSH_iff_nativeThetaPotential α u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential α v).mp hv) hvu (sub_pos.mpr ht)
  have hform : atlasClosedFormToNative α + (1-t) • omega.form = atlasClosedFormToNative β := by
    dsimp only [α, β, ωt]
    rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native,
      KahlerBackground.smul_form]
    module
  rw [hLM, hSM]
  simpa only [sourceNALimitMassReal_eq, sourceNASliceMassReal,
    sourcePotentialNonPluripolarMeasure, diagonalPotentialMass, hform, α, β, u, v, ωt] using hn

/-- Actual positive errors tending to zero; index zero is the unscaled background. -/
def sourceNAError (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem sourceNAError_pos (j : ℕ) : 0 < sourceNAError j := by
  dsimp only [sourceNAError]
  positivity

theorem sourceNAError_antitone : Antitone sourceNAError := by
  intro i j hij
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem sourceNAError_tendsto : Tendsto sourceNAError atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem sourceNAError_le_one (j : ℕ) : sourceNAError j ≤ 1 := by
  simpa only [sourceNAError, Nat.cast_zero, zero_add, div_one] using
    sourceNAError_antitone (Nat.zero_le j)

/-- Literal actual Kähler forms ε_jω, not their arbitrarily chosen off-target representatives. -/
def sourceNAStageBackground (omega : KahlerBackground n M) (j : ℕ) : KahlerBackground n M :=
  KahlerBackground.smul (sourceNAError_pos j) omega

/-- Actual original stage functions on the unchanged entire open interval. -/
def sourceNAStagePotential (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) (j : ℕ) : M → EReal :=
  sourceNACommonSlice omega Γ (sourceNAStageBackground omega j) τ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
theorem sourceNAStageBackground_native (omega : KahlerBackground n M) (j : ℕ) :
    atlasClosedFormToNative (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ) =
      atlasClosedFormToNative θ + sourceNAError j • omega.form := by
  rw [sourceTestCurveEnlargedBackground_native]
  rfl

/-- The stage model fields are produced from the actual original component curve. -/
theorem sourceNAStagePotential_native_model (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) (j : ℕ) :
    IsModelPotential (atlasClosedFormToNative θ + sourceNAError j • omega.form)
      (sourceNAStagePotential omega Γ τ j) := by
  simpa only [sourceNAStageBackground_native, sourceNAStagePotential] using
    (sourceNACommonSlice_model omega Γ (sourceNAStageBackground omega j) τ).toNative

theorem sourceNAStagePotential_native_iModel (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) (j : ℕ) :
    IEnvelope.IsIModelPotential (atlasClosedFormToNative θ + sourceNAError j • omega.form).val
      (sourceNAStagePotential omega Γ τ j) := by
  have h := (sourceIModel_iff_native _ _).mp
    (sourceNACommonSlice_iModel omega Γ (sourceNAStageBackground omega j) τ)
  simpa only [sourceNAStageBackground_native, sourceNAStagePotential] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
theorem sourceNAStageBackground_difference (omega : KahlerBackground n M)
    {i j : ℕ} (hij : i ≤ j) :
    ((sourceNAStageBackground omega i).form -
      (sourceNAStageBackground omega j).form).val.IsSemipositive := by
  have he : (sourceNAStageBackground omega i).form - (sourceNAStageBackground omega j).form =
      (sourceNAError i - sourceNAError j) • omega.form := by
    dsimp only [sourceNAStageBackground]
    rw [KahlerBackground.smul_form, KahlerBackground.smul_form]
    module
  rw [he]
  exact KahlerDomination.isSemipositive_smul omega.isSemipositive
    (sub_nonneg.mpr (sourceNAError_antitone hij))

/-- Compatibility and the actual normalized competitor manufacture decreasing stage functions. -/
theorem sourceNAStagePotential_antitone (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    Antitone (sourceNAStagePotential omega Γ τ) := by
  intro i j hij
  have hdiff := sourceNAStageBackground_difference omega hij
  have he := sourceNACommonSlice_transition omega Γ hdiff τ
  have hab :
      (atlasClosedFormToNative (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega i) θ) -
       atlasClosedFormToNative (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ)).val.IsSemipositive := by
    have hform : atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega i) θ) -
        atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ) =
          (sourceNAStageBackground omega i).form - (sourceNAStageBackground omega j).form := by
      rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native]
      abel
    rw [hform]
    exact hdiff
  have hu := sourceThetaPSH_of_semipositive_difference hab
    (sourceNACommonSlice_thetaPSH omega Γ (sourceNAStageBackground omega j) τ)
  have hzero : sourceNAStagePotential omega Γ τ j ≤ 0 :=
    (Γ.realizedComponent (sourceNAStageBackground omega j)).val.le_zero _
  exact (le_sourceIEnvelope hu hzero
    (sourceIEquivalent_refl ⟨_, hu⟩)).trans_eq he.symm

theorem sourceNASliceMassReal_eq_massAt (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : KahlerBackground n M)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceNASliceMassReal omega Γ ω τ =
      sourceTestCurveRealMassAt omega (Γ.realizedComponent ω).val τ.val := by
  symm
  exact sourceTestCurveRealMassAt_of_lt omega _
    (by rw [Γ.realizedComponent_max_eq_cutoff omega ω]; exact τ.property)

/-- Finite real masses decrease with the unchanged original open parameter. -/
theorem sourceNASliceMassReal_antitone (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : KahlerBackground n M) :
    Antitone (sourceNASliceMassReal omega Γ ω) := by
  intro τ σ hτσ
  apply ENNReal.toReal_mono
    (globalMixedMass_lt_top omega (fun _ : Fin n =>
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp
        (sourceNACommonSlice_thetaPSH omega Γ ω τ)).1)).ne
  apply sourcePotentialNonPluripolarMass_mono omega
    (sourceNACommonSlice_thetaPSH omega Γ ω σ) (sourceNACommonSlice_thetaPSH omega Γ ω τ)
  apply MoreSingularOn.of_le
  intro x _
  exact (Γ.realizedComponent ω).val.antitone x hτσ

/-- Actual negative-infinity mass convergence and the mass-drop theorem
produce one uniform positive earlier slice, with no such bound supplied. -/
theorem sourceNA_uniform_positive_early (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) :
    ∃ τ₀ : Iio (sourceNAPotentialCutoff omega Γ),
      ∀ j, (sourceNAVolume Γ).toReal / 2 ≤
        sourceNASliceMassReal omega Γ (sourceNAStageBackground omega j) τ₀ := by
  have he : 0 < (sourceNAVolume Γ).toReal :=
    ENNReal.toReal_pos hpos.ne' (sourceNAVolume_lt_top omega Γ).ne
  let C := (Γ.realizedComponent omega).val
  let A := sourceNALimitMassReal Γ omega
  have hlim := sourceTestCurveRealMassAt_tendsto_atBot omega C
  have hA :
      (sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground omega θ)
        (sourceTestCurveLimit C.toSourceTestCurvePredata) C.limit_thetaPSH univ).toReal = A :=
    (sourceNALimitMassReal_eq Γ omega).symm
  rw [hA] at hlim
  have : Nonempty (Iio C.max) := ⟨⟨C.max - 1, by change C.max - 1 < C.max; linarith⟩⟩
  have hev : ∀ᶠ r : Iio C.max in atBot,
      A - (sourceNAVolume Γ).toReal / 2 < sourceTestCurveRealMassAt omega C r.val :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨r, hr⟩ := hev.exists
  let τ₀ : Iio (sourceNAPotentialCutoff omega Γ) := ⟨r.val, by
    rw [← Γ.realizedComponent_max_eq_cutoff omega omega]
    exact r.property⟩
  have hgap : A - sourceNASliceMassReal omega Γ omega τ₀ < (sourceNAVolume Γ).toReal / 2 := by
    rw [sourceNASliceMassReal_eq_massAt]
    change A - sourceTestCurveRealMassAt omega C r.val < (sourceNAVolume Γ).toReal / 2
    linarith
  refine ⟨τ₀, fun j => ?_⟩
  have hdrop := sourceNAMassDrop_le omega Γ (sourceNAError_pos j) (sourceNAError_le_one j) τ₀
  have hlower : (sourceNAVolume Γ).toReal ≤
      sourceNALimitMassReal Γ (sourceNAStageBackground omega j) :=
    ENNReal.toReal_mono (sourceNAComponentMass_lt_top omega Γ _).ne
      (sourceNAVolume_le_component Γ _)
  change sourceNALimitMassReal Γ (sourceNAStageBackground omega j) -
    sourceNASliceMassReal omega Γ (sourceNAStageBackground omega j) τ₀ ≤
      A - sourceNASliceMassReal omega Γ omega τ₀ at hdrop
  linarith

/-- Original concavity manufactures a uniform positive actual mass for
EVERY fixed original open slice, in all natural dimensions. -/
theorem sourceNA_uniform_positive_slice (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j,
      δ ≤ sourceNASliceMassReal omega Γ (sourceNAStageBackground omega j) τ := by
  obtain ⟨τ₀, hτ₀⟩ := sourceNA_uniform_positive_early omega Γ hpos
  have he : 0 < (sourceNAVolume Γ).toReal / 2 := half_pos
    (ENNReal.toReal_pos hpos.ne' (sourceNAVolume_lt_top omega Γ).ne)
  by_cases hτ : τ ≤ τ₀
  · exact ⟨(sourceNAVolume Γ).toReal / 2, he, fun j =>
      (hτ₀ j).trans (sourceNASliceMassReal_antitone omega Γ _ hτ)⟩
  have hτ₀τ : τ₀.val < τ.val := lt_of_not_ge hτ
  have hτm : τ.val < sourceNAPotentialCutoff omega Γ := τ.property
  let b : ℝ := (τ.val + sourceNAPotentialCutoff omega Γ) / 2
  have hτb : τ.val < b := by dsimp only [b]; linarith
  have hbm : b < sourceNAPotentialCutoff omega Γ := by dsimp only [b]; linarith
  have hden : 0 < b - τ₀.val := by linarith
  let s : ℝ := (b - τ.val) / (b - τ₀.val)
  have hs0 : 0 < s := div_pos (sub_pos.mpr hτb) (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith : 0 < b - τ₀.val)).mpr (by linarith)
  have hpar : s * τ₀.val + (1-s) * b = τ.val := by
    dsimp only [s]
    field_simp [ne_of_gt hden]
    ring
  refine ⟨s ^ n * ((sourceNAVolume Γ).toReal / 2), mul_pos (pow_pos hs0 n) he, fun j => ?_⟩
  have ha : τ₀.val < (Γ.realizedComponent (sourceNAStageBackground omega j)).val.max := by
    rw [Γ.realizedComponent_max_eq_cutoff omega]
    exact τ₀.property
  have hb : b < (Γ.realizedComponent (sourceNAStageBackground omega j)).val.max := by
    rw [Γ.realizedComponent_max_eq_cutoff omega]
    exact hbm
  have hc := sourceTestCurveRealMassAt_chord_lower_bound omega
    (Γ.realizedComponent (sourceNAStageBackground omega j)).val ha hb hs0 hs1
  rw [hpar, ← sourceNASliceMassReal_eq_massAt omega Γ _ τ₀,
    ← sourceNASliceMassReal_eq_massAt omega Γ _ τ] at hc
  exact (mul_le_mul_of_nonneg_left (hτ₀ j) (pow_nonneg hs0.le n)).trans hc

/-- The literal original-background pointwise infimum; no class or limit certificate is stored. -/
def sourceNAInfPotential (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) : M → EReal :=
  ⨅ j, sourceNAStagePotential omega Γ τ j

/-- Actual native varying-model analysis manufactures full original PSH. -/
theorem sourceNAInfPotential_native_thetaPSH (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val (sourceNAInfPotential omega Γ τ) :=
  IEnvelopeVaryingBackgroundModelInfimum.isThetaPshPotential_iInf_varying_models
    omega (atlasClosedFormToNative θ) sourceNAError_antitone sourceNAError_tendsto
    (sourceNAStagePotential_native_model omega Γ τ) (sourceNAStagePotential_antitone omega Γ τ)

/-- The same literal infimum is genuinely I-model, without assuming that output. -/
theorem sourceNAInfPotential_native_iModel (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val (sourceNAInfPotential omega Γ τ) :=
  VaryingBackgroundIModelGlobalClass.isIModelPotential_iInf_varying_models
    omega (atlasClosedFormToNative θ) sourceNAError_pos sourceNAError_antitone sourceNAError_tendsto
    (sourceNAStagePotential_native_model omega Γ τ) (sourceNAStagePotential_native_iModel omega Γ τ)
    (sourceNAStagePotential_antitone omega Γ τ)

/-- Actual varying-model masses converge to the unchanged original infimum mass, including n=0. -/
theorem sourceNAInfPotential_mass_tendsto (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    Tendsto (fun j => diagonalPotentialMass
      (atlasClosedFormToNative θ + sourceNAError j • omega.form)
      (sourceNAStagePotential omega Γ τ j)
      (sourceNAStagePotential_native_model omega Γ τ j).plurisubharmonic) atTop
      (𝓝 (diagonalPotentialMass (atlasClosedFormToNative θ) (sourceNAInfPotential omega Γ τ)
        (sourceNAInfPotential_native_thetaPSH omega Γ τ))) :=
  IEnvelopeVaryingBackgroundModelInfimum.tendsto_diagonalPotentialMass_iInf_varying_models
    omega (atlasClosedFormToNative θ) sourceNAError_pos sourceNAError_antitone sourceNAError_tendsto
    (sourceNAStagePotential_native_model omega Γ τ) (sourceNAStagePotential_antitone omega Γ τ)

/-- The proved uniform stage bound and actual mass convergence PRODUCE positive infimum mass. -/
theorem sourceNAInfPotential_mass_positive (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    HasPositivePotentialMass (atlasClosedFormToNative θ) (sourceNAInfPotential omega Γ τ)
      (sourceNAInfPotential_native_thetaPSH omega Γ τ) := by
  obtain ⟨δ, hδ, hbound⟩ := sourceNA_uniform_positive_slice omega Γ hpos τ
  have hb (j : ℕ) : ENNReal.ofReal δ ≤ diagonalPotentialMass
      (atlasClosedFormToNative θ + sourceNAError j • omega.form)
      (sourceNAStagePotential omega Γ τ j)
      (sourceNAStagePotential_native_model omega Γ τ j).plurisubharmonic := by
    have hfin : diagonalPotentialMass
        (atlasClosedFormToNative θ + sourceNAError j • omega.form)
        (sourceNAStagePotential omega Γ τ j)
        (sourceNAStagePotential_native_model omega Γ τ j).plurisubharmonic ≠ ⊤ :=
      (globalMixedMass_lt_top omega (fun _ : Fin n =>
        (sourceNAStagePotential_native_model omega Γ τ j).plurisubharmonic.1)).ne
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
    simpa only [sourceNASliceMassReal, sourcePotentialNonPluripolarMeasure,
      diagonalPotentialMass, sourceNAStageBackground_native, sourceNAStagePotential] using hbound j
  exact (ENNReal.ofReal_pos.mpr hδ).trans_le
    (le_of_tendsto_of_tendsto tendsto_const_nhds (sourceNAInfPotential_mass_tendsto omega Γ τ)
      (Eventually.of_forall hb))

/-- The genuine varying-background output is the original source theta-PSH function. -/
theorem sourceNAInfPotential_thetaPSH (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceNAInfPotential omega Γ τ) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr (sourceNAInfPotential_native_thetaPSH omega Γ τ)

theorem sourceNAInfPotential_iModel (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIModel θ (sourceNAInfPotential omega Γ τ) :=
  (sourceIModel_iff_native θ _).mpr (sourceNAInfPotential_native_iModel omega Γ τ)

/-- Infima of the original decreasing parameter families retain that order. -/
theorem sourceNAInfPotential_antitone (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (x : M) :
    Antitone (fun τ => sourceNAInfPotential omega Γ τ x) := by
  intro a b hab
  simp only [sourceNAInfPotential, iInf_apply]
  exact iInf_mono fun j => (Γ.realizedComponent (sourceNAStageBackground omega j)).val.antitone x hab

/-- Genuine original strict chords pass to the unchanged literal infimum, retaining poles. -/
theorem sourceNAInfPotential_chord (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (a b : Iio (sourceNAPotentialCutoff omega Γ))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t
      (sourceNAInfPotential omega Γ a) (sourceNAInfPotential omega Γ b) ≤
      sourceNAInfPotential omega Γ
        ⟨t*a.val+(1-t)*b.val, by
          change t*a.val+(1-t)*b.val < sourceNAPotentialCutoff omega Γ
          have ha : a.val < sourceNAPotentialCutoff omega Γ := a.property
          have hb : b.val < sourceNAPotentialCutoff omega Γ := b.property
          nlinarith [mul_pos ht0 (sub_pos.mpr ha), mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hb)]⟩ := by
  intro x
  simp only [ThetaPshConvexCombination.convexComb, sourceNAInfPotential, iInf_apply]
  refine le_iInf fun j => ?_
  have ha : sourceNAInfPotential omega Γ a x ≤ sourceNAStagePotential omega Γ a j x :=
    iInf_le (sourceNAStagePotential omega Γ a) j x
  have hb : sourceNAInfPotential omega Γ b x ≤ sourceNAStagePotential omega Γ b j x :=
    iInf_le (sourceNAStagePotential omega Γ b) j x
  have hchord := (Γ.realizedComponent (sourceNAStageBackground omega j)).val.toSourceTestCurvePredata.convexComb_le
    ⟨a.val, by rw [Γ.realizedComponent_max_eq_cutoff omega]; exact a.property⟩
    ⟨b.val, by rw [Γ.realizedComponent_max_eq_cutoff omega]; exact b.property⟩ ht0 ht1 x
  simpa only [sourceNAInfPotential, iInf_apply, sourceNAStagePotential, sourceNACommonSlice] using (add_le_add
    (mul_le_mul_of_nonneg_left ha (EReal.coe_nonneg.mpr ht0.le))
    (mul_le_mul_of_nonneg_left hb (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le))).trans hchord

/-- Positive actual infimum mass and its produced I-model fields give the literal ordinary fixed point. -/
theorem sourceNAInfPotential_fixedPoint (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceSingularityEnvelope θ (sourceNAInfPotential omega Γ τ) = sourceNAInfPotential omega Γ τ := by
  have hi := sourceNAInfPotential_iModel omega Γ τ
  have hg := (sourceIModel_positive_iGood θ _ hi
    (sourceNAInfPotential_mass_positive omega Γ hpos τ)).1
  exact hg.2.trans hi.2.symm

/-- All original preliminary test-curve fields are manufactured from the actual system. -/
def sourceNAInfPredata (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) : SourceTestCurvePredata θ where
  max := sourceNAPotentialCutoff omega Γ
  potential := sourceNAInfPotential omega Γ
  thetaPSH := sourceNAInfPotential_thetaPSH omega Γ
  antitone := sourceNAInfPotential_antitone omega Γ
  concave := sourceTestCurveNegativeTrace_convex_of_chords _ (sourceNAInfPotential_chord omega Γ)
  fixedPoint := sourceNAInfPotential_fixedPoint omega Γ hpos

/-- The genuine spatial supremum limit has actual positive mass, produced from one actual slice. -/
theorem sourceNAInfPredata_positiveLimitMass (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) :
    0 < sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveLimit (sourceNAInfPredata omega Γ hpos))
      (sourceNAInfPredata omega Γ hpos).limit_thetaPSH univ := by
  let τ : Iio (sourceNAPotentialCutoff omega Γ) :=
    ⟨sourceNAPotentialCutoff omega Γ - 1, by change sourceNAPotentialCutoff omega Γ - 1 < _; linarith⟩
  have hle : sourceNAInfPotential omega Γ τ ≤ sourceTestCurveLimit (sourceNAInfPredata omega Γ hpos) := by
    intro x
    exact (le_iSup (fun r => sourceNAInfPotential omega Γ r x) τ).trans
      (le_uscRegularization (fun y => ⨆ r, sourceNAInfPotential omega Γ r y) x)
  exact (sourceNAInfPotential_mass_positive omega Γ hpos τ).trans_le
    (sourcePotentialNonPluripolarMass_mono omega (sourceNAInfPotential_thetaPSH omega Γ τ)
      (sourceNAInfPredata omega Γ hpos).limit_thetaPSH (MoreSingularOn.of_le fun x _ => hle x))

/-- The actual original positive I-model curve, with its original based-union witness produced internally. -/
def sourceNARecoveredPositiveCurve (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) : SourcePositiveIModelTestCurve θ := by
  let G : SourceTestCurve θ :=
    { toSourceTestCurvePredata := sourceNAInfPredata omega Γ hpos
      positiveLimitMass := sourceNAInfPredata_positiveLimitMass omega Γ hpos }
  refine ⟨G, (sourceIModelTestCurvesPositive_iff_slices omega G).mpr ?_⟩
  exact sourceNAInfPotential_native_iModel omega Γ

theorem sourceNARecoveredPositiveCurve_max (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) :
    (sourceNARecoveredPositiveCurve omega Γ hpos).val.max = sourceNAPotentialCutoff omega Γ := rfl

theorem sourceNARecoveredPositiveCurve_potential (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    (sourceNARecoveredPositiveCurve omega Γ hpos).val.potential τ = sourceNAInfPotential omega Γ τ := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
theorem sourceNAStageEnlarged_difference (omega : KahlerBackground n M) {i j : ℕ} (hij : i ≤ j) :
    (atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega i) θ) -
      atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ)).val.IsSemipositive := by
  have he : atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega i) θ) -
      atlasClosedFormToNative
        (sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ) =
      (sourceNAStageBackground omega i).form - (sourceNAStageBackground omega j).form := by
    rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native]
    abel
  rw [he]
  exact sourceNAStageBackground_difference omega hij

/-- Constant genuine global P-class of the actual stages is PROVED from
compatibility and positive admissible-background I-goodness. -/
theorem sourceNAStagePotential_globalP (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (τ : Iio (sourceNAPotentialCutoff omega Γ)) (j : ℕ) :
    SingularGlobalPOrder.SourcePEquivalent (n := n)
      (sourceNAStagePotential omega Γ τ j) (sourceNAStagePotential omega Γ τ 0) := by
  let α := sourceTestCurveEnlargedBackground (sourceNAStageBackground omega j) θ
  let β := sourceTestCurveEnlargedBackground (sourceNAStageBackground omega 0) θ
  let u := sourceNAStagePotential omega Γ τ j
  have hab := sourceNAStageEnlarged_difference (θ := θ) omega (Nat.zero_le j)
  have hi := sourceNACommonSlice_iModel omega Γ (sourceNAStageBackground omega j) τ
  have hp := (sourceNACommonSlice_model omega Γ (sourceNAStageBackground omega j) τ).choose_spec.2
  have hu := sourceThetaPSH_of_semipositive_difference hab hi.1
  have hP := (sourceIModel_transition_envelope_and_mass omega hab hi hp).1
  have htrans := sourceNACommonSlice_transition omega Γ
    (sourceNAStageBackground_difference omega (Nat.zero_le j)) τ
  have he : sourceSingularityEnvelope β u = sourceNAStagePotential omega Γ τ 0 :=
    hP.trans htrans.symm
  have hen : FirstPass.singularityEnvelope (atlasClosedFormToNative β).val u =
      sourceNAStagePotential omega Γ τ 0 := (sourceSingularityEnvelope_eq_native β u).symm.trans he
  have hg := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
    (atlasClosedFormToNative β) ((isThetaPSH_iff_nativeThetaPotential β u).mp hu)
  rw [hen] at hg
  exact hg

/-- The actual analytic varying-I-model global-class theorem now gives
the class of the literal infimum, using its already PRODUCED positive mass. -/
theorem sourceNAInfPotential_globalP (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    SingularGlobalPOrder.SourcePEquivalent (n := n)
      (sourceNAInfPotential omega Γ τ) (sourceNAStagePotential omega Γ τ 0) :=
  VaryingBackgroundIModelGlobalClass.sourcePEquivalent_iInf_of_varying_iModels
    omega (atlasClosedFormToNative θ) sourceNAError_pos sourceNAError_antitone sourceNAError_tendsto
    (sourceNAStagePotential_native_model omega Γ τ) (sourceNAStagePotential_native_iModel omega Γ τ)
    (sourceNAStagePotential_antitone omega Γ τ) (sourceNAInfPotential_mass_positive omega Γ hpos τ)
    (sourceNAStagePotential_globalP omega Γ τ)

/-- The actual global ordinary class gives equality of all original multiplier germs. -/
theorem sourceNAInfPotential_iEquivalent_stageZero (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIEquivalent (ofFixedModel n M)
      (sourceNAInfPotential omega Γ τ) (sourceNAStagePotential omega Γ τ 0) := by
  apply (sourceIEquivalent_iff_native ⟨θ, sourceNAInfPotential_thetaPSH omega Γ τ⟩
    ⟨sourceTestCurveEnlargedBackground (sourceNAStageBackground omega 0) θ,
      sourceNACommonSlice_thetaPSH omega Γ _ τ⟩).mpr
  exact GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    (sourceNAInfPotential_globalP omega Γ hpos τ)

/-- The SAME raw original component slice, using only the proved common real cutoff. -/
def sourceNAIndexedSlice (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) : M → EReal :=
  (Γ.component κ).val.potential ⟨τ.val, by
    rw [← sourceNAPotentialCutoff_eq_component omega Γ κ]
    exact τ.property⟩

theorem sourceNAIndexedSlice_thetaPSH (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    (ofFixedModel n M).IsThetaPSH (sourceNAComponentBackground θ κ)
      (sourceNAIndexedSlice omega Γ κ τ) := (Γ.component κ).val.thetaPSH _

theorem sourceNAIndexedSlice_iModel (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIModel (sourceNAComponentBackground θ κ) (sourceNAIndexedSlice omega Γ κ τ) :=
  (sourceIModel_iff_native _ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices omega _).mp (Γ.component κ).property) _)

omit [BorelSpace M] [ConnectedSpace M] in
private theorem indexedCurve_potential_congr
    {α : AtlasClosedRealOneOneForm (ofFixedModel n M)} {C D : SourceTestCurve α} (h : C = D)
    (r : ℝ) (hr : r < C.max) (hs : r < D.max) :
    C.potential ⟨r, hr⟩ = D.potential ⟨r, hs⟩ := by
  cases h
  rfl

/-- Original compatibility reindexed to the same open interval, at every geometric index. -/
theorem sourceNAIndexedSlice_transition (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {κ ξ : SourceKahlerForm n M} (h : sourceKahlerFormLE κ ξ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceNAIndexedSlice omega Γ ξ τ =
      sourceIEnvelope (sourceNAComponentBackground θ ξ) (sourceNAIndexedSlice omega Γ κ τ) := by
  have hrκ : τ.val < (Γ.component κ).val.max := by
    rw [← sourceNAPotentialCutoff_eq_component omega Γ κ]
    exact τ.property
  have hrξ : τ.val < (Γ.component ξ).val.max := by
    rw [← sourceNAPotentialCutoff_eq_component omega Γ ξ]
    exact τ.property
  have hrT : τ.val < (sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ξ)
      (sourceNAComponentBackground_difference θ h) (Γ.component κ)).val.max := by
    simpa only [sourceIModelTestCurveTransition_max] using hrκ
  have he := indexedCurve_potential_congr (congrArg Subtype.val (Γ.compatible κ ξ h)) τ.val hrT hrξ
  rw [sourceIModelTestCurveTransition_potential _ _ _ τ.val hrκ hrT] at he
  exact he.symm

theorem sourceNAIndexedSlice_iEquivalent_of_le (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) {κ ξ : SourceKahlerForm n M} (h : sourceKahlerFormLE κ ξ)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIEquivalent (ofFixedModel n M)
      (sourceNAIndexedSlice omega Γ κ τ) (sourceNAIndexedSlice omega Γ ξ τ) := by
  have hu := sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_difference θ h)
    (sourceNAIndexedSlice_thetaPSH omega Γ κ τ)
  have hi := sourceIEquivalent_iEnvelope hu
  rw [← sourceNAIndexedSlice_transition omega Γ h τ] at hi
  exact hi

/-- Actual compatibility through a common larger form compares any two original slices. -/
theorem sourceNAIndexedSlice_iEquivalent (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (κ ξ : SourceKahlerForm n M)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIEquivalent (ofFixedModel n M)
      (sourceNAIndexedSlice omega Γ κ τ) (sourceNAIndexedSlice omega Γ ξ τ) :=
  sourceIEquivalent_trans
    (sourceNAIndexedSlice_iEquivalent_of_le omega Γ (sourceKahlerFormLE_commonUpper_left κ ξ) τ)
    (sourceIEquivalent_symm
      (sourceNAIndexedSlice_iEquivalent_of_le omega Γ (sourceKahlerFormLE_commonUpper_right κ ξ) τ))

/-- The literal-background slice and its indexed original component are the SAME function. -/
theorem sourceNACommonSlice_eq_indexedSlice (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (ω : KahlerBackground n M)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceNACommonSlice omega Γ ω τ =
      sourceNAIndexedSlice omega Γ (sourceKahlerFormOfBackground ω) τ :=
  Γ.realizedComponent_potential ω τ.val _ _

/-- The produced original infimum has the original multiplier type at EVERY geometric index. -/
theorem sourceNAInfPotential_iEquivalent_component (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) (κ : SourceKahlerForm n M)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIEquivalent (ofFixedModel n M)
      (sourceNAInfPotential omega Γ τ) (sourceNAIndexedSlice omega Γ κ τ) := by
  have hi := sourceNAInfPotential_iEquivalent_stageZero omega Γ hpos τ
  change sourceIEquivalent (ofFixedModel n M) (sourceNAInfPotential omega Γ τ)
    (sourceNACommonSlice omega Γ (sourceNAStageBackground omega 0) τ) at hi
  rw [sourceNACommonSlice_eq_indexedSlice] at hi
  exact sourceIEquivalent_trans hi (sourceNAIndexedSlice_iEquivalent omega Γ _ κ τ)

/-- Entire competitor-set invariance and actual output fixedness recover each literal component slice. -/
theorem sourceNAInfPotential_component_envelope (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) (κ : SourceKahlerForm n M)
    (τ : Iio (sourceNAPotentialCutoff omega Γ)) :
    sourceIEnvelope (sourceNAComponentBackground θ κ) (sourceNAInfPotential omega Γ τ) =
      sourceNAIndexedSlice omega Γ κ τ :=
  (sourceIEnvelope_eq_of_equivalent
    (sourceNAInfPotential_iEquivalent_component omega Γ hpos κ τ)).trans
      (sourceNAIndexedSlice_iModel omega Γ κ τ).2.symm

/-- The actual constructed original curve recovers ALL original components and compatibility. -/
theorem sourceNARecoveredPositiveCurve_embedding (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (hpos : 0 < sourceNAVolume Γ) :
    sourcePositiveTestCurveToNA (sourceNARecoveredPositiveCurve omega Γ hpos) = Γ := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact (sourcePositiveTestCurveToNA_max _ κ).trans
      ((sourceNARecoveredPositiveCurve_max omega Γ hpos).trans
        (sourceNAPotentialCutoff_eq_component omega Γ κ))
  · intro r hr hs
    have hrG : r < (sourceNARecoveredPositiveCurve omega Γ hpos).val.max := by
      simpa only [sourcePositiveTestCurveToNA_max] using hr
    have hm : r < sourceNAPotentialCutoff omega Γ := by
      simpa only [← sourceNAPotentialCutoff_eq_component omega Γ κ] using hs
    let τ : Iio (sourceNAPotentialCutoff omega Γ) := ⟨r, hm⟩
    rw [sourcePositiveTestCurveToNA_potential _ κ r hrG hr]
    change sourceIEnvelope (sourceNAComponentBackground θ κ) (sourceNAInfPotential omega Γ τ) =
      sourceNAIndexedSlice omega Γ κ τ
    exact sourceNAInfPotential_component_envelope omega Γ hpos κ τ

/-- Whole original lma:positivemasspart, for the existing canonical injection
and the zero-allowed volume on the ENTIRE original inverse-system space. -/
theorem sourceNA_positive_image_whole (omega : KahlerBackground n M) :
    Set.range (sourcePositiveTestCurveToNA (θ := θ)) = {Γ | 0 < sourceNAVolume Γ} := by
  ext Γ
  constructor
  · rintro ⟨G, rfl⟩
    exact sourceNAVolume_positiveTestCurve_pos omega G
  · intro hpos
    exact ⟨sourceNARecoveredPositiveCurve omega Γ hpos,
      sourceNARecoveredPositiveCurve_embedding omega Γ hpos⟩

end SGPT.PSH.VariableComplexAtlas
