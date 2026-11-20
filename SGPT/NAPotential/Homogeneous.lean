import SGPT.NAPotential.DecreasingInfimum
import SGPT.Foundations.Analysis.Pending.IGoodMassReduction
import SGPT.Foundations.Analysis.Pending.ThetaCapacity
import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra

/-! # Homogeneous non-Archimedean metrics

Source `ex:embedpshintona` of `chapter_NApotential.tex`.  For `φ ∈ PSH(X, θ)` the homogeneous
non-Archimedean metric `Γ^φ` has `Γ^φ_max = 0` and, for every Kähler form `ω` and `τ < 0`,
`Γ^{φ,θ+ω}_τ = P_{θ+ω}[φ]_𝓘`.  The components are constant test curves; their positivity
uses the lower bound `∫ (θ + ω + dd^c φ)^n ≥ ∫ ω^n`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine `θ`-psh function is more singular than its `𝓘`-envelope. -/
theorem sourceSingularityLE_sourceIEnvelope {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH α φ) :
    SGPT.PSH.SingularityLE φ (sourceIEnvelope α φ) := by
  rw [sourceIEnvelope_eq_native α φ hφ]
  exact SGPT.Foundations.Analysis.Pending.moreSingularOn_iSingularityEnvelope
    ((isThetaPSH_iff_nativeThetaPotential α φ).mp hφ)

/-- The constant test curve with cutoff `0` and every slice equal to a positive-mass
`𝓘`-model potential `u`. -/
def sourceConstantIModelTestCurve (omega : KahlerBackground n M) (u : M → EReal)
    (hu : sourceIModel α u) (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ) :
    SourceTestCurve α where
  max := 0
  potential _ := u
  thetaPSH _ := hu.1
  antitone _ _ _ _ := le_rfl
  concave x := sourceTestCurveNegativeTrace_convex_of_chords _
    (fun _ _ _ ht0 ht1 => (ThetaCapacity.convexComb_self ht0 ht1 u).le) x
  fixedPoint _ := by
    have hg := (sourceIModel_positive_iGood α u hu hpos).2
    rw [(sourceIGood_iff_PI_eq omega hu.1 hpos).mp hg]
    exact hu.2.symm
  positiveLimitMass := by
    have : Nonempty (Iio (0 : ℝ)) := ⟨⟨-1, by norm_num⟩⟩
    have hlim : SGPT.PSH.uscSup (fun _ : Iio (0 : ℝ) => u) = u := by
      change uscRegularization (fun y => ⨆ _ : Iio (0 : ℝ), u y) = u
      simp only [ciSup_const]
      exact uscRegularization_eq
        ((isThetaPSH_iff_nativeThetaPotential α u).mp hu.1).1.quasiPlurisubharmonic.upperSemicontinuous
    exact hpos.trans_eq (sourcePotentialMass_congr hlim.symm _ _)

theorem sourceConstantIModelTestCurve_max (omega : KahlerBackground n M) (u : M → EReal)
    (hu : sourceIModel α u) (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ) :
    (sourceConstantIModelTestCurve omega u hu hpos).max = 0 := rfl

theorem sourceConstantIModelTestCurve_potential (omega : KahlerBackground n M) (u : M → EReal)
    (hu : sourceIModel α u) (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ)
    (r : Iio (sourceConstantIModelTestCurve omega u hu hpos).max) :
    (sourceConstantIModelTestCurve omega u hu hpos).potential r = u := rfl

/-- The constant curve is a positive `𝓘`-model test curve. -/
theorem sourceConstantIModelTestCurve_mem (omega : KahlerBackground n M) (u : M → EReal)
    (hu : sourceIModel α u) (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ) :
    sourceConstantIModelTestCurve omega u hu hpos ∈ SourceIModelTestCurvesPositive α :=
  (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
    (fun _ => (sourceIModel_iff_native α u).mp hu)

/-- The limit of a constant curve is its value. -/
theorem sourceConstantIModelTestCurve_limit (omega : KahlerBackground n M) (u : M → EReal)
    (hu : sourceIModel α u) (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu.1 univ) :
    sourceTestCurveLimit (sourceConstantIModelTestCurve omega u hu hpos).toSourceTestCurvePredata =
      u := by
  have : Nonempty (Iio (0 : ℝ)) := ⟨⟨-1, by norm_num⟩⟩
  change uscRegularization (fun y => ⨆ _ : Iio (0 : ℝ), u y) = u
  simp only [ciSup_const]
  exact uscRegularization_eq
    ((isThetaPSH_iff_nativeThetaPotential α u).mp hu.1).1.quasiPlurisubharmonic.upperSemicontinuous

/-- A `θ`-psh function has mass at least `∫ ω^n` in the class `θ + ω`; so does its
`𝓘`-envelope there. -/
theorem sourceNA_iEnvelope_component_mass_pos {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (κ : SourceKahlerForm n M) :
    0 < sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
      (sourceIEnvelope (sourceNAComponentBackground θ κ) φ)
      (isThetaPSH_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference
        (sourceNAComponentBackground_positive θ κ) hφ)) univ := by
  let ω := sourceKahlerFormRepresentative κ
  have hφκ := sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ κ) hφ
  have hform : atlasClosedFormToNative (sourceNAComponentBackground θ κ) =
      atlasClosedFormToNative θ + (1 : ℝ) • ω.form := by
    rw [sourceNAComponentBackground_native, one_smul]
  have hnat := (isThetaPSH_iff_nativeThetaPotential _ _).mp hφκ
  have hnat' : IsThetaPshPotential (atlasClosedFormToNative θ + (1 : ℝ) • ω.form).val φ :=
    hform ▸ hnat
  have hlow := sourceNA_diagonalMass_add_smul_lower_bound ω
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hφ) one_pos hnat'
  have hK : 0 < ENNReal.ofReal ((1 : ℝ) ^ n * (DiagonalMass.diagonalPotentialMass ω.form
      (fun _ => 0) (PluripolarCapacityDichotomy.isThetaPshPotential_zero ω)).toReal) := by
    apply ENNReal.ofReal_pos.mpr
    rw [one_pow, one_mul]
    exact ENNReal.toReal_pos (KahlerVolumePositive.diagonalPotentialMass_zero_pos _).ne'
      (MixedMass.globalMixedMass_lt_top ω
        (fun _ : Fin n => (PluripolarCapacityDichotomy.isThetaPshPotential_zero ω).1)).ne
  have hmφ : DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ + (1 : ℝ) • ω.form) φ
      hnat' = sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ) φ hφκ univ :=
    sourceNA_diagonalMass_congr_form hform.symm _ _
  exact (hK.trans_le hlow).trans_le (hmφ.trans_le
    (sourcePotentialNonPluripolarMass_mono ω hφκ _ (sourceSingularityLE_sourceIEnvelope hφκ)))

/-- The component of the homogeneous metric at a geometric Kähler index: the constant test
curve with value `P_{θ+ω}[φ]_𝓘`. -/
def sourceNAHomogeneousComponent {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (κ : SourceKahlerForm n M) : SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) :=
  ⟨sourceConstantIModelTestCurve (sourceKahlerFormRepresentative κ)
      (sourceIEnvelope (sourceNAComponentBackground θ κ) φ)
      (sourceIEnvelope_isIModel (sourceThetaPSH_of_semipositive_difference
        (sourceNAComponentBackground_positive θ κ) hφ))
      (sourceNA_iEnvelope_component_mass_pos hφ κ),
    sourceConstantIModelTestCurve_mem _ _ _ _⟩

theorem sourceNAHomogeneousComponent_max {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (κ : SourceKahlerForm n M) : (sourceNAHomogeneousComponent hφ κ).val.max = 0 := rfl

theorem sourceNAHomogeneousComponent_potential {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (κ : SourceKahlerForm n M)
    (r : Iio (sourceNAHomogeneousComponent hφ κ).val.max) :
    (sourceNAHomogeneousComponent hφ κ).val.potential r =
      sourceIEnvelope (sourceNAComponentBackground θ κ) φ := rfl

theorem sourceNAHomogeneousComponent_limit {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (κ : SourceKahlerForm n M) :
    sourceTestCurveLimit (sourceNAHomogeneousComponent hφ κ).val.toSourceTestCurvePredata =
      sourceIEnvelope (sourceNAComponentBackground θ κ) φ :=
  sourceConstantIModelTestCurve_limit (sourceKahlerFormRepresentative κ)
    (sourceIEnvelope (sourceNAComponentBackground θ κ) φ)
    (sourceIEnvelope_isIModel (sourceThetaPSH_of_semipositive_difference
      (sourceNAComponentBackground_positive θ κ) hφ))
    (sourceNA_iEnvelope_component_mass_pos hφ κ)

/-- Source `ex:embedpshintona`: the homogeneous non-Archimedean metric `Γ^φ` associated with
`φ ∈ PSH(X, θ)`. -/
def SourceNAPotential.homogeneous {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    SourceNAPotential θ where
  component κ := sourceNAHomogeneousComponent hφ κ
  compatible κ ζ h := by
    have hφκ := sourceThetaPSH_of_semipositive_difference
      (sourceNAComponentBackground_positive θ κ) hφ
    apply Subtype.ext
    apply SourceTestCurve.ext_of_max_potential
    · rw [sourceIModelTestCurveTransition_max, sourceNAHomogeneousComponent_max,
        sourceNAHomogeneousComponent_max]
    · intro r hr hs
      have hr' : r < (sourceNAHomogeneousComponent hφ κ).val.max := by
        rw [sourceIModelTestCurveTransition_max] at hr
        exact hr
      have e1 := sourceIModelTestCurveTransition_potential (sourceKahlerFormRepresentative ζ)
        (sourceNAComponentBackground_difference θ h) (sourceNAHomogeneousComponent hφ κ) r hr' hr
      have e2 := sourceNAHomogeneousComponent_potential hφ κ ⟨r, hr'⟩
      have e3 := sourceNAHomogeneousComponent_potential hφ ζ ⟨r, hs⟩
      rw [e1, e2, e3]
      exact sourceIEnvelope_eq_of_equivalent
        (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope hφκ))

/-- `ex:embedpshintona`, clause 1: `Γ^φ_max = 0`. -/
theorem sourceNAPotentialCutoff_homogeneous (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceNAPotentialCutoff omega (SourceNAPotential.homogeneous hφ) = 0 :=
  sourceNAHomogeneousComponent_max hφ _

/-- `ex:embedpshintona`, clause 2 at every geometric Kähler index:
`Γ^{φ,θ+ω}_τ = P_{θ+ω}[φ]_𝓘` for `τ < 0`. -/
theorem SourceNAPotential.homogeneous_component_potential {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (κ : SourceKahlerForm n M)
    (r : Iio ((SourceNAPotential.homogeneous hφ).component κ).val.max) :
    ((SourceNAPotential.homogeneous hφ).component κ).val.potential r =
      sourceIEnvelope (sourceNAComponentBackground θ κ) φ :=
  sourceNAHomogeneousComponent_potential hφ κ r

/-- `ex:embedpshintona`, clause 2 in every literal background `θ + ω`. -/
theorem SourceNAPotential.homogeneous_realizedComponent_potential {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (omega : KahlerBackground n M) (r : ℝ)
    (hr : r < ((SourceNAPotential.homogeneous hφ).realizedComponent omega).val.max) :
    ((SourceNAPotential.homogeneous hφ).realizedComponent omega).val.potential ⟨r, hr⟩ =
      sourceIEnvelope (sourceTestCurveEnlargedBackground omega θ) φ := by
  have hr' : r < ((SourceNAPotential.homogeneous hφ).component
      (sourceKahlerFormOfBackground omega)).val.max := by
    rwa [SourceNAPotential.realizedComponent_max] at hr
  rw [SourceNAPotential.realizedComponent_potential _ omega r hr' hr,
    SourceNAPotential.homogeneous_component_potential]
  exact sourceIEnvelope_geometricallyEq (sourceNAComponentBackground_geometricallyEq omega) φ

/-- The homogeneous metric is the unique element with the components of `ex:embedpshintona`. -/
theorem SourceNAPotential.homogeneous_unique {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (Γ : SourceNAPotential θ)
    (hmax : ∀ κ : SourceKahlerForm n M, (Γ.component κ).val.max = 0)
    (hpot : ∀ (κ : SourceKahlerForm n M) (r : ℝ) (hr : r < (Γ.component κ).val.max),
      (Γ.component κ).val.potential ⟨r, hr⟩ = sourceIEnvelope (sourceNAComponentBackground θ κ) φ) :
    Γ = SourceNAPotential.homogeneous hφ := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact (hmax κ).trans (sourceNAHomogeneousComponent_max hφ κ).symm
  · intro r hr hs
    exact (hpot κ r hr).trans (sourceNAHomogeneousComponent_potential hφ κ _).symm

/-- Every component mass of `Γ^φ` is the `𝓘`-volume of `φ` in the class `θ + ω`. -/
theorem sourceNAComponentMass_homogeneous {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (κ : SourceKahlerForm n M) :
    sourceNAComponentMass (SourceNAPotential.homogeneous hφ) κ =
      sourceIVolume (sourceNAComponentBackground θ κ) φ
        (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ κ) hφ) := by
  unfold sourceNAComponentMass sourceIVolume
  exact sourcePotentialMass_congr (sourceNAHomogeneousComponent_limit hφ κ) _ _

omit [BorelSpace M] in
/-- The `𝓘`-volume only depends on the background through the form. -/
theorem sourceIVolume_congr_form {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)} (h : α = β)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u)
    (hv : (ofFixedModel n M).IsThetaPSH β u) : sourceIVolume α u hu = sourceIVolume β u hv := by
  subst h
  rfl

/-- The `𝓘`-volume is unchanged under geometric equality of backgrounds. -/
theorem sourceIVolume_geometricallyEq {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (h : (atlasClosedFormToNative α).val.GeometricallyEq (atlasClosedFormToNative β).val)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u)
    (hv : (ofFixedModel n M).IsThetaPSH β u) : sourceIVolume α u hu = sourceIVolume β u hv := by
  have he := sourceIEnvelope_geometricallyEq h u
  have hα : (ofFixedModel n M).IsThetaPSH α (sourceIEnvelope β u) :=
    he ▸ isThetaPSH_sourceIEnvelope hu
  unfold sourceIVolume
  calc sourcePotentialNonPluripolarMeasure α (sourceIEnvelope α u) (isThetaPSH_sourceIEnvelope hu)
        univ
      = sourcePotentialNonPluripolarMeasure α (sourceIEnvelope β u) hα univ :=
        sourcePotentialMass_congr he _ _
    _ = sourcePotentialNonPluripolarMeasure β (sourceIEnvelope β u) (isThetaPSH_sourceIEnvelope hv)
          univ := (sourcePotentialMass_geometricallyEq h _ _).symm

/-- The `𝓘`-volume grows under a semipositive change of background. -/
theorem sourceIVolume_le_of_semipositive_difference
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (omega : KahlerBackground n M) {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH α u) :
    sourceIVolume α u hu ≤ sourceIVolume β u (sourceThetaPSH_of_semipositive_difference hαβ hu) := by
  have hv := sourceThetaPSH_of_semipositive_difference hαβ hu
  have hle : sourceIEnvelope α u ≤ sourceIEnvelope β u :=
    le_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference hαβ (isThetaPSH_sourceIEnvelope hu))
      (sourceIEnvelope_le_zero α u) (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope hu))
  unfold sourceIVolume
  exact (sourcePotentialMass_mono_background hαβ (isThetaPSH_sourceIEnvelope hu)).trans
    (sourcePotentialNonPluripolarMass_mono omega _ (isThetaPSH_sourceIEnvelope hv)
      (MoreSingularOn.of_le fun x _ => hle x))

/-- `ex:embedpshintona`, volume identity: `vol Γ^φ = vol θ_φ`, where
`vol θ_φ = lim_{ε → 0+} ∫ (θ + ε ω + dd^c P_{θ+εω}[φ]_𝓘)^n` (`def:mix_vol`); the latter equals
`∫ (θ + dd^c P_θ[φ]_𝓘)^n` by `sourceGeneralMixedIVolume_diagonal`. -/
theorem sourceNAVolume_homogeneous (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceNAVolume (SourceNAPotential.homogeneous hφ) =
      sourceGeneralMixedIVolume omega (fun _ : Fin n => θ) (fun _ => φ) (fun _ => hφ) ∧
    sourceNAVolume (SourceNAPotential.homogeneous hφ) = sourceIVolume θ φ hφ := by
  have hdiag := sourceGeneralMixedIVolume_diagonal omega hφ
  suffices h : sourceNAVolume (SourceNAPotential.homogeneous hφ) = sourceIVolume θ φ hφ from
    ⟨h.trans hdiag.symm, h⟩
  apply le_antisymm
  · rw [← hdiag]
    apply le_iInf
    intro ε
    have hε : (0 : ℝ) < ((ε : NNReal) : ℝ) := by exact_mod_cast ε.property
    let ωε := KahlerBackground.smul hε omega
    let κ := sourceKahlerFormOfBackground ωε
    let θε := nativeClosedFormToAtlas (atlasClosedFormToNative θ + ((ε : NNReal) : ℝ) • omega.form)
    have hθε : (ofFixedModel n M).IsThetaPSH θε φ := by
      apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      simp only [θε, sourceNativeAtlasForm_roundTrip]
      exact LocalPotentials.isThetaPshPotential_add_of_semipositive
        ((isThetaPSH_iff_nativeThetaPotential _ _).mp hφ)
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.le)
    have hpert : sourceMixedIVolumeKahlerPerturbation omega (fun _ : Fin n => θ) (fun _ => φ)
        (fun _ => hφ) ε = sourceIVolume θε φ hθε :=
      sourceEnvelopeMixedIVolume_diagonal θε φ hθε
    have henl : sourceTestCurveEnlargedBackground ωε θ = θε := by
      apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
      simp only [sourceTestCurveEnlargedBackground_native, θε, sourceNativeAtlasForm_roundTrip, ωε,
        KahlerBackground.smul_form]
    have hφenl : (ofFixedModel n M).IsThetaPSH (sourceTestCurveEnlargedBackground ωε θ) φ :=
      henl.symm ▸ hθε
    refine (sourceNAVolume_le_component _ κ).trans (le_of_eq ?_)
    rw [sourceNAComponentMass_homogeneous, hpert]
    exact (sourceIVolume_geometricallyEq (sourceNAComponentBackground_geometricallyEq ωε) _
      hφenl).trans (sourceIVolume_congr_form henl _ _)
  · apply le_iInf
    intro κ
    rw [sourceNAComponentMass_homogeneous]
    exact sourceIVolume_le_of_semipositive_difference (sourceNAComponentBackground_positive θ κ)
      omega hφ

end SGPT.PSH.VariableComplexAtlas
