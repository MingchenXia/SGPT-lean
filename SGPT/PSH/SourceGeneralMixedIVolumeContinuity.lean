import SGPT.PSH.SourceGeneralMixedIVolumePerturbation
import SGPT.PSH.SourceIEnvelopeSingularityContinuity
import SGPT.PSH.SourceSingularityBackgroundChange
import SGPT.PSH.SourceCurrentMixedIVolume

/-! # General mixed I-volume continuity, including vanishing masses

The constant in the uniform perturbation bound is selected before all net
potentials. Positive actual mass is produced only in the genuinely enlarged
background. No positive original mass, stage mass, convergence certificate,
or countable-cofinality assumption is made. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem mixedCont_perturbPSH (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {t : ℝ} (ht : 0 ≤ t) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + t • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem mixedCont_perturbBig (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {t : ℝ} (ht : 0 ≤ t) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + t • ω.form)))) := by
  have hη : (atlasClosedFormToNative (nativeClosedFormToAtlas (t • ω.form))).val.IsSemipositive := by
    rw [sourceNativeAtlasForm_roundTrip]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive ht
  have h := sourceBigClass_add_semipositive θ (nativeClosedFormToAtlas (t • ω.form)) hbig hη
  change IsBigClass (RealBottChern.ofRepresentative
    (atlasClosedFormToNative θ + atlasClosedFormToNative (nativeClosedFormToAtlas (t • ω.form)))) at h
  simpa only [sourceNativeAtlasForm_roundTrip] using h

private theorem mixedCont_perturbedFinite (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ a, (ofFixedModel n M).IsThetaPSH (θ a) (u a))
    (t : ℝ) (ht : 0 ≤ t) :
    sourceGeneralMixedIVolumeKahlerPerturbed ω θ u hu t ht < ⊤ := by
  change sourceGeneralMixedIVolume ω _ _ _ < ⊤
  exact sourceGeneralMixedIVolume_lt_top ω _ _ _

/-- Every fixed positive enlargement has the actual general mixed-volume
limit. Enlarged genuine domains, big classes and positive ACTUAL limit masses
are all produced internally; original zero masses and every pole remain. -/
theorem tendsto_sourceGeneralMixedIVolumeKahlerPerturbed_of_sourceSingularityTopology
    (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i => ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a)) (sourceSingularityTopology ω (θ a) (hbig a)) (u a)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun i => sourceGeneralMixedIVolumeKahlerPerturbed ω θ
      (fun a => (ui i a).val) (fun a => (ui i a).property) t ht.le) F
      (𝓝 (sourceGeneralMixedIVolumeKahlerPerturbed ω θ
        (fun a => (u a).val) (fun a => (u a).property) t ht.le)) := by
  let Γ a := nativeClosedFormToAtlas (atlasClosedFormToNative (θ a) + t • ω.form)
  have hΓ a := mixedCont_perturbBig ω (θ a) (hbig a) ht.le
  let wi (i : I) (a : Fin n) : SourceThetaPotentialL1 (Γ a) :=
    ⟨(ui i a).val, mixedCont_perturbPSH ω (ui i a).property ht.le⟩
  let v (a : Fin n) : SourceThetaPotentialL1 (Γ a) :=
    ⟨(u a).val, mixedCont_perturbPSH ω (u a).property ht.le⟩
  have hwi a : Tendsto (fun i => wi i a) F
      (@nhds (SourceThetaPotentialL1 (Γ a)) (sourceSingularityTopology ω (Γ a) (hΓ a)) (v a)) :=
    (tendsto_sourceSingularityTopology_iff_common_backgrounds ω (θ a) (Γ a)
      (hbig a) (hΓ a) F (fun i => ui i a) (u a)
      (fun i => mixedCont_perturbPSH ω (ui i a).property ht.le)
      (mixedCont_perturbPSH ω (u a).property ht.le)).mp (hlim a)
  have hpos a : 0 < sourcePotentialNonPluripolarMeasure (Γ a) (v a).val (v a).property univ := by
    have h := SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
      ((isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (u a).property) ht
    simpa only [DiagonalMass.HasPositivePotentialMass, DiagonalMass.diagonalPotentialMass,
      sourcePotentialNonPluripolarMeasure, Γ, v, sourceNativeAtlasForm_roundTrip] using h
  have hQ a := tendsto_sourceIEnvelope_of_sourceSingularityTopology
    ω (Γ a) (hΓ a) F (fun i => wi i a) (v a) (hpos a) (hwi a)
  have hmass := tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology
    ω Γ hΓ F (fun i a => sourceThetaPotentialIEnvelope (wi i a))
    (fun a => sourceThetaPotentialIEnvelope (v a)) hQ
  have he (w : (a : Fin n) → SourceThetaPotentialL1 (θ a)) :
      sourceGeneralMixedIVolumeKahlerPerturbed ω θ (fun a => (w a).val)
        (fun a => (w a).property) t ht.le =
      sourceMixedNonPluripolarMass Γ (fun a => sourceIEnvelope (Γ a) (w a).val)
        (fun a => isThetaPSH_sourceIEnvelope (mixedCont_perturbPSH ω (w a).property ht.le)) := by
    change sourceGeneralMixedIVolume ω Γ _ _ = _
    apply sourceGeneralMixedIVolume_eq_positive
    intro a
    exact sourceIVolume_add_kahler_pos ω (w a).property (ε := ⟨t, ht.le⟩) ht
  convert hmass using 1
  · funext i
    exact he (ui i)
  · exact congrArg nhds (he u)

/-- WHOLE original thm:mvolcont and eq:convmixedvolds: arbitrary source dS
filters give the actual general mixed I-volume limit, including ALL original
zero masses, independent backgrounds, poles and the original n=0 tuple. -/
theorem tendsto_sourceGeneralMixedIVolume_of_sourceSingularityTopology
    (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i => ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a)) (sourceSingularityTopology ω (θ a) (hbig a)) (u a))) :
    Tendsto (fun i => sourceGeneralMixedIVolume ω θ
      (fun a => (ui i a).val) (fun a => (ui i a).property)) F
      (𝓝 (sourceGeneralMixedIVolume ω θ (fun a => (u a).val) (fun a => (u a).property))) := by
  let g i := sourceGeneralMixedIVolume ω θ (fun a => (ui i a).val) (fun a => (ui i a).property)
  let g₀ := sourceGeneralMixedIVolume ω θ (fun a => (u a).val) (fun a => (u a).property)
  obtain ⟨C, hC, hbound⟩ := sourceGeneralMixedIVolume_class_uniform_perturbation_bound ω
    (fun a => RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a)))
  have hreal : Tendsto (fun i => (g i).toReal) F (𝓝 g₀.toReal) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let t : ℝ := min 1 (δ / (4 * C))
    have ht : 0 < t := lt_min zero_lt_one (div_pos hδ (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have hCt : C * t ≤ δ / 4 := by
      have h := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (δ / (4 * C))) hC.le
      have he : C * (δ / (4 * C)) = δ / 4 := by field_simp
      exact h.trans_eq he
    have hpert := tendsto_sourceGeneralMixedIVolumeKahlerPerturbed_of_sourceSingularityTopology
      ω θ hbig F ui u hlim ht
    have hpertReal := (ENNReal.tendsto_toReal (mixedCont_perturbedFinite ω θ
      (fun a => (u a).val) (fun a => (u a).property) t ht.le).ne).comp hpert
    have hev := Metric.tendsto_nhds.mp hpertReal (δ / 2) (half_pos hδ)
    filter_upwards [hev] with i hi
    have hb_i := hbound θ (fun a => (ui i a).val) (fun a => (ui i a).property)
      (fun _ => rfl) t ht.le ht1
    have hb₀ := hbound θ (fun a => (u a).val) (fun a => (u a).property)
      (fun _ => rfl) t ht.le ht1
    rw [Real.dist_eq] at hi ⊢
    change |(g i).toReal - g₀.toReal| < δ
    dsimp only [Function.comp_def] at hi
    have hhi := abs_lt.mp hi
    apply abs_lt.mpr
    dsimp only [g, g₀]
    constructor <;> linarith [hb_i.1, hb_i.2, hb₀.1, hb₀.2, hhi.1, hhi.2]
  have hENN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hfin_i i : g i ≠ ⊤ := (sourceGeneralMixedIVolume_lt_top ω θ
    (fun a => (ui i a).val) (fun a => (ui i a).property)).ne
  have hfin₀ : g₀ ≠ ⊤ := (sourceGeneralMixedIVolume_lt_top ω θ
    (fun a => (u a).val) (fun a => (u a).property)).ne
  convert hENN using 1
  · funext i
    exact (ENNReal.ofReal_toReal (hfin_i i)).symm
  · exact congrArg nhds (ENNReal.ofReal_toReal hfin₀).symm

/-- WHOLE original cor:contvolu2 and eq:Ivolcont2. BOTH the actual I-volume
and the actual original diagonal NP measure on X converge, with no positive
original mass assumption and no substitution of I-volume for actual mass. -/
theorem tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology_all_mass
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hlim : Tendsto ui F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) u)) :
    Tendsto (fun i => sourceIVolume θ (ui i).val (ui i).property) F
      (𝓝 (sourceIVolume θ u.val u.property)) ∧
    Tendsto (fun i => sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ) F
      (𝓝 (sourcePotentialNonPluripolarMeasure θ u.val u.property univ)) := by
  constructor
  · simpa only [sourceGeneralMixedIVolume_diagonal] using
      tendsto_sourceGeneralMixedIVolume_of_sourceSingularityTopology
        ω (fun _ : Fin n => θ) (fun _ => hbig) F (fun i _ => ui i) (fun _ => u) (fun _ => hlim)
  · simpa only [sourceMixedNonPluripolarMass_diagonal] using
      tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology
        ω (fun _ : Fin n => θ) (fun _ => hbig) F (fun i _ => ui i) (fun _ => u) (fun _ => hlim)

section OriginalCurrent

open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The whole mixed continuity conclusion on the LITERAL entire currents
θᵢ+ddC uᵢ. Natural closed/type/full-positive domains are internally produced.
The native degree-two interface uses its genuine dimension m+1; the theorem
above separately retains the original zero-dimensional empty tuple. -/
theorem tendsto_sourceCurrentMixedIVolume_of_sourceSingularityTopology
    (ω : KahlerBackground (m + 1) X)
    (θ : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin (m + 1)) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin (m + 1)) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i => ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a)) (sourceSingularityTopology ω (θ a) (hbig a)) (u a))) :
    let hn (a : Fin (m + 1)) (w : SourceThetaPotentialL1 (θ a)) :=
      (isThetaPSH_iff_nativeThetaPotential (θ a) w.val).mp w.property
    let T (w : (a : Fin (m + 1)) → SourceThetaPotentialL1 (θ a)) a :=
      thetaPotentialCurrent (atlasClosedFormToNative (θ a)).val (w a).val (hn a (w a))
    let hT (w : (a : Fin (m + 1)) → SourceThetaPotentialL1 (θ a)) a :=
      thetaPotentialCurrent_closed_type_positive
        (atlasClosedFormToNative (θ a)).val (w a).val (hn a (w a))
    Tendsto (fun i => sourceCurrentMixedIVolume ω (T (ui i))
      (fun a => (hT (ui i) a).1) (fun a => (hT (ui i) a).2.1) (fun a => (hT (ui i) a).2.2)) F
      (𝓝 (sourceCurrentMixedIVolume ω (T u)
        (fun a => (hT u a).1) (fun a => (hT u a).2.1) (fun a => (hT u a).2.2))) := by
  dsimp only
  have he (w : (a : Fin (m + 1)) → SourceThetaPotentialL1 (θ a)) :
      sourceCurrentMixedIVolume ω
        (fun a => thetaPotentialCurrent (atlasClosedFormToNative (θ a)).val (w a).val
          ((isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (w a).property))
        (fun a => (thetaPotentialCurrent_closed_type_positive _ _
          ((isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (w a).property)).1)
        (fun a => (thetaPotentialCurrent_closed_type_positive _ _
          ((isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (w a).property)).2.1)
        (fun a => (thetaPotentialCurrent_closed_type_positive _ _
          ((isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (w a).property)).2.2) =
      sourceGeneralMixedIVolume ω θ (fun a => (w a).val) (fun a => (w a).property) := by
    simpa only [sourceAtlasNativeForm_roundTrip] using
      sourceCurrentMixedIVolume_eq_representation ω _ _ _ _
        (fun a => atlasClosedFormToNative (θ a)) (fun a => (w a).val)
        (fun a => (isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (w a).property)
        (fun _ => rfl)
  have h := tendsto_sourceGeneralMixedIVolume_of_sourceSingularityTopology ω θ hbig F ui u hlim
  convert h using 1
  · funext i
    exact he (ui i)
  · exact congrArg nhds (he u)

end OriginalCurrent

end SGPT.PSH.VariableComplexAtlas
