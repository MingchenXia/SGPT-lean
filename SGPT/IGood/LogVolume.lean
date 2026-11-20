import SGPT.NPP.LogConcavityAnalytic
import SGPT.PSH.SourceQuasiEquisingularCriterion
import SGPT.PSH.SourceGeneralMixedIVolumeContinuity
import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra
import SGPT.PSH.SourceCurrentMixedIVolumeAlgebra
import SGPT.NAPotential.Homogeneous
import SGPT.NPP.DimensionZero
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood

/-!
# Log-concavity of mixed volumes

Source `prop:logvol` (chapter *𝓘-good singularities*, section *Mixed volumes*): for closed
positive `(1,1)`-currents `T₁, …, Tₙ` on a connected compact Kähler manifold `X` of dimension
`n`,

`vol(T₁, …, Tₙ) ≥ ∏ᵢ (vol Tᵢ)^{1/n}`,

where `vol(T₁, …, Tₙ)` is the general mixed volume (`def:mix_vol`,
`sourceGeneralMixedIVolume`, the limit of the positive-volume mixed volumes of the Kähler
perturbations `Tᵢ + εω`) and `vol Tᵢ` the volume (`def:volqpsh`, `sourceIVolume`).

## Proof

The book reduces to the general case of `thm:logconc`, applied to the `𝓘`-model envelopes. We
instead use the case of potentials with analytic singularities (proved in
`SGPT.NPP.LogConcavityAnalytic`) and approximation:

* If some `vol Tᵢ = 0` there is nothing to prove.
* Otherwise fix `t > 0`. Let `Pᵢ = P_{θᵢ}[uᵢ]_𝓘` (positive mass `vol Tᵢ`). Demailly's
  quasi-equisingular approximation (TN `exists_quasiEquisingularApproximation_ofType_pos`) gives
  potentials `Uᵢᵏ` with *global* analytic singularities of type `(2^{-k}, 𝓘(2^k Pᵢ))`; by
  `cor:quasi-equichar` (`sourceQuasiEquisingular_enlarged_tendsto`) a tail of them converges in
  `d_S` of the enlarged class `θᵢ + tω` to `P_{θᵢ}[Pᵢ]_𝓘`.
* Potentials with analytic singularities and positive mass are `𝓘`-good (TN
  `iGoodWith_of_analytic_type_of_positive_mass`), hence `P`-equivalent to their `𝓘`-envelopes;
  so their (mixed) volumes are their (mixed) non-pluripolar masses, and the analytic case of
  `thm:logconc` gives `∏ᵢ vol(Uᵢᵏ)^{1/n} ≤ vol(U₁ᵏ, …, Uₙᵏ)` in the backgrounds `θᵢ + tω`.
* By `thm:mvolcont` (`tendsto_sourceGeneralMixedIVolume_of_sourceSingularityTopology`, used also
  for the diagonal tuples) both sides converge; the limits only depend on the `𝓘`-classes, so
  `∏ᵢ vol_{θᵢ+tω}(uᵢ)^{1/n} ≤ vol(T₁ + tω, …, Tₙ + tω)`.
* `vol_{θᵢ}(uᵢ) ≤ vol_{θᵢ+tω}(uᵢ)` (`sourceIVolume_le_of_semipositive_difference`), and
  `vol(T₁ + tω, …) → vol(T₁, …, Tₙ)` as `t → 0+` (`sourceGeneralMixedIVolume_tendsto`).

## Main declarations

* `SGPT.IGood.LogVolume.prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume`: `prop:logvol`
  for potentials, `∏ᵢ (vol θᵢ,uᵢ)^{1/n} ≤ vol(θ₁ + ddᶜu₁, …, θₙ + ddᶜuₙ)`, dimension `n = q + 1`;
  `prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume_of_dim` in every dimension (in dimension
  `0` both sides are `1`, `sourceGeneralMixedIVolume_eq_one_of_dim_zero`).
* `SGPT.IGood.LogVolume.prod_sourceCurrentIVolume_rpow_le_sourceCurrentMixedIVolume`:
  `prop:logvol` for arbitrary closed positive `(1,1)`-currents.
* `SGPT.IGood.LogVolume.sourceGeneralMixedIVolume_eq_mass_of_iGoodWith`,
  `SGPT.IGood.LogVolume.sourceIVolume_eq_mass_of_iGoodWith`: for `𝓘`-good potentials the (mixed)
  volumes are the (mixed) non-pluripolar masses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.IGood.LogVolume

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

/-! ### `𝓘`-good potentials: volumes are masses -/

section Good

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- An `𝓘`-good potential (in a given background) is `P`-equivalent to its `𝓘`-envelope. -/
theorem sourcePEquivalent_sourceIEnvelope_of_iGoodWith (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hg : sourceIGoodWith θ u hu) :
    SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) u (sourceIEnvelope θ u) := by
  rw [← hg.2, sourceSingularityEnvelope_eq_native]
  exact SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ω
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- For an `𝓘`-good potential the volume is the non-pluripolar mass. -/
theorem sourceIVolume_eq_mass_of_iGoodWith (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hg : sourceIGoodWith θ u hu) :
    sourceIVolume θ u hu = sourcePotentialNonPluripolarMeasure θ u hu univ := by
  have hE := isThetaPSH_sourceIEnvelope hu
  have h := sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω
    (θ := fun _ : Fin n => θ) (u := fun _ => u) (v := fun _ => sourceIEnvelope θ u)
    (fun _ => hu) (fun _ => hE) (fun _ => sourcePEquivalent_sourceIEnvelope_of_iGoodWith ω hu hg)
  rw [sourceMixedNonPluripolarMass_diagonal, sourceMixedNonPluripolarMass_diagonal] at h
  exact h.symm

/-- For `𝓘`-good potentials the general mixed volume is the mixed non-pluripolar mass. -/
theorem sourceGeneralMixedIVolume_eq_mass_of_iGoodWith (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hg : ∀ i, sourceIGoodWith (θ i) (u i) (hu i)) :
    sourceGeneralMixedIVolume ω θ u hu = sourceMixedNonPluripolarMass θ u hu := by
  have hpos : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i) := fun i => by
    rw [sourceIVolume_eq_mass_of_iGoodWith ω (hu i) (hg i)]
    exact (hg i).1
  rw [sourceGeneralMixedIVolume_eq_positive ω θ u hu hpos]
  exact (sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω hu
    (fun i => isThetaPSH_sourceIEnvelope (hu i))
    (fun i => sourcePEquivalent_sourceIEnvelope_of_iGoodWith ω (hu i) (hg i))).symm

/-- Volumes are finite. -/
theorem sourceIVolume_lt_top' (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : sourceIVolume θ u hu < ⊤ := by
  rw [← sourceGeneralMixedIVolume_diagonal ω hu]
  exact sourceGeneralMixedIVolume_lt_top ω _ _ _

/-- A potential with analytic singularities and positive mass is `𝓘`-good. -/
theorem sourceIGoodWith_of_analytic (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hA : HasManifoldAnalyticSingularityType (n := n) u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceIGoodWith θ u hu := by
  apply (sourceIGoodWith_iff_native θ u hu).mpr
  exact AnalyticPotentialsIGood.iGoodWith_of_analytic_type_of_positive_mass ω
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hA hpos

end Good

/-! ### The analytic case in terms of volumes -/

section Analytic

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **Log-concavity of mixed volumes for analytic singularities.** For potentials with (global)
analytic singularities and positive masses,
`∏ᵢ (vol θᵢ,Wᵢ)^{1/n} ≤ vol(θ₁ + ddᶜW₁, …, θₙ + ddᶜWₙ)`. -/
theorem prod_sourceIVolume_rpow_le_of_analytic (ω : KahlerBackground (q + 1) M)
    (Γ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (W : Fin (q + 1) → M → EReal) (hW : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (Γ i) (W i))
    (han : ∀ i, HasAnalyticSingularities (n := q + 1) (W i))
    (hA : ∀ i, HasManifoldAnalyticSingularityType (n := q + 1) (W i))
    (hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure (Γ i) (W i) (hW i) univ) :
    ∏ i, (sourceIVolume (Γ i) (W i) (hW i)).toReal ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceGeneralMixedIVolume ω Γ W hW).toReal := by
  have hg : ∀ i, sourceIGoodWith (Γ i) (W i) (hW i) := fun i =>
    sourceIGoodWith_of_analytic ω (hW i) (hA i) (hpos i)
  rw [sourceGeneralMixedIVolume_eq_mass_of_iGoodWith ω Γ W hW hg]
  have h := SGPT.NPP.LogConcavity.prod_sourceMass_rpow_le_sourceMixedMass_of_analytic ω Γ W hW han
  refine le_of_eq_of_le ?_ h
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sourceIVolume_eq_mass_of_iGoodWith ω (hW i) (hg i), sourceMixedNonPluripolarMass_diagonal]

end Analytic

/-! ### Approximation in a fixed Kähler enlargement -/

section Enlarged

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem enlargedPSH (ω : KahlerBackground (q + 1) M) {θ : ClosedRealOneOneForm (q + 1) M}
    {v : M → EReal} (hv : IsThetaPshPotential θ.val v) {t : ℝ} (ht : 0 ≤ t) :
    (ofFixedModel (q + 1) M).IsThetaPSH (nativeClosedFormToAtlas (θ + t • ω.form)) v := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive hv
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem enlargedPSH' {θ : ClosedRealOneOneForm (q + 1) M} {v : M → EReal}
    (hv : IsThetaPshPotential θ.val v) :
    (ofFixedModel (q + 1) M).IsThetaPSH (nativeClosedFormToAtlas θ) v := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact hv

/-- **The key step.** If all volumes `vol θᵢ,uᵢ` are positive, then for every `t > 0`,
`∏ᵢ (vol θᵢ,uᵢ)^{1/n} ≤ vol(θ₁ + tω + ddᶜu₁, …, θₙ + tω + ddᶜuₙ)`. -/
theorem prod_sourceIVolume_rpow_le_kahlerPerturbation (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i))
    (hvol : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i)) {t : NNReal} (ht : 0 < (t : ℝ)) :
    ∏ i, (sourceIVolume (θ i) (u i) (hu i)).toReal ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedIVolumeKahlerPerturbation ω θ u hu t).toReal := by
  classical
  -- the `𝓘`-envelopes, in native form
  set θn : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M := fun i => atlasClosedFormToNative (θ i)
    with hθn
  set P : Fin (q + 1) → M → EReal := fun i => sourceIEnvelope (θ i) (u i) with hPdef
  have hP : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (P i) := fun i =>
    isThetaPSH_sourceIEnvelope (hu i)
  have hPn : ∀ i, IsThetaPshPotential (θn i).val (P i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (θ i) (P i)).mp (hP i)
  have hPpos : ∀ i, DiagonalMass.HasPositivePotentialMass (θn i) (P i) (hPn i) := by
    intro i
    have h := hvol i
    simpa only [sourceIVolume, sourcePotentialNonPluripolarMeasure,
      DiagonalMass.HasPositivePotentialMass, DiagonalMass.diagonalPotentialMass] using h
  -- Demailly's quasi-equisingular approximations, with global analytic type
  choose ε U hqea hεpos htype using fun i =>
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType_pos
      (Nat.succ_pos q) ω (θn i) (hPn i)
  -- convergence in the enlarged classes `θᵢ + tω`
  have hconv := fun i => sourceQuasiEquisingular_enlarged_tendsto ω ω (θn i) (P i) (ε i) (U i)
    (hPn i) (hPpos i) (hqea i).error (hqea i).term
    (SGPT.PSH.sourceQuasiEquisingularApproximation_of_native (hqea i)) (t : ℝ) ht
  choose N hU hE hlim using hconv
  set Γ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M) := fun i =>
    nativeClosedFormToAtlas (θn i + (t : ℝ) • ω.form) with hΓ
  have hbig : ∀ i, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (Γ i))) :=
    fun i => by
      simp only [hΓ, sourceNativeAtlasForm_roundTrip]
      exact PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential ω (θn i)
        ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) ht
  let ui : ℕ → (i : Fin (q + 1)) → SourceThetaPotentialL1 (Γ i) := fun j i =>
    ⟨U i (j + N i), enlargedPSH' (hU i j)⟩
  let L : (i : Fin (q + 1)) → SourceThetaPotentialL1 (Γ i) := fun i =>
    ⟨sourceIEnvelope (nativeClosedFormToAtlas (θn i)) (P i), enlargedPSH' (hE i)⟩
  have hlim' : ∀ i, Tendsto (fun j => ui j i) atTop
      (@nhds (SourceThetaPotentialL1 (Γ i)) (sourceSingularityTopology ω (Γ i) (hbig i)) (L i)) :=
    fun i => hlim i
  -- the approximants have positive masses in the enlarged backgrounds
  have hPΓ : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (Γ i) (P i) := fun i =>
    enlargedPSH ω (hPn i) ht.le
  have hPΓpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure (Γ i) (P i) (hPΓ i) univ := by
    intro i
    have h := SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
      (hPn i) ht
    simpa only [DiagonalMass.HasPositivePotentialMass, DiagonalMass.diagonalPotentialMass,
      sourcePotentialNonPluripolarMeasure, hΓ, sourceNativeAtlasForm_roundTrip] using h
  have hupos : ∀ j i, 0 < sourcePotentialNonPluripolarMeasure (Γ i) (ui j i).val
      (ui j i).property univ := by
    intro j i
    have hle : ∀ x, P i x ≤ U i (j + N i) x := fun x =>
      Antitone.le_of_tendsto ((hqea i).term_antitone x) ((hqea i).term_tendsto x) (j + N i)
    exact (hPΓpos i).trans_le (sourcePotentialNonPluripolarMass_mono ω (hPΓ i) (ui j i).property
      (MoreSingularOn.of_le fun x _ => hle x))
  -- the inequality for the analytic approximants
  have hk : ∀ j, ∏ i, (sourceIVolume (Γ i) (ui j i).val (ui j i).property).toReal ^
      (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceGeneralMixedIVolume ω Γ (fun i => (ui j i).val) (fun i => (ui j i).property)).toReal :=
    fun j => prod_sourceIVolume_rpow_le_of_analytic ω Γ (fun i => (ui j i).val)
      (fun i => (ui j i).property) (fun i => ⟨_, _, htype i (j + N i)⟩)
      (fun i => (hqea i).term_hasAnalyticSingularityType (j + N i)) (hupos j)
  -- passage to the limit
  have hmix := tendsto_sourceGeneralMixedIVolume_of_sourceSingularityTopology ω Γ hbig atTop ui L
    hlim'
  have hdiag : ∀ i, Tendsto (fun j => sourceIVolume (Γ i) (ui j i).val (ui j i).property) atTop
      (𝓝 (sourceIVolume (Γ i) (L i).val (L i).property)) := fun i =>
    (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology_all_mass ω (Γ i) (hbig i) atTop
      (fun j => ui j i) (L i) (hlim' i)).1
  have hR := (ENNReal.tendsto_toReal (sourceGeneralMixedIVolume_lt_top ω Γ _ _).ne).comp hmix
  have hL : Tendsto (fun j => ∏ i, (sourceIVolume (Γ i) (ui j i).val (ui j i).property).toReal ^
      (((q + 1 : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 (∏ i, (sourceIVolume (Γ i) (L i).val (L i).property).toReal ^
        (((q + 1 : ℕ) : ℝ)⁻¹))) := by
    apply tendsto_finsetProd
    intro i _
    exact ((ENNReal.tendsto_toReal (sourceIVolume_lt_top' ω _).ne).comp
      (hdiag i)).rpow_const (Or.inr (by positivity))
  have hlimit := le_of_tendsto_of_tendsto' hL hR hk
  -- the limits only depend on the `𝓘`-classes
  have huΓ : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (Γ i) (u i) := fun i =>
    enlargedPSH ω ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) ht.le
  have hIeq : ∀ i, sourceIEquivalent (ofFixedModel (q + 1) M) (u i) (L i).val := fun i =>
    sourceIEquivalent_trans (sourceIEquivalent_iEnvelope (hu i))
      (sourceIEquivalent_iEnvelope (enlargedPSH' (hPn i)))
  have hvolL : ∀ i, sourceIVolume (Γ i) (L i).val (L i).property =
      sourceIVolume (Γ i) (u i) (huΓ i) := by
    intro i
    rw [← sourceGeneralMixedIVolume_diagonal ω (L i).property,
      ← sourceGeneralMixedIVolume_diagonal ω (huΓ i)]
    exact le_antisymm
      (sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω _ _ _ _ _ _
        (fun _ => rfl) (fun _ => (hIeq i).2))
      (sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω _ _ _ _ _ _
        (fun _ => rfl) (fun _ => (hIeq i).1))
  have hmixL : sourceGeneralMixedIVolume ω Γ (fun i => (L i).val) (fun i => (L i).property) =
      sourceMixedIVolumeKahlerPerturbation ω θ u hu t := by
    have hpert : ∀ i, 0 < sourceIVolume (Γ i) (u i) (huΓ i) := fun i =>
      sourceIVolume_add_kahler_pos ω (hu i) (ε := t) ht
    calc sourceGeneralMixedIVolume ω Γ (fun i => (L i).val) (fun i => (L i).property)
        = sourceGeneralMixedIVolume ω Γ u huΓ :=
          le_antisymm
            (sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω _ _ _ _ _ _
              (fun _ => rfl) (fun i => (hIeq i).2))
            (sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω _ _ _ _ _ _
              (fun _ => rfl) (fun i => (hIeq i).1))
      _ = sourceEnvelopeMixedIVolume Γ u huΓ := sourceGeneralMixedIVolume_eq_positive ω Γ u huΓ hpert
      _ = sourceMixedIVolumeKahlerPerturbation ω θ u hu t := rfl
  rw [← hmixL]
  refine le_trans (Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_) hlimit
  rw [hvolL i]
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (by positivity)
  apply ENNReal.toReal_mono (sourceIVolume_lt_top' ω _).ne
  have hdiff : (atlasClosedFormToNative (Γ i) - atlasClosedFormToNative (θ i)).val.IsSemipositive := by
    simp only [hΓ, sourceNativeAtlasForm_roundTrip, hθn, add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive ht.le
  exact sourceIVolume_le_of_semipositive_difference hdiff ω (hu i)

end Enlarged

/-! ### The general case -/

section Main

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`prop:logvol`, potential form.** On a compact connected Kähler manifold of dimension
`n = q + 1`, for smooth closed real `(1,1)`-forms `θᵢ` and `θᵢ`-psh functions `uᵢ`,
`∏ᵢ (vol (θᵢ + ddᶜuᵢ))^{1/n} ≤ vol(θ₁ + ddᶜu₁, …, θₙ + ddᶜuₙ)`,
with the volumes of `def:volqpsh` (`sourceIVolume`) and the general mixed volume of
`def:mix_vol` (`sourceGeneralMixedIVolume`); all quantities are finite and read as reals.
No positivity of any volume or mass is assumed. -/
theorem prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i)) :
    ∏ i, (sourceIVolume (θ i) (u i) (hu i)).toReal ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceGeneralMixedIVolume ω θ u hu).toReal := by
  by_cases hvol : ∀ i, 0 < sourceIVolume (θ i) (u i) (hu i)
  · have htend := sourceGeneralMixedIVolume_tendsto ω θ u hu
    have hR := (ENNReal.tendsto_toReal (sourceGeneralMixedIVolume_lt_top ω θ u hu).ne).comp htend
    refine ge_of_tendsto hR ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact prod_sourceIVolume_rpow_le_kahlerPerturbation ω θ u hu hvol (by exact_mod_cast ht)
  · push Not at hvol
    obtain ⟨i, hi⟩ := hvol
    have h0 : sourceIVolume (θ i) (u i) (hu i) = 0 := le_antisymm hi (zero_le)
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [h0, ENNReal.toReal_zero, Real.zero_rpow (by positivity)])]
    exact ENNReal.toReal_nonneg

open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction in
/-- **`prop:logvol`, current form.** For closed positive `(1,1)`-currents `T₁, …, Tₙ` on a compact
connected Kähler manifold of dimension `n = q + 1`,
`∏ᵢ (vol Tᵢ)^{1/n} ≤ vol(T₁, …, Tₙ)`,
where `vol(T₁, …, Tₙ)` is the mixed volume of currents (`sourceCurrentMixedIVolume`, independent of
the representations `Tᵢ = θᵢ + ddᶜuᵢ`) and `vol Tᵢ = vol(Tᵢ, …, Tᵢ)` (`prop:vollinearlimit` (6):
it is the volume `sourceIVolume` of every representation of `Tᵢ`,
`sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation`). -/
theorem prod_sourceCurrentIVolume_rpow_le_sourceCurrentMixedIVolume
    (ω : KahlerBackground (q + 1) M)
    (T : Fin (q + 1) → GlobalCurrent (q + 1) M (degreeTwo (Nat.succ_pos q)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (q + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (q + 1)) (Nat.succ_pos q))
    (hp : ∀ i, IsFullPositive (T i)) :
    ∏ i, (sourceCurrentMixedIVolume ω (fun _ => T i) (fun _ => hc i) (fun _ => h11 i)
        (fun _ => hp i)).toReal ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceCurrentMixedIVolume ω T hc h11 hp).toReal := by
  choose θ u hu hread _ using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  rw [sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  simp_rw [fun i => sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation ω (T i) (hc i)
    (h11 i) (hp i) (θ i) (u i) (hu i) (hread i)]
  exact prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume ω _ u _

end Main

/-! ### Dimension zero and the statement in every dimension -/

section AllDimensions

/-- In dimension `0` the mixed volume of the empty tuple is `1` (the manifold is a point). -/
theorem sourceGeneralMixedIVolume_eq_one_of_dim_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M] (ω : KahlerBackground 0 M)
    (θ : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : Fin 0 → M → EReal)
    (hu : ∀ i, (ofFixedModel 0 M).IsThetaPSH (θ i) (u i)) :
    sourceGeneralMixedIVolume ω θ u hu = 1 := by
  have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have : Unique M := uniqueOfSubsingleton x₀
  have h1 : ∀ ε : Ioi (0 : NNReal), sourceMixedIVolumeKahlerPerturbation ω θ u hu ε = 1 := by
    intro ε
    unfold sourceMixedIVolumeKahlerPerturbation
    rw [sourceEnvelopeMixedIVolume_eq_native]
    unfold MixedMass.globalMixedMass
    rw [(ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count _ _ _).2.1,
      Nat.card_unique, Nat.cast_one]
  unfold sourceGeneralMixedIVolume
  simp only [h1, ciInf_const]

/-- **`prop:logvol`, potential form, in every dimension** (including `n = 0`, where both sides
are `1`): `∏ᵢ (vol (θᵢ + ddᶜuᵢ))^{1/n} ≤ vol(θ₁ + ddᶜu₁, …, θₙ + ddᶜuₙ)`. -/
theorem prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume_of_dim {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    (ω : KahlerBackground n M) (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal) (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    ∏ i, (sourceIVolume (θ i) (u i) (hu i)).toReal ^ ((n : ℝ)⁻¹) ≤
      (sourceGeneralMixedIVolume ω θ u hu).toReal := by
  cases n with
  | zero =>
    rw [sourceGeneralMixedIVolume_eq_one_of_dim_zero ω θ u hu]
    simp
  | succ q => exact prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume ω θ u hu

end AllDimensions

end SGPT.IGood.LogVolume
