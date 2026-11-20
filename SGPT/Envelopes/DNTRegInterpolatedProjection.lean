import SGPT.Envelopes.SourceInterpolatedEnvelopeGenuine

/-!
# The interpolating envelopes `P_{θ,0}` and `P_{θ,n}` are projections

Source `rmk:envelopes:L2443` (`author/chapter_envelopes.tex`, lines 2445–2455)
defines, for `φ ∈ PSH(X,θ)_{>0}` and `j ∈ {0, …, n}`,
`P_{θ,j}[φ] = usc sup {ψ ∈ PSH(X,θ) : ψ ≤ 0, φ ⪯ ψ,
  ∫ θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j} = ∫ θ_ψ^j ∧ θ_{P_θ[ψ]_I}^{n-j}}`
(`sourceInterpolatedEnvelope`), says that `j = 0` and `j = n` recover the `I`- and the
`P`-envelope (`sourceInterpolatedEnvelope_zero`, `sourceInterpolatedEnvelope_last`), and asserts
that every `P_{θ,j}` is a projection operator (`SourceInterpolatedEnvelopeProjection`).

This file proves the projection property at the two endpoints:

* `sourceInterpolatedEnvelopeProjection_last`: `P_{θ,n}` is a projection on `PSH(X,θ)_{>0}`
  (from `P_θ[P_θ[φ]] = P_θ[φ]`, source `thm:Pvarphidiffdef`);
* `sourceInterpolatedEnvelopeProjection_zero`: `P_{θ,0}` is a projection on `PSH(X,θ)_{>0}`
  (from `P_θ[P_θ[φ]_I]_I = P_θ[φ]_I`);
* `sourceInterpolatedEnvelopeProjection_of_le_one`: hence, in dimension `n ≤ 1`, where
  `{0, …, n} = {0, n}`, every `P_{θ,j}` is a projection, i.e. the remark's projection claim holds
  in full.

Moreover, on `I`-good inputs (`def:Igoodpot`: `P_θ[φ] = P_θ[φ]_I`) every interpolating envelope
is the `P`-envelope and is idempotent:

* `sourceInterpolatedMass_eq_mass_of_iGood`: for `I`-good `φ`,
  `∫ θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j} = ∫ θ_φ^n`;
* `sourceInterpolatedEnvelope_eq_of_iGood`: for `I`-good `φ`, `P_{θ,j}[φ] = P_θ[φ]` for every `j`;
* `sourceInterpolatedEnvelope_projection_of_iGood`: for `I`-good `φ`,
  `P_{θ,j}[P_{θ,j}[φ]] = P_{θ,j}[φ]` for every `j`.

The projection property of the intermediate operators `0 < j < n` (possible only for `n ≥ 2`)
on inputs that are not `I`-good is not treated here.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Source `rmk:envelopes:L2443`, projection property for `j = n`: `P_{θ,n}` is a projection
operator on `PSH(X,θ)_{>0}`. -/
theorem sourceInterpolatedEnvelopeProjection_last (ω : KahlerBackground n M) :
    SourceInterpolatedEnvelopeProjection θ (Fin.last n) := by
  intro u hu hpos
  refine ⟨isThetaPSH_sourceInterpolatedEnvelope ω _ hu,
    sourceInterpolatedEnvelope_positive ω _ hu hpos, ?_⟩
  have h1 := sourceInterpolatedEnvelope_last ω hu hpos
  have key : ∀ (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH θ v),
      v = sourceSingularityEnvelope θ u →
        sourceInterpolatedEnvelope θ (Fin.last n) v hv = sourceSingularityEnvelope θ u := by
    intro v hv hveq
    subst hveq
    have hposP : 0 < sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u) hv
        univ :=
      lt_of_lt_of_eq hpos (sourceOrdinaryEnvelope_diagonalMass_eq ω hu).symm
    rw [sourceInterpolatedEnvelope_last ω hv hposP, sourceOrdinaryEnvelope_projection ω hu hpos]
  rw [key _ _ h1, h1]

/-- Source `rmk:envelopes:L2443`, projection property for `j = 0`: `P_{θ,0}` is a projection
operator on `PSH(X,θ)_{>0}`. -/
theorem sourceInterpolatedEnvelopeProjection_zero (ω : KahlerBackground n M) :
    SourceInterpolatedEnvelopeProjection θ ⟨0, Nat.zero_lt_succ n⟩ := by
  intro u hu hpos
  refine ⟨isThetaPSH_sourceInterpolatedEnvelope ω _ hu,
    sourceInterpolatedEnvelope_positive ω _ hu hpos, ?_⟩
  have h1 := sourceInterpolatedEnvelope_zero ω hu hpos
  have key : ∀ (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH θ v),
      v = sourceIEnvelope θ u →
        sourceInterpolatedEnvelope θ ⟨0, Nat.zero_lt_succ n⟩ v hv = sourceIEnvelope θ u := by
    intro v hv hveq
    subst hveq
    have hposI : 0 < sourcePotentialNonPluripolarMeasure θ (sourceIEnvelope θ u) hv univ :=
      lt_of_lt_of_le hpos (sourceMass_le_iVolume ω hu)
    rw [sourceInterpolatedEnvelope_zero ω hv hposI, sourceIEnvelope_idempotent hu]
  rw [key _ _ h1, h1]

/-- Source `rmk:envelopes:L2443` in dimension `n ≤ 1`: every interpolating envelope
`P_{θ,j}`, `j ∈ {0, …, n}`, is a projection operator on `PSH(X,θ)_{>0}`. -/
theorem sourceInterpolatedEnvelopeProjection_of_le_one (ω : KahlerBackground n M) (hn : n ≤ 1)
    (j : Fin (n + 1)) : SourceInterpolatedEnvelopeProjection θ j := by
  rcases j with ⟨j, hj⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact sourceInterpolatedEnvelopeProjection_zero ω
  · have hjn : (⟨j, hj⟩ : Fin (n + 1)) = Fin.last n := by
      ext
      simp only [Fin.val_last]
      omega
    rw [hjn]
    exact sourceInterpolatedEnvelopeProjection_last ω

/-! ### `I`-good inputs -/

/-- For an `I`-good `φ` the interpolated mass `∫ θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j}` is the
non-pluripolar mass `∫ θ_φ^n`. -/
theorem sourceInterpolatedMass_eq_mass_of_iGood (ω : KahlerBackground n M) (j : Fin (n + 1))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hgood : sourceIGoodWith θ u hu) :
    sourceInterpolatedMass θ j u hu = sourcePotentialNonPluripolarMeasure θ u hu univ := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hP := sourceOrdinaryEnvelope_genuine hu
  have hPn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hP
  have hIn := (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hu)
  have huP : SGPT.PSH.SingularityLE u (sourceSingularityEnvelope θ u) :=
    (sourceEnvelopeEqualMassCompetitor ω hu).2.2.2.1
  have hIP : sourceIEnvelope θ u = sourceSingularityEnvelope θ u := hgood.2.symm
  let U : Fin n → M → EReal := fun i => if i.val < j.val then u else sourceIEnvelope θ u
  have hU (i : Fin n) : IsThetaPshPotential (atlasClosedFormToNative θ).val (U i) := by
    dsimp only [U]
    split_ifs
    · exact hn
    · exact hIn
  apply le_antisymm
  · have h := GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential
      (θ := fun _ : Fin n => atlasClosedFormToNative θ) (u := U)
      (v := fun _ => sourceSingularityEnvelope θ u) ω hU (fun _ => hPn) (fun i => by
        dsimp only [U]
        split_ifs
        · exact huP
        · rw [hIP]
          exact MoreSingularOn.of_le fun x _ => le_rfl)
    calc sourceInterpolatedMass θ j u hu
        ≤ sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u) hP univ := h
      _ = sourcePotentialNonPluripolarMeasure θ u hu univ :=
          sourceOrdinaryEnvelope_diagonalMass_eq ω hu
  · exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential
      (θ := fun _ : Fin n => atlasClosedFormToNative θ) (u := fun _ => u) (v := U) ω
      (fun _ => hn) hU (fun i => by
        dsimp only [U]
        split_ifs
        · exact MoreSingularOn.of_le fun x _ => le_rfl
        · rw [hIP]
          exact huP)

/-- The non-pluripolar mass is at most the interpolated mass. -/
theorem sourceMass_le_interpolatedMass (ω : KahlerBackground n M) (j : Fin (n + 1))
    {v : M → EReal} (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    sourcePotentialNonPluripolarMeasure θ v hv univ ≤ sourceInterpolatedMass θ j v hv := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hIn := (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hv)
  have horder : MoreSingularOn v (sourceIEnvelope θ v) univ := by
    rw [sourceIEnvelope_eq_native θ v hv]
    exact moreSingularOn_iSingularityEnvelope hn
  let V : Fin n → M → EReal := fun i => if i.val < j.val then v else sourceIEnvelope θ v
  have hV (i : Fin n) : IsThetaPshPotential (atlasClosedFormToNative θ).val (V i) := by
    dsimp only [V]
    split_ifs
    · exact hn
    · exact hIn
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential
    (θ := fun _ : Fin n => atlasClosedFormToNative θ) (u := fun _ => v) (v := V) ω
    (fun _ => hn) hV (fun i => by
      dsimp only [V]
      split_ifs
      · exact MoreSingularOn.of_le fun x _ => le_rfl
      · exact horder)

/-- The `P`-envelope of an `I`-good potential is `I`-good. -/
theorem sourceIGoodWith_singularityEnvelope (ω : KahlerBackground n M) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hgood : sourceIGoodWith θ u hu) :
    sourceIGoodWith θ (sourceSingularityEnvelope θ u) (sourceOrdinaryEnvelope_genuine hu) := by
  refine ⟨lt_of_lt_of_eq hgood.1 (sourceOrdinaryEnvelope_diagonalMass_eq ω hu).symm, ?_⟩
  rw [sourceOrdinaryEnvelope_projection ω hu hgood.1, sourceIEnvelope_pEnvelope hu]
  exact hgood.2

/-- Source `rmk:envelopes:L2443` on `I`-good inputs: for an `I`-good `φ` (`def:Igoodpot`), every
interpolating envelope is the `P`-envelope, `P_{θ,j}[φ] = P_θ[φ]`. -/
theorem sourceInterpolatedEnvelope_eq_of_iGood (ω : KahlerBackground n M) (j : Fin (n + 1))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hgood : sourceIGoodWith θ u hu) :
    sourceInterpolatedEnvelope θ j u hu = sourceSingularityEnvelope θ u := by
  have hpos := hgood.1
  have hF := sourceInterpolatedMass_eq_mass_of_iGood ω j hu hgood
  have hP := sourceOrdinaryEnvelope_genuine hu
  have huP : SGPT.PSH.SingularityLE u (sourceSingularityEnvelope θ u) :=
    (sourceEnvelopeEqualMassCompetitor ω hu).2.2.2.1
  apply le_antisymm
  · refine uscRegularization_le (upperSemicontinuous_sourceSingularityEnvelope θ u)
      (fun x => iSup_le fun v => ?_)
    obtain ⟨hv, hv0, huv, hmass⟩ := v.2
    have h1 := sourceMass_le_interpolatedMass ω j hv
    have h2 := sourcePotentialNonPluripolarMass_mono ω hu hv huv
    have hm : sourcePotentialNonPluripolarMeasure θ u hu univ =
        sourcePotentialNonPluripolarMeasure θ v.1 hv univ := by
      refine le_antisymm h2 (h1.trans ?_)
      rw [← hmass, hF]
    exact le_sourceSingularityEnvelope_of_equalMass ω hu hpos ⟨v.1, hv, hv0, huv, hm⟩ x
  · intro x
    refine le_trans ?_ (le_uscRegularization _ x)
    have hgP := sourceIGoodWith_singularityEnvelope ω hu hgood
    refine le_iSup (fun v : sourceInterpolatedEnvelopeCompetitors θ j u hu => v.1 x)
      ⟨sourceSingularityEnvelope θ u, hP, sourceSingularityEnvelope_le_zero θ u, huP, ?_⟩
    rw [hF, sourceInterpolatedMass_eq_mass_of_iGood ω j hP hgP,
      sourceOrdinaryEnvelope_diagonalMass_eq ω hu]

/-- Source `rmk:envelopes:L2443` on `I`-good inputs: for an `I`-good `φ`, every interpolating
envelope `P_{θ,j}` satisfies `P_{θ,j}[P_{θ,j}[φ]] = P_{θ,j}[φ]`, and the output has positive
mass. -/
theorem sourceInterpolatedEnvelope_projection_of_iGood (ω : KahlerBackground n M)
    (j : Fin (n + 1)) {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hgood : sourceIGoodWith θ u hu) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ (sourceInterpolatedEnvelope θ j u hu),
      0 < sourcePotentialNonPluripolarMeasure θ _ hP univ ∧
      sourceInterpolatedEnvelope θ j (sourceInterpolatedEnvelope θ j u hu) hP =
        sourceInterpolatedEnvelope θ j u hu := by
  refine ⟨isThetaPSH_sourceInterpolatedEnvelope ω _ hu,
    sourceInterpolatedEnvelope_positive ω _ hu hgood.1, ?_⟩
  have h1 := sourceInterpolatedEnvelope_eq_of_iGood ω j hu hgood
  have key : ∀ (v : M → EReal) (hv : (ofFixedModel n M).IsThetaPSH θ v),
      v = sourceSingularityEnvelope θ u →
        sourceInterpolatedEnvelope θ j v hv = sourceSingularityEnvelope θ u := by
    intro v hv hveq
    subst hveq
    rw [sourceInterpolatedEnvelope_eq_of_iGood ω j hv
      (sourceIGoodWith_singularityEnvelope ω hu hgood),
      sourceOrdinaryEnvelope_projection ω hu hgood.1]
  rw [key _ _ h1, h1]

end SGPT.PSH.VariableComplexAtlas
