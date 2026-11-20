import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.IGoodBasic
import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra
import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Envelopes.SourceRelativeEnergyClosure

/-!
# The volume of the partial Okounkov body of a Kähler current

Source: the book's `prop:Okounkov:L1551` (chapter *The theory of Okounkov bodies*, section
*Transcendental partial Okounkov bodies*); blueprint chapter `claude-pob`, node
`claude-pob:volume-kahler`.

For a Kähler current `T = θ + dd^c φ`, `vol Δ_{Y•}(T) = (1/n!) vol T`, where `vol T` is the
volume of `def:volqpsh`, `∫_X ⟨(θ + dd^c P_θ[φ]_𝓘)^n⟩` (TN's `iVolume`; the project's
`SGPT.PSH.VariableComplexAtlas.sourceIVolume` is the same number,
`sourceIVolume_eq_native`).

The book's proof: for a quasi-equisingular approximation `(T_j)`, `Δ(T_j)` decreases to `Δ(T)`
(so the volumes converge), `vol Δ(T_j) = (1/n!) ∫ T_j^n` (`eq:volpobanaly`, i.e.
`lma:Okounkovanalycomp`, which rests on `thm:Okounkovtranmain` (1)), and
`∫ T_j^n → vol T` (`thm:contvolu` with `cor:quasi-equichar`). Here:

* `tendsto_diagonalPotentialMass_of_isKahlerQEA` (unconditional): `∫ T_j^n → vol T` for every
  Kähler approximation, from TN's identification of the native limit of a quasi-equisingular
  approximation with the `𝓘`-envelope (`iInf_envelopes_eq_iEnvelope_and_native_limit`) and the
  `d_S`-continuity of masses (`diagonalPotentialMass_uniformContinuous`);
* `volume_kahlerPartialBody`: the proposition, **conditional exactly on**
  `VolumeIdentityAllStatement m` (`thm:Okounkovtranmain` (1) in dimension `n = m + 1`), the input
  of `eq:volpobanaly` (`TranscendentalL2.volume_analyticPartialBody`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.PartialBody

open Set Filter MeasureTheory
open scoped Pointwise Topology Matrix ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial

/-- The carrier of a flag geometry is nonempty (it contains the point `Y_n` of the flag). -/
theorem nonempty_carrier {n : ℕ} (F : OriginalFlagGeometry.{u} n) : Nonempty F.carrier :=
  ⟨(F.smooth.2.2 0).2.1.nonempty.some⟩

/-! ### Masses of quasi-equisingular approximations -/

section Mass

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X] [Nonempty X]

omit [ConnectedSpace X] in
/-- A Kähler current has positive non-pluripolar mass. -/
theorem diagonalPotentialMass_pos_of_isKahlerCurrentPotential
    {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hφθ : IsThetaPshPotential θ.val φ) : 0 < diagonalPotentialMass θ φ hφθ := by
  obtain ⟨κ, hκ⟩ := hφ
  exact RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul κ one_pos
    (by rwa [one_smul]) hφθ

/-- The class of a Kähler current is big. -/
theorem isBigClass_of_isKahlerCurrentPotential {θ : ClosedRealOneOneForm (m + 1) X}
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative θ) := by
  have hφθ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hpos := diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hφθ
  obtain ⟨κ, -⟩ := hφ
  have hvol := hpos.trans_le
    (TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume κ θ hφθ)
  exact (TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass κ _).mp hvol

/-- **`∫ T_j^n → vol T`** (`thm:contvolu` with `cor:quasi-equichar`, for the approximations of
`def:POBKahcurr`): for a Kähler current `T = θ + dd^c φ` and a quasi-equisingular approximation
`(T_j)` in `𝒵₊(X, α)` by Kähler currents with analytic singularities,
`∫_X ⟨T_j^n⟩ → vol T = ∫_X ⟨(θ + dd^c P_θ[φ]_𝓘)^n⟩`. -/
theorem tendsto_diagonalPotentialMass_of_isKahlerQEA {θ : ClosedRealOneOneForm (m + 1) X}
    {φ : X → EReal} {U : ℕ → X → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    (hU : IsKahlerQEA θ φ U) :
    Tendsto (fun j => diagonalPotentialMass θ (U j) (hU.2 j).1.1) atTop
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ
        (isThetaPshPotential_of_isKahlerCurrentPotential hφ))) := by
  have hφθ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hpos := diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hφθ
  have hbig := isBigClass_of_isKahlerCurrentPotential hφ
  obtain ⟨ω, ε, hnat⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  obtain ⟨-, hI, -, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit ω θ hbig
      hnat (fun j => (hU.2 j).1.1) hpos
  let _ := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω θ hbig
  let _ : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 θ.val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω θ
      hbig).toUniformSpace.toTopologicalSpace
  have hcont := ((SingularCanonicalSingularityMassLipschitz.diagonalPotentialMass_uniformContinuous
    ω θ hbig).continuous.tendsto _).comp hlim
  have hfin : ∀ j, diagonalPotentialMass θ (U j) (hU.2 j).1.1 ≠ ⊤ := fun j =>
    (MixedMass.globalMixedMass_lt_top ω (fun _ : Fin (m + 1) => (hU.2 j).1.1.1)).ne
  have hfin' : iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top ω (fun _ : Fin (m + 1) => hI.1)).ne
  rw [← ENNReal.tendsto_toReal_iff hfin hfin']
  exact hcont

end Mass

/-! ### `prop:Okounkov:L1551` -/

section Body

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **`prop:Okounkov:L1551`** (`eq:volOkocur`), **conditional** on the volume identity
`VolumeIdentityAllStatement m` (`thm:Okounkovtranmain` (1) in dimension `n = m + 1`, the input
of `eq:volpobanaly`): for a Kähler current `T = θ + dd^c φ`,
`vol Δ_{Y•}(T) = (1/n!) vol T` (Lebesgue measure on `ℝⁿ`; `vol T` the volume of
`def:volqpsh`, for the Borel structure of `X`). -/
theorem volume_kahlerPartialBody (hA : VolumeIdentityAllStatement.{u} m)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    haveI : Nonempty F.carrier := nonempty_carrier F
    volume (kahlerPartialBody F θ φ) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ
        (isThetaPshPotential_of_isKahlerCurrentPotential hφ) / ((m + 1).factorial : ℝ≥0∞) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := nonempty_carrier F
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU]
  have hanti : Antitone (fun j => partialOkounkovBody F θ (U j)) := fun i j hij =>
    partialOkounkovBody_mono θ (singularityLE_succ_of_sourceQuasiEquisingularApproximation hU.1 hij)
  have hmeas : ∀ j, NullMeasurableSet (partialOkounkovBody F θ (U j)) volume := fun j =>
    (isClosed_partialOkounkovBody θ _).measurableSet.nullMeasurableSet
  have hfin : ∃ j, volume (partialOkounkovBody F θ (U j)) ≠ ⊤ :=
    ⟨0, (isCompact_partialOkounkovBody θ _).measure_lt_top.ne⟩
  have h1 := tendsto_measure_iInter_atTop hmeas hanti hfin
  have hfact : ((m + 1).factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have h2 : Tendsto (fun j => volume (partialOkounkovBody F θ (U j))) atTop
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ
        (isThetaPshPotential_of_isKahlerCurrentPotential hφ) / ((m + 1).factorial : ℝ≥0∞))) := by
    refine (ENNReal.Tendsto.div_const (tendsto_diagonalPotentialMass_of_isKahlerQEA hφ hU)
      (Or.inr hfact)).congr fun j => ?_
    rw [← TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody (hU.2 j).1 (hU.2 j).2]
    exact (TranscendentalL2.volume_analyticPartialBody hA (hU.2 j).1 (hU.2 j).2).symm
  exact tendsto_nhds_unique h1 h2

/-! ### `thm:pobmain` (1) -/

/-- The I-volume only depends on the form, not on the proof witnesses. -/
theorem iVolume_congr {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] {θ₁ θ₂ : ClosedRealOneOneForm (m + 1) X} (h : θ₁ = θ₂)
    (h₁ : HasSmoothLocalPotentials θ₁.val) (h₂ : HasSmoothLocalPotentials θ₂.val)
    (φ : X → EReal) (p₁ : IsThetaPshPotential θ₁.val φ) (p₂ : IsThetaPshPotential θ₂.val φ) :
    iVolume θ₁ h₁ φ p₁ = iVolume θ₂ h₂ φ p₂ := by
  subst h
  rfl

/-- **`vol(T + t ω) → vol T` as `t → 0+`** (the book's `def:mix_vol` with `prop:vollinearlimit`
(6): `vol T = vol(T, …, T) = lim_{t → 0+} vol(T + t ω)`), for every `T = θ + dd^c φ`. -/
theorem tendsto_iVolume_add_smul {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
    [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (ω : KahlerBackground (m + 1) X) {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    Tendsto (fun t : NNReal => iVolume (θ + (t : ℝ) • ω.form)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
          (KahlerDomination.isSemipositive_smul ω.isSemipositive t.property)))
      (𝓝[>] (0 : NNReal))
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ)) := by
  open SGPT.PSH.VariableComplexAtlas in
  set θa := nativeClosedFormToAtlas θ with hθa
  have hu : (ofFixedModel (m + 1) X).IsThetaPSH θa φ :=
    (isThetaPSH_iff_nativeThetaPotential θa φ).mpr (by rw [sourceNativeAtlasForm_roundTrip]; exact hφ)
  have h1 := sourceGeneralMixedIVolume_tendsto ω (fun _ : Fin (m + 1) => θa) (fun _ => φ)
    (fun _ => hu)
  rw [sourceGeneralMixedIVolume_diagonal ω hu,
    sourceIVolume_eq_native θa φ hu (LocalPotentials.closedRealOneOne_hasLocalPotentials _)] at h1
  rw [iVolume_congr (sourceNativeAtlasForm_roundTrip θ).symm _
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ
    ((isThetaPSH_iff_nativeThetaPotential θa φ).mp hu)]
  refine h1.congr fun t => ?_
  show sourceEnvelopeMixedIVolume _ _ _ = _
  rw [sourceEnvelopeMixedIVolume_diagonal, sourceIVolume_eq_native _ _ _
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _)]
  · refine iVolume_congr ?_ _ _ φ _ _
    rw [sourceNativeAtlasForm_roundTrip, sourceNativeAtlasForm_roundTrip]
  · refine (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_
    rw [sourceNativeAtlasForm_roundTrip]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
      (KahlerDomination.isSemipositive_smul ω.isSemipositive t.property)

/-- **`thm:pobmain` (1)** (`eq:volpobgeneral`), **conditional** on the volume identity
`VolumeIdentityAllStatement m` (`thm:Okounkovtranmain` (1) in dimension `n = m + 1`): for
`T = θ + dd^c φ ∈ 𝒵₊(X, α)`, `vol Δ_{Y•}(T) = (1/n!) vol T` (`vol T` of `def:volqpsh`). The book
states it for `T ∈ 𝒵₊(X, α)_{>0}`; the proof (`eq:volOkocur` for `T + j⁻¹ ω` and
`prop:vollinearlimit`) needs no positivity. -/
theorem volume_generalPartialBody (hA : VolumeIdentityAllStatement.{u} m)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    haveI : Nonempty F.carrier := nonempty_carrier F
    volume (generalPartialBody F θ φ) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ /
        ((m + 1).factorial : ℝ≥0∞) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := nonempty_carrier F
  have ht0 : ∀ j : ℕ, (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := fun j => by positivity
  have hK : ∀ j : ℕ, IsKahlerCurrentPotential (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ := fun j =>
    isKahlerCurrentPotential_add_smul hφ F.omega (ht0 j)
  have hanti : Antitone (fun j : ℕ => kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ) :=
    fun i j hij => kahlerPartialBody_add_smul_mono hφ F.omega (ht0 j)
      (inv_anti₀ (by positivity) (by gcongr))
  have hmeas : ∀ j : ℕ, NullMeasurableSet
      (kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ) volume := fun j =>
    (isClosed_kahlerPartialBody _ φ).measurableSet.nullMeasurableSet
  have hfin : ∃ j : ℕ, volume (kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ) ≠ ⊤ :=
    ⟨0, (kahlerPartialBody_convexBody (hK 0)).2.1.measure_lt_top.ne⟩
  have h1 := tendsto_measure_iInter_atTop hmeas hanti hfin
  have hfact : ((m + 1).factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  -- `t_j = (j + 1)⁻¹ → 0+` in `ℝ≥0`
  have htj : Tendsto (fun j : ℕ => (((j : NNReal) + 1)⁻¹ : NNReal)) atTop (𝓝[>] (0 : NNReal)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal)
      simpa only [one_div] using h
    · show (0 : NNReal) < ((j : NNReal) + 1)⁻¹
      positivity
  have hvol := ((tendsto_iVolume_add_smul F.omega hφ).comp htj)
  have h2 : Tendsto (fun j : ℕ => volume
      (kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ)) atTop
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ /
        ((m + 1).factorial : ℝ≥0∞))) := by
    refine (ENNReal.Tendsto.div_const hvol (Or.inr hfact)).congr fun j => ?_
    rw [volume_kahlerPartialBody hA (hK j)]
    congr 1
  rw [generalPartialBody]
  exact tendsto_nhds_unique h1 h2

end Body

end SGPT.Okounkov.PartialBody
