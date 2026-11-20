import SGPT.Okounkov.PartialBodyDSConvex
import SGPT.Okounkov.PartialBodyVolume
import SGPT.Okounkov.TranscendentalMainTheorem
import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion
import SGPT.Foundations.Analysis.Pending.IEnvelopeNativeContinuity
import Mathlib.Analysis.Convex.Body

/-!
# `d_S`-continuity of partial Okounkov bodies

Source: the book's `thm:pobmain` (4) (chapter *The theory of Okounkov bodies*, section
*Transcendental partial Okounkov bodies*, subsection *The general case*); blueprint chapter
`claude-pob-ds`.

For a big class `α = {θ}`, the map `𝒵₊(X, α)_{>0} → 𝒦ₙ`, `T ↦ Δ_{Y•}(T)`, is continuous for the
`d_S`-pseudometric on `𝒵₊(X, α)_{>0}` and the Hausdorff metric on `𝒦ₙ`. Currents
`T = θ + dd^c φ` are represented by their potentials `φ ∈ PSH(X, θ)` (`ThetaPshL1 θ.val`, the
carrier of the singularity pseudometric `singularityPseudoMetricSpace ω θ` of TN, the book's
`def:dS`, for any reference Kähler form `ω`), `Δ_{Y•}(T)` is `generalPartialBody F θ φ`
(`def:generalPOB`), positive mass is `0 < ∫_X ⟨θ_φ^n⟩` (`HasPositivePotentialMass`), and `𝒦ₙ`
is Mathlib's `ConvexBody (EuclideanSpace ℝ (Fin n))` with the Hausdorff distance.

The book's proof uses the volume identity (1) (`thm:pobmain` (1), S51's `volume_generalPartialBody`,
which rests on `thm:Okounkovtranmain` (1)); it is discharged by
`TranscendentalPartial.volumeIdentityAll`, so all results here are **unconditional**.

## Route (blueprint `claude-pob-ds:pobmain-4`)

The book reduces to monotone sequences by the sandwich `prop:incanddec` and concludes with the
Blaschke selection theorem. Here: for `φ_i → φ` in `d_S` with `∫ θ_φ^n > 0`, put
`ψ_i = max(φ_i, φ)`. Then

* `Δ(φ_i) ⊆ Δ(ψ_i)` and `Δ(φ) ⊆ Δ(ψ_i)` (`thm:pobmain` (2)), all inside `Δ(α)`;
* `ψ_i → φ` in `d_S` (`prop:lor_dS_conv`, TN `tendsto_native_iff_max_and_endpointMixedMass`);
* `vol Δ(φ_i) → vol Δ(φ)` and `vol Δ(ψ_i) → vol Δ(φ)`, by `thm:pobmain` (1) and the
  `d_S`-continuity of the volume `vol θ_φ = ∫ ⟨(θ + dd^c P_θ[φ]_𝓘)^n⟩` at positive mass
  (`thm:contvolu`: `tendsto_iVolume_of_tendsto`);
* `vol Δ(φ) = (1/n!) vol θ_φ ≥ (1/n!) ∫ θ_φ^n > 0`;

and the volume-gap lemma `tendsto_hausdorffDist_of_tendsto_measure` gives
`d_Haus(Δ(φ_i), Δ(φ)) → 0`.

## Main results

* `tendsto_iVolume_of_tendsto`: `thm:contvolu` (volume part) on the native carrier;
* `tendsto_hausdorffDist_generalPartialBody`: `thm:pobmain` (4) for arbitrary filters;
* `nonempty_generalPartialBody`, `partialConvexBody`: `Δ_{Y•}(T)` is a convex body for every
  `T ∈ 𝒵₊(X, α)` (unconditional), i.e. `T ↦ Δ_{Y•}(T)` is a map `𝒵₊(X, α) → 𝒦ₙ`;
* `continuousOn_partialConvexBody`, `continuous_partialConvexBody_positiveMass`: `thm:pobmain` (4)
  literally, the continuity of `𝒵₊(X, α)_{>0} → 𝒦ₙ`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.PartialBody

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial

/-! ### The volume of a positive-mass potential -/

section Volume

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- The non-pluripolar mass is at most the volume: `∫ θ_φ^n ≤ vol θ_φ`
(`cor:compnppmassandvol`, since `φ ⪯ P_θ[φ]_𝓘`). -/
theorem diagonalPotentialMass_le_iVolume (ω : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    diagonalPotentialMass θ φ hφ ≤
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ :=
  GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential
    (θ := fun _ : Fin n => θ) (u := fun _ => φ) (v := fun _ => iSingularityEnvelope θ.val φ)
    ω (fun _ => hφ)
    (fun _ => iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ)
    (fun _ => moreSingularOn_iSingularityEnvelope hφ)

/-- The volume of a `θ`-psh potential is finite. -/
theorem iVolume_ne_top (ω : KahlerBackground n X) {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ ≠ ⊤ :=
  (MixedMass.globalMixedMass_lt_top ω (fun _ : Fin n =>
    (iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ).1)).ne

/-- **`thm:contvolu`** (volume part, on the native carrier): if `φ_i → φ` in `d_S` and
`∫ θ_φ^n > 0`, then `vol θ_{φ_i} → vol θ_φ` (`vol` of `def:volqpsh`). -/
theorem tendsto_iVolume_of_tendsto (ω : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ι : Type*} (l : Filter ι)
    (u : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hv : HasPositivePotentialMass θ v.val v.property)
    (hlim : Tendsto u l (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto (fun i => iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
        (u i).val (u i).property) l
      (𝓝 (iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) v.val
        v.property)) := by
  let _ := singularityPseudoMetricSpace ω θ hbig
  let _ : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
  have hQ := IEnvelopeNativeContinuity.tendsto_iEnvelope_of_tendsto_positive_mass ω θ hbig l u
    v hv hlim
  have hc := ((SingularCanonicalSingularityMassLipschitz.diagonalPotentialMass_uniformContinuous
    ω θ hbig).continuous.tendsto _).comp hQ
  rw [← ENNReal.tendsto_toReal_iff (fun i => iVolume_ne_top ω (u i).property)
    (iVolume_ne_top ω v.property)]
  exact hc

end Volume

/-! ### `thm:pobmain` (4) -/

section Flag

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `thm:pobmain` (1) for any Borel measurable structure on `X` (unconditional, through
`TranscendentalPartial.volumeIdentityAll`). -/
theorem volume_generalPartialBody_of_borelSpace [MeasurableSpace F.carrier]
    [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    volume (generalPartialBody F θ φ) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ /
        ((m + 1).factorial : ℝ≥0∞) := by
  obtain ⟨h⟩ := ‹BorelSpace F.carrier›
  subst h
  exact volume_generalPartialBody (volumeIdentityAll m) hφ

/-- `T ⪯ S` pointwise (`φ ≤ ψ`) gives `Δ(T) ⊆ Δ(S) ⊆ Δ(α)` (`thm:pobmain` (2)). -/
theorem generalPartialBody_subset_of_pointwise_le {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) (hle : φ ≤ ψ)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    generalPartialBody F θ φ ⊆ generalPartialBody F θ ψ ∧
      generalPartialBody F θ ψ ⊆ tradOkounkovBody F θ :=
  generalPartialBody_subset_of_iOrder hφ hψ
    (iOrderOnManifold_of_le hψ.1.quasiPlurisubharmonic hle)
    ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr hbig)

/-- The volume of the partial Okounkov body of a positive-mass current is positive:
`vol Δ(T) = (1/n!) vol T ≥ (1/n!) ∫ T^n > 0` (`thm:pobmain` (1)). -/
theorem volume_generalPartialBody_pos [MeasurableSpace F.carrier]
    [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hpos : HasPositivePotentialMass θ φ hφ) :
    0 < volume (generalPartialBody F θ φ) := by
  rw [volume_generalPartialBody_of_borelSpace hφ]
  exact ENNReal.div_pos (hpos.trans_le (diagonalPotentialMass_le_iVolume F.omega hφ)).ne'
    (ENNReal.natCast_ne_top _)

/-- **`thm:pobmain` (4)** (filter form): let `α = {θ}` be big, `ω` any Kähler form (the
reference form of the `d_S`-pseudometric), and `φ_i → φ` in `d_S` with `∫_X θ_φ^n > 0`. Then
`d_Haus(Δ_{Y•}(θ + dd^c φ_i), Δ_{Y•}(θ + dd^c φ)) → 0` (Euclidean Hausdorff distance). -/
theorem tendsto_hausdorffDist_generalPartialBody [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (ω : KahlerBackground (m + 1) F.carrier)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ι : Type*} (l : Filter ι)
    (u : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hv : HasPositivePotentialMass θ v.val v.property)
    (hlim : Tendsto u l (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto (fun i => hausdorffDist
        (TranscendentalMain.euclideanImage (generalPartialBody F θ (u i).val))
        (TranscendentalMain.euclideanImage (generalPartialBody F θ v.val))) l (𝓝 0) := by
  let _ := singularityPseudoMetricSpace ω θ hbig
  let _ : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
  -- the maxima `ψ_i = max(φ_i, φ)` converge to `φ`
  set Z : ι → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((u i).val x) (v.val x), IsThetaPshPotential.max (u i).property v.property⟩
    with hZdef
  have hZ : Tendsto Z l (𝓝 v) :=
    ((SingularCanonicalSingularityMaximumCriterion.tendsto_native_iff_max_and_endpointMixedMass
      ω θ hbig l u v).mp hlim).1
  have hfact : ((m + 1).factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have hvol : ∀ w : ι → ThetaPshL1 θ.val, Tendsto w l (𝓝 v) →
      Tendsto (fun i => volume (TranscendentalMain.euclideanImage
        (generalPartialBody F θ (w i).val))) l
        (𝓝 (volume (TranscendentalMain.euclideanImage (generalPartialBody F θ v.val)))) := by
    intro w hw
    simp only [volume_euclideanImage, volume_generalPartialBody_of_borelSpace (w _).property,
      volume_generalPartialBody_of_borelSpace v.property]
    exact ENNReal.Tendsto.div_const (tendsto_iVolume_of_tendsto ω θ hbig l w v hv hw)
      (Or.inr hfact)
  have hsub : ∀ i, generalPartialBody F θ (u i).val ⊆ generalPartialBody F θ (Z i).val ∧
      generalPartialBody F θ (Z i).val ⊆ tradOkounkovBody F θ := fun i =>
    generalPartialBody_subset_of_pointwise_le (u i).property (Z i).property
      (fun x => le_max_left _ _) hbig
  have hsubv : ∀ i, generalPartialBody F θ v.val ⊆ generalPartialBody F θ (Z i).val := fun i =>
    (generalPartialBody_subset_of_pointwise_le v.property (Z i).property
      (fun x => le_max_right _ _) hbig).1
  refine tendsto_hausdorffDist_of_tendsto_measure volume
    (B := TranscendentalMain.euclideanImage (tradOkounkovBody F θ))
    (L := fun i => TranscendentalMain.euclideanImage (generalPartialBody F θ (Z i).val))
    (convex_euclideanImage (convex_isCompact_generalPartialBody v.property).1) ?_ ?_
    (isBounded_euclideanImage (TranscendentalBody.isBounded_tradOkounkovBody θ))
    (fun i => convex_euclideanImage (convex_isCompact_generalPartialBody (Z i).property).1)
    (fun i => image_mono (hsub i).1) (fun i => image_mono (hsubv i))
    (fun i => image_mono (hsub i).2) (hvol Z hZ) (hvol u hlim)
  · rw [volume_euclideanImage]
    exact volume_generalPartialBody_pos v.property hv
  · exact (isCompact_euclideanImage
      (convex_isCompact_generalPartialBody v.property).2).measure_lt_top.ne

/-- **`Δ_{Y•}(T)` is a convex body** for every `T = θ + dd^c φ ∈ 𝒵₊(X, α)` (`thm:pobmain`, first
sentence): it is convex and compact (`convex_isCompact_generalPartialBody`) and nonempty, as the
intersection of the decreasing nonempty compact bodies `Δ_{Y•}(T + j⁻¹ ω)`
(`kahlerPartialBody_convexBody`). Unconditional; no bigness or positive mass needed. -/
theorem nonempty_generalPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    (generalPartialBody F θ φ).Nonempty := by
  have ht0 : ∀ j : ℕ, (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := fun j => by positivity
  have hK := fun j : ℕ => kahlerPartialBody_convexBody (F := F)
    (isKahlerCurrentPotential_add_smul hφ F.omega (ht0 j))
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ (fun j => ?_)
    (fun j => (hK j).2.2.1) (hK 0).2.1 (fun j => isClosed_kahlerPartialBody _ φ)
  refine kahlerPartialBody_add_smul_mono hφ F.omega (ht0 (j + 1)) ?_
  exact inv_anti₀ (by positivity) (by push_cast; linarith)

variable (F) in
/-- **The map `T ↦ Δ_{Y•}(T)` into `𝒦ₙ`** (convex bodies of the Euclidean `ℝⁿ` with the Hausdorff
metric, Mathlib's `ConvexBody`), on the potentials `φ ∈ PSH(X, θ)` of the currents
`T = θ + dd^c φ ∈ 𝒵₊(X, {θ})`. -/
def partialConvexBody (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : ThetaPshL1 θ.val) :
    ConvexBody (EuclideanSpace ℝ (Fin (m + 1))) where
  carrier := TranscendentalMain.euclideanImage (generalPartialBody F θ v.val)
  convex' := convex_euclideanImage (convex_isCompact_generalPartialBody v.property).1
  isCompact' := isCompact_euclideanImage (convex_isCompact_generalPartialBody v.property).2
  nonempty' := (nonempty_generalPartialBody v.property).image _

/-- The underlying set of `partialConvexBody F θ φ` is (the Euclidean copy of)
`Δ_{Y•}(θ + dd^c φ)`. -/
theorem coe_partialConvexBody (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : ThetaPshL1 θ.val) :
    (partialConvexBody F θ v : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      TranscendentalMain.euclideanImage (generalPartialBody F θ v.val) :=
  rfl

/-- **`thm:pobmain` (4)**: for a big class `α = {θ}`, the map `T ↦ Δ_{Y•}(T)`,
`𝒵₊(X, α) → 𝒦ₙ`, is continuous on `𝒵₊(X, α)_{>0}` (the potentials of positive non-pluripolar
mass), for the `d_S`-pseudometric (with any reference Kähler form `ω`) and the Hausdorff
metric. -/
theorem continuousOn_partialConvexBody [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (ω : KahlerBackground (m + 1) F.carrier)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
    ContinuousOn (partialConvexBody F θ)
      {v : ThetaPshL1 θ.val | HasPositivePotentialMass θ v.val v.property} := by
  let _ : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
  intro v hv
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  have h := tendsto_hausdorffDist_generalPartialBody (F := F) ω hbig
    (𝓝[{v : ThetaPshL1 θ.val | HasPositivePotentialMass θ v.val v.property}] v) id v hv
    nhdsWithin_le_nhds
  refine h.congr fun w => ?_
  exact ConvexBody.hausdorffDist_coe (partialConvexBody F θ w) (partialConvexBody F θ v)

/-- **`thm:pobmain` (4)**, restricted form: `𝒵₊(X, α)_{>0} → 𝒦ₙ`, `T ↦ Δ_{Y•}(T)`, is
continuous for the subspace `d_S` topology. -/
theorem continuous_partialConvexBody_positiveMass [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (ω : KahlerBackground (m + 1) F.carrier)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
    Continuous (fun v : {v : ThetaPshL1 θ.val // HasPositivePotentialMass θ v.val v.property} =>
      partialConvexBody F θ v.val) := by
  let _ : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace ω θ hbig).toUniformSpace.toTopologicalSpace
  exact (continuousOn_partialConvexBody (F := F) ω hbig).domRestrict

end Flag

end SGPT.Okounkov.PartialBody
