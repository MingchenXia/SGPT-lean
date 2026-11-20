import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.FirstPass.AnalyticPoleSet
import SGPT.Foundations.Analysis.FirstPass.ExceptionalLocus
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.Pending.ModificationInputs
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity
import SGPT.Foundations.Analysis.Pending.RestrictedMassFiniteness
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSet
import SGPT.Foundations.Analysis.Pending.RestrictedVolumeOneBlowup
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence
import SGPT.Foundations.Analysis.Pending.FullSpaceAmbientVanishing

set_option autoImplicit false

/-!
# Loci, positivity of restricted volumes, and modifications

Source: Copy-4, `sec:nK`, `sec:restricted-volumes` (including `it:rv-positive`
and `it:rv-birational`) and the deduction of `thm:main` in `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); CT22, Section 2 and Lemmas 2.7,
4.1--4.3; Boucksom, *Divisorial Zariski decompositions*, Theorem 3.17;
blueprint `ana:locus-properties`.

Standing situation: `X` is a connected compact Kähler manifold (a Kähler form
`omega` is given) and classes are real Bott--Chern classes.  Explicit first-pass
obligations, one per assertion:

* `numericalRestrictedVolume_ne_top`: restricted volumes of a pseudoeffective
  class along positive-dimensional subvarieties are finite (nonnegativity is
  built into `ℝ≥0∞`).
* `numericalRestrictedVolume_eq_zero_iff_not_isBigClass`: for `V = X`,
  `⟨α^n⟩_{X|X} = vol(α)` vanishes exactly when `α` is not big.  The volume
  `vol(α)` is not defined in Lean; only the vanishing criterion, which is what the
  manuscript uses, is stated.
* `isComplexAnalyticSubset_nonKahlerLocus`, `nonKahlerLocus_ne_univ`: for a big
  class, `E_nK(α)` is a proper analytic subset.
* `nonNefLocus_subset_nonKahlerLocus`: `E_nn(α) ⊆ E_nK(α)` for big `α`.
* `exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`: a big class contains a Kähler
  current with analytic singularities (`GlobalAnalyticSingularities`) whose polar
  set is exactly `E_nK(α)`.
* `numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus` (`it:rv-positive`).
* For a modification `μ : X̃ → X` (a blowup sequence), with `μ^* α` represented by
  `μ^* θ`: `compactSpace_and_kahler_of_isBlowupSequence`,
  `isBigClass_pullback`, the transformation rules `nonNefLocus_pullback` and
  `nonKahlerLocus_pullback` (`eq:transformation-rules`, for big `α`), and
  `exists_strictTransform_numericalRestrictedVolume_eq` (`it:rv-birational`).  The
  non-nef locus and restricted volume do not depend on the Kähler form, so the
  rules are asserted for all Kähler forms on `X` and `X̃`.

The hypothesis `0 < n` appears where the encoding needs it: in dimension zero
every punctured neighbourhood filter is trivial, Lelong numbers are `⊤`, and
`E_nK` of every class is the whole (point) manifold.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.LocusProperties

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.BlowupSequences FirstPass.GlobalAnalyticSingularities
  ModificationInputs AnalyticIrreducibleComponents

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

section Loci

variable [CompactSpace X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- Numerical restricted volumes are finite.

Proved from CT22, Lemma 2.1 (`RestrictedMassFiniteness.exists_acTopMass_le`, itself
proved from its Kähler-class case
`KahlerRestrictedMassBound.exists_acTopMass_le_of_zero_representative`, which is in
turn proved by smooth truncation of the potential (`KahlerMassTruncation`) from the
two remaining classical inputs of `SubvarietyStokesMass`, both about SMOOTH
`β`-psh potentials: Stokes against the closed current `[V]` and Lelong's finiteness
of the volume of `V_reg`): on `V ⊆ E_nn(α)` the volume is `0`; otherwise it is the
infimum of the admissible mass envelopes
(`RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf`), hence at most the
envelope at error `1`, which is finite.  Neither pseudoeffectivity nor
`0 < dim V` is used. -/
theorem numericalRestrictedVolume_ne_top (omega : KahlerBackground n X)
    (alpha : RealBottChern n X) (_hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (_hdim_pos : 0 < V.dim) :
    numericalRestrictedVolume omega alpha V ≠ ⊤ := by
  by_cases hV : V.carrier ⊆ nonNefLocus omega alpha
  · rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omega alpha V hV]
    exact ENNReal.zero_ne_top
  · rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega alpha V hV]
    exact ne_top_of_le_ne_top
      (RestrictedMassFiniteness.restrictedMassEnvelope_ne_top omega alpha V ⟨1, one_pos⟩)
      (iInf_le _ _)

omit [CompactSpace X] in
/-- The non-Kähler locus of a big class is a proper subset.

A Kähler current `T = θ + ddᶜu` in `α` has a locally nondegenerate potential:
`u` is finite at some point `y` of every nonempty open set, in particular
somewhere on `X`.  A positive Lelong number at `y` would force `u y = ⊥`
(`NonKahlerLocus.eq_bot_of_lelongNumber_pos`, the classical circle-mean
argument), so `lelongNumber u y = 0` and `y ∉ E_nK(α)`.

Neither compactness nor `hKahler` is used: a big class carries a Kähler
current, whose `lowerBound` field already supplies a Kähler background.
`hKahler` is retained (underscored) because `Pending.ComponentVanishing`
applies this lemma positionally. -/
theorem nonKahlerLocus_ne_univ (hn : 0 < n)
    (_hKahler : Nonempty (KahlerBackground n X)) (alpha : RealBottChern n X)
    (hbig : IsBigClass alpha) :
    nonKahlerLocus alpha ≠ univ := by
  obtain ⟨T⟩ := hbig
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, -, hy⟩ := T.strictlyPsh.2 x univ isOpen_univ (mem_univ x)
  intro hcontra
  have hmem : y ∈ nonKahlerLocus alpha := hcontra ▸ mem_univ y
  exact hy (eq_bot_of_lelongNumber_pos hn T.strictlyPsh.1 (hmem T))

omit [CompactSpace X] [ConnectedSpace X] in
/-- `E_nn(α) ⊆ E_nK(α)`.

STATEMENT STRENGTHENED (the blueprint asserts this for big `α` only): neither
bigness of `α` nor compactness or connectedness of `X` is used.  A Kähler
current `T ∈ α` produces the Kähler current `T + εω ∈ α + ε{ω}` with the *same*
potential, hence with the same Lelong numbers
(`NonKahlerLocus.KahlerCurrent.addSmulKahler`), so a point of `E_nK(α + ε{ω})`
is a point of `E_nK(α)`.  For non-big `α` both sides are `X`. -/
theorem nonNefLocus_subset_nonKahlerLocus (omega : KahlerBackground n X)
    (alpha : RealBottChern n X) :
    nonNefLocus omega alpha ⊆ nonKahlerLocus alpha := by
  intro x hx T
  obtain ⟨epsilon, hxeps⟩ := mem_nonNefLocus.mp hx
  exact hxeps (T.addSmulKahler omega epsilon.2)

omit [ConnectedSpace X] in
/-- A big class contains a Kähler current with analytic singularities whose polar
set is exactly `E_nK(α)`.

The singularities are asserted in the two `I-0489` forms actually used:
rational coefficient with a bounded remainder (`HasAnalyticSingularities`, used
for analyticity of the pole set) and smoothness off the pole set
(`HasManifoldAnalyticSingularitiesSmoothOffPole`, the convention of the
admissible presentations defining restricted volumes).  A bounded logarithmic
remainder alone cannot establish smoothness at a pole; Demailly's Step 3--4
smooth-off-pole conclusion is supplied separately by the source interface.

`Pending.NonKahlerLocusPoleSet` derives this result from Demailly
regularization (`KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`)
and the Noether property of analytic sets
(`AnalyticNoetherProperty.exists_minimal_of_isComplexAnalyticSubset`).  Among the
polar sets of Kähler currents in `α` with analytic singularities (a nonempty
family, by regularizing any Kähler current) pick a minimal one, `P(S)`.  It
contains `E_nK(α)`, since a positive Lelong number forces a pole.  Conversely, for
any Kähler current `T`, the maximum `R` of `S` and `T` (`KahlerCurrentMax`) has
Lelong numbers below both; its regularization `S'` has
`P(S') ⊆ {ν(R) > 0} ⊆ {ν(S) > 0} ⊆ P(S)`, so `P(S') = P(S)` by minimality, and
every point of `P(S)` has `ν(T) ≥ ν(R) > 0`.  Hence `P(S) ⊆ E_nK(α)`.  The
Kähler background `hKahler` (kept, underscored, for positional callers) and
connectedness of `X` are not used. -/
theorem exists_kahlerCurrent_poleSet_eq_nonKahlerLocus (hn : 0 < n)
    (_hKahler : Nonempty (KahlerBackground n X)) (alpha : RealBottChern n X)
    (hbig : IsBigClass alpha) :
    ∃ T : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) T.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) T.potential ∧
        poleSet T.potential = nonKahlerLocus alpha :=
  NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn alpha hbig

omit [ConnectedSpace X] in
/-- **The non-Kähler locus of a big class is an analytic subset.**

Proved from Boucksom's preceding pole-set theorem: its current has global
analytic singularities and exactly the non-Kähler locus as polar set; the latter
is analytic by `FirstPass.AnalyticPoleSet`. -/
theorem isComplexAnalyticSubset_nonKahlerLocus (hn : 0 < n)
    (_hKahler : Nonempty (KahlerBackground n X)) (alpha : RealBottChern n X)
    (hbig : IsBigClass alpha) :
    IsComplexAnalyticSubset (n := n) (nonKahlerLocus alpha) :=
  NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus hn alpha hbig

omit [ConnectedSpace X] in
/-- **Positivity off the non-Kähler locus** (Copy-4, `it:rv-positive`).

Proved from Boucksom's theorem (`exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`)
and density of the top-dimensional regular locus of an irreducible subvariety
(`AnalyticIrreducibleComponents.exists_mem_regularLocus_not_mem_of_not_subset`).
`V ⊄ E_nK(α)` makes `α` big (otherwise `E_nK(α) = X`), so it carries a Kähler
current `T ≥ ω'` with analytic singularities smooth off its polar set and polar
set `E_nK(α)`;
`V ⊄ E_nn(α)` since `E_nn ⊆ E_nK`; and some regular point of `V` lies off the
poles.  The analytic core, `RestrictedVolumePositivity.numericalRestrictedVolume_pos_of_kahlerCurrent`,
is sorry-free: `T` is `ε`-admissible for every `ε`, and near that point the
top-power density of `(T + εω)|_V` is bounded below by that of `ω'|_V`,
uniformly in `ε`.  Pseudoeffectivity is not used. -/
theorem numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (_hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hdim_pos : 0 < V.dim)
    (hV : ¬ V.carrier ⊆ nonKahlerLocus alpha) :
    0 < numericalRestrictedVolume omega alpha V := by
  have hn : 0 < n := hdim_pos.trans_le V.dim_le
  have hbig : IsBigClass alpha := by
    by_contra hnot
    exact hV fun y _ T => absurd ⟨T⟩ hnot
  obtain ⟨T, hsingA, hsingS, hpole⟩ :=
    exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn ⟨omega⟩ alpha hbig
  have hA := isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities hsingA
  obtain ⟨x, hx, hxP⟩ := exists_mem_regularLocus_not_mem_of_not_subset V hA (by rwa [hpole])
  exact RestrictedVolumePositivity.numericalRestrictedVolume_pos_of_kahlerCurrent T hsingS
    hA.isClosed V hx hxP
    (fun h => hV (h.trans (nonNefLocus_subset_nonKahlerLocus omega alpha)))

/-- A cofinal sequence of positive errors converging to zero.  Writing the
errors this way makes the remaining full-space volume input a discrete mass
vanishing problem. -/
def reciprocalPositiveError (k : ℕ) : PositiveError :=
  ⟨1 / ((k : ℝ) + 1), one_div_pos.mpr (by positivity)⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- The infimum over all positive errors is already attained as an infimum over
the cofinal errors `1 / (k + 1)`.  This is a genuine order-continuity reduction:
the reverse inequality uses the monotonicity of the restricted mass envelope,
not a compactness or bigness hypothesis. -/
theorem iInf_restrictedMassEnvelope_eq_iInf_reciprocalPositiveError
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X) :
    (⨅ epsilon : PositiveError,
      restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) =
      ⨅ k : ℕ,
        restrictedMassEnvelope (acTopMassData omega) alpha V (reciprocalPositiveError k) := by
  apply le_antisymm
  · refine le_iInf fun k => ?_
    exact iInf_le _ (reciprocalPositiveError k)
  · refine le_iInf fun epsilon => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt epsilon.2
    have hk' : (reciprocalPositiveError k : ℝ) ≤ (epsilon : ℝ) := hk.le
    exact (iInf_le (fun k : ℕ =>
      restrictedMassEnvelope (acTopMassData omega) alpha V (reciprocalPositiveError k)) k).trans
      (RestrictedVolumePositivity.restrictedMassEnvelope_mono omega alpha V hk')

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Full-space restricted-volume decomposition.**

When `V = X`, the definition has two genuinely different zero mechanisms.  If
`E_nn(α) = X`, the defining non-nef branch is zero.  If `E_nn(α) ≠ X`, then the
full-space restricted volume is exactly the infimum of the actual admissible
full-space masses.  The latter branch includes nef non-big boundary classes, so
it cannot be replaced by the false implication `¬ big → E_nn(α) = X`.

This theorem isolates the remaining analytic content of the non-big branch:
the classical ambient-volume theorem must show that this mass infimum vanishes
when `α` is pseudoeffective and not big. -/
theorem numericalRestrictedVolume_eq_if_nonNefLocus_eq_univ_of_carrier_eq_univ
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.carrier = univ) :
    numericalRestrictedVolume omega alpha V =
      if nonNefLocus omega alpha = univ then 0 else
        ⨅ epsilon : PositiveError,
          restrictedMassEnvelope (acTopMassData omega) alpha V epsilon := by
  classical
  by_cases hnn : nonNefLocus omega alpha = univ
  · have hsubset : V.carrier ⊆ nonNefLocus omega alpha := by
      rw [hV, hnn]
    simp only [hnn, if_true]
    exact numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omega alpha V hsubset
  · have hsubset : ¬ V.carrier ⊆ nonNefLocus omega alpha := by
      intro hsubset
      apply hnn
      rw [Set.eq_univ_iff_forall]
      intro x
      apply hsubset
      rw [hV]
      exact mem_univ x
    simp only [hnn, if_false]
    exact RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega alpha V hsubset

omit [CompactSpace X] [ConnectedSpace X] in
/-- The full-space volume vanishes exactly through either the defining non-nef
branch or the ambient admissible-mass infimum.  This is a definition-level
reduction, not the missing analytic theorem that proves the second alternative
from pseudoeffectivity and non-bigness. -/
theorem numericalRestrictedVolume_eq_zero_iff_nonNefLocus_eq_univ_or_iInf_eq_zero
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.carrier = univ) :
    numericalRestrictedVolume omega alpha V = 0 ↔
      nonNefLocus omega alpha = univ ∨
        (⨅ epsilon : PositiveError,
          restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) = 0 := by
  rw [numericalRestrictedVolume_eq_if_nonNefLocus_eq_univ_of_carrier_eq_univ omega alpha V hV]
  by_cases hnn : nonNefLocus omega alpha = univ
  · simp [hnn]
  · simp [hnn]

omit [ConnectedSpace X] in
/-- A pseudoeffective class that is not big has zero volume.

This is the hard half of Boucksom's characterization `α big ⟺ vol(α) > 0`
(Boucksom, *On the volume of a line bundle*; Demailly--Păun for the transcendental
statement).  The other implication is derived below from
`numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus` and
`nonKahlerLocus_ne_univ`.

Assembled from `Pending.FullSpaceAmbientVanishing.iInf_restrictedMassEnvelope_eq_zero`,
which leaves exactly two NAMED classical inputs: the localization statement
`Pending.FullSpaceAmbientComparison.lintegral_patchDensity_eq_globalMixedMeasure_image`
and the volume theorem
`Pending.FullSpaceAmbientVanishing.tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero`.
The ambient Borel structure is installed locally (the statement carries no
measurable-space hypothesis) as `borel X`. -/
theorem numericalRestrictedVolume_eq_zero_of_not_isBigClass (_hn : 0 < n)
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.carrier = univ)
    (hnotbig : ¬ IsBigClass alpha) :
    numericalRestrictedVolume omega alpha V = 0 := by
  rw [numericalRestrictedVolume_eq_zero_iff_nonNefLocus_eq_univ_or_iInf_eq_zero
    omega alpha V hV]
  by_cases hnn : nonNefLocus omega alpha = univ
  · exact Or.inl hnn
  · right
    /- The `E_nn(α) ≠ X` branch is the ambient non-pluripolar volume vanishing
       theorem; it is not implied by non-bigness through the non-nef branch.
       It is assembled in `Pending.FullSpaceAmbientVanishing` from the ambient
       mass comparison and the Demailly--Păun volume theorem. -/
    let _ : MeasurableSpace X := borel X
    have _ : BorelSpace X := ⟨rfl⟩
    have hdim : V.dim = n := dim_eq_of_carrier_eq_univ V hV
    have herrors : Filter.Tendsto
        (fun k : ℕ => ((reciprocalPositiveError k : PositiveError) : ℝ))
        Filter.atTop (nhds (0 : ℝ)) := by
      have hfun : (fun k : ℕ => ((reciprocalPositiveError k : PositiveError) : ℝ))
          = fun k : ℕ => 1 / ((k : ℝ) + 1) := rfl
      rw [hfun]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    exact FullSpaceAmbientVanishing.iInf_restrictedMassEnvelope_eq_zero omega alpha V hV hdim
      hpsef hnotbig reciprocalPositiveError herrors
      (iInf_restrictedMassEnvelope_eq_iInf_reciprocalPositiveError omega alpha V)

/-- `⟨α^n⟩_{X|X} = vol(α)`, which vanishes exactly when `α` is not big.

The forward implication is PROVED here: `V.carrier = univ` forces `V.dim = n`
(`AnalyticIrreducibleComponents.dim_eq_of_carrier_eq_univ`), hence
`0 < V.dim`; a big class has `E_nK(α) ≠ X` (`nonKahlerLocus_ne_univ`), so `V` is
not contained in it, and `numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus`
gives a positive restricted volume.  Only the converse is an open classical
input (`numericalRestrictedVolume_eq_zero_of_not_isBigClass`). -/
theorem numericalRestrictedVolume_eq_zero_iff_not_isBigClass (hn : 0 < n)
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.carrier = univ) :
    numericalRestrictedVolume omega alpha V = 0 ↔ ¬ IsBigClass alpha := by
  refine ⟨fun hzero hbig => ?_,
    numericalRestrictedVolume_eq_zero_of_not_isBigClass hn omega alpha hpsef V hV⟩
  have hdim : 0 < V.dim := by
    rw [dim_eq_of_carrier_eq_univ V hV]
    exact hn
  have hnotsub : ¬ V.carrier ⊆ nonKahlerLocus alpha := by
    rw [hV]
    exact fun hsub =>
      nonKahlerLocus_ne_univ hn ⟨omega⟩ alpha hbig (univ_subset_iff.mp hsub)
  have hpos := numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus
    omega alpha hpsef V hdim hnotsub
  rw [hzero] at hpos
  exact absurd hpos (lt_irrefl 0)

end Loci

section Modifications

variable [CompactSpace X] [ConnectedSpace X]
  {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
  [IsComplexManifold n Xt]

omit [ConnectedSpace X] in
/-- **A modification of a compact Kähler manifold is compact Kähler.**

Proved by induction over `IsBlowupSequence`: the reflexive case is `X` itself,
and each step is the one-blowup statement
`ModificationInputs.compactSpace_and_kahler_of_isBlowupAlong` (Blanchard /
Voisin I, 3.24), the only genuine content.  This derivation is sorry-free;
connectedness of `X` is not used. -/
theorem compactSpace_and_kahler_of_isBlowupSequence
    (hKahler : Nonempty (KahlerBackground n X)) (μ : Xt → X)
    (hμ : IsBlowupSequence n X Xt μ) :
    CompactSpace Xt ∧ Nonempty (KahlerBackground n Xt) := by
  induction hμ with
  | refl => exact ⟨inferInstance, hKahler⟩
  | step f C g _hf hg ih =>
      obtain ⟨hcompact, hkahler⟩ := ih
      have := hcompact
      exact compactSpace_and_kahler_of_isBlowupAlong hkahler hg

omit [ConnectedSpace X] in
/-- **The pullback of a big class under a modification is big.**

Proved by induction over `IsBlowupSequence`, using functoriality of the pullback
of forms on real Bott--Chern classes
(`ClosedRealOneOneForm.ofRepresentative_pullback_id` and
`..._pullback_comp`) and, at each step, the one-blowup input
`ModificationInputs.isBigClass_pullback_of_isBlowupAlong`.  The intermediate
manifold is compact Kähler by `compactSpace_and_kahler_of_isBlowupSequence`. -/
theorem isBigClass_pullback (hKahler : Nonempty (KahlerBackground n X))
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ) :
    IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) := by
  induction hμ with
  | refl =>
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_id]
      exact hbig
  | step f C g hfs hg ih =>
      obtain ⟨hcompact, hkahlerY⟩ :=
        compactSpace_and_kahler_of_isBlowupSequence hKahler f hfs
      have := hcompact
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_comp hfs.contMDiff hg.contMDiff θ]
      exact isBigClass_pullback_of_isBlowupAlong hkahlerY _ ih hg

omit [ConnectedSpace X] in
/-- **Transformation rule for the non-nef locus**: `E_nn(μ^* α) = μ⁻¹ E_nn(α)` for
big `α`.

Proved by induction over `IsBlowupSequence`, after reverting the Kähler
background on the blown-up manifold so that the induction hypothesis is
available for EVERY background there (the intermediate manifold of the sequence
carries no distinguished one).  The reflexive case is independence of `E_nn` of
the Kähler background (`ModificationInputs.nonNefLocus_kahler_independent`),
the step case is the one-blowup rule
`ModificationInputs.nonNefLocus_pullback_of_isBlowupAlong` composed with the
induction hypothesis.  No exceptional term appears here, unlike for `E_nK`. -/
theorem nonNefLocus_pullback (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ) (omegaT : KahlerBackground n Xt) :
    nonNefLocus omegaT (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) =
      μ ⁻¹' nonNefLocus omega (RealBottChern.ofRepresentative θ) := by
  revert omegaT
  induction hμ with
  | refl =>
      intro omegaT
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_id, preimage_id]
      exact nonNefLocus_kahler_independent omegaT omega
        (RealBottChern.ofRepresentative θ)
  | step f C g hfs hg ih =>
      intro omegaT
      obtain ⟨hcompact, hkahlerY⟩ :=
        compactSpace_and_kahler_of_isBlowupSequence ⟨omega⟩ f hfs
      have := hcompact
      obtain ⟨omegaY⟩ := hkahlerY
      have hbigY : IsBigClass (RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hfs.contMDiff θ)) :=
        isBigClass_pullback ⟨omega⟩ θ hbig f hfs
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_comp hfs.contMDiff hg.contMDiff θ,
        nonNefLocus_pullback_of_isBlowupAlong omegaY omegaT _ hbigY hg, ih omegaY]
      rfl

omit [ConnectedSpace X] in
/-- **Transformation rule for the non-Kähler locus**:
`E_nK(μ^* α) = μ⁻¹ E_nK(α) ∪ Exc(μ)` for big `α`.

Proved by induction over `IsBlowupSequence`.  The reflexive case is
`Exc(id) = ∅` (`exceptionalLocus_id`) together with `id^* θ = θ`; the step case
composes the one-blowup rule
`ModificationInputs.nonKahlerLocus_pullback_of_isBlowupAlong` with the induction
hypothesis, and the bookkeeping closes because
`Exc(f ∘ g) = Exc(g) ∪ g⁻¹(Exc f)` (`exceptionalLocus_comp`).  That identity is
exactly what makes the extra exceptional term accumulate correctly along a
sequence. -/
theorem nonKahlerLocus_pullback (hKahler : Nonempty (KahlerBackground n X))
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ) :
    nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) =
      μ ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪ exceptionalLocus n μ := by
  induction hμ with
  | refl =>
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_id, exceptionalLocus_id]
      simp
  | step f C g hfs hg ih =>
      obtain ⟨hcompact, hkahlerY⟩ :=
        compactSpace_and_kahler_of_isBlowupSequence hKahler f hfs
      have := hcompact
      have hbigY : IsBigClass (RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hfs.contMDiff θ)) :=
        isBigClass_pullback hKahler θ hbig f hfs
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_comp hfs.contMDiff hg.contMDiff θ,
        nonKahlerLocus_pullback_of_isBlowupAlong hkahlerY _ hbigY hg, ih,
        exceptionalLocus_comp (hfs.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp)), preimage_union]
      ext y
      simp only [mem_union, mem_preimage, Function.comp_apply]
      tauto

omit [ConnectedSpace X] in
/-- **Birational invariance of restricted volumes** (Copy-4, `it:rv-birational`):
if `V ⊄ μ(Exc μ)` and `α` is big, the strict transform `Ṽ` is an irreducible
subvariety of the same dimension with `⟨(μ^* α)^k⟩_{X̃|Ṽ} = ⟨α^k⟩_{X|V}`.

Proved by induction over `IsBlowupSequence` from the one-blowup statement
`RestrictedVolumeOneBlowup.exists_strictTransform_numericalRestrictedVolume_eq_of_isBlowupAlong`
(CT22, Lemma 4.3 for one blowup, assembled from three explicit classical inputs:
the strict transform is a subvariety, and the two inequalities).  The reflexive case is independence
of the restricted volume of the Kähler form
(`RestrictedVolumeKahlerIndependence`, sorry-free).  In the step case
`μ = f ∘ g`, both factors are surjective (a blowup of a compact manifold is onto,
`StrictTransformComposition.IsBlowupSequence.compactSpace_surjective`), so
`V ⊄ f(Exc f)` and `Ṽ_f ⊄ g(Exc g)`; strict transforms compose
(`StrictTransformComposition.strictTransform_comp`), and the volumes chain through
any Kähler form on the intermediate manifold.  Connectedness of `X` is not used. -/
theorem exists_strictTransform_numericalRestrictedVolume_eq
    (hKahler : Nonempty (KahlerBackground n X))
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hdim_pos : 0 < V.dim)
    (hV : ¬ V.carrier ⊆ μ '' exceptionalLocus n μ) :
    ∃ Vt : ClosedIrreducibleAnalyticSubvariety n Xt,
      Vt.carrier = strictTransform n μ V.carrier ∧ Vt.dim = V.dim ∧
      ∀ (omega : KahlerBackground n X) (omegaT : KahlerBackground n Xt),
        numericalRestrictedVolume omegaT (RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hμ.contMDiff θ)) Vt =
          numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V := by
  induction hμ with
  | refl =>
      refine ⟨V, ?_, rfl, fun omega omegaT => ?_⟩
      · simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
      · rw [ClosedRealOneOneForm.ofRepresentative_pullback_id]
        exact RestrictedVolumeKahlerIndependence.numericalRestrictedVolume_kahler_independent
          omegaT omega _ V
  | step f C g hfs hg ih =>
      obtain ⟨hcompact, hsurjf⟩ :=
        StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hfs
      have := hcompact
      obtain ⟨-, hkahlerY⟩ := compactSpace_and_kahler_of_isBlowupSequence hKahler f hfs
      have hsurjg := StrictTransformComposition.surjective_of_isBlowupAlong hg
      have hVf : ¬ V.carrier ⊆ f '' exceptionalLocus n f := fun h =>
        hV (h.trans (StrictTransformComposition.image_exceptionalLocus_subset_comp
          (hfs.contMDiff.mdifferentiable (by simp)) (hg.contMDiff.mdifferentiable (by simp))
          hsurjg))
      obtain ⟨W, hWc, hWd, hWvol⟩ := ih hVf
      have hbigY := isBigClass_pullback hKahler θ hbig f hfs
      have hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g := by
        rw [hWc]
        exact StrictTransformComposition.not_strictTransform_subset_image_exceptionalLocus
          hfs.contMDiff hg.contMDiff hsurjf hsurjg hV
      obtain ⟨Vt, hVc, hVd, hVvol⟩ :=
        RestrictedVolumeOneBlowup.exists_strictTransform_numericalRestrictedVolume_eq_of_isBlowupAlong
          _ hbigY hg W (hWd ▸ hdim_pos) hW
      refine ⟨Vt, ?_, hVd.trans hWd, fun omega omegaT => ?_⟩
      · rw [hVc, hWc, StrictTransformComposition.strictTransform_comp hfs.contMDiff
          hg.contMDiff]
      · obtain ⟨omegaY⟩ := hkahlerY
        rw [ClosedRealOneOneForm.ofRepresentative_pullback_comp hfs.contMDiff hg.contMDiff θ,
          hVvol omegaY omegaT, hWvol omega omegaY]

end Modifications

end

end SGPT.Foundations.Analysis.Pending.LocusProperties
