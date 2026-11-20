import SGPT.Foundations.Analysis.Pending.GermParametrizationProof
import SGPT.Foundations.Analysis.Pending.ParametrizationFibreBound
import SGPT.Foundations.Analysis.Pending.ChartGermSheetBound
import SGPT.Foundations.Analysis.Pending.ShearTowerNormalization
import SGPT.Foundations.Analysis.Pending.CoordinateProjectionDense
import SGPT.Foundations.Analysis.Pending.GermParametrizationDimUnique

set_option autoImplicit false

/-!
# The sheet bound of an irreducible germ, in the coordinates the germ chooses

`Pending.ParametrizationFibreBound.exists_fibreBound` bounds the fibres of the
adapted projection of `ParametrizationData`: it assumes the coordinates already
put the germ in Noether position, and its projection is literally
`coordinateProjection n d`.  `Pending.GermNoetherNormalization` produces those
coordinates for the vanishing ideal of an irreducible germ, but as a linear
automorphism `L` of `ℂⁿ` about which nothing is asserted.

This module composes the two, exactly as
`Pending.GermParametrization.LocalParametrization.transport` composes them for
the density statement.  The output is `Pending.ChartGermSheetBound.GermSheetBound`
for the projection `transportedProjection L P.dim` DETERMINED by parametrization
data `P` for `L⁻¹A`.

The data must be part of the statement.  A sheet bound whose direction is only
existentially quantified says nothing: with `d = n` and `B` the identity every
fibre is a single point, and with `d ≥ 1` and `B = 0` every fibre over a value
other than `0` is empty, so the almost-everywhere clause is satisfied by a
degenerate direction as well.  All the content of the local parametrization
theorem sits in the direction, which is why `exists_germSheetBound` exhibits the
normalizing `L` and its parametrization data rather than just a map.

For the same reason the consumer of this bound,
`Pending.AdaptedProjectionGerm.exists_adaptedProjection`, prescribes the direction
up to `δ`: only then is a degenerate `B` excluded, and only then does
`Pending.PluckerSpanningOpen` return the spanning of the perturbed family.  That
difference is the genericity of the normalizing direction, isolated here as
`exists_parametrizationData_near` and now PROVED from `Pending.ShearTowerNormalization`,
`Pending.CoordinateProjectionDense` and `Pending.GermParametrizationDimUnique`;
everything else in Demailly CADG III.2.6's perturbation sentence is proved in this
module and in `Pending.ChartGermSheetBound`.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IrreducibleGermSheetBound

open FirstPass FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Foundations.Analysis.Pending.GermParametrization
open SGPT.Foundations.Analysis.Pending.ChartGermSheetBound

variable {n : ℕ}

/-- The projection of a germ put in Noether position by `L`, read in the original
coordinates. -/
def transportedProjection (L : ComplexModel n ≃L[ℂ] ComplexModel n) (d : ℕ) :
    ComplexModel n →L[ℂ] ComplexModel d :=
  (coordinateProjection n d).comp (L.symm : ComplexModel n →L[ℂ] ComplexModel n)

@[simp] theorem transportedProjection_apply (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (d : ℕ) (z : ComplexModel n) :
    transportedProjection L d z = coordinateProjection n d (L.symm z) := rfl

/-- Transport of the parametrization fibre bound along a linear change of
coordinates: the fibres upstairs are the `L`-images of the fibres downstairs, so
nothing about the base space changes — the target of the projection, the base set
`Δ` and the null set of bad values are literally the same. -/
theorem germSheetBound_transport {A : Set (ComplexModel n)}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) (P : ParametrizationData (L ⁻¹' A))
    (S : SetsData P) {d : ℕ} (hd : P.dim = d) :
    GermSheetBound A (transportedProjection L d) := by
  subst hd
  obtain ⟨U₀, Δ, N, hU₀open, h0U₀, hΔm, hΔtop, hmaps, hfib⟩ :=
    ParametrizationFibreBound.exists_fibreBound P S
  refine ⟨(L.symm : ComplexModel n → ComplexModel n) ⁻¹' U₀, Δ, N,
    hU₀open.preimage L.symm.continuous, by simpa using h0U₀, hΔm, hΔtop, ?_, ?_⟩
  · rintro z ⟨hzA, hzU⟩
    exact hmaps _ ⟨by simpa using hzA, hzU⟩
  · have hset : ∀ y : ComplexModel P.dim,
        A ∩ ((L.symm : ComplexModel n → ComplexModel n) ⁻¹' U₀) ∩
            transportedProjection L P.dim ⁻¹' {y} =
          (L : ComplexModel n → ComplexModel n) ''
            ((L ⁻¹' A) ∩ U₀ ∩ coordinateProjection n P.dim ⁻¹' {y}) := by
      intro y
      ext z
      constructor
      · rintro ⟨⟨hzA, hzU⟩, hzy⟩
        exact ⟨L.symm z, ⟨⟨by simpa using hzA, hzU⟩, hzy⟩, by simp⟩
      · rintro ⟨w, ⟨⟨hwA, hwU⟩, hwy⟩, rfl⟩
        refine ⟨⟨hwA, ?_⟩, ?_⟩ <;> simpa using ‹_›
    refine hfib.mono fun y hy => ?_
    rw [hset y, Function.Injective.encard_image L.injective]
    exact hy

/-- Noether normalization, the algebraic parametrization and the pointwise
identities, packaged as the existence of parametrization data for an irreducible
germ in SOME coordinates. -/
theorem exists_noetherParametrizationData {A : Set (ComplexModel n)}
    (hA : IsIrreducibleGerm A) :
    ∃ L : ComplexModel n ≃L[ℂ] ComplexModel n, Nonempty (ParametrizationData (L ⁻¹' A)) := by
  have hprime : (vanishingIdeal A).IsPrime := (isIrreducibleGerm_iff_isPrime hA.1).1 hA
  obtain ⟨d, L, hN⟩ := exists_isNoetherNormalization (vanishingIdeal A)
  rw [map_vanishingIdeal_comapEquiv] at hN
  have hprime' : (vanishingIdeal (L ⁻¹' A)).IsPrime := by
    rw [← map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨AP⟩ := exists_algebraicParametrization hN
  exact ⟨L, nonempty_parametrizationData (isAnalyticGerm_preimage L hA.1) AP⟩

/-- **The sheet bound of an irreducible germ, PROVED.**  Every irreducible
analytic germ `A` at `0 ∈ ℂⁿ` admits a linear change of coordinates `L` putting it
in Noether position, with parametrization data `P` for `L⁻¹A`, such that the
transported adapted projection has at most finitely many points of `A` over almost
every value near `0`.

This is Demailly CADG II.4.19 in the almost-everywhere form the Lelong local
volume bound consumes, with the adapted coordinates PRODUCED rather than assumed.
The parametrization data is part of the conclusion on purpose: see the module
docstring for why a bound whose direction is merely existential is empty. -/
theorem exists_germSheetBound {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A) :
    ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n) (P : ParametrizationData (L ⁻¹' A)),
      GermSheetBound A (transportedProjection L P.dim) := by
  obtain ⟨L, ⟨P⟩⟩ := exists_noetherParametrizationData hA
  obtain ⟨S⟩ := nonempty_setsData P
  exact ⟨L, P, germSheetBound_transport L P S rfl⟩

/-- **THE GENERICITY OF THE NORMALIZING DIRECTION, PROVED.**  The linear changes
of coordinates that put FINITELY MANY irreducible germs of the same dimension `d`
simultaneously in Noether position over `𝒪_d` are DENSE: given one for each germ
separately, and given any `ℂ`-linear `B₀ : ℂⁿ → ℂᵈ` and any `δ > 0`, there is a
SINGLE one, within `δ` of `B₀`, that serves them all.

`Pending.GermNoetherNormalization.exists_isNoetherNormalization` produces one
normalizing `L` per germ and says nothing about it.  The two things added here are
that ONE `L` serves the whole family — the germ of a subvariety at a point is
reducible, and one direction has to be finite on all its components at once — and
that `L` may be prescribed up to `δ`.

The proof is in three imported pieces and an assembly.

* `Pending.ShearTowerNormalization.noetherShearProperty`: one `L` normalizes the
  whole family with `‖L⁻¹ - id‖ ≤ ε`.  This is the induction of
  `exists_isNoetherNormalization_succ` re-run with the Weierstrass direction taken
  from `Pending.WeierstrassPreparationDense`, whose good directions are open and
  dense (`Pending.RegularDirectionDense`) and hence collapse a finite family to
  one shear, as close to `0` as asked.
* `Pending.CoordinateProjectionDense.exists_continuousLinearEquiv_near`: every
  `B₀` is within `δ/2` of `coordinateProjection n d ∘ K⁻¹` for some automorphism
  `K` of `ℂⁿ` — which is where the tower is then conjugated, so that a statement
  produced near the standard projection comes out near `B₀`.  This is why a `B₀`
  of rank `< d` is not a counterexample: it is approximated, never matched.
* `Pending.GermParametrizationDimUnique.dim_eq_dim`: the dimension of
  parametrization data of an irreducible germ is intrinsic (it is the pure
  dimension), which is what identifies the dimension the tower produces — one per
  member, since nothing inside the induction knows they agree — with the `d` the
  statement prescribes.  `Pending.GermParametrizationData.nonempty_parametrizationData`
  forgets the dimension it was given, and this is what recovers it.

Checked against the degenerate cases.  If `d = 0` — every germ a point, or `n = 0`
— the target `ComplexModel 0` is the zero space, so `B₀` and every
`transportedProjection L 0` are the zero map and any of the given `L₀ i` serves.
Germs empty near `0` are excluded by `IsIrreducibleGerm`.  The hypothesis is never
vacuous: `exists_noetherParametrizationData` supplies an `L₀ i` and a `P₀ i` for
every irreducible germ.

`hdn : d ≤ n` is NOT redundant, and is the reason the empty family is not a
counterexample.  `coordinateProjection n d` zero-pads: its coordinates of index
`≥ n` are identically `0`, so for `d > n` no `transportedProjection L d` comes
within `δ` of a `B₀` with a nonzero coordinate there.  For `r ≥ 1` the bound is
forced by `(P₀ i).dim_le`, but at `r = 0` that evidence is absent and the
hypothesis has to be carried.  Its consumer supplies it from
`ClosedIrreducibleAnalyticSubvariety.dim_le`. -/
theorem exists_parametrizationData_near {r : ℕ} {A : Fin r → Set (ComplexModel n)}
    (hA : ∀ i, IsIrreducibleGerm (A i)) {d : ℕ}
    {L₀ : Fin r → ComplexModel n ≃L[ℂ] ComplexModel n}
    (P₀ : ∀ i, ParametrizationData (L₀ i ⁻¹' A i)) (hd : ∀ i, (P₀ i).dim = d)
    (hdn : d ≤ n)
    (B₀ : ComplexModel n →L[ℂ] ComplexModel d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n) (P : ∀ i, ParametrizationData (L ⁻¹' A i)),
      (∀ i, (P i).dim = d) ∧ ‖transportedProjection L d - B₀‖ < δ := by
  classical
  -- a change of coordinates whose transported projection is already within `δ/2` of `B₀`
  obtain ⟨K, hK⟩ :=
    CoordinateProjectionDense.exists_continuousLinearEquiv_near hdn B₀ (half_pos hδ)
  set C : ℝ := (‖coordinateProjection n d‖ + 1) *
    (‖(K.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1) with hCdef
  have hC : 0 < C := by positivity
  set ε : ℝ := δ / (2 * C) with hεdef
  have hε : 0 < ε := div_pos hδ (by positivity)
  -- one shear tower, close to the identity, normalizing every `K⁻¹ Aᵢ` at once
  have hprime : ∀ i, ((vanishingIdeal (A i)).map (HolGerm.comapEquiv K)).IsPrime := by
    intro i
    have : (vanishingIdeal (A i)).IsPrime := (isIrreducibleGerm_iff_isPrime (hA i).1).1 (hA i)
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨U, d', hN, hU⟩ :=
    ShearTowerNormalization.noetherShearProperty n
      (fun i => (vanishingIdeal (A i)).map (HolGerm.comapEquiv K)) hprime hε
  set L := U.trans K with hL
  have hNL : ∀ i, IsNoetherNormalization (vanishingIdeal (L ⁻¹' A i)) (d' i) := by
    intro i
    have h := hN i
    rw [← HolGerm.map_comapEquiv_trans, map_vanishingIdeal_comapEquiv] at h
    exact h
  have hPex : ∀ i, Nonempty (ParametrizationData (L ⁻¹' A i)) := by
    intro i
    have hprime' : (vanishingIdeal (L ⁻¹' A i)).IsPrime := by
      have : (vanishingIdeal (A i)).IsPrime := (isIrreducibleGerm_iff_isPrime (hA i).1).1 (hA i)
      rw [← map_vanishingIdeal_comapEquiv]
      exact Ideal.map_isPrime_of_equiv _
    obtain ⟨AP⟩ := exists_algebraicParametrization (hNL i)
    exact nonempty_parametrizationData (isAnalyticGerm_preimage L (hA i).1) AP
  refine ⟨L, fun i => (hPex i).some, fun i => ?_, ?_⟩
  · -- the dimension is intrinsic, so it is the one the hypothesis prescribes
    obtain ⟨S⟩ := nonempty_setsData (hPex i).some
    obtain ⟨S₀⟩ := nonempty_setsData (P₀ i)
    exact (GermParametrizationDimUnique.dim_eq_dim (hA i) S₀ S).trans (hd i)
  · -- the transported projection moved by at most `δ/2` from the one `K` prescribes
    have hcoe : ((L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n)
        = (U.symm : ComplexModel n →L[ℂ] ComplexModel n).comp
            (K.symm : ComplexModel n →L[ℂ] ComplexModel n) := by
      ext z
      simp [hL]
    have hsplit : transportedProjection L d - B₀
        = (coordinateProjection n d).comp
            (((U.symm : ComplexModel n →L[ℂ] ComplexModel n) -
              ContinuousLinearMap.id ℂ (ComplexModel n)).comp
                (K.symm : ComplexModel n →L[ℂ] ComplexModel n))
          + ((coordinateProjection n d).comp
              (K.symm : ComplexModel n →L[ℂ] ComplexModel n) - B₀) := by
      rw [transportedProjection, hcoe, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hsplit]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have hXle : ‖((U.symm : ComplexModel n →L[ℂ] ComplexModel n) -
        ContinuousLinearMap.id ℂ (ComplexModel n)).comp
          (K.symm : ComplexModel n →L[ℂ] ComplexModel n)‖
        ≤ ε * ‖(K.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ :=
      le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
    have h1 : ‖(coordinateProjection n d).comp
        (((U.symm : ComplexModel n →L[ℂ] ComplexModel n) -
          ContinuousLinearMap.id ℂ (ComplexModel n)).comp
            (K.symm : ComplexModel n →L[ℂ] ComplexModel n))‖
        ≤ ‖coordinateProjection n d‖ *
            (ε * ‖(K.symm : ComplexModel n →L[ℂ] ComplexModel n)‖) :=
      le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_left hXle (norm_nonneg _))
    have hεC : ε * C = δ / 2 := by
      rw [hεdef]; field_simp
    have h2 : ‖coordinateProjection n d‖ *
        (ε * ‖(K.symm : ComplexModel n →L[ℂ] ComplexModel n)‖) ≤ δ / 2 := by
      rw [← hεC, hCdef]
      nlinarith [norm_nonneg (coordinateProjection n d),
        norm_nonneg (K.symm : ComplexModel n →L[ℂ] ComplexModel n), hε.le,
        mul_nonneg hε.le (norm_nonneg (coordinateProjection n d)),
        mul_nonneg hε.le (norm_nonneg (K.symm : ComplexModel n →L[ℂ] ComplexModel n))]
    linarith

/-- **The sheet bound of a finite family of irreducible germs in a PRESCRIBED
direction**, modulo the genericity of the normalizing direction alone.  This is
the germ-level form of
`Pending.AdaptedProjectionGerm.exists_adaptedProjection`: together with
`Pending.ChartGermSheetBound.exists_adaptedProjection_of_chartGermSheetBound` it
lacks only the identification of the chart germ of a subvariety with the union of
its irreducible components and of their common dimension with `V.dim`. -/
theorem exists_germSheetBound_near {r : ℕ} {A : Fin r → Set (ComplexModel n)}
    (hA : ∀ i, IsIrreducibleGerm (A i)) {d : ℕ}
    {L₀ : Fin r → ComplexModel n ≃L[ℂ] ComplexModel n}
    (P₀ : ∀ i, ParametrizationData (L₀ i ⁻¹' A i)) (hd : ∀ i, (P₀ i).dim = d)
    (hdn : d ≤ n)
    (B₀ : ComplexModel n →L[ℂ] ComplexModel d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ComplexModel n →L[ℂ] ComplexModel d,
      ‖B - B₀‖ < δ ∧ GermSheetBound (⋃ i, A i) B := by
  obtain ⟨L, P, hPd, hnorm⟩ := exists_parametrizationData_near hA P₀ hd hdn B₀ hδ
  refine ⟨transportedProjection L d, hnorm, exists_sheetBound_iUnion fun i => ?_⟩
  obtain ⟨S⟩ := nonempty_setsData (P i)
  exact germSheetBound_transport L (P i) S (hPd i)

end SGPT.Foundations.Analysis.Pending.IrreducibleGermSheetBound
