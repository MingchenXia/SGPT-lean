import SGPT.Okounkov.TranscendentalSlice
import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Okounkov.PartialBodyVolume
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Okounkov.TranscendentalLiftingApprox

/-!
# The slice at `0` of the Okounkov body of a big and nef class

Source: the book's `lma:Kahlerclassokounrest` (chapter *The theory of Okounkov bodies*,
section *Transcendental partial Okounkov bodies*, subsection *The valuative characterization*,
lines 1696--1726); blueprint chapter `claude-okoun-val`.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag
`Y•`, and `β` a big and nef class on `X`. Then

`{y ∈ ℝ^{n-1} : (0, y) ∈ Δ_{Y•}(β)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(β|_{Y₁})`,

where the right-hand side is understood in the sense of `def:generalPOB` when `β|_{Y₁}` is not
big; the book's proof (Step 1) uses it in the form
`Δ_{Y₁ ⊇ ⋯}(β|_{Y₁}) = ⋂_{ε > 0} Δ_{Y₁ ⊇ ⋯}(β|_{Y₁} + ε α|_{Y₁})` (`α` Kähler).

* `slice_zero_eq_of_kahler`: the case of a Kähler class `β` (Step 2 of the book), where both
  sides are the bodies of `def:tradOk`;
* `slice_zero_eq_iInter_of_nef` (**`lma:Kahlerclassokounrest`**): for `β` big and nef,
  the slice is `⋂_{ε > 0} Δ_{Y₁ ⊇ ⋯}((β + ε{ω})|_{Y₁})`;
* `slice_zero_eq_of_nef_of_big_restriction`: if moreover `β|_{Y₁}` is big (and `n ≥ 2`), the
  slice is `Δ_{Y₁ ⊇ ⋯}(β|_{Y₁})` of `def:tradOk`;
* `iInter_tradOkounkovBody_eq_generalPartialBody`: the right-hand side is the body of
  `def:generalPOB` of every current `T ∈ 𝒵₊(Y₁, β|_{Y₁})` whose Kähler perturbations
  `T + ε ω` have minimal singularities in `β|_{Y₁} + ε{ω}` (e.g. `T` with bounded potential,
  `iInter_tradOkounkovBody_eq_generalPartialBody_of_bounded`), which is the sense in which the
  book reads `Δ(β|_{Y₁})` (the right-hand side of `lma:Kahlerclassokounrest` in the proof of
  `lma:slicepob`, Step 1).

## Proof

Kähler case. `⊇` (extension): `Δ_{Y₁ ⊇ ⋯}(κ|_{Y₁})` is the closure of the valuations of gentle
Kähler currents `κ|_{Y₁} + dd^c w` (`tok:density`), and each of them extends to a gentle Kähler
current of `{κ}` with valuation `(0, ν(w))` (`cons_mem_tradOkounkovBody_of_extension` with
`t = 0`, DRWNXZ Theorem 6.4, the book's `thm:CT-thm-refined'`). `⊆`: a point `(0, y)` of
`Δ(β)` is a limit of valuations `(c_j, ν(w_j))` of gentle currents, `c_j → 0`,
`ν(w_j) ∈ Δ_{Y₁ ⊇ ⋯}((β - c_j{Y₁})|_{Y₁})` (`tok:valuation-analytic`, `tok:density`), and these
bodies converge to `Δ_{Y₁ ⊇ ⋯}(β|_{Y₁})` in the Hausdorff metric (`tok:hausdorff-continuity` on
`Y₁`, `TranscendentalSlice.sliceTarget_hausdorff` around `t = 0`, which is possible since
`β - t{Y₁}` is Kähler for `|t|` small). ROUTE CHANGE: the book derives `⊆` from the slice formula
`thm:Okounkovtranmain` (5) at `t > 0` and `lma:Hausdorffconvslice`; here the limit is taken
directly in the slice-wise description of the valuations, which needs neither.

Big and nef case (Step 1 of the book): `Δ(β) = ⋂_{ε > 0} Δ(β + ε{ω})`
(`thm:Okounkovtranmain` (4), `TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler`), and
`β + ε{ω}` is a Kähler class for `ε > 0`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.Valuative

open Set Filter Metric
open scoped Topology Manifold ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice

section KahlerSlice

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- A unit metric of `Y₁` exists. -/
theorem exists_isFirstDivisorUnitMetric (F : OriginalFlagGeometry.{u} (m + 1)) :
    ∃ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
      TranscendentalMain.IsFirstDivisorUnitMetric F E := by
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero
      (PluripolarCapacityDichotomy.isThetaPshPotential_zero F.omega) F.firstDivisor
  exact ⟨E, D, hDI, hEW, hmetric⟩

/-- `κ - s η` is a Kähler form (up to cohomology) for `|s|` small. -/
theorem exists_pos_forall_kahler_sub_abs (κ₀ : KahlerBackground (m + 1) F.carrier)
    (η : ClosedRealOneOneForm (m + 1) F.carrier) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ s ∈ Ioo (-t₁) t₁, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (κ₀.form - s • η) := by
  obtain ⟨a, ha, hA⟩ := exists_pos_forall_kahler_sub κ₀ η
  obtain ⟨b, hb, hB⟩ := exists_pos_forall_kahler_sub κ₀ (-η)
  refine ⟨min a b, lt_min ha hb, fun s hs => ?_⟩
  rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
  · obtain ⟨κ, hκ⟩ := hB (-s) ⟨by linarith, by linarith [hs.1, min_le_right a b]⟩
    refine ⟨κ, congrArg RealBottChern.ofRepresentative ?_⟩
    rw [hκ]
    module
  · subst hs0
    exact ⟨κ₀, by rw [zero_smul, sub_zero]⟩
  · obtain ⟨κ, hκ⟩ := hA s ⟨hs0, lt_of_lt_of_le hs.2 (min_le_left a b)⟩
    exact ⟨κ, by rw [hκ]⟩

/-- The class of `θ - s Θ_E` is Kähler for `|s|` small if `{θ}` is Kähler. -/
theorem exists_pos_forall_kahler_sub_of_class {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    (η : ClosedRealOneOneForm (m + 1) F.carrier) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ s ∈ Ioo (-t₁) t₁, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • η) := by
  obtain ⟨t₁, ht₁, h⟩ := exists_pos_forall_kahler_sub_abs κ₀ η
  refine ⟨t₁, ht₁, fun s hs => ?_⟩
  obtain ⟨κ, hκ⟩ := h s hs
  refine ⟨κ, hκ.trans ?_⟩
  rw [sub_eq_add_neg, sub_eq_add_neg, RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_add, hθ]

/-- `sliceTarget` only depends on `θ - s Θ_E`. -/
theorem sliceTarget_add_smul (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (a s : ℝ) :
    sliceTarget F (θ + a • E.curvature) E s = sliceTarget F θ E (s - a) := by
  unfold sliceTarget
  congr 2
  module

/-- **The right side is Hausdorff continuous at `t = 0`** on `(-t₁, t₁)` if `θ - s Θ_E` is a
Kähler class for every `s ∈ (-t₁, t₁)`. -/
theorem sliceTarget_hausdorff_zero (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hK : ∀ s ∈ Ioo (-t₁) t₁, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • E.curvature)) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ioo (-t₁) t₁, |s - 0| < δ →
      hausdorffDist (TranscendentalMain.euclideanImage (sliceTarget F θ E s))
        (TranscendentalMain.euclideanImage (sliceTarget F θ E 0)) < ε := by
  set a : ℝ := t₁ / 2 with ha
  have ha0 : 0 < a := half_pos ht₁
  have hK' : ∀ s ∈ Ioo 0 t₁, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ + a • E.curvature - s • E.curvature) := by
    intro s hs
    obtain ⟨κ, hκ⟩ := hK (s - a) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨κ, hκ.trans (congrArg RealBottChern.ofRepresentative ?_)⟩
    module
  have hH := sliceTarget_hausdorff (θ + a • E.curvature) E hK' (t := a)
    ⟨ha0, by linarith⟩
  intro ε hε
  obtain ⟨δ, hδ, hδH⟩ := hH ε hε
  refine ⟨min δ a, lt_min hδ ha0, fun s hs hsδ => ?_⟩
  have hs' : s + a ∈ Ioo 0 t₁ := by
    rw [sub_zero] at hsδ
    have h1 := (abs_lt.mp (hsδ.trans_le (min_le_right δ a)))
    constructor <;> linarith [h1.1, h1.2]
  have h := hδH (s + a) hs' (by
    rw [add_sub_cancel_right]
    rw [sub_zero] at hsδ
    exact hsδ.trans_le (min_le_left δ a))
  rwa [sliceTarget_add_smul, sliceTarget_add_smul, add_sub_cancel_right, sub_self] at h

/-- **`⊆` in `lma:Kahlerclassokounrest` for a Kähler class**. -/
theorem slice_zero_subset_of_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) 0 ⊆
      sliceTarget F θ E 0 := by
  obtain ⟨t₁, ht₁, hK⟩ := exists_pos_forall_kahler_sub_of_class hθ E.curvature
  intro y hy
  obtain ⟨D, hDI, hEW, hmetric⟩ := hE
  change Fin.cons 0 y ∈ tradOkounkovBody F θ at hy
  rw [tradOkounkovBody_eq_closure_image] at hy
  obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose φ hφ hφx using hx
  have hc : Tendsto (fun j => x j 0) atTop (𝓝 0) := by
    have := ((continuous_apply (0 : Fin (m + 1))).tendsto _).comp hxlim
    simpa [Function.comp_def] using this
  have hp : Tendsto (fun j => fun i : Fin m => x j i.succ) atTop (𝓝 y) := by
    have hcont : Continuous fun v : Fin (m + 1) → ℝ => fun i : Fin m => v i.succ :=
      continuous_pi fun i => continuous_apply _
    have := (hcont.tendsto _).comp hxlim
    simpa [Function.comp_def] using this
  have h0S : (0 : ℝ) ∈ Ioo (-t₁) t₁ := ⟨by linarith, ht₁⟩
  refine mem_of_hausdorff_limit (A := sliceTarget F θ E) (S := Ioo (-t₁) t₁)
    (fun s _ => isCompact_sliceTarget θ E s)
    (fun s hs => by obtain ⟨κ, hκ⟩ := hK s hs; exact sliceTarget_nonempty hκ) h0S
    (sliceTarget_hausdorff_zero θ E ht₁ hK) hc ?_ hp
  filter_upwards [hc.eventually (isOpen_Ioo.mem_nhds h0S)] with j hj
  refine ⟨hj, ?_⟩
  show (fun i : Fin m => x j i.succ) ∈ sliceTarget F θ E (x j 0)
  obtain ⟨-, h0, hw, htail⟩ := flagValuation_of_analytic F
    (gentleCurrents_subset_analyticCurrents θ (hφ j)) D hDI E hEW hmetric
  rw [hφx j] at h0 htail
  rw [h0] at hj ⊢
  obtain ⟨κ, hκ⟩ := hK _ hj
  have hΩ := gentleKahlerCurrents_nonempty_of_class_eq (F := F.tail) (restrictedKahlerForm κ)
    (restriction_class_eq hκ)
  rw [htail]
  exact closure_minimal (image_gentleKahlerCurrents_subset_tradOkounkovBody _)
    (isClosed_tradOkounkovBody _)
    (SGPT.Okounkov.TranscendentalDensity.densityStatement m F.tail _ hΩ _ hw)

/-- **`⊇` in `lma:Kahlerclassokounrest` for a Kähler class** (the extension theorem
`thm:CT-thm-refined'`). -/
theorem sliceTarget_zero_subset_of_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) :
    sliceTarget F θ E 0 ⊆
      TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) 0 := by
  set θ' := κ₀.form + (((0 : ℚ) : ℝ)) • E.curvature with hθ'def
  have hθ' : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ := by
    rw [hθ'def, Rat.cast_zero, zero_smul, add_zero, hθ]
  have hbody : tradOkounkovBody F θ = tradOkounkovBody F θ' :=
    tradOkounkovBody_eq_of_class_eq hθ'.symm
  have htail : sliceTarget F θ E 0 =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F κ₀.form) := by
    unfold sliceTarget
    rw [zero_smul, sub_zero]
    exact tradOkounkovBody_eq_of_class_eq (firstFlagRestriction_class_congr F hθ)
  rw [htail, hbody]
  have hΩY := gentleKahlerCurrents_nonempty_of_kahler (restrictedKahlerForm κ₀)
  have hΩ : (gentleKahlerCurrents θ').Nonempty :=
    gentleKahlerCurrents_nonempty_of_class_eq κ₀ (hθ'.trans hθ)
  have hclosed : IsClosed (TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ')
      (0 : ℝ)) :=
    (isClosed_tradOkounkovBody _).preimage (continuous_const.finCons continuous_id)
  rw [tradOkounkovBody_eq_closure_image]
  refine closure_minimal ?_ hclosed
  rintro _ ⟨w, hw, rfl⟩
  have hw' := SGPT.Okounkov.TranscendentalDensity.densityStatement m F.tail _ hΩY w
    (gentleCurrents_subset_analyticCurrents _ hw)
  refine (closure_minimal ?_ hclosed) hw'
  rintro _ ⟨w', hw'', rfl⟩
  have h := cons_mem_tradOkounkovBody_of_extension κ₀ hE (t := 0) le_rfl hΩ hw''
  change Fin.cons (0 : ℝ) (flagValuation F.tail w') ∈ tradOkounkovBody F θ'
  rw [hθ'def]
  simpa only [Rat.cast_zero] using h

/-- **`lma:Kahlerclassokounrest` for a Kähler class `β = {θ}`** (Step 2 of the book's proof):
`{y ∈ ℝ^{n-1} : (0, y) ∈ Δ_{Y•}(β)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(β|_{Y₁})`. -/
theorem slice_zero_eq_of_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hθ : TranscendentalMain.IsKahlerClass F (RealBottChern.ofRepresentative θ)) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) 0 =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F θ) := by
  obtain ⟨κ₀', hκ₀', hκ₀θ⟩ := hθ
  let κ₀ : KahlerBackground (m + 1) F.carrier := ⟨κ₀', hκ₀'⟩
  obtain ⟨E, hE⟩ := exists_isFirstDivisorUnitMetric F
  have htarget : sliceTarget F θ E 0 =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F θ) := by
    unfold sliceTarget
    rw [zero_smul, sub_zero]
  rw [← htarget]
  exact Subset.antisymm (slice_zero_subset_of_kahler (κ₀ := κ₀) hκ₀θ.symm hE)
    (sliceTarget_zero_subset_of_kahler (κ₀ := κ₀) hκ₀θ.symm hE)

end KahlerSlice

section Nef

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- A nef class plus a positive multiple of a Kähler class is a Kähler class. -/
theorem isKahlerClass_add_smul_of_nef {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ωK : KahlerBackground (m + 1) F.carrier} (hnef : NefWithRespectTo ωK θ) {ε : ℝ}
    (hε : 0 < ε) :
    TranscendentalMain.IsKahlerClass F (RealBottChern.ofRepresentative (θ + ε • ωK.form)) := by
  obtain ⟨f, hf, hsemi⟩ := NefMixedMass.exists_isSemipositive_of_nef hnef (half_pos hε)
  have hK := NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive ωK hsemi (half_pos hε)
  refine ⟨_, hK, ?_⟩
  have heq : θ + (ε / 2) • ωK.form + ManifoldTubePositivity.ddcClosedForm f hf +
      (ε / 2) • ωK.form = (θ + ε • ωK.form) + ManifoldTubePositivity.ddcClosedForm f hf := by
    have : ε = ε / 2 + ε / 2 := by ring
    conv_rhs => rw [this]
    module
  rw [heq]
  exact SGPT.Okounkov.TranscendentalLifting.ofRepresentative_add_ddc _ hf

/-- **`lma:Kahlerclassokounrest`** (big and nef classes): for a big class `β = {θ}` which is nef
(with respect to a Kähler form `ω`),
`{y ∈ ℝ^{n-1} : (0, y) ∈ Δ_{Y•}(β)} = ⋂_{ε > 0} Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((β + ε{ω})|_{Y₁})`;
the right-hand side is the book's `Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(β|_{Y₁})` in the sense of `def:generalPOB`
(Step 1 of the book's proof; `slice_zero_eq_of_nef_of_big_restriction` for `β|_{Y₁}` big,
`iInter_tradOkounkovBody_eq_generalPartialBody` for the comparison with `def:generalPOB`). -/
theorem slice_zero_eq_iInter_of_nef {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {ωK : KahlerBackground (m + 1) F.carrier} (hnef : NefWithRespectTo ωK θ) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) 0 =
      ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody F.tail
        (TranscendentalMain.firstFlagRestriction F (θ + ε • ωK.form)) := by
  have hslice : ∀ ε : ℝ, 0 < ε →
      TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F (θ + ε • ωK.form)) 0 =
        tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F (θ + ε • ωK.form)) :=
    fun ε hε => slice_zero_eq_of_kahler (isKahlerClass_add_smul_of_nef hnef hε)
  -- `Δ(β) = ⋂_{ε > 0} Δ(β + ε{ω})`
  have hinter : tradOkounkovBody F θ =
      ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody F (θ + ε • ωK.form) := by
    apply Subset.antisymm
    · refine subset_iInter₂ fun ε hε => PartialBody.tradOkounkovBody_subset_of_le ?_
      rw [add_sub_cancel_left]
      exact KahlerDomination.isSemipositive_smul ωK.isSemipositive hε.le
    · rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig]
      refine subset_iInter₂ fun q hq => ?_
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      -- `ε ω ≤ q ω_F` for `ε` small
      obtain ⟨C, hC, hCs⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
        F.omega ![-ωK.form]
      have hC₁ : (-ωK.form + C • F.omega.form).val.IsSemipositive := by simpa using hCs 0
      set ε : ℝ := q / C with hεdef
      have hε : 0 < ε := div_pos hq' hC
      refine (iInter₂_subset ε hε).trans (PartialBody.tradOkounkovBody_subset_of_le ?_)
      have heq : θ + (q : ℝ) • F.omega.form - (θ + ε • ωK.form) =
          ε • (-ωK.form + C • F.omega.form) := by
        rw [smul_add, smul_neg, smul_smul, hεdef, div_mul_cancel₀ _ hC.ne']
        abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul hC₁ hε.le
  rw [hinter]
  ext y
  simp only [TranscendentalMain.firstCoordinateSlice, mem_ofPred_eq, mem_iInter]
  refine forall₂_congr fun ε hε => ?_
  rw [← hslice ε hε]
  rfl

end Nef

section BigRestriction

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 2)}

/-- `(θ + ε ω)|_{Y₁} = θ|_{Y₁} + ε ω|_{Y₁}`. -/
theorem firstFlagRestriction_add_smul (θ η : ClosedRealOneOneForm (m + 2) F.carrier) (ε : ℝ) :
    TranscendentalMain.firstFlagRestriction F (θ + ε • η) =
      TranscendentalMain.firstFlagRestriction F θ +
        ε • TranscendentalMain.firstFlagRestriction F η := by
  have h := firstFlagRestriction_sub_smul (F := F) θ η (-ε)
  rw [neg_smul, sub_neg_eq_add, neg_smul, sub_neg_eq_add] at h
  exact h

/-- **`⋂_{ε > 0} Δ_{Y₁ ⊇ ⋯}(γ + ε{ω}|_{Y₁}) = Δ_{Y₁ ⊇ ⋯}(γ)`** for a big class `γ` on `Y₁`
(`thm:Okounkovtranmain` (4) on `Y₁`). -/
theorem iInter_tradOkounkovBody_tail_eq {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative
      (TranscendentalMain.firstFlagRestriction F θ)))
    (ωK : KahlerBackground (m + 2) F.carrier) :
    ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody F.tail
        (TranscendentalMain.firstFlagRestriction F (θ + ε • ωK.form)) =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F θ) := by
  set ωY : KahlerBackground (m + 1) F.tail.carrier := restrictedKahlerForm ωK with hωY
  have hωYf : ωY.form = TranscendentalMain.firstFlagRestriction F ωK.form := rfl
  simp_rw [firstFlagRestriction_add_smul, ← hωYf]
  apply Subset.antisymm
  · rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig]
    refine subset_iInter₂ fun q hq => ?_
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨C, hC, hCs⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
      F.tail.omega ![-ωY.form]
    have hC₁ : (-ωY.form + C • F.tail.omega.form).val.IsSemipositive := by simpa using hCs 0
    set ε : ℝ := q / C with hεdef
    have hε : 0 < ε := div_pos hq' hC
    refine (iInter₂_subset ε hε).trans (PartialBody.tradOkounkovBody_subset_of_le ?_)
    have heq : TranscendentalMain.firstFlagRestriction F θ + (q : ℝ) • F.tail.omega.form -
        (TranscendentalMain.firstFlagRestriction F θ + ε • ωY.form) =
          ε • (-ωY.form + C • F.tail.omega.form) := by
      rw [smul_add, smul_neg, smul_smul, hεdef, div_mul_cancel₀ _ hC.ne']
      abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul hC₁ hε.le
  · refine subset_iInter₂ fun ε hε => PartialBody.tradOkounkovBody_subset_of_le ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul ωY.isSemipositive hε.le

/-- **`lma:Kahlerclassokounrest`** when `β|_{Y₁}` is big (`n ≥ 2`): for a big and nef class
`β = {θ}`, `{y : (0, y) ∈ Δ_{Y•}(β)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(β|_{Y₁})` (bodies of `def:tradOk`). -/
theorem slice_zero_eq_of_nef_of_big_restriction {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {ωK : KahlerBackground (m + 2) F.carrier} (hnef : NefWithRespectTo ωK θ)
    (hbigY : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative
      (TranscendentalMain.firstFlagRestriction F θ))) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) 0 =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F θ) := by
  rw [slice_zero_eq_iInter_of_nef hbig hnef, iInter_tradOkounkovBody_tail_eq hbigY ωK]

end BigRestriction

section GeneralPOB

variable {m : ℕ} {G : OriginalFlagGeometry.{u} (m + 1)}

/-- **The right-hand side of `lma:Kahlerclassokounrest` in the sense of `def:generalPOB`**: let
`γ = {σ}` be a class on a compact Kähler manifold (here `Y₁` with its flag) and `T = σ + dd^c φ`
a current whose Kähler perturbations `T + ε ω` have minimal singularities in `γ + ε{ω}`
(every `(σ + ε ω)`-psh potential is more singular than `φ`). Then
`Δ(T) = ⋂_{ε > 0} Δ(γ + ε{ω})` (`def:generalPOB`, `thm:pobmain` (3) for each `ε`). -/
theorem iInter_tradOkounkovBody_eq_generalPartialBody {σ : ClosedRealOneOneForm (m + 1) G.carrier}
    {φ : G.carrier → EReal} (hφ : IsThetaPshPotential σ.val φ)
    (ωK : KahlerBackground (m + 1) G.carrier)
    (hmin : ∀ ε : ℝ, 0 < ε → ∀ ψ : G.carrier → EReal,
      IsThetaPshPotential (σ + ε • ωK.form).val ψ → SingularityLE ψ φ) :
    PartialBody.generalPartialBody G σ φ =
      ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody G (σ + ε • ωK.form) := by
  have hεK : ∀ ε : ℝ, 0 < ε →
      PartialBody.kahlerPartialBody G (σ + ε • ωK.form) φ = tradOkounkovBody G (σ + ε • ωK.form) := by
    intro ε hε
    have hK := PartialBody.isKahlerCurrentPotential_add_smul hφ ωK hε
    have hbigε : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative (σ + ε • ωK.form)) := by
      let : MeasurableSpace G.carrier := borel G.carrier
      have : BorelSpace G.carrier := ⟨rfl⟩
      have : CompactSpace G.carrier := G.compact
      have : ConnectedSpace G.carrier := G.connected
      obtain ⟨κ, hκ⟩ := hK
      exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr
        (PartialBody.isBigClass_of_isKahlerCurrentPotential ⟨κ, hκ⟩)
    rw [← PartialBody.generalPartialBody_eq_kahlerPartialBody hK]
    exact PartialBody.generalPartialBody_eq_tradOkounkovBody_of_minimal hbigε
      (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hK) (hmin ε hε)
  rw [PartialBody.generalPartialBody_eq_of_kahler hφ ωK]
  apply Subset.antisymm
  · refine subset_iInter₂ fun ε hε => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    have hj' : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
    refine (iInter_subset _ j).trans ?_
    rw [hεK _ hj']
    refine PartialBody.tradOkounkovBody_subset_of_le ?_
    have heq : σ + ε • ωK.form - (σ + ((j : ℝ) + 1)⁻¹ • ωK.form) =
        (ε - ((j : ℝ) + 1)⁻¹) • ωK.form := by module
    rw [heq]
    refine KahlerDomination.isSemipositive_smul ωK.isSemipositive ?_
    rw [inv_eq_one_div]
    linarith
  · refine subset_iInter fun j => ?_
    have hj' : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
    rw [hεK _ hj']
    exact iInter₂_subset _ hj'

/-- The hypothesis of `iInter_tradOkounkovBody_eq_generalPartialBody` holds for a potential
bounded from below: then `T` has bounded potential, and `T + ε ω` has minimal singularities. -/
theorem iInter_tradOkounkovBody_eq_generalPartialBody_of_bounded
    {σ : ClosedRealOneOneForm (m + 1) G.carrier} {φ : G.carrier → EReal}
    (hφ : IsThetaPshPotential σ.val φ) (ωK : KahlerBackground (m + 1) G.carrier)
    {C : ℝ} (hC : ∀ x, (C : EReal) ≤ φ x) :
    PartialBody.generalPartialBody G σ φ =
      ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody G (σ + ε • ωK.form) := by
  refine iInter_tradOkounkovBody_eq_generalPartialBody hφ ωK fun ε _ ψ hψ => ?_
  obtain ⟨A, hA⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hψ
  refine ⟨A - C, fun x _ => ?_⟩
  calc ψ x ≤ (A : EReal) := hA x
    _ = ((A - C : ℝ) : EReal) + (C : EReal) := by rw [← EReal.coe_add, sub_add_cancel]
    _ ≤ ((A - C : ℝ) : EReal) + φ x := add_le_add le_rfl (hC x)
    _ = φ x + ((A - C : ℝ) : EReal) := add_comm _ _

end GeneralPOB

end SGPT.Okounkov.Valuative
