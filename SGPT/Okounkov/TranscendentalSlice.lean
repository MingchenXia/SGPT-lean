import SGPT.Okounkov.TranscendentalSliceValuation
import SGPT.Okounkov.TranscendentalBodyHausdorff
import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Okounkov.TranscendentalCoreRepresentative
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

/-!
# Slices of the Okounkov body of a Kähler class

Source: the book's `thm:Okounkovtranmain` item 5 (chapter *The theory of Okounkov bodies*,
lines 1380--1400), **corrected** to Kähler classes (the book states it for every big class,
which is false, see `TranscendentalMain.SliceFormulaBookStatement` and blueprint
`tok:slice-erratum`); blueprint node `tok:slice-kahler` (chapter
`claude-okounkov-transcendental`; sub-lemmas in `claude-tok-slice.tex`). The proof follows
the extension argument of Darvas--Reboulet--Witt Nyström--Xia--Zhang (DRWNXZ),
*Transcendental Okounkov bodies*, Lemma 7.5.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag
`Y•`, and `α = {θ}` a Kähler class. Then there is `t₀ > 0` such that for every `t ∈ (0, t₀)`
and every unit metric `E` of `Y₁` (curvature `Θ_E ∈ {Y₁}`),

`{y ∈ ℝ^{n-1} : (t, y) ∈ Δ_{Y•}(α)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((θ - t Θ_E)|_{Y₁})`

(`kahlerSliceFormula`, the conjunct `KahlerSliceFormulaStatement` of the fixed target
`OkounkovTranMainStatement`). Here `t₀` is chosen so that `α - t{Y₁}` is a Kähler class for
`t ∈ (0, t₀)` (`exists_pos_forall_kahler_sub`; the class `{Y₁}` does not depend on `E`,
`ofRepresentative_curvature_eq`).

## Proof

Write `R(s) = Δ_{Y₁ ⊇ ⋯}((θ - s Θ_E)|_{Y₁})` for `s ∈ (0, t₀)`.

* `R(s)` is a nonempty compact set, and `s ↦ R(s)` is continuous for the Hausdorff metric
  (`sliceTarget_hausdorff`: `tok:hausdorff-continuity` on `Y₁`, package BODY, applied to the
  Kähler classes `(α - s{Y₁})|_{Y₁}`; trivial if `n = 1`).
* `⊆` (`slice_subset_sliceTarget`): a point `(t, y)` of `Δ(α)` is a limit of valuations
  `ν(T_k) = (t_k, ν(w_k))` of gentle currents, where `t_k = ν(T_k, Y₁)` and `w_k ∈
  𝒜(Y₁, (α - t_k{Y₁})|_{Y₁})` is the restriction of `T_k - t_k[Y₁]`
  (`tok:valuation-analytic`, package CORE); by `tok:density` on `Y₁`, `ν(w_k) ∈ R(t_k)`, and
  `R(t_k) → R(t)`.
* `⊇` for rational `t` (`sliceTarget_subset_slice_rat`): after changing the representative,
  `θ - t Θ_E = κ` is a Kähler form; `R(t)` is the closure of the valuations of the gentle
  Kähler currents `κ|_{Y₁} + dd^c w` (`tok:density` on `Y₁`), and each of them extends
  (`cons_mem_tradOkounkovBody_of_extension`, DRWNXZ Theorem 6.4) to a current of `α` with
  valuation `(t, ν(w))`.
* `⊇` for real `t` (`sliceTarget_subset_slice`): approximate `t` by rationals and use the
  Hausdorff continuity of `R` and the closedness of `Δ(α)`.

The blueprint route through `tok:slice-density` and the Hausdorff continuity of the slices of
`Δ(α)` (`ok:source-body-slice-continuity`) is replaced by the Hausdorff continuity of the
right-hand side, which needs neither.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalSlice

open Set Filter Metric
open scoped Topology Manifold ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore

section Metric

variable {k : ℕ}

/-- The sup distance on `ℝᵏ` is at most the Euclidean distance. -/
theorem dist_le_dist_symm_equiv (p y : Fin k → ℝ) :
    dist p y ≤ dist ((EuclideanSpace.equiv (Fin k) ℝ).symm p)
      ((EuclideanSpace.equiv (Fin k) ℝ).symm y) := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  have := PiLp.dist_apply_le ((EuclideanSpace.equiv (Fin k) ℝ).symm p)
    ((EuclideanSpace.equiv (Fin k) ℝ).symm y) i
  simpa using this

theorem isCompact_euclideanImage {A : Set (Fin k → ℝ)} (hA : IsCompact A) :
    IsCompact (TranscendentalMain.euclideanImage A) :=
  hA.image (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous

theorem hausdorffEDist_euclideanImage_ne_top {A B : Set (Fin k → ℝ)} (hA : IsCompact A)
    (hB : IsCompact B) (hA' : A.Nonempty) (hB' : B.Nonempty) :
    hausdorffEDist (TranscendentalMain.euclideanImage A)
      (TranscendentalMain.euclideanImage B) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded (hA'.image _) (hB'.image _)
    (isCompact_euclideanImage hA).isBounded (isCompact_euclideanImage hB).isBounded

/-- **Limits along a Hausdorff-continuous family**: if `A(s)` are nonempty compact sets with
`A(s) → A(t)` in the Hausdorff metric as `s → t` in `S`, `s_j → t`, `p_j ∈ A(s_j)` and
`p_j → y`, then `y ∈ A(t)`. -/
theorem mem_of_hausdorff_limit {A : ℝ → Set (Fin k → ℝ)} {S : Set ℝ} {t : ℝ}
    (hcpt : ∀ s ∈ S, IsCompact (A s)) (hne : ∀ s ∈ S, (A s).Nonempty) (ht : t ∈ S)
    (hH : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, |s - t| < δ →
      hausdorffDist (TranscendentalMain.euclideanImage (A s))
        (TranscendentalMain.euclideanImage (A t)) < ε)
    {s : ℕ → ℝ} {p : ℕ → Fin k → ℝ} {y : Fin k → ℝ} (hs : Tendsto s atTop (𝓝 t))
    (hsp : ∀ᶠ j in atTop, s j ∈ S ∧ p j ∈ A (s j)) (hpy : Tendsto p atTop (𝓝 y)) :
    y ∈ A t := by
  rw [← (hcpt t ht).isClosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδH⟩ := hH (ε / 2) (half_pos hε)
  have h1 : ∀ᶠ j in atTop, |s j - t| < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hs) δ hδ] with j hj
    rwa [Real.dist_eq] at hj
  have h2 : ∀ᶠ j in atTop, dist y (p j) < ε / 2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hpy) (ε / 2) (half_pos hε)] with j hj
    rwa [dist_comm] at hj
  obtain ⟨j, hj1, ⟨hjS, hjA⟩, hj2⟩ := (h1.and (hsp.and h2)).exists
  obtain ⟨b', hb', hdist⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_image_of_mem _ hjA)
    (hδH (s j) hjS hj1)
    (hausdorffEDist_euclideanImage_ne_top (hcpt _ hjS) (hcpt t ht) (hne _ hjS) (hne t ht))
  obtain ⟨b, hb, rfl⟩ := hb'
  refine ⟨b, hb, ?_⟩
  calc dist y b ≤ dist y (p j) + dist (p j) b := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hj2 ((dist_le_dist_symm_equiv _ _).trans_lt hdist)
    _ = ε := add_halves ε

/-- **Approximation along a Hausdorff-continuous family**: every point of `A(t)` is close to
points of `A(s)` for `s` close to `t`. -/
theorem exists_near_of_hausdorff {A : ℝ → Set (Fin k → ℝ)} {S : Set ℝ} {t : ℝ}
    (hcpt : ∀ s ∈ S, IsCompact (A s)) (hne : ∀ s ∈ S, (A s).Nonempty) (ht : t ∈ S)
    (hH : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, |s - t| < δ →
      hausdorffDist (TranscendentalMain.euclideanImage (A s))
        (TranscendentalMain.euclideanImage (A t)) < ε)
    {y : Fin k → ℝ} (hy : y ∈ A t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ S, |s - t| < δ → ∃ p ∈ A s, dist p y < ε := by
  obtain ⟨δ, hδ, hδH⟩ := hH ε hε
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  obtain ⟨x, hx, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_image_of_mem _ hy)
    (hδH s hs hst)
    (hausdorffEDist_euclideanImage_ne_top (hcpt s hs) (hcpt t ht) (hne s hs) (hne t ht))
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, hp, (dist_le_dist_symm_equiv _ _).trans_lt hxy⟩

end Metric

section Kahler

/-- A Kähler form `κ` has gentle Kähler currents: `Ω({κ}) ≠ ∅`. -/
theorem gentleKahlerCurrents_nonempty_of_kahler {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (κ : KahlerBackground n X) : (gentleKahlerCurrents κ.form).Nonempty := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have heq : κ.form - (KahlerBackground.smul hhalf κ).form =
      (KahlerBackground.smul hhalf κ).form := by
    rw [KahlerBackground.smul_form]
    module
  have h0 : IsThetaPshPotential (κ.form - (KahlerBackground.smul hhalf κ).form).val
      (fun _ => (0 : EReal)) := by
    rw [heq]
    exact PluripolarCapacityDichotomy.isThetaPshPotential_zero _
  obtain ⟨ψ, hψ, -⟩ := SGPT.Okounkov.TranscendentalBody.exists_mem_gentleKahlerCurrents_ge h0
  exact ⟨ψ, hψ⟩

/-- `Ω(ξ) ≠ ∅` for a Kähler class `ξ = {θ}`. -/
theorem gentleKahlerCurrents_nonempty_of_class_eq {n : ℕ} {F : OriginalFlagGeometry.{u} n}
    {θ : ClosedRealOneOneForm n F.carrier} (κ : KahlerBackground n F.carrier)
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ.form) :
    (gentleKahlerCurrents θ).Nonempty := by
  obtain ⟨ψ, hψ⟩ := gentleKahlerCurrents_nonempty_of_kahler κ
  have hmem : flagValuation F ψ ∈ flagValuation F '' gentleKahlerCurrents θ := by
    rw [image_gentleKahlerCurrents_eq_of_class_eq h]
    exact ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', -⟩ := hmem
  exact ⟨ψ', hψ'⟩

/-- `r ω + d ζ ≥ 0` if `±ζ + C ω ≥ 0` and `|d| C ≤ r`. -/
theorem isSemipositive_smul_add_smul {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (w₀ : KahlerBackground n X)
    {ζ : ClosedRealOneOneForm n X} {C r d : ℝ}
    (h₁ : (ζ + C • w₀.form).val.IsSemipositive) (h₂ : (-ζ + C • w₀.form).val.IsSemipositive)
    (hd : |d| * C ≤ r) : (r • w₀.form + d • ζ).val.IsSemipositive := by
  rcases le_or_gt 0 d with hd0 | hd0
  · rw [abs_of_nonneg hd0] at hd
    have heq : r • w₀.form + d • ζ = d • (ζ + C • w₀.form) + (r - d * C) • w₀.form := by
      module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul h₁ hd0)
      (KahlerDomination.isSemipositive_smul w₀.isSemipositive (by linarith))
  · rw [abs_of_neg hd0] at hd
    have heq : r • w₀.form + d • ζ = (-d) • (-ζ + C • w₀.form) + (r + d * C) • w₀.form := by
      module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul h₂ (by linarith))
      (KahlerDomination.isSemipositive_smul w₀.isSemipositive (by linarith))

end Kahler

section Slice

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable (F) in
/-- The right side `Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((θ - s Θ_E)|_{Y₁})` of the slice formula. -/
def sliceTarget (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (s : ℝ) : Set (Fin m → ℝ) :=
  tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F (θ - s • E.curvature))

theorem firstFlagRestriction_sub_smul (θ η : ClosedRealOneOneForm (m + 1) F.carrier) (s : ℝ) :
    TranscendentalMain.firstFlagRestriction F (θ - s • η) =
      TranscendentalMain.firstFlagRestriction F θ -
        s • TranscendentalMain.firstFlagRestriction F η := by
  unfold TranscendentalMain.firstFlagRestriction
  exact (SGPT.Okounkov.TranscendentalBody.pullback_sub' _ θ (s • η)).trans
    (congrArg (fun z => _ - z) (SGPT.Okounkov.TranscendentalBody.pullback_smul' _ s η))

/-- The restriction of a class containing the Kähler form `κ` contains the Kähler form
`κ|_{Y₁}`. -/
theorem restriction_class_eq {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ : KahlerBackground (m + 1) F.carrier}
    (h : RealBottChern.ofRepresentative κ.form = RealBottChern.ofRepresentative θ) :
    RealBottChern.ofRepresentative (TranscendentalMain.firstFlagRestriction F θ) =
      RealBottChern.ofRepresentative (restrictedKahlerForm κ).form :=
  firstFlagRestriction_class_congr F h.symm

theorem isCompact_sliceTarget (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (s : ℝ) :
    IsCompact (sliceTarget F θ E s) :=
  SGPT.Okounkov.TranscendentalBody.isCompact_tradOkounkovBody _

theorem sliceTarget_nonempty {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} {s : ℝ}
    {κ : KahlerBackground (m + 1) F.carrier}
    (h : RealBottChern.ofRepresentative κ.form =
      RealBottChern.ofRepresentative (θ - s • E.curvature)) :
    (sliceTarget F θ E s).Nonempty := by
  obtain ⟨ψ, hψ⟩ := gentleKahlerCurrents_nonempty_of_class_eq (F := F.tail)
    (restrictedKahlerForm κ) (restriction_class_eq h)
  exact ⟨_, image_gentleKahlerCurrents_subset_tradOkounkovBody _ ⟨ψ, hψ, rfl⟩⟩

/-- **The right side is Hausdorff continuous in `t`** on an interval where `α - t{Y₁}` is a
Kähler class (`tok:hausdorff-continuity` on `Y₁`). -/
theorem sliceTarget_hausdorff (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) {t₀ : ℝ}
    (hK : ∀ s ∈ Ioo 0 t₀, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • E.curvature))
    {t : ℝ} (ht : t ∈ Ioo 0 t₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Ioo 0 t₀, |s - t| < δ →
      hausdorffDist (TranscendentalMain.euclideanImage (sliceTarget F θ E s))
        (TranscendentalMain.euclideanImage (sliceTarget F θ E t)) < ε := by
  intro ε hε
  cases m with
  | zero =>
      refine ⟨1, one_pos, fun s hs _ => ?_⟩
      obtain ⟨κs, hκs⟩ := hK s hs
      obtain ⟨κt, hκt⟩ := hK t ht
      obtain ⟨a, ha⟩ := sliceTarget_nonempty hκs
      obtain ⟨b, hb⟩ := sliceTarget_nonempty hκt
      have hle : hausdorffDist (TranscendentalMain.euclideanImage (sliceTarget F θ E s))
          (TranscendentalMain.euclideanImage (sliceTarget F θ E t)) ≤ 0 := by
        refine hausdorffDist_le_of_mem_dist le_rfl (fun x _ => ?_) (fun x _ => ?_)
        · exact ⟨_, mem_image_of_mem _ hb, by rw [Subsingleton.elim x _, dist_self]⟩
        · exact ⟨_, mem_image_of_mem _ ha, by rw [Subsingleton.elim x _, dist_self]⟩
      linarith
  | succ m =>
      obtain ⟨κt, hκt⟩ := hK t ht
      have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative
          (TranscendentalMain.firstFlagRestriction F (θ - t • E.curvature))) := by
        rw [restriction_class_eq hκt]
        exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr
          (PluripolarCapacityDichotomy.isBigClass_kahler _)
      obtain ⟨r, hr, hrH⟩ := SGPT.Okounkov.TranscendentalBody.exists_hausdorffDist_lt hbig hε
      set η₀ := TranscendentalMain.firstFlagRestriction F E.curvature
      obtain ⟨C, hC, hCs⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
        F.tail.omega ![η₀, -η₀]
      have hC₁ : (η₀ + C • F.tail.omega.form).val.IsSemipositive := by simpa using hCs 0
      have hC₂ : (-η₀ + C • F.tail.omega.form).val.IsSemipositive := by simpa using hCs 1
      refine ⟨r / C, div_pos hr hC, fun s _ hst => ?_⟩
      have hd : |t - s| * C ≤ r := by
        rw [abs_sub_comm]
        have := (lt_div_iff₀ hC).mp hst
        linarith
      have hd' : |-(t - s)| * C ≤ r := by rwa [abs_neg]
      have key : TranscendentalMain.firstFlagRestriction F (θ - t • E.curvature) +
          (t - s) • η₀ = TranscendentalMain.firstFlagRestriction F (θ - s • E.curvature) := by
        rw [firstFlagRestriction_sub_smul, firstFlagRestriction_sub_smul]
        module
      have h := hrH ((t - s) • η₀)
        (isSemipositive_smul_add_smul F.tail.omega hC₁ hC₂ hd)
        (by
          have := isSemipositive_smul_add_smul F.tail.omega hC₁ hC₂ hd'
          rwa [neg_smul, ← sub_eq_add_neg] at this)
      rw [key] at h
      exact h

/-- **`⊆` in the slice formula** (blueprint `tok:slice-kahler`). -/
theorem slice_subset_sliceTarget (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t₀ : ℝ}
    (hK : ∀ s ∈ Ioo 0 t₀, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • E.curvature))
    {t : ℝ} (ht : t ∈ Ioo 0 t₀) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) t ⊆
      sliceTarget F θ E t := by
  intro y hy
  obtain ⟨D, hDI, hEW, hmetric⟩ := hE
  change Fin.cons t y ∈ tradOkounkovBody F θ at hy
  rw [tradOkounkovBody_eq_closure_image] at hy
  obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose φ hφ hφx using hx
  have hc : Tendsto (fun j => x j 0) atTop (𝓝 t) := by
    have := ((continuous_apply (0 : Fin (m + 1))).tendsto _).comp hxlim
    simpa [Function.comp_def] using this
  have hp : Tendsto (fun j => fun i : Fin m => x j i.succ) atTop (𝓝 y) := by
    have hcont : Continuous fun v : Fin (m + 1) → ℝ => fun i : Fin m => v i.succ :=
      continuous_pi fun i => continuous_apply _
    have := (hcont.tendsto _).comp hxlim
    simpa [Function.comp_def] using this
  refine mem_of_hausdorff_limit (A := sliceTarget F θ E) (S := Ioo 0 t₀)
    (fun s _ => isCompact_sliceTarget θ E s)
    (fun s hs => by obtain ⟨κ, hκ⟩ := hK s hs; exact sliceTarget_nonempty hκ) ht
    (sliceTarget_hausdorff θ E hK ht) hc ?_ hp
  filter_upwards [hc.eventually (isOpen_Ioo.mem_nhds ht)] with j hj
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

/-- **`⊇` in the slice formula for rational `t`** (blueprint `tok:slice-kahler`): the extension
argument. -/
theorem sliceTarget_subset_slice_rat {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t : ℚ} (ht : 0 < (t : ℝ))
    {κ : KahlerBackground (m + 1) F.carrier}
    (hκ : RealBottChern.ofRepresentative κ.form =
      RealBottChern.ofRepresentative (θ - (t : ℝ) • E.curvature)) :
    sliceTarget F θ E t ⊆ TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) t := by
  set θ' := κ.form + (t : ℝ) • E.curvature with hθ'def
  have hθ' : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ := by
    rw [hθ'def, RealBottChern.ofRepresentative_add, hκ, ← RealBottChern.ofRepresentative_add,
      sub_add_cancel]
  have hbody : tradOkounkovBody F θ = tradOkounkovBody F θ' :=
    tradOkounkovBody_eq_of_class_eq hθ'.symm
  have htail : sliceTarget F θ E t =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F κ.form) :=
    tradOkounkovBody_eq_of_class_eq (firstFlagRestriction_class_congr F hκ.symm)
  rw [htail, hbody]
  have hΩY := gentleKahlerCurrents_nonempty_of_kahler (restrictedKahlerForm κ)
  have hΩ : (gentleKahlerCurrents θ').Nonempty :=
    gentleKahlerCurrents_nonempty_of_class_eq κ₀ (hθ'.trans hθ)
  have hclosed : IsClosed (TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ')
      (t : ℝ)) :=
    (isClosed_tradOkounkovBody _).preimage (continuous_const.finCons continuous_id)
  rw [tradOkounkovBody_eq_closure_image]
  refine closure_minimal ?_ hclosed
  rintro _ ⟨w, hw, rfl⟩
  have hw' := SGPT.Okounkov.TranscendentalDensity.densityStatement m F.tail _ hΩY w
    (gentleCurrents_subset_analyticCurrents _ hw)
  refine (closure_minimal ?_ hclosed) hw'
  rintro _ ⟨w', hw'', rfl⟩
  exact cons_mem_tradOkounkovBody_of_extension κ hE (by exact_mod_cast ht.le) hΩ hw''

/-- **`⊇` in the slice formula** (blueprint `tok:slice-kahler`): rational approximation and
the Hausdorff continuity of the right side. -/
theorem sliceTarget_subset_slice {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t₀ : ℝ}
    (hK : ∀ s ∈ Ioo 0 t₀, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • E.curvature))
    {t : ℝ} (ht : t ∈ Ioo 0 t₀) :
    sliceTarget F θ E t ⊆ TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) t := by
  intro y hy
  change Fin.cons t y ∈ tradOkounkovBody F θ
  rw [← (isClosed_tradOkounkovBody _).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := exists_near_of_hausdorff (A := sliceTarget F θ E) (S := Ioo 0 t₀)
    (fun s _ => isCompact_sliceTarget θ E s)
    (fun s hs => by obtain ⟨κ, hκ⟩ := hK s hs; exact sliceTarget_nonempty hκ) ht
    (sliceTarget_hausdorff θ E hK ht) hy hε
  have hη : 0 < min δ ε := lt_min hδ hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (max_lt (sub_lt_self t hη) ht.1 : max (t - min δ ε) 0 < t)
  have hqS : (q : ℝ) ∈ Ioo 0 t₀ := ⟨lt_of_le_of_lt (le_max_right _ _) hq1, hq2.trans ht.2⟩
  have hqt : |(q : ℝ) - t| < min δ ε := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith [le_max_left (t - min δ ε) 0]
  obtain ⟨p, hp, hpy⟩ := hnear q hqS (hqt.trans_le (min_le_left _ _))
  obtain ⟨κ, hκ⟩ := hK q hqS
  have hmem := sliceTarget_subset_slice_rat hθ hE hqS.1 hκ hp
  refine ⟨Fin.cons (q : ℝ) p, hmem, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Real.dist_eq]
    rw [abs_sub_comm]
    exact hqt.trans_le (min_le_right _ _)
  · simp only [Fin.cons_succ]
    rw [dist_comm]
    exact (dist_le_pi_dist p y j).trans_lt hpy

/-- **The slice formula on an interval of Kähler classes** (blueprint `tok:slice-kahler`): if
`α = {θ}` is a Kähler class, `E` a unit metric of `Y₁` and `α - s{Y₁}` is a Kähler class for
every `s ∈ (0, t₀)`, then for every `t ∈ (0, t₀)`,
`{y : (t, y) ∈ Δ_{Y•}(α)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((θ - t Θ_E)|_{Y₁})`. -/
theorem slice_eq_sliceTarget {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ₀ : KahlerBackground (m + 1) F.carrier}
    (hθ : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ₀.form)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t₀ : ℝ}
    (hK : ∀ s ∈ Ioo 0 t₀, ∃ κ : KahlerBackground (m + 1) F.carrier,
      RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative (θ - s • E.curvature))
    {t : ℝ} (ht : t ∈ Ioo 0 t₀) :
    TranscendentalMain.firstCoordinateSlice (tradOkounkovBody F θ) t =
      tradOkounkovBody F.tail (TranscendentalMain.firstFlagRestriction F (θ - t • E.curvature)) :=
  Subset.antisymm (slice_subset_sliceTarget θ hE hK ht) (sliceTarget_subset_slice hθ hE hK ht)

end Slice

/-- **Source `thm:Okounkovtranmain` (5), corrected to Kähler classes** (blueprint
`tok:slice-kahler`; the conjunct `KahlerSliceFormulaStatement` of the fixed target
`OkounkovTranMainStatement`): for a Kähler class `α = {θ}` there is `t₀ > 0` such that for
every `t ∈ (0, t₀)` and every unit metric `E` of `Y₁`,
`{y : (t, y) ∈ Δ_{Y•}(α)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((θ - t Θ_E)|_{Y₁})`. -/
theorem kahlerSliceFormula {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.KahlerSliceFormulaStatement F := by
  intro θ hθK
  obtain ⟨κ₀', hκ₀', hκ₀θ⟩ := hθK
  let κ₀ : KahlerBackground (m + 1) F.carrier := ⟨κ₀', hκ₀'⟩
  by_cases hex : ∃ E₀, TranscendentalMain.IsFirstDivisorUnitMetric F E₀
  · obtain ⟨E₀, hE₀⟩ := hex
    obtain ⟨t₀, ht₀, hkah⟩ := exists_pos_forall_kahler_sub κ₀ E₀.curvature
    refine ⟨t₀, ht₀, fun t ht E hE => ?_⟩
    have hK : ∀ s ∈ Ioo 0 t₀, ∃ κ : KahlerBackground (m + 1) F.carrier,
        RealBottChern.ofRepresentative κ.form =
          RealBottChern.ofRepresentative (θ - s • E.curvature) := by
      intro s hs
      obtain ⟨κ, hκ⟩ := hkah s hs
      refine ⟨κ, ?_⟩
      rw [hκ, sub_eq_add_neg, sub_eq_add_neg, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
        RealBottChern.ofRepresentative_neg, RealBottChern.ofRepresentative_smul,
        RealBottChern.ofRepresentative_smul, ofRepresentative_curvature_eq hE₀ hE]
      exact congrArg (· + _) hκ₀θ
    exact slice_eq_sliceTarget (κ₀ := κ₀) hκ₀θ.symm hE hK ht
  · exact ⟨1, one_pos, fun t _ E hE => absurd ⟨E, hE⟩ hex⟩

end SGPT.Okounkov.TranscendentalSlice
