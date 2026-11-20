import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false

/-!
# The area bound for a map with bounded fibres

Mathlib's change-of-variables formula
`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` needs the map to be
INJECTIVE on the set of integration.  A branched covering is not, and that is
exactly the situation of Demailly's local finite-volume theorem (CADG III.2.6):
the coordinate projection `π_I` restricted to an analytic subvariety is finite
but not injective.

This module supplies the multiplicity form that such an argument needs.  The
route is the standard one:

* where the Jacobian does not vanish, the inverse function theorem makes the map
  injective on a neighbourhood (`exists_isOpen_injOn`);
* the resulting cover of `{det ≠ 0}` has a countable subcover (the space is
  second countable), and `disjointed` turns it into a countable measurable
  PARTITION of a measurable `S` on each block of which the map is injective
  (`exists_disjointed_injOn`);  no openness of `S` is needed, only strict
  differentiability at each of its points;
* on the rest of `S` the integrand vanishes, so the integral is the sum of the
  measures of the images of the blocks (`lintegral_abs_det_eq_tsum_image`);
* and a family of measurable subsets of `Δ` covering ALMOST EVERY point at most
  `N` times has total measure at most `N · μ Δ` (`tsum_measure_le_of_card_le`).

The conclusion, `sum_lintegral_abs_det_le`, is stated for a FINITE
FAMILY of pairwise unrelated maps, because that is how the pieces of a
regular-piece family arrive: the fibre hypothesis is on the total number of
preimages of a point across the whole family.

Nothing here mentions this project: the file is pure measure theory.
-/

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound

/-- **A family of measurable subsets of `Δ` covering each point at most `N`
times has total measure at most `N · μ Δ`.** -/
theorem tsum_measure_le_of_card_le {X : Type*} [MeasurableSpace X] {ι : Type*}
    [Countable ι] (μ : Measure X)
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) {Δ : Set X} (hΔ : MeasurableSet Δ)
    (hsub : ∀ i, A i ⊆ Δ) {N : ℕ}
    (hN : ∀ᵐ y ∂μ, y ∈ Δ → ∀ s : Finset ι, (∀ i ∈ s, y ∈ A i) → s.card ≤ N) :
    ∑' i, μ (A i) ≤ (N : ℝ≥0∞) * μ Δ := by
  classical
  have hmeas : ∀ i, Measurable ((A i).indicator (fun _ => (1 : ℝ≥0∞))) := fun i =>
    measurable_one.indicator (hA i)
  have h1 : ∑' i, μ (A i) = ∫⁻ y, ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := by
    rw [lintegral_tsum (fun i => (hmeas i).aemeasurable)]
    exact tsum_congr fun i => (lintegral_indicator_one (hA i)).symm
  have h2 : ∀ᵐ y ∂μ, ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) y ≤
      Δ.indicator (fun _ => (N : ℝ≥0∞)) y := by
    filter_upwards [hN] with y hyN
    by_cases hy : y ∈ Δ
    · rw [Set.indicator_of_mem hy, ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s => ?_
      have hcard : (s.filter (fun i => y ∈ A i)).card ≤ N :=
        hyN hy _ fun i hi => (Finset.mem_filter.1 hi).2
      have hsum : ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) y =
          ((s.filter (fun i => y ∈ A i)).card : ℝ≥0∞) := by
        simp [Set.indicator_apply, Finset.sum_boole]
      rw [hsum]
      exact_mod_cast Nat.cast_le.2 hcard
    · have hzero : ∀ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) y = 0 := fun i =>
        Set.indicator_of_notMem (fun h => hy (hsub i h)) _
      simp [hzero, Set.indicator_of_notMem hy]
  calc ∑' i, μ (A i)
      = ∫⁻ y, ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := h1
    _ ≤ ∫⁻ y, Δ.indicator (fun _ => (N : ℝ≥0∞)) y ∂μ := lintegral_mono_ae h2
    _ = (N : ℝ≥0∞) * μ Δ := lintegral_indicator_const hΔ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local injectivity from a nonvanishing Jacobian.**  A map with an invertible
strict derivative at `x` is injective on a neighbourhood of `x`. -/
theorem exists_isOpen_injOn {f : E → E} {f' : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f f' x) (hdet : f'.det ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  have hf2 : HasStrictFDerivAt f
      ((f'.toContinuousLinearEquivOfDetNeZero hdet : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
    simpa using hf
  refine ⟨(hf2.toOpenPartialHomeomorph f).source, (hf2.toOpenPartialHomeomorph f).open_source,
    hf2.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hf2.toOpenPartialHomeomorph f).injOn
  simpa using this

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- **A countable measurable partition adapted to `f`.**  A measurable set `S` at
every point of which `f` is strictly differentiable carries a countable pairwise disjoint family
of measurable subsets, on each of which `f` is injective, whose union contains
every point of `S` at which the Jacobian does not vanish. -/
theorem exists_disjointed_injOn {f : E → E} {f' : E → E →L[ℝ] E} {S : Set E}
    (hS : MeasurableSet S) (hf : ∀ x ∈ S, HasStrictFDerivAt f (f' x) x) :
    ∃ D : ℕ → Set E, (∀ n, MeasurableSet (D n)) ∧ (∀ n, D n ⊆ S) ∧
      Pairwise (Disjoint on D) ∧ (∀ n, InjOn f (D n)) ∧
      {x | x ∈ S ∧ (f' x).det ≠ 0} ⊆ ⋃ n, D n := by
  classical
  set R : Set E := {x | x ∈ S ∧ (f' x).det ≠ 0} with hRdef
  have hchoice : ∀ x : R, ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧ InjOn f U := by
    rintro ⟨x, hxS, hxdet⟩
    exact exists_isOpen_injOn (hf x hxS) hxdet
  choose U hUo hxU hUinj using hchoice
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have : Countable T := hTc.to_subtype
  obtain ⟨g, hg⟩ := exists_surjective_nat (Option T)
  set V : ℕ → Set E := fun m => (g m).elim ∅ (fun i => U i.1) with hVdef
  have hVopen : ∀ m, IsOpen (V m) := by
    intro m
    rcases hgm : g m with _ | i
    · simp [hVdef, hgm]
    · simpa [hVdef, hgm] using hUo i.1
  have hVinj : ∀ m, InjOn f (V m) := by
    intro m
    rcases hgm : g m with _ | i
    · simp [hVdef, hgm]
    · simpa [hVdef, hgm] using hUinj i.1
  have hRV : R ⊆ ⋃ m, V m := by
    intro x hx
    have hxU' : x ∈ ⋃ i, U i := mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    rw [← hTU] at hxU'
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.1 hxU'
    obtain ⟨m, hm⟩ := hg (some ⟨i, hiT⟩)
    exact mem_iUnion.2 ⟨m, by simp [hVdef, hm, hxi]⟩
  refine ⟨fun n => disjointed V n ∩ S,
    fun n => (MeasurableSet.disjointed (fun m => (hVopen m).measurableSet) n).inter hS,
    fun n => inter_subset_right,
    fun a b hab => ((disjoint_disjointed V hab).mono inter_subset_left inter_subset_left),
    fun n => (hVinj n).mono ((inter_subset_left).trans (disjointed_subset V n)), ?_⟩
  intro x hx
  have hxW : x ∈ ⋃ m, disjointed V m := by rw [iUnion_disjointed]; exact hRV hx
  obtain ⟨m, hm⟩ := mem_iUnion.1 hxW
  exact mem_iUnion.2 ⟨m, hm, hx.1⟩

/-- **The Jacobian integral as the total measure of the images of the blocks.**
Points where the Jacobian vanishes contribute nothing, and on the rest the
change-of-variables formula applies block by block. -/
theorem lintegral_abs_det_eq_tsum_image (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {f' : E → E →L[ℝ] E} {S : Set E} (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, HasStrictFDerivAt f (f' x) x)
    {D : ℕ → Set E} (hD : ∀ n, MeasurableSet (D n)) (hDS : ∀ n, D n ⊆ S)
    (hdisj : Pairwise (Disjoint on D)) (hinj : ∀ n, InjOn f (D n))
    (hcov : {x | x ∈ S ∧ (f' x).det ≠ 0} ⊆ ⋃ n, D n) :
    ∫⁻ x in S, ENNReal.ofReal |(f' x).det| ∂μ = ∑' n, μ (f '' D n) := by
  have hWm : MeasurableSet (⋃ n, D n) := MeasurableSet.iUnion hD
  have hWS : (⋃ n, D n) ⊆ S := iUnion_subset hDS
  have hsplit := lintegral_inter_add_sdiff (μ := μ)
    (fun x => ENNReal.ofReal |(f' x).det|) S hWm
  have hSW : S ∩ (⋃ n, D n) = ⋃ n, D n := inter_eq_self_of_subset_right hWS
  have hzero : ∫⁻ x in S \ (⋃ n, D n), ENNReal.ofReal |(f' x).det| ∂μ = 0 := by
    rw [setLIntegral_congr_fun (hS.diff hWm)
      (g := fun _ => (0 : ℝ≥0∞)) (fun x hx => ?_), lintegral_zero]
    have hdet : (f' x).det = 0 := by
      by_contra h
      exact hx.2 (hcov ⟨hx.1, h⟩)
    simp [hdet]
  rw [hSW, hzero, add_zero] at hsplit
  rw [← hsplit, lintegral_iUnion hD hdisj]
  refine tsum_congr fun n => ?_
  exact lintegral_abs_det_fderiv_eq_addHaar_image μ (hD n)
    (fun x hx => (hf x (hDS n hx)).hasFDerivAt.hasFDerivWithinAt) (hinj n)

/-- **The area bound with multiplicity, for a finite family of maps.**  If each
`f i` is strictly differentiable at every point of the measurable set `S i`, sends `S i`
into a measurable set `Δ`, and the total number of preimages in the family of
almost every point of `Δ` is at most `N`, then the total Jacobian integral is at
most `N · μ Δ`.

Mathlib's change-of-variables formula needs injectivity; this is the branched
version, and it is what bounds the volume of an analytic subvariety by the sheet
number of a finite projection. -/
theorem sum_lintegral_abs_det_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] {S : ι → Set E} {f : ι → E → E} {f' : ι → E → E →L[ℝ] E}
    (hS : ∀ i, MeasurableSet (S i))
    (hf : ∀ i, ∀ x ∈ S i, HasStrictFDerivAt (f i) (f' i x) x)
    {Δ : Set E} (hΔ : MeasurableSet Δ) (hmaps : ∀ i, MapsTo (f i) (S i) Δ)
    {N : ℕ} (hN : ∀ᵐ y ∂μ, y ∈ Δ → ∑ i, (S i ∩ f i ⁻¹' {y}).encard ≤ (N : ℕ∞)) :
    ∑ i, ∫⁻ x in S i, ENNReal.ofReal |(f' i x).det| ∂μ ≤ (N : ℝ≥0∞) * μ Δ := by
  classical
  choose D hDm hDS hDdisj hDinj hDcov using fun i => exists_disjointed_injOn (hS i) (hf i)
  set A : ι × ℕ → Set E := fun p => f p.1 '' D p.1 p.2 with hAdef
  have hAm : ∀ p : ι × ℕ, MeasurableSet (A p) := fun p =>
    measurable_image_of_fderivWithin (hDm p.1 p.2)
      (fun x hx => (hf p.1 x (hDS p.1 p.2 hx)).hasFDerivAt.hasFDerivWithinAt) (hDinj p.1 p.2)
  have hAsub : ∀ p : ι × ℕ, A p ⊆ Δ := by
    rintro p _ ⟨x, hx, rfl⟩
    exact hmaps p.1 (hDS p.1 p.2 hx)
  have hcount : ∀ᵐ y ∂μ, y ∈ Δ → ∀ s : Finset (ι × ℕ), (∀ p ∈ s, y ∈ A p) → s.card ≤ N := by
    filter_upwards [hN] with y hyN hy s hs
    have hch : ∀ p ∈ s, ∃ x, x ∈ D p.1 p.2 ∧ f p.1 x = y := fun p hp => hs p hp
    choose! x hxD hxf using hch
    have hfib : ∀ i : ι,
        ((s.filter (fun p => p.1 = i)).card : ℕ∞) ≤ (S i ∩ f i ⁻¹' {y}).encard := by
      intro i
      have hinjOn : Set.InjOn x (s.filter (fun p => p.1 = i)) := by
        intro p hp q hq hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
        have hp1 : p.1 = i := hp.2
        have hq1 : q.1 = i := hq.2
        have hpD : x p ∈ D i p.2 := hp1 ▸ hxD p hp.1
        have hqD : x q ∈ D i q.2 := hq1 ▸ hxD q hq.1
        have hsnd : p.2 = q.2 := by
          by_contra hne
          have := hDdisj i hne
          exact (Set.disjoint_left.1 this hpD) (hxy ▸ hqD)
        exact Prod.ext (hp1.trans hq1.symm) hsnd
      have hcard : ((s.filter (fun p => p.1 = i)).image x).card =
          (s.filter (fun p => p.1 = i)).card := Finset.card_image_of_injOn hinjOn
      have hsubset : (((s.filter (fun p => p.1 = i)).image x : Finset E) : Set E) ⊆
          S i ∩ f i ⁻¹' {y} := by
        intro z hz
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
        obtain ⟨p, hp, rfl⟩ := hz
        have hp' := Finset.mem_filter.1 hp
        have hp1 : p.1 = i := hp'.2
        refine ⟨hp1 ▸ hDS p.1 p.2 (hxD p hp'.1), ?_⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact hp1 ▸ hxf p hp'.1
      calc ((s.filter (fun p => p.1 = i)).card : ℕ∞)
          = (((s.filter (fun p => p.1 = i)).image x : Finset E) : Set E).encard := by
            rw [Set.encard_coe_eq_coe_finsetCard, hcard]
        _ ≤ (S i ∩ f i ⁻¹' {y}).encard := Set.encard_le_encard hsubset
    have hsplit : s.card = ∑ i : ι, (s.filter (fun p => p.1 = i)).card :=
      Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ p.1
    have hle : (s.card : ℕ∞) ≤ (N : ℕ∞) := by
      calc (s.card : ℕ∞) = ∑ i : ι, ((s.filter (fun p => p.1 = i)).card : ℕ∞) := by
            rw [hsplit]; push_cast; rfl
        _ ≤ ∑ i : ι, (S i ∩ f i ⁻¹' {y}).encard := Finset.sum_le_sum fun i _ => hfib i
        _ ≤ (N : ℕ∞) := hyN hy
    exact_mod_cast hle
  have hmain : ∑' p : ι × ℕ, μ (A p) =
      ∑ i, ∫⁻ x in S i, ENNReal.ofReal |(f' i x).det| ∂μ := by
    rw [ENNReal.tsum_prod', tsum_fintype]
    exact Finset.sum_congr rfl fun i _ =>
      (lintegral_abs_det_eq_tsum_image μ (hS i) (hf i) (hDm i) (hDS i) (hDdisj i) (hDinj i)
        (hDcov i)).symm
  rw [← hmain]
  exact tsum_measure_le_of_card_le μ hAm hΔ hAsub hcount


end Measurable

end SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound
