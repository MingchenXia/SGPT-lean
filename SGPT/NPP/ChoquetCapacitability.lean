import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Choquet's capacitability theorem

This file proves Choquet's capacitability theorem for abstract capacities, in the generality
needed for the Borel case of source `thm:pp_cap` (`chapter_npp.tex`, "a Borel set is
pluripolar iff it has capacity zero").

A *capacity* here is an arbitrary set function `c : Set α → β` with values in a complete linear
order, defined on **all** subsets of a topological space `α`, which is monotone and continuous
along increasing sequences of arbitrary sets (`UpContinuous`):
`c (⋃ j, E j) ≤ ⨆ j, c (E j)` whenever `E` is increasing.

* `exists_isCompact_subset_forall_isOpen_lt`: for every analytic set `A` (Mathlib's
  `MeasureTheory.AnalyticSet`: a continuous image of the Baire space `ℕ → ℕ`) and every
  `t < c A`, there is a compact `K ⊆ A` such that `t < c U` for **every open** `U ⊇ K`.
  No regularity of `c` at compact sets and no separation axiom on `α` are needed for this form.
* `le_iSup_isCompact_of_analyticSet` (Choquet's capacitability theorem): if moreover `c` is outer
  regular at compact sets (`c K = ⨅ {c U | U open, K ⊆ U}`, the usual "continuity along
  decreasing sequences of compact sets" in a metrizable space), then
  `c A = ⨆ {c K | K ⊆ A compact}` for every analytic `A`; by
  `MeasureTheory.MeasurableSet.analyticSet` this applies to every Borel subset of a Polish space
  (`le_iSup_isCompact_of_measurableSet`).
* `exists_isCompact_subset_forall_isOpen_gt_of_antitone`: the same statement for antitone set
  functions continuous along increasing sequences (`⨅ j, s (E j) ≤ s (⋃ j, E j)`), obtained by
  passing to the order dual.  This is the form used for the extremal height of
  `SGPT.NPP.ChoquetPluripolar`.

The proof follows Xia, *Foundations of pluripotential theory*, `thm:choquet-capacitability`,
written directly for continuous images of the Baire space: given `t < c (f '' univ)`, increasing
continuity chooses bounds `N 0, N 1, …` one coordinate at a time so that the images of the
cylinders `{σ | ∀ i < k, σ i ≤ N i}` keep capacity `> t`; the compact set is the image of the
compact product `{σ | ∀ i, σ i ≤ N i}`, and a subsequence argument shows that every open
neighbourhood of it contains the image of one of the cylinders.
-/

set_option autoImplicit false

namespace SGPT.NPP.Choquet

open Set Filter MeasureTheory
open scoped Topology

variable {α : Type*} [TopologicalSpace α] {β : Type*} [CompleteLinearOrder β]

/-- A set function is *continuous along increasing sequences* (of arbitrary sets) if
`c (⋃ j, E j) ≤ ⨆ j, c (E j)` for every increasing sequence `E`; for a monotone `c` this is
`c (⋃ j, E j) = ⨆ j, c (E j)`. -/
def UpContinuous (c : Set α → β) : Prop :=
  ∀ E : ℕ → Set α, Monotone E → c (⋃ j, E j) ≤ ⨆ j, c (E j)

/-- The cylinder of the Baire space cut out by the bounds `N i` on the first `k` coordinates. -/
def boundedCylinder (N : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) :=
  {σ | ∀ i < k, σ i ≤ N i}

/-- The compact product of the bounds `N i`. -/
theorem isCompact_setOf_forall_le (N : ℕ → ℕ) : IsCompact {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} := by
  have h := isCompact_univ_pi (fun i => (finite_Iic (N i)).isCompact)
  convert h using 1
  ext σ
  simp only [mem_ofPred_eq, mem_univ_pi, mem_Iic]

/-- If every open neighbourhood of the image of the compact product `{σ | ∀ i, σ i ≤ N i}`
failed to contain the image of every cylinder, a subsequence argument would produce a point of
that image outside the neighbourhood. -/
theorem exists_image_boundedCylinder_subset {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ)
    {U : Set α} (hU : IsOpen U) (hKU : f '' {σ | ∀ i, σ i ≤ N i} ⊆ U) :
    ∃ k, f '' boundedCylinder N k ⊆ U := by
  by_contra h
  push Not at h
  have hex : ∀ k, ∃ σ ∈ boundedCylinder N k, f σ ∉ U := by
    intro k
    obtain ⟨y, ⟨σ, hσ, rfl⟩, hyU⟩ := not_subset.mp (h k)
    exact ⟨σ, hσ, hyU⟩
  choose σ hσ hσU using hex
  set τ : ℕ → ℕ → ℕ := fun k i => min (σ k i) (N i) with hτ
  have hτP : ∀ k, τ k ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} := fun k i => min_le_right _ _
  obtain ⟨a, haP, φ, hφ, hlim⟩ := (isCompact_setOf_forall_le N).tendsto_subseq hτP
  have hlimσ : Tendsto (fun l => σ (φ l)) atTop (𝓝 a) := by
    rw [tendsto_pi_nhds] at hlim ⊢
    intro i
    refine (hlim i).congr' ?_
    filter_upwards [eventually_gt_atTop i] with l hl
    have hi : i < φ l := lt_of_lt_of_le hl (hφ.id_le l)
    have hle : σ (φ l) i ≤ N i := hσ (φ l) i hi
    simp only [Function.comp_apply, hτ, min_eq_left hle]
  have hfa : f a ∈ U := hKU ⟨a, haP, rfl⟩
  obtain ⟨l, hl⟩ := (((hf.tendsto a).comp hlimσ).eventually (hU.mem_nhds hfa)).exists
  exact hσU (φ l) hl

/-- **Choquet's capacitability theorem, approximation form.**  Let `c` be a monotone set function
on all subsets of `α`, continuous along increasing sequences.  For every analytic set `A` and
every `t < c A` there is a compact set `K ⊆ A` such that `t < c U` for every open `U ⊇ K`. -/
theorem exists_isCompact_subset_forall_isOpen_lt (c : Set α → β) (hmono : Monotone c)
    (hup : UpContinuous c) {A : Set α} (hA : AnalyticSet A) {t : β} (ht : t < c A) :
    ∃ K, IsCompact K ∧ K ⊆ A ∧ ∀ U, IsOpen U → K ⊆ U → t < c U := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact ⟨∅, isCompact_empty, subset_rfl, fun U _ _ => ht.trans_le (hmono (empty_subset U))⟩
  -- one step of the construction: bound one more coordinate, keeping the capacity above `t`
  have step : ∀ (k : ℕ) (S : Set (ℕ → ℕ)), t < c (f '' S) →
      ∃ m : ℕ, t < c (f '' (S ∩ {σ | σ k ≤ m})) := by
    intro k S hS
    have hmon : Monotone fun m : ℕ => f '' (S ∩ {σ | σ k ≤ m}) := by
      intro m m' hmm'
      exact image_mono (inter_subset_inter_right _ fun σ (hσ : σ k ≤ m) => le_trans hσ hmm')
    have hU : (⋃ m : ℕ, f '' (S ∩ {σ | σ k ≤ m})) = f '' S := by
      rw [← image_iUnion, ← inter_iUnion]
      congr 1
      refine inter_eq_left.mpr fun σ _ => mem_iUnion.mpr ⟨σ k, show σ k ≤ σ k from le_rfl⟩
    have h := hup _ hmon
    rw [hU] at h
    exact lt_iSup_iff.mp (hS.trans_le h)
  choose m hm using step
  -- the recursively chosen constraint sets
  let seq : ℕ → {S : Set (ℕ → ℕ) // t < c (f '' S)} := fun k =>
    Nat.rec (motive := fun _ => {S : Set (ℕ → ℕ) // t < c (f '' S)})
      ⟨univ, by rwa [image_univ]⟩
      (fun k S => ⟨S.1 ∩ {σ | σ k ≤ m k S.1 S.2}, hm k S.1 S.2⟩) k
  set N : ℕ → ℕ := fun k => m k (seq k).1 (seq k).2 with hN
  have hseq : ∀ k, (seq k).1 = boundedCylinder N k := by
    intro k
    induction k with
    | zero =>
      ext σ
      simp [seq, boundedCylinder]
    | succ k ih =>
      change (seq k).1 ∩ {σ | σ k ≤ N k} = boundedCylinder N (k + 1)
      rw [ih]
      ext σ
      simp only [boundedCylinder, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h1 i hi
        · exact h2
      · intro h
        exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k)⟩
  refine ⟨f '' {σ | ∀ i, σ i ≤ N i}, (isCompact_setOf_forall_le N).image hf,
    image_subset_range _ _, fun U hU hKU => ?_⟩
  obtain ⟨k, hk⟩ := exists_image_boundedCylinder_subset hf N hU hKU
  have h := (seq k).2
  rw [hseq k] at h
  exact h.trans_le (hmono hk)

/-- **Choquet's capacitability theorem.**  If, in addition, `c` is outer regular at compact sets
(`⨅ {c U | U open, K ⊆ U} ≤ c K`), then every analytic set `A` is capacitable:
`c A ≤ ⨆ {c K | K compact, K ⊆ A}` (the reverse inequality is monotonicity). -/
theorem le_iSup_isCompact_of_analyticSet [DenselyOrdered β] (c : Set α → β) (hmono : Monotone c)
    (hup : UpContinuous c)
    (hreg : ∀ K, IsCompact K → (⨅ (U : Set α) (_ : IsOpen U ∧ K ⊆ U), c U) ≤ c K)
    {A : Set α} (hA : AnalyticSet A) :
    c A ≤ ⨆ (K : Set α) (_ : IsCompact K ∧ K ⊆ A), c K := by
  refine le_of_forall_lt fun t ht => ?_
  obtain ⟨t', htt', ht'A⟩ := exists_between ht
  obtain ⟨K, hK, hKA, hKU⟩ := exists_isCompact_subset_forall_isOpen_lt c hmono hup hA ht'A
  have h1 : t' ≤ c K :=
    le_trans (le_iInf₂ fun U hU => (hKU U hU.1 hU.2).le) (hreg K hK)
  exact lt_of_lt_of_le htt' (h1.trans (le_iSup₂ (f := fun K (_ : IsCompact K ∧ K ⊆ A) => c K)
    K ⟨hK, hKA⟩))

/-- Choquet's capacitability theorem for Borel subsets of a Polish space. -/
theorem le_iSup_isCompact_of_measurableSet [DenselyOrdered β] [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] (c : Set α → β) (hmono : Monotone c) (hup : UpContinuous c)
    (hreg : ∀ K, IsCompact K → (⨅ (U : Set α) (_ : IsOpen U ∧ K ⊆ U), c U) ≤ c K)
    {A : Set α} (hA : MeasurableSet A) :
    c A ≤ ⨆ (K : Set α) (_ : IsCompact K ∧ K ⊆ A), c K :=
  le_iSup_isCompact_of_analyticSet c hmono hup hreg hA.analyticSet

/-- **Choquet's theorem for antitone set functions.**  Let `s` be antitone on all subsets of `α`
and continuous along increasing sequences in the sense `⨅ j, s (E j) ≤ s (⋃ j, E j)`.  For every
analytic set `A` and every `t > s A` there is a compact `K ⊆ A` with `s U < t` for every open
`U ⊇ K`. -/
theorem exists_isCompact_subset_forall_isOpen_gt_of_antitone (s : Set α → β) (hanti : Antitone s)
    (hdown : ∀ E : ℕ → Set α, Monotone E → ⨅ j, s (E j) ≤ s (⋃ j, E j))
    {A : Set α} (hA : AnalyticSet A) {t : β} (ht : s A < t) :
    ∃ K, IsCompact K ∧ K ⊆ A ∧ ∀ U, IsOpen U → K ⊆ U → s U < t := by
  have hmono : Monotone (fun E => OrderDual.toDual (s E)) := fun E F hEF => hanti hEF
  have hup : UpContinuous (fun E => OrderDual.toDual (s E)) := by
    intro E hE
    change OrderDual.toDual (s (⋃ j, E j)) ≤ ⨆ j, OrderDual.toDual (s (E j))
    rw [← toDual_iInf]
    exact hdown E hE
  obtain ⟨K, hK, hKA, hKU⟩ := exists_isCompact_subset_forall_isOpen_lt
    (fun E => OrderDual.toDual (s E)) hmono hup hA (t := OrderDual.toDual t) ht
  exact ⟨K, hK, hKA, fun U hU hKU' => hKU U hU hKU'⟩

end SGPT.NPP.Choquet
