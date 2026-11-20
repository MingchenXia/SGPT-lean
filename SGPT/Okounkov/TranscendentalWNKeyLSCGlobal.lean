import SGPT.Okounkov.TranscendentalWNKeyLSCStrict

/-!
# From local to global lower semicontinuity (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-lsc`, nodes `tok-wn-lsc:global-strict`, `tok-wn-lsc:global-exceptional`;
source WN21 §5 (the assembly of the proof of the easy inequality of Theorem 1.7).

Measure-theoretic globalization of the two local statements.

* `eventually_le_of_local` (the part away from `ℰ`): if near every point of a compact `K` the
  measure `ν` is eventually dominated by `νᵢ` up to `ε` on measurable sets, then the same holds
  on every measurable subset of `K` (finite subcover, induction).
* `TransportGood` (the part near `ℰ \ X'`): a set `K ⊆ ℰ` is *good* if for every open
  `O ⊇ K` in `𝒳` and `ε > 0` there are measurable `T(τ) ⊆ X` with `s_τ(T(τ)) ⊆ O` and
  `ν_ℰ(K) ≤ ν_τ(T(τ)) + ε` eventually.  Disjoint unions of good compact sets are good
  (`TransportGood.union`: separate the images by disjoint open sets, so that the transported sets
  are disjoint), and a compact set covered by open sets in which every compact set is good, is
  good (`transportGood_of_local`: disjointify the cover, approximate the pieces from inside by
  compact sets — inner regularity of the finite measure `ν_ℰ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal

namespace SGPT.Okounkov.TranscendentalWN.LSC

/-! ### Away from `ℰ`: measurable pieces -/

section Strict

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {l : Filter ι} {ν : Measure X} {νp : ι → Measure X}

/-- **`tok-wn-lsc:global-strict`**: local eventual domination on measurable sets near every point
of a compact set `K` gives eventual domination on every measurable subset of `K`. -/
theorem eventually_le_of_local {K : Set X} (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∀ S : Set X, MeasurableSet S → S ⊆ N →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ i in l, ν S ≤ νp i S + ε)
    {S : Set X} (hS : MeasurableSet S) (hSK : S ⊆ K) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ i in l, ν S ≤ νp i S + ε := by
  classical
  choose N hNo hxN hN using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => N x.1 x.2)
    (fun x => hNo x.1 x.2) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxN x hx⟩)
  have key : ∀ s : Finset K, ∀ S : Set X, MeasurableSet S → S ⊆ ⋃ i ∈ s, N i.1 i.2 →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ i in l, ν S ≤ νp i S + ε := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro S _ hSs ε _
      have : S = ∅ := by simpa using hSs
      simp [this]
    | insert a s ha ih =>
      intro S hS hSs ε hε
      have hNm : MeasurableSet (N a.1 a.2) := (hNo a.1 a.2).measurableSet
      have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
      have h1 := hN a.1 a.2 (S ∩ N a.1 a.2) (hS.inter hNm) inter_subset_right _ hε2
      have h2 := ih (S \ N a.1 a.2) (hS.diff hNm) (fun y hy => by
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp (hSs hy.1)
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact absurd hyj hy.2
        · exact mem_iUnion₂.mpr ⟨j, hj, hyj⟩) _ hε2
      filter_upwards [h1, h2] with i hi1 hi2
      rw [← measure_inter_add_sdiff S hNm, ← measure_inter_add_sdiff (μ := νp i) S hNm]
      calc ν (S ∩ N a.1 a.2) + ν (S \ N a.1 a.2)
          ≤ (νp i (S ∩ N a.1 a.2) + ε / 2) + (νp i (S \ N a.1 a.2) + ε / 2) :=
            add_le_add hi1 hi2
        _ = νp i (S ∩ N a.1 a.2) + νp i (S \ N a.1 a.2) + ε := by
            rw [add_add_add_comm, ENNReal.add_halves]
  exact key t S hS (hSK.trans ht) ε hε

end Strict

/-! ### Near `ℰ \ X'`: transported compact pieces -/

section Exceptional

variable {E X Y ι : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace X]
  {l : Filter ι} (νE : Measure E) (incl : E → Y) (s : ι → X → Y) (νp : ι → Measure X)

/-- A set `K ⊆ E` is *good* for the transport to the fibres: for every open `O ⊇ incl(K)` and
`ε > 0` there are measurable sets `T(i)` with `s_i(T(i)) ⊆ O` and `ν_E(K) ≤ ν_i(T(i)) + ε`,
eventually. -/
def TransportGood (K : Set E) : Prop :=
  ∀ O : Set Y, IsOpen O → incl '' K ⊆ O → ∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ι → Set X,
    ∀ᶠ i in l, MeasurableSet (T i) ∧ MapsTo (s i) (T i) O ∧ νE K ≤ νp i (T i) + ε

variable {νE incl s νp}

theorem TransportGood.empty : TransportGood (l := l) νE incl s νp ∅ := by
  intro O _ _ ε _
  exact ⟨fun _ => ∅, Eventually.of_forall fun _ => ⟨MeasurableSet.empty, mapsTo_empty _ _,
    by simp⟩⟩

/-- **Disjoint unions of good compact sets are good.** -/
theorem TransportGood.union (hincl : Continuous incl) (hinj : Function.Injective incl)
    {K₁ K₂ : Set E} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hd : Disjoint K₁ K₂)
    (h₁ : TransportGood (l := l) νE incl s νp K₁) (h₂ : TransportGood (l := l) νE incl s νp K₂) :
    TransportGood (l := l) νE incl s νp (K₁ ∪ K₂) := by
  intro O hO hKO ε hε
  have hd' : Disjoint (incl '' K₁) (incl '' K₂) := (disjoint_image_iff hinj).mpr hd
  obtain ⟨U₁, U₂, hU₁, hU₂, hKU₁, hKU₂, hU⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hK₁.image hincl) (hK₂.image hincl) hd'
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨T₁, hT₁⟩ := h₁ (O ∩ U₁) (hO.inter hU₁)
    (subset_inter ((image_mono subset_union_left).trans hKO) hKU₁) _ hε2
  obtain ⟨T₂, hT₂⟩ := h₂ (O ∩ U₂) (hO.inter hU₂)
    (subset_inter ((image_mono subset_union_right).trans hKO) hKU₂) _ hε2
  refine ⟨fun i => T₁ i ∪ T₂ i, ?_⟩
  filter_upwards [hT₁, hT₂] with i hi1 hi2
  refine ⟨hi1.1.union hi2.1, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact (hi1.2.1 hx).1
    · exact (hi2.2.1 hx).1
  · have hdT : Disjoint (T₁ i) (T₂ i) := by
      refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
      exact Set.disjoint_left.mp hU (hi1.2.1 hx1).2 (hi2.2.1 hx2).2
    calc νE (K₁ ∪ K₂) ≤ νE K₁ + νE K₂ := measure_union_le _ _
      _ ≤ (νp i (T₁ i) + ε / 2) + (νp i (T₂ i) + ε / 2) := add_le_add hi1.2.2 hi2.2.2
      _ = νp i (T₁ i ∪ T₂ i) + ε := by
          rw [measure_union hdT hi2.1, add_add_add_comm, ENNReal.add_halves]

/-- **Approximation from inside.**  If `K` is approximated in measure by good subsets, it is
good. -/
theorem TransportGood.of_approx {K : Set E}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K' ⊆ K, TransportGood (l := l) νE incl s νp K' ∧
      νE K ≤ νE K' + ε) :
    TransportGood (l := l) νE incl s νp K := by
  intro O hO hKO ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K', hK'K, hK'g, hK'⟩ := h _ hε2
  obtain ⟨T, hT⟩ := hK'g O hO ((image_mono hK'K).trans hKO) _ hε2
  refine ⟨T, ?_⟩
  filter_upwards [hT] with i hi
  refine ⟨hi.1, hi.2.1, ?_⟩
  calc νE K ≤ νE K' + ε / 2 := hK'
    _ ≤ (νp i (T i) + ε / 2) + ε / 2 := add_le_add_left hi.2.2 _
    _ = νp i (T i) + ε := by rw [add_assoc, ENNReal.add_halves]

/-- Finite disjoint unions of good compact sets are good. -/
theorem transportGood_biUnion (hincl : Continuous incl) (hinj : Function.Injective incl)
    {C : ℕ → Set E} (hC : ∀ i, IsCompact (C i)) (hCg : ∀ i, TransportGood (l := l) νE incl s νp (C i))
    (hCd : Pairwise (Disjoint on C)) (r : ℕ) :
    TransportGood (l := l) νE incl s νp (⋃ i ∈ Finset.range r, C i) := by
  induction r with
  | zero => simpa using TransportGood.empty
  | succ r ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    refine TransportGood.union hincl hinj ?_ (hC r) ?_ ih (hCg r)
    · exact (Finset.range r).isCompact_biUnion fun i _ => hC i
    · refine Set.disjoint_left.mpr fun x hx hxr => ?_
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp (hCd (Finset.mem_range.mp hi).ne) hxi hxr

/-- **`tok-wn-lsc:global-exceptional`**: a compact set covered by open sets in which every
compact set is good, is good (for a finite measure). -/
theorem transportGood_of_local [IsFiniteMeasure νE] [νE.InnerRegularCompactLTTop]
    (hincl : Continuous incl) (hinj : Function.Injective incl) {K : Set E} (hK : IsCompact K)
    (hloc : ∀ q ∈ K, ∃ N : Set E, IsOpen N ∧ q ∈ N ∧ ∀ K' ⊆ N, IsCompact K' →
      TransportGood (l := l) νE incl s νp K') :
    TransportGood (l := l) νE incl s νp K := by
  classical
  choose N hNo hqN hN using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun q : K => N q.1 q.2)
    (fun q => hNo q.1 q.2) (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, hqN q hq⟩)
  -- enumerate the cover
  set r := t.card with hr
  set f : Fin r ≃ t := t.equivFin.symm with hf
  set A : ℕ → Set E := fun i =>
    if h : i < r then K ∩ N (f ⟨i, h⟩).1.1 (f ⟨i, h⟩).1.2 else ∅ with hA
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    simp only [hA]
    split_ifs
    · exact hK.measurableSet.inter (hNo _ _).measurableSet
    · exact MeasurableSet.empty
  have hAK : ∀ i, A i ⊆ K := by
    intro i
    simp only [hA]
    split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  have hKA : K = ⋃ i, disjointed A i := by
    rw [iUnion_disjointed]
    refine Subset.antisymm (fun q hq => ?_) (iUnion_subset hAK)
    obtain ⟨c, hc, hqc⟩ := mem_iUnion₂.mp (ht hq)
    obtain ⟨i, hi⟩ := f.surjective ⟨c, hc⟩
    refine mem_iUnion.mpr ⟨i.1, ?_⟩
    simp only [hA, i.2, dite_true]
    refine ⟨hq, ?_⟩
    have : (f ⟨i.1, i.2⟩) = ⟨c, hc⟩ := hi
    rw [this]
    exact hqc
  have hDm : ∀ i, MeasurableSet (disjointed A i) := MeasurableSet.disjointed hAm
  have hD0 : ∀ i, r ≤ i → disjointed A i = ∅ := by
    intro i hi
    refine subset_empty_iff.mp ((disjointed_subset A i).trans ?_)
    simp [hA, not_lt.mpr hi]
  refine TransportGood.of_approx fun ε hε => ?_
  -- inner approximation of each piece by a compact set
  have hεr : (ε / (r + 1 : ℕ)) ≠ 0 := by
    exact (ENNReal.div_pos_iff.mpr ⟨hε.ne', by simp⟩).ne'
  have happ : ∀ i, ∃ C ⊆ disjointed A i, IsCompact C ∧
      νE (disjointed A i) < νE C + ε / (r + 1 : ℕ) := fun i =>
    (hDm i).exists_isCompact_lt_add (measure_ne_top _ _) hεr
  choose C hCD hCc hCν using happ
  have hCd : Pairwise (Disjoint on C) := fun i j hij =>
    ((disjoint_disjointed A) hij).mono (hCD i) (hCD j)
  have hCg : ∀ i, TransportGood (l := l) νE incl s νp (C i) := by
    intro i
    by_cases hi : i < r
    · refine hN (f ⟨i, hi⟩).1.1 (f ⟨i, hi⟩).1.2 (C i) (fun q hq => ?_) (hCc i)
      have := disjointed_subset A i (hCD i hq)
      simp only [hA, hi, dite_true] at this
      exact this.2
    · have : C i = ∅ := subset_empty_iff.mp ((hCD i).trans (hD0 i (not_lt.mp hi)).subset)
      rw [this]
      exact TransportGood.empty
  refine ⟨⋃ i ∈ Finset.range r, C i, ?_, transportGood_biUnion hincl hinj hCc hCg hCd r, ?_⟩
  · refine iUnion₂_subset fun i _ => ?_
    rw [hKA]
    exact (hCD i).trans (subset_iUnion _ i)
  · -- the measure estimate
    have hsum : νE K = ∑ i ∈ Finset.range r, νE (disjointed A i) := by
      have h1 : K = ⋃ i ∈ Finset.range r, disjointed A i := by
        rw [hKA]
        refine Subset.antisymm (fun q hq => ?_) (iUnion₂_subset fun i _ => subset_iUnion _ i)
        obtain ⟨i, hi⟩ := mem_iUnion.mp hq
        by_cases hir : i < r
        · exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hir, hi⟩
        · rw [hD0 i (not_lt.mp hir)] at hi
          exact absurd hi (notMem_empty _)
      rw [h1, measure_biUnion_finset (fun i _ j _ hij => disjoint_disjointed A hij)
        (fun i _ => hDm i)]
    have hsumC : νE (⋃ i ∈ Finset.range r, C i) = ∑ i ∈ Finset.range r, νE (C i) :=
      measure_biUnion_finset (fun i _ j _ hij => hCd hij) (fun i _ => (hCc i).measurableSet)
    rw [hsum, hsumC]
    calc ∑ i ∈ Finset.range r, νE (disjointed A i)
        ≤ ∑ i ∈ Finset.range r, (νE (C i) + ε / (r + 1 : ℕ)) :=
          Finset.sum_le_sum fun i _ => (hCν i).le
      _ = ∑ i ∈ Finset.range r, νE (C i) + r * (ε / (r + 1 : ℕ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range r, νE (C i) + ε := by
          gcongr
          have hne : ((r + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
          have hnt : ((r + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          calc (r : ℝ≥0∞) * (ε / (r + 1 : ℕ)) ≤ ((r + 1 : ℕ) : ℝ≥0∞) * (ε / (r + 1 : ℕ)) := by
                gcongr
                exact_mod_cast Nat.le_succ r
            _ = ε := ENNReal.mul_div_cancel hne hnt

end Exceptional

end SGPT.Okounkov.TranscendentalWN.LSC
