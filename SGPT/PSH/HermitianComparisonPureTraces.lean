import SGPT.PSH.HermitianComparisonSymmetry
import SGPT.PSH.HermitianComparisonTraceAlgebra
import SGPT.PSH.HermitianExtremalPoleAlternative

/-!
# Actual canonical pure traces and selection of their factors

The pure trace is the canonical global mixed measure of the original
bounded potential in its first slots and genuine zero potentials elsewhere.
A manufactured finite permutation identifies every binary selected tuple
with this same actual measure.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonPureTraces

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian SGPT.PSH.HermitianGlobalProducts SGPT.PSH.HermitianExtremal
open scoped Topology

private theorem exists_perm_piecewise_prefix_blocks {Z : Type*}
    (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = k) (a b : Z) :
    ∃ π : Equiv.Perm (Fin (k + l)),
      (s.piecewise (fun _ => a) (fun _ => b)) ∘ π =
        fun i => if i.val < k then a else b := by
  classical
  have hc : (sᶜ).card = l := by simp only [Finset.card_compl, Fintype.card_fin, hs]; omega
  let es : Fin k ≃ ↥s := (s.orderIsoOfFin hs).toEquiv
  let ec : Fin l ≃ ↥((s : Set (Fin (k + l)))ᶜ) :=
    ((sᶜ).orderIsoOfFin hc).toEquiv.trans (Equiv.subtypeEquivRight (fun i => by simp))
  let e : Fin k ⊕ Fin l ≃ Fin (k + l) :=
    (Equiv.sumCongr es ec).trans (Equiv.Set.sumCompl (s : Set (Fin (k + l))))
  let π : Equiv.Perm (Fin (k + l)) := finSumFinEquiv.symm.trans e
  have hleft (i : Fin k) : π (i.castAdd l) = s.orderEmbOfFin hs i := by
    simp only [π, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
      e, Equiv.sumCongr_apply, Sum.map_inl]
    rfl
  have hright (i : Fin l) : π (Fin.natAdd k i) = (ec i : Fin (k + l)) := by
    simp only [π, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      e, Equiv.sumCongr_apply, Sum.map_inr]
    rfl
  refine ⟨π, ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Function.comp_apply, hleft,
      s.piecewise_eq_of_mem _ _ (s.orderEmbOfFin_mem hs j)]
    exact (if_pos j.isLt).symm
  · rw [Function.comp_apply, hright,
      s.piecewise_eq_of_notMem _ _ (by exact (ec j).property)]
    exact (if_neg (by change ¬ k + j.val < k; omega)).symm

private theorem exists_perm_piecewise_prefix_of_eq {Z : Type*}
    (N k l : ℕ) (hN : N = k + l) (s : Finset (Fin N)) (hs : s.card = k) (a b : Z) :
    ∃ π : Equiv.Perm (Fin N), (s.piecewise (fun _ => a) (fun _ => b)) ∘ π =
      fun i => if i.val < k then a else b := by
  subst N
  exact exists_perm_piecewise_prefix_blocks k l s hs a b

/-- The actual finite permutation sorting a binary tuple is produced from
the selected subset, with no ordering or permutation certificate input. -/
theorem exists_perm_piecewise_prefix {Z : Type*}
    (N : ℕ) (s : Finset (Fin N)) (a b : Z) :
    ∃ π : Equiv.Perm (Fin N), (s.piecewise (fun _ => a) (fun _ => b)) ∘ π =
      fun i => if i.val < s.card then a else b := by
  have hs : s.card ≤ N := by simpa using Finset.card_le_univ s
  exact exists_perm_piecewise_prefix_of_eq N s.card (N - s.card) (by omega) s rfl a b

def pureTuple {M : Type*} (N k : ℕ) (u : M → EReal) : Fin N → M → EReal :=
  fun i => if i.val < k then u else fun _ => 0

def binaryTuple {M : Type*} {N : ℕ} (s : Finset (Fin N)) (u : M → EReal) : Fin N → M → EReal :=
  s.piecewise (fun _ => u) (fun _ _ => 0)

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

theorem pureTuple_isHermitianPSH {N : ℕ} {u : M → EReal} (hu : IsHermitianPSH omega u) (k : ℕ) :
    ∀ i, IsHermitianPSH omega (pureTuple N k u i) := by
  intro i
  unfold pureTuple
  split_ifs
  · exact hu
  · exact isHermitianPSH_zero omega

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem pureTuple_bounded {N : ℕ} {u : M → EReal}
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (k : ℕ) :
    ∀ i : Fin N, ∃ a b : ℝ, ∀ x,
      (a : EReal) ≤ pureTuple N k u i x ∧ pureTuple N k u i x ≤ (b : EReal) := by
  intro i
  unfold pureTuple
  split_ifs
  · exact hb
  · exact ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩

theorem binaryTuple_isHermitianPSH {N : ℕ} {u : M → EReal} (hu : IsHermitianPSH omega u)
    (s : Finset (Fin N)) : ∀ i, IsHermitianPSH omega (binaryTuple s u i) := by
  intro i
  classical
  by_cases hi : i ∈ s
  · rw [binaryTuple, s.piecewise_eq_of_mem _ _ hi]
    exact hu
  · rw [binaryTuple, s.piecewise_eq_of_notMem _ _ hi]
    exact isHermitianPSH_zero omega

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem binaryTuple_bounded {N : ℕ} {u : M → EReal}
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (s : Finset (Fin N)) : ∀ i, ∃ a b : ℝ, ∀ x,
      (a : EReal) ≤ binaryTuple s u i x ∧ binaryTuple s u i x ≤ (b : EReal) := by
  intro i
  classical
  by_cases hi : i ∈ s
  · rw [binaryTuple, s.piecewise_eq_of_mem _ _ hi]
    exact hb
  · rw [binaryTuple, s.piecewise_eq_of_notMem _ _ hi]
    exact ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The literal canonical global Hermitian pure trace measure. -/
def pureTraceMeasure (omega : Background (m + 1) M) {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (k : ℕ) : Measure M :=
  globalMixedMeasure omega (pureTuple (m + 1) k u) (pureTuple_isHermitianPSH hu k)
    (pureTuple_bounded hb k)

def pureTraceMass (omega : Background (m + 1) M) {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (E : Set M) (k : ℕ) : ℝ :=
  (pureTraceMeasure omega hu hb k E).toReal

theorem pureTraceMeasure_isFiniteMeasure {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (k : ℕ) :
    IsFiniteMeasure (pureTraceMeasure omega hu hb k) :=
  globalMixedMeasure_isFiniteMeasure _ _ _

omit [BorelSpace M] in
theorem pureTraceMass_nonneg {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (E : Set M) (k : ℕ) :
    0 ≤ pureTraceMass omega hu hb E k := ENNReal.toReal_nonneg

omit [BorelSpace M] in
theorem globalMixedMeasure_congr_tuple
    {u v : Fin (m + 1) → M → EReal}
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hub : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (huv : u = v) : globalMixedMeasure omega u hu hub = globalMixedMeasure omega v hv hvb := by
  subst v
  rfl

/-- Every genuine binary selected tuple has exactly its canonical pure
trace measure; permutation symmetry and all native class inputs are internal. -/
theorem binaryTuple_measure_eq_pureTraceMeasure {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (s : Finset (Fin (m + 1))) :
    globalMixedMeasure omega (binaryTuple s u) (binaryTuple_isHermitianPSH hu s)
        (binaryTuple_bounded hb s) = pureTraceMeasure omega hu hb s.card := by
  classical
  obtain ⟨π, hπ⟩ := exists_perm_piecewise_prefix (m + 1) s u (fun _ : M => (0 : EReal))
  have htuple : (fun i => binaryTuple s u (π i)) = pureTuple (m + 1) s.card u := hπ
  have h := globalMixedMeasure_comp_perm (binaryTuple s u) (binaryTuple_isHermitianPSH hu s)
    (binaryTuple_bounded hb s) π
  exact h.symm.trans (globalMixedMeasure_congr_tuple _ _ _ _ htuple)

omit [BorelSpace M] in
theorem pureTraceMeasure_zero {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    pureTraceMeasure omega hu hb 0 = globalMixedMeasure omega (fun _ _ => (0 : EReal))
      (fun _ => isHermitianPSH_zero omega) (fun _ => ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩) := by
  apply globalMixedMeasure_congr_tuple
  funext i
  simp only [pureTuple, Nat.not_lt_zero, if_false]

omit [BorelSpace M] in
theorem pureTraceMeasure_top {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    pureTraceMeasure omega hu hb (m + 1) = globalMixedMeasure omega (fun _ => u)
      (fun _ => hu) (fun _ => hb) := by
  apply globalMixedMeasure_congr_tuple
  funext i
  exact if_pos i.isLt

/-- Binary factors supported in the first `L` slots supply their actual
selected subset of cardinality at most `L`, even when the two values agree. -/
theorem exists_binary_selection_card_le {Z : Type*} {N L : ℕ}
    (v : Fin N → Z) (a b : Z) (hvalues : ∀ i, v i = a ∨ v i = b)
    (houtside : ∀ i, L ≤ i.val → v i = b) :
    ∃ s : Finset (Fin N), s.card ≤ L ∧ v = s.piecewise (fun _ => a) (fun _ => b) := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun i => i.val < L ∧ v i = a)
  let e : ↥s → Fin L := fun i => ⟨i.val.val, (Finset.mem_filter.mp i.property).2.1⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin L => z.val) hij
  have hcard : s.card ≤ L := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective e he
  refine ⟨s, hcard, ?_⟩
  funext i
  by_cases hi : i ∈ s
  · rw [s.piecewise_eq_of_mem _ _ hi]
    exact (Finset.mem_filter.mp hi).2.2
  · rw [s.piecewise_eq_of_notMem _ _ hi]
    by_cases hpref : i.val < L
    · rcases hvalues i with hia | hib
      · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpref, hia⟩))
      · exact hib
    · exact houtside i (le_of_not_gt hpref)

/-- An actual selected Hermitian tuple containing only `u` and zero, with
at most `L` possibly nonzero slots, is an actual pure trace of degree ≤L. -/
theorem measure_eq_some_pureTraceMeasure {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (v : Fin (m + 1) → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    {L : ℕ} (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0)
    (houtside : ∀ i, L ≤ i.val → v i = fun _ => 0) :
    ∃ k : ℕ, k ≤ L ∧ globalMixedMeasure omega v hv hvb = pureTraceMeasure omega hu hb k := by
  obtain ⟨s, hcard, htuple⟩ := exists_binary_selection_card_le v u (fun _ => (0 : EReal)) hvalues houtside
  refine ⟨s.card, hcard, ?_⟩
  exact (globalMixedMeasure_congr_tuple hv hvb _ _ htuple).trans
    (binaryTuple_measure_eq_pureTraceMeasure hu hb s)

/-- Every genuine lower binary product mass is bounded by the finite sum
of the original canonical pure traces. No rank relative to the current
replacement step is needed for the global pure absorption argument. -/
theorem lower_binary_mass_le_pureTrace_sum {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (v : Fin (m + 1) → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    {L : ℕ} (hL : L < m + 1) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0)
    (houtside : ∀ i, L ≤ i.val → v i = fun _ => 0) (E : Set M) :
    (globalMixedMeasure omega v hv hvb E).toReal ≤
      ∑ k ∈ Finset.range (m + 1), pureTraceMass omega hu hb E k := by
  obtain ⟨k, hk, he⟩ := measure_eq_some_pureTraceMeasure hu hb v hv hvb hvalues houtside
  rw [he]
  exact Finset.single_le_sum (fun j _ => pureTraceMass_nonneg hu hb E j)
    (Finset.mem_range.mpr (hk.trans_lt hL))

end SGPT.PSH.HermitianComparisonPureTraces
