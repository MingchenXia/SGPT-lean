import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm
import SGPT.Foundations.Analysis.Pending.MixedMass
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# The finite polynomial calculus of global mixed non-pluripolar products

Blueprint `mmass:product-calculus-np` (the project-normalized form of `mmass:product-calculus`;
Boucksom--Eyssidieux--Guedj--Zeriahi, Proposition 1.4; Darvas--Di Nezza--Lu, Section 2.1).

Let `β_a` (`a ∈ ι`, `ι` finite) be closed real `(1,1)`-forms with theta-PSH potentials `q_a`, and
let `c_{k a} ≥ 0` (`k` a slot).  Put `θ_k = ∑_a c_{k a} β_a` and `u_k = ∑_a c_{k a} q_a`.  Then
\[
  NP_θ(u) = ∑_{g : slots → ι} (∏_k c_{k, g k}) NP_{β ∘ g}(q ∘ g)
\]
(`globalMixedMeasure_sumPot_expand`), every measure on the right is finite on a compact Kähler
manifold, and so the total mass of the left side is a polynomial in the coefficients
(`globalMixedMass_sumPot_expand_toReal`).  The products are symmetric in the slots
(`GlobalSlotPerm.globalMixedMeasure_perm`).

The positive case with slot-dependent supports and weights
(`globalMixedMeasure_sumPot_slots`) extends
`GlobalMultilinearExpansion.globalMixedMeasure_diagonal_sumPot` (one combination in every slot)
by the same induction over the slots.  Zero coefficients are
dropped from the sums; a slot whose coefficients all vanish carries the zero form and the zero
potential, and the global mixed measure of such a tuple is `0`
(`globalMixedMeasure_update_zero`: it equals twice itself and is finite).
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalDiagonalScaling GlobalMultilinearExpansion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {ι : Type*} [DecidableEq ι]

/-! ### Partially expanded tuples -/

/-- The tuple whose first `m` slots follow `g` through `a`, slot `k ≥ m` being `s k`. -/
def slotMix {β : Type*} (m : ℕ) (g : Fin n → ι) (a : ι → β) (s : Fin n → β) : Fin n → β :=
  fun k => if (k : ℕ) < m then a (g k) else s k

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [DecidableEq ι] in
theorem slotMix_self {β : Type*} {m : ℕ} (hm : m < n) (g : Fin n → ι) (a : ι → β)
    (s : Fin n → β) :
    Function.update (slotMix m g a s) ⟨m, hm⟩ (s ⟨m, hm⟩) = slotMix m g a s :=
  Function.update_eq_self_iff.mpr (by simp [slotMix])

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [DecidableEq ι] in
theorem update_slotMix {β : Type*} {m : ℕ} (hm : m < n) (g : Fin n → ι) (a : ι → β)
    (s : Fin n → β) (i : ι) :
    Function.update (slotMix m g a s) ⟨m, hm⟩ (a i) =
      slotMix (m + 1) (Function.update g ⟨m, hm⟩ i) a s := by
  funext k
  by_cases hk : k = ⟨m, hm⟩
  · subst hk; simp [slotMix]
  · have hk' : (k : ℕ) ≠ m := fun h => hk (Fin.ext h)
    rw [Function.update_of_ne hk]
    simp only [slotMix, Function.update_of_ne hk]
    split_ifs <;> first | rfl | omega

omit [DecidableEq ι] in
theorem slotMix_thetaPlurisubharmonic (m : ℕ) (g : Fin n → ι) {T : Fin n → Finset ι}
    (hT : ∀ k, (T k).Nonempty) {w : Fin n → ι → ℝ} (hw : ∀ k i, 0 < w k i)
    {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i)) :
    ∀ k, ThetaPlurisubharmonic (slotMix m g α (fun k => sumForm (T k) (w k) α) k).val
      (slotMix m g f (fun k => sumPot (T k) (w k) f) k) := by
  intro k
  by_cases hk : (k : ℕ) < m
  · simpa only [slotMix, hk, if_true] using hf (g k)
  · simpa only [slotMix, hk, if_false] using thetaPlurisubharmonic_sumPot (hT k) (hw k) hf

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### Positive coefficients with slot-dependent supports -/

/-- **Multilinear expansion with slot-dependent positive combinations.**  If slot `k` carries
`∑_{i ∈ T_k} w_{k i} α_i` and `∑_{i ∈ T_k} w_{k i} f_i` (nonempty `T_k`, positive weights), the
global mixed measure is `∑_{g ∈ ∏ T_k} (∏_k w_{k, g k}) μ(α ∘ g, f ∘ g)`. -/
theorem globalMixedMeasure_sumPot_slots {T : Fin n → Finset ι} (hT : ∀ k, (T k).Nonempty)
    {w : Fin n → ι → ℝ} (hw : ∀ k i, 0 < w k i) {α : ι → ClosedRealOneOneForm n M}
    {f : ι → M → EReal} (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i))
    (hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i)) :
    globalMixedMeasure (fun k => sumForm (T k) (w k) α) (fun k => sumPot (T k) (w k) f)
        (fun k => thetaPlurisubharmonic_sumPot (hT k) (hw k) hf) =
      ∑ g ∈ Fintype.piFinset T, ENNReal.ofReal (∏ k, w k (g k)) •
        globalMixedMeasure (fun k => α (g k)) (fun k => f (g k)) (fun k => hf (g k)) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n → ι, ∀ k, i₀ k ∈ T k :=
    ⟨fun k => (hT k).choose, fun k => (hT k).choose_spec⟩
  have hT' : ∀ k, (T k).Nonempty := hT
  set S : Fin n → ClosedRealOneOneForm n M := fun k => sumForm (T k) (w k) α with hSdef
  set Q : Fin n → M → EReal := fun k => sumPot (T k) (w k) f with hQdef
  let A : ℕ → Fin n → Finset ι := fun m k => if (k : ℕ) < m then T k else {i₀ k}
  let c : ℕ → (Fin n → ι) → Fin n → ℝ := fun m g k => if (k : ℕ) < m then w k (g k) else 1
  have hc0 : ∀ m g, 0 ≤ ∏ k, c m g k := fun m g =>
    Finset.prod_nonneg fun k _ => by
      simp only [c]; split_ifs
      · exact (hw _ _).le
      · exact zero_le_one
  have claim : ∀ m, m ≤ n →
      globalMixedMeasure S Q (fun k => thetaPlurisubharmonic_sumPot (hT' k) (hw k) hf) =
        ∑ g ∈ Fintype.piFinset (A m), ENNReal.ofReal (∏ k, c m g k) •
          globalMixedMeasure (slotMix m g α S) (slotMix m g f Q)
            (slotMix_thetaPlurisubharmonic m g hT' hw hf) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hA : A 0 = fun k => ({i₀ k} : Finset ι) := by funext k; simp [A]
      rw [hA, Fintype.piFinset_singleton i₀, Finset.sum_singleton]
      have hc : ∏ k, c 0 i₀ k = 1 := by simp [c]
      rw [hc, ENNReal.ofReal_one, one_smul]
      exact globalMixedMeasure_congr (by funext k; simp [slotMix])
        (by funext k; simp [slotMix]) _ _
    | succ m ih =>
      intro hm
      have hmn : m < n := hm
      set k : Fin n := ⟨m, hmn⟩ with hkdef
      rw [ih (Nat.le_of_succ_le hm)]
      have hAk : A m k = {i₀ k} := by simp [A, k]
      have hA1 : A (m + 1) = Function.update (A m) k (T k) := by
        funext k'
        by_cases hk : k' = k
        · subst hk; simp [A, k]
        · have hk' : (k' : ℕ) ≠ m := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne hk]
          simp only [A]
          split_ifs <;> first | rfl | omega
      rw [hA1, ← sum_piFinset_update_sum (A m) k hAk (T k)]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hFP : ∀ k', k' ≠ k → ThetaPlurisubharmonic
          (slotMix m g α S k').val (slotMix m g f Q k') :=
        fun k' _ => slotMix_thetaPlurisubharmonic m g hT' hw hf k'
      have hexp := globalMixedMeasure_update_sum k hFP (hT' k) (hw k) hf hq
      rw [← globalMixedMeasure_congr (slotMix_self hmn g α S) (slotMix_self hmn g f Q)
        (update_thetaPlurisubharmonic hFP (thetaPlurisubharmonic_sumPot (hT' k) (hw k) hf))
        (slotMix_thetaPlurisubharmonic m g hT' hw hf), hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← ENNReal.ofReal_mul (hc0 m g)]
      have hprod : (∏ k', c m g k') * w k i = ∏ k', c (m + 1) (Function.update g k i) k' := by
        have e1 : c m g = Function.update (c m g) k 1 :=
          (Function.update_eq_self_iff.mpr (by simp [c, k])).symm
        have e2 : c (m + 1) (Function.update g k i) = Function.update (c m g) k (w k i) := by
          funext k'
          by_cases hk : k' = k
          · subst hk; simp [c, k]
          · have hk' : (k' : ℕ) ≠ m := fun h => hk (Fin.ext h)
            rw [Function.update_of_ne hk]
            simp only [c, Function.update_of_ne hk]
            split_ifs <;> first | rfl | omega
        rw [e2, Finset.prod_update_of_mem (Finset.mem_univ k)]
        conv_lhs => rw [e1, Finset.prod_update_of_mem (Finset.mem_univ k)]
        ring
      rw [hprod]
      exact congrArg _ (globalMixedMeasure_congr (update_slotMix hmn g α S i)
        (update_slotMix hmn g f Q i) _ _)
  rw [claim n le_rfl]
  have hAn : A n = T := by funext k; simp [A, k.isLt]
  rw [hAn]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcn : ∏ k, c n g k = ∏ k, w k (g k) := by simp [c]
  rw [hcn]
  exact congrArg _ (globalMixedMeasure_congr (by funext k; simp [slotMix])
    (by funext k; simp [slotMix]) _ _)

/-! ### Zero coefficients -/

omit [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Terms with a zero coefficient can be dropped from a combination of forms. -/
theorem sumForm_filter_pos [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (α : ι → ClosedRealOneOneForm n M) :
    sumForm (Finset.univ.filter fun i => 0 < c i) c α = sumForm Finset.univ c α := by
  unfold sumForm
  refine Finset.sum_filter_of_ne fun i _ hi => ?_
  rcases (hc i).lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [← h, zero_smul]) hi

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Terms with a zero coefficient can be dropped from a combination of potentials. -/
theorem sumPot_filter_pos [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (f : ι → M → EReal) :
    sumPot (Finset.univ.filter fun i => 0 < c i) c f = sumPot Finset.univ c f := by
  funext p
  unfold sumPot
  refine Finset.sum_filter_of_ne fun i _ hi => ?_
  rcases (hc i).lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [← h, EReal.coe_zero, zero_mul]) hi

omit [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A combination with only zero coefficients is the zero form. -/
theorem sumForm_eq_zero [Fintype ι] {c : ι → ℝ} (hc : ∀ i, c i = 0)
    (α : ι → ClosedRealOneOneForm n M) : sumForm Finset.univ c α = 0 := by
  unfold sumForm
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, zero_smul]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A combination with only zero coefficients is the zero potential. -/
theorem sumPot_eq_zero [Fintype ι] {c : ι → ℝ} (hc : ∀ i, c i = 0) (f : ι → M → EReal) :
    sumPot Finset.univ c f = fun _ => 0 := by
  funext p
  unfold sumPot
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, EReal.coe_zero, zero_mul]

omit [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The zero potential is psh for the zero form. -/
theorem thetaPlurisubharmonic_zero_zero :
    ThetaPlurisubharmonic (0 : ClosedRealOneOneForm n M).val (fun _ => 0) :=
  (LocalPotentials.thetaPlurisubharmonic_zero_iff 0).mpr fun _ _ _ _ => le_rfl

omit [DecidableEq ι] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **Nonnegative combinations of theta-PSH functions.**  For coefficients `c_i ≥ 0`,
`∑ c_i f_i` is `(∑ c_i α_i)`-PSH. -/
theorem thetaPlurisubharmonic_sumPot_of_nonneg [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {α : ι → ClosedRealOneOneForm n M} {f : ι → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (α i).val (f i)) :
    ThetaPlurisubharmonic (sumForm Finset.univ c α).val (sumPot Finset.univ c f) := by
  classical
  set P := Finset.univ.filter fun i => 0 < c i with hP
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · have hz : ∀ i, c i = 0 := fun i => by
      have : i ∉ P := by rw [hPe]; exact Finset.notMem_empty i
      rw [hP, Finset.mem_filter] at this
      exact le_antisymm (not_lt.mp fun h => this ⟨Finset.mem_univ i, h⟩) (hc i)
    rw [sumForm_eq_zero hz, sumPot_eq_zero hz]
    exact thetaPlurisubharmonic_zero_zero
  · set w : ι → ℝ := fun i => if 0 < c i then c i else 1 with hwdef
    have hw : ∀ i, 0 < w i := fun i => by
      simp only [hwdef]; split_ifs with h
      · exact h
      · exact one_pos
    have eF : sumForm P w α = sumForm P c α :=
      Finset.sum_congr rfl fun i hi => by
        rw [hP, Finset.mem_filter] at hi
        simp only [hwdef, if_pos hi.2]
    have eP : sumPot P w f = sumPot P c f := by
      funext p
      exact Finset.sum_congr rfl fun i hi => by
        rw [hP, Finset.mem_filter] at hi
        simp only [hwdef, if_pos hi.2]
    have h := thetaPlurisubharmonic_sumPot hPne hw hf
    rwa [eF, eP, hP, sumForm_filter_pos hc, sumPot_filter_pos hc] at h

/-- **A slot carrying the zero form and the zero potential has zero global mixed measure**, on a
compact Kähler manifold: the measure is unchanged by scaling that slot by `2`, and it is finite. -/
theorem globalMixedMeasure_update_zero (omega : KahlerBackground n M) (j : Fin n)
    {F : Fin n → ClosedRealOneOneForm n M} {P : Fin n → M → EReal}
    (hFP : ∀ k, k ≠ j → ThetaPlurisubharmonic (F k).val (P k)) :
    globalMixedMeasure (Function.update F j 0) (Function.update P j (fun _ => 0))
        (update_thetaPlurisubharmonic hFP thetaPlurisubharmonic_zero_zero) = 0 := by
  set μ := globalMixedMeasure (Function.update F j 0) (Function.update P j (fun _ => 0))
    (update_thetaPlurisubharmonic hFP thetaPlurisubharmonic_zero_zero) with hμ
  have hzq : IsGlobalQuasiPshPotential (n := n) (M := M) (fun _ => 0) := by
    have h := (LocalPotentials.isThetaPshPotential_zero_iff (0 : ClosedRealOneOneForm n M)).mpr
      fun _ _ _ _ => le_rfl
    exact ⟨h.1.quasiPlurisubharmonic, h.2⟩
  have hsmul := globalMixedMeasure_update_smul j hFP two_pos thetaPlurisubharmonic_zero_zero hzq
  have e1 : Function.update F j ((2 : ℝ) • (0 : ClosedRealOneOneForm n M)) =
      Function.update F j 0 := by rw [smul_zero]
  have e2 : Function.update P j (fun p => ((2 : ℝ) : EReal) * (fun _ : M => (0 : EReal)) p) =
      Function.update P j (fun _ => 0) := by
    congr 1; funext p; simp
  rw [globalMixedMeasure_congr e1 e2 _
    (update_thetaPlurisubharmonic hFP thetaPlurisubharmonic_zero_zero)] at hsmul
  ext s hs
  have hfin : μ s < ⊤ := globalMixedMeasure_apply_lt_top omega _ s
  have h2 : μ s = ENNReal.ofReal 2 * μ s := by
    simpa [hμ] using congrArg (fun ν : Measure M => ν s) hsmul
  have hr : (μ s).toReal = 2 * (μ s).toReal := by
    have := congrArg ENNReal.toReal h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal zero_le_two] at this
  have h0 : (μ s).toReal = 0 := by linarith
  rw [Measure.coe_zero, Pi.zero_apply]
  rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
  · exact h
  · exact absurd h hfin.ne

/-! ### The product calculus -/

/-- **Finite polynomial calculus of global mixed products** (blueprint `mmass:product-calculus-np`).
On a compact Kähler manifold, let `α_i` (`i ∈ ι`, `ι` finite) be closed real `(1,1)`-forms with
theta-PSH potentials `f_i`, and `c_{k i} ≥ 0`.  The tuple whose slot `k` is
`(∑_i c_{k i} α_i, ∑_i c_{k i} f_i)` has global mixed measure
`∑_{g : Fin n → ι} (∏_k c_{k, g k}) μ(α ∘ g, f ∘ g)`. -/
theorem globalMixedMeasure_sumPot_expand [Fintype ι] (omega : KahlerBackground n M)
    {c : Fin n → ι → ℝ} (hc : ∀ k i, 0 ≤ c k i) {α : ι → ClosedRealOneOneForm n M}
    {f : ι → M → EReal} (hf : ∀ i, IsThetaPshPotential (α i).val (f i)) :
    globalMixedMeasure (fun k => sumForm Finset.univ (c k) α)
        (fun k => sumPot Finset.univ (c k) f)
        (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun i => (hf i).1) =
      ∑ g : Fin n → ι, ENNReal.ofReal (∏ k, c k (g k)) •
        globalMixedMeasure (fun k => α (g k)) (fun k => f (g k)) (fun k => (hf (g k)).1) := by
  classical
  have hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (f i) := fun i =>
    ⟨(hf i).1.quasiPlurisubharmonic, (hf i).2⟩
  set T : Fin n → Finset ι := fun k => Finset.univ.filter fun i => 0 < c k i with hTdef
  have hTmem : ∀ k i, i ∈ T k ↔ 0 < c k i := fun k i => by simp [hTdef]
  -- terms outside the positive supports vanish
  have hvanish : ∀ g : Fin n → ι, g ∉ Fintype.piFinset T → ∏ k, c k (g k) = 0 := by
    intro g hg
    rw [Fintype.mem_piFinset, not_forall] at hg
    obtain ⟨k, hk⟩ := hg
    have hk0 : c k (g k) = 0 := by
      rw [hTmem] at hk
      exact le_antisymm (not_lt.mp hk) (hc k (g k))
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk0
  by_cases hne : ∀ k, (T k).Nonempty
  · set w : Fin n → ι → ℝ := fun k i => if 0 < c k i then c k i else 1 with hwdef
    have hw : ∀ k i, 0 < w k i := fun k i => by
      simp only [hwdef]; split_ifs with h
      · exact h
      · exact one_pos
    have eF : ∀ k, sumForm (T k) (w k) α = sumForm Finset.univ (c k) α := fun k => by
      rw [← sumForm_filter_pos (hc k)]
      exact Finset.sum_congr rfl fun i hi => by
        simp only [hwdef, if_pos ((hTmem k i).mp hi)]
    have eP : ∀ k, sumPot (T k) (w k) f = sumPot Finset.univ (c k) f := fun k => by
      rw [← sumPot_filter_pos (hc k)]
      funext p
      exact Finset.sum_congr rfl fun i hi => by
        simp only [hwdef, if_pos ((hTmem k i).mp hi)]
    have h := globalMixedMeasure_sumPot_slots hne hw (fun i => (hf i).1) hq
    rw [globalMixedMeasure_congr (funext eF) (funext eP) _
      (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun i => (hf i).1)] at h
    rw [h, ← Finset.sum_subset (Finset.subset_univ (Fintype.piFinset T)) fun g _ hg => by
      rw [hvanish g hg, ENNReal.ofReal_zero, zero_smul]]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Fintype.mem_piFinset] at hg
    have hprod : ∏ k, w k (g k) = ∏ k, c k (g k) := Finset.prod_congr rfl fun k _ => by
      simp only [hwdef, if_pos ((hTmem k (g k)).mp (hg k))]
    rw [hprod]
  · push Not at hne
    obtain ⟨j, hj⟩ := hne
    have hz : ∀ i, c j i = 0 := fun i => by
      have : i ∉ T j := by rw [hj]; exact Finset.notMem_empty i
      rw [hTmem] at this
      exact le_antisymm (not_lt.mp this) (hc j i)
    have hrhs : ∑ g : Fin n → ι, ENNReal.ofReal (∏ k, c k (g k)) •
        globalMixedMeasure (fun k => α (g k)) (fun k => f (g k)) (fun k => (hf (g k)).1) = 0 :=
      Finset.sum_eq_zero fun g _ => by
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (hz (g j)), ENNReal.ofReal_zero, zero_smul]
    rw [hrhs]
    have hFP : ∀ k, k ≠ j → ThetaPlurisubharmonic (sumForm Finset.univ (c k) α).val
        (sumPot Finset.univ (c k) f) := fun k _ =>
      thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun i => (hf i).1
    have eF : (fun k => sumForm Finset.univ (c k) α) =
        Function.update (fun k => sumForm Finset.univ (c k) α) j 0 := by
      rw [Function.update_eq_self_iff.mpr (sumForm_eq_zero hz α).symm]
    have eP : (fun k => sumPot Finset.univ (c k) f) =
        Function.update (fun k => sumPot Finset.univ (c k) f) j (fun _ => 0) := by
      rw [Function.update_eq_self_iff.mpr (sumPot_eq_zero hz f).symm]
    rw [globalMixedMeasure_congr eF eP _
      (update_thetaPlurisubharmonic hFP thetaPlurisubharmonic_zero_zero)]
    exact globalMixedMeasure_update_zero omega j hFP

/-- **The total mixed mass is a polynomial in the coefficients**, with the finite masses
`m(α ∘ g, f ∘ g)` as coefficients (blueprint `mmass:product-calculus-np`). -/
theorem globalMixedMass_sumPot_expand_toReal [Fintype ι] (omega : KahlerBackground n M)
    {c : Fin n → ι → ℝ} (hc : ∀ k i, 0 ≤ c k i) {α : ι → ClosedRealOneOneForm n M}
    {f : ι → M → EReal} (hf : ∀ i, IsThetaPshPotential (α i).val (f i)) :
    (MixedMass.globalMixedMass (fun k => sumForm Finset.univ (c k) α)
        (fun k => sumPot Finset.univ (c k) f)
        (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun i => (hf i).1)).toReal =
      ∑ g : Fin n → ι, (∏ k, c k (g k)) *
        (MixedMass.globalMixedMass (fun k => α (g k)) (fun k => f (g k))
          (fun k => (hf (g k)).1)).toReal := by
  unfold MixedMass.globalMixedMass
  rw [globalMixedMeasure_sumPot_expand omega hc hf, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_sum fun g _ => ?_]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Finset.prod_nonneg fun k _ => hc k (g k))]
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (globalMixedMeasure_apply_lt_top omega _ univ).ne

end

end SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
