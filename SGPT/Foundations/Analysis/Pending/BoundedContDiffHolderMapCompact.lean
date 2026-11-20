import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMapInclusion
import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMapBilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

set_option autoImplicit false

/-!
# Compactness of `C^{k,r} ⊂ C^{k,s}` on a fixed compact support

Let `E`, `F` be finite-dimensional real normed spaces, `K ⊆ E` compact and `0 ≤ s < r ≤ 1`.
Every sequence in `C^{k,r}_b(E, F)` which is bounded and vanishes outside `K` has a subsequence
converging in `C^{k,s}_b(E, F)` (`exists_subseq_tendsto_ofLE`).

Proof (Gilbarg--Trudinger, Lemma 6.36): the derivatives `Dⁱ fₙ`, `i ≤ k`, are uniformly bounded
and uniformly `r`-Hölder (`holderWith_iteratedFDeriv`), so by Arzelà--Ascoli on `K` (applied to all
`i ≤ k` at once in the product of the spaces `C(K, E [×i]→L F)`) a subsequence converges uniformly
on `K`, hence on `E` since every `Dⁱ fₙ` vanishes outside `K`.  The interpolation inequality
`[g]_s ≤ [g]_r ^ (s / r) (2 ‖g‖_∞) ^ (1 - s / r)` for the top derivatives of the differences
turns this into a Cauchy sequence of `C^{k,s}_b`, which converges by completeness.

As a consequence the inclusion of the maps supported in `K` is a compact operator
(`isCompactOperator_ofLE_supportedIn`), the form used by the Fredholm alternative on a compact
manifold through a finite atlas.

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace SGPT.Foundations.Analysis.Pending

/-- Continuous multilinear maps between finite-dimensional spaces form a finite-dimensional
space. -/
theorem finiteDimensional_continuousMultilinearMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (i : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F) :=
  Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- Continuous multilinear maps between finite-dimensional spaces form a proper space. -/
theorem properSpace_continuousMultilinearMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (i : ℕ) :
    ProperSpace (ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F) :=
  haveI := finiteDimensional_continuousMultilinearMap (E := E) (F := F) i
  FiniteDimensional.proper ℝ _

/-- The derivatives of a map vanishing outside a closed set vanish outside it. -/
theorem iteratedFDeriv_eq_zero_of_notMem {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K : Set E} (hK : IsClosed K)
    (hf : ∀ x ∉ K, f x = 0) (i : ℕ) {x : E} (hx : x ∉ K) : iteratedFDeriv ℝ i f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy using hf y hy
  rw [(h.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

namespace BoundedContDiffHolderMap

/-- Bounded continuous maps `X →ᵇ (E [×i]→L[ℝ] F)` with the normed-group metric (see the note in
`BoundedContDiffHolderMap`). -/
local notation "C_b(" X ", " i ", " E ", " F ")" =>
  @BoundedContinuousFunction X (ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F) _
    SeminormedAddCommGroup.toPseudoMetricSpace

variable {k : ℕ} {r s : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Compactness of `C^{k,r} ⊂ C^{k,s}` on a fixed compact support** (`s < r ≤ 1`): a bounded
sequence in `C^{k,r}_b(E, F)` vanishing outside a compact set `K` has a subsequence converging in
`C^{k,s}_b(E, F)`. -/
theorem exists_subseq_tendsto_ofLE (hr : r ≤ 1) (hsr : s < r) {K : Set E} (hK : IsCompact K)
    (f : ℕ → BoundedContDiffHolderMap k r E F) (hsupp : ∀ n, ∀ x ∉ K, f n x = 0) {M : ℝ}
    (hM : ∀ n, ‖f n‖ ≤ M) :
    ∃ g : BoundedContDiffHolderMap k s E F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ofLE hsr.le (f (φ n))) atTop (𝓝 g) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hr0 : 0 < r := lt_of_le_of_lt zero_le hsr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hvan : ∀ n i, ∀ x ∉ K, iteratedFDeriv ℝ i (f n) x = 0 := fun n i x hx =>
    iteratedFDeriv_eq_zero_of_notMem hK.isClosed (hsupp n) i hx
  -- the derivatives restricted to `K`
  let R : ℕ → (i : ℕ) → C_b(K, i, E, F) := fun n i =>
    ((f n).iteratedFDerivBCF i).compContinuous ⟨Subtype.val, continuous_subtype_val⟩
  have hR : ∀ n i, i ≤ k → ∀ x : K, R n i x = iteratedFDeriv ℝ i (f n) x := fun n i hi x => by
    simp only [R, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [coe_iteratedFDerivBCF _ hi]
  -- Arzelà--Ascoli for each order `i ≤ k`
  have hcpt : ∀ i : Fin (k + 1), IsCompact (closure (range fun n => R n i)) := by
    intro i
    have := properSpace_continuousMultilinearMap (E := E) (F := F) i
    have hik : (i : ℕ) ≤ k := Nat.lt_succ_iff.1 i.2
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 M)
      (isCompact_closedBall 0 M) _ ?_ ?_
    · rintro _ x ⟨n, rfl⟩
      rw [mem_closedBall_zero_iff, hR n i hik]
      exact ((f n).norm_iteratedFDeriv_apply_le hik x).trans (hM n)
    · intro x₀
      refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
      have hcont : Continuous fun x : K => 2 * M * dist x₀ x ^ (r : ℝ) :=
        continuous_const.mul ((continuous_const.dist continuous_id).rpow_const
          fun _ => Or.inr r.coe_nonneg)
      have h0 : 2 * M * dist x₀ x₀ ^ (r : ℝ) = 0 := by
        rw [dist_self, Real.zero_rpow (NNReal.coe_pos.2 hr0).ne', mul_zero]
      have hev := (hcont.tendsto x₀).eventually (gt_mem_nhds (a := ε) (by rw [h0]; exact hε))
      filter_upwards [hev] with x hx
      rintro ⟨_, ⟨n, rfl⟩⟩
      simp only
      rw [hR n i hik, hR n i hik]
      have hH := ((f n).holderWith_iteratedFDeriv hr hik).dist_le (x₀ : E) x
      refine lt_of_le_of_lt (hH.trans ?_) hx
      rw [Subtype.dist_eq x₀ x]
      push_cast
      gcongr
      exact hM n
  -- a common subsequence
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_univ_pi hcpt).tendsto_subseq
    (x := fun n (i : Fin (k + 1)) => R n i) fun n i _ => subset_closure ⟨n, rfl⟩
  -- the distances of the derivatives along the subsequence tend to `0`
  have hδ : ∀ i ≤ k, Tendsto (fun p : ℕ × ℕ => dist (R (φ p.1) i) (R (φ p.2) i))
      atTop (𝓝 0) := fun i hi =>
    cauchySeq_iff_tendsto_dist_atTop_0.1
      (tendsto_pi_nhds.1 hlim ⟨i, Nat.lt_succ_of_le hi⟩).cauchySeq
  -- pointwise control on `E` by the distances on `K`
  have hpt : ∀ i ≤ k, ∀ (m n : ℕ) (x : E),
      ‖iteratedFDeriv ℝ i (f m) x - iteratedFDeriv ℝ i (f n) x‖ ≤ dist (R m i) (R n i) := by
    intro i hi m n x
    by_cases hx : x ∈ K
    · rw [← dist_eq_norm, ← hR m i hi ⟨x, hx⟩, ← hR n i hi ⟨x, hx⟩]
      exact BoundedContinuousFunction.dist_coe_le_dist _
    · rw [hvan m i x hx, hvan n i x hx, sub_zero, norm_zero]
      exact dist_nonneg
  -- the subsequence is Cauchy in `C^{k,s}_b`
  set t : ℝ≥0 := s / r with ht
  have ht1 : t ≤ 1 := div_le_one_of_le₀ hsr.le zero_le
  have ht2 : (0 : ℝ) < ((1 - t : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_pos, tsub_pos_iff_lt, ht]
    exact (div_lt_one hr0).2 hsr
  have hrt : r * t = s := by rw [ht, mul_div_cancel₀ _ hr0.ne']
  have hbound : ∀ m n : ℕ, dist (ofLE hsr.le (f m)) (ofLE hsr.le (f n)) ≤
      ∑ i ∈ Finset.range k, dist (R m i) (R n i) + dist (R m k) (R n k) +
        (2 * M) ^ (t : ℝ) * (2 * dist (R m k) (R n k)) ^ ((1 - t : ℝ≥0) : ℝ) := by
    intro m n
    set D := f m - f n with hD
    have hDofLE : ofLE hsr.le (f m) - ofLE hsr.le (f n) = ofLE hsr.le D := ext fun _ => rfl
    have hDi : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i D x‖ ≤ dist (R m i) (R n i) := fun i hi x => by
      rw [hD, coe_sub, iteratedFDeriv_sub_apply
        ((f m).contDiff.of_le (by exact_mod_cast hi)).contDiffAt
        ((f n).contDiff.of_le (by exact_mod_cast hi)).contDiffAt]
      exact hpt i hi m n x
    have hBCF : ∀ i ≤ k, ‖(ofLE hsr.le D).iteratedFDerivBCF i‖ ≤ dist (R m i) (R n i) :=
      fun i hi => (BoundedContinuousFunction.norm_le dist_nonneg).2 fun x => by
        rw [iteratedFDerivBCF_ofLE, coe_iteratedFDerivBCF _ hi]
        exact hDi i hi x
    -- the Hölder seminorm of the top derivative by interpolation
    have hDM : ‖D‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hM m, hM n])
    have hint := D.holderWith_iteratedFDeriv_interpolate ht1
    rw [hrt] at hint
    have hHol : HolderWith ((2 * M).toNNReal ^ (t : ℝ) *
        (2 * (dist (R m k) (R n k)).toNNReal) ^ ((1 - t : ℝ≥0) : ℝ)) s
        (ofLE hsr.le D).iteratedFDerivHolder := by
      have he : ⇑(ofLE hsr.le D).iteratedFDerivHolder = iteratedFDeriv ℝ k D := by
        rw [coe_iteratedFDerivHolder, coe_ofLE]
      rw [he]
      refine hint.mono ?_
      gcongr
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
        have := D.iteratedFDerivHolder.nnHolderNorm_le_norm
        rw [coe_iteratedFDerivHolder] at this
        linarith [D.norm_iteratedFDerivHolder_le]
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ dist_nonneg, coe_nnnorm]
        exact (BoundedContinuousFunction.norm_le dist_nonneg).2 fun x => by
          rw [coe_iteratedFDerivBCF _ le_rfl]
          exact hDi k le_rfl x
    have hH := (ofLE hsr.le D).iteratedFDerivHolder.norm_le_of_holderWith hHol
    rw [iteratedFDerivHolder_toBoundedContinuousFunction] at hH
    have hk := hBCF k le_rfl
    have hsum : ∑ i ∈ Finset.range k, ‖(ofLE hsr.le D).iteratedFDerivBCF i‖ ≤
        ∑ i ∈ Finset.range k, dist (R m i) (R n i) :=
      Finset.sum_le_sum fun i hi => hBCF i (Finset.mem_range.1 hi).le
    have hC : ((((2 * M).toNNReal ^ (t : ℝ) *
        (2 * (dist (R m k) (R n k)).toNNReal) ^ ((1 - t : ℝ≥0) : ℝ)) : ℝ≥0) : ℝ) =
        (2 * M) ^ (t : ℝ) * (2 * dist (R m k) (R n k)) ^ ((1 - t : ℝ≥0) : ℝ) := by
      push_cast
      rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ dist_nonneg]
    rw [dist_eq_norm, hDofLE, norm_def]
    linarith
  -- conclusion
  have hcau : CauchySeq fun n => ofLE hsr.le (f (φ n)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    refine squeeze_zero (fun _ => dist_nonneg) (fun p => hbound (φ p.1) (φ p.2)) ?_
    have h1 : Tendsto (fun p : ℕ × ℕ => ∑ i ∈ Finset.range k, dist (R (φ p.1) i) (R (φ p.2) i))
        atTop (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := Finset.range k)]
      exact tendsto_finsetSum _ fun i hi => hδ i (Finset.mem_range.1 hi).le
    have h2 : Tendsto (fun p : ℕ × ℕ => (2 * M) ^ (t : ℝ) *
        (2 * dist (R (φ p.1) k) (R (φ p.2) k)) ^ ((1 - t : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (2 : ℝ))).mul (hδ k le_rfl)).rpow_const
        (p := ((1 - t : ℝ≥0) : ℝ)) (Or.inr ht2.le)
      rw [mul_zero, Real.zero_rpow ht2.ne'] at this
      simpa using (tendsto_const_nhds (x := (2 * M) ^ (t : ℝ))).mul this
    simpa using (h1.add (hδ k le_rfl)).add h2
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨g, φ, hφ, hg⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The maps in `C^{k,r}_b(E, F)` that vanish outside a set `K`. -/
def supportedIn (K : Set E) : Submodule ℝ (BoundedContDiffHolderMap k r E F) where
  carrier := {f | ∀ x ∉ K, f x = 0}
  add_mem' hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' _ _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem mem_supportedIn {K : Set E} {f : BoundedContDiffHolderMap k r E F} :
    f ∈ supportedIn K ↔ ∀ x ∉ K, f x = 0 :=
  Iff.rfl

/-- **Compact embedding**: for `K` compact and `s < r ≤ 1`, the inclusion of the maps of
`C^{k,r}_b(E, F)` supported in `K` into `C^{k,s}_b(E, F)` is a compact operator. -/
theorem isCompactOperator_ofLE_supportedIn (hr : r ≤ 1) (hsr : s < r) {K : Set E}
    (hK : IsCompact K) :
    IsCompactOperator fun f : supportedIn (k := k) (r := r) (F := F) K =>
      ofLE hsr.le (f : BoundedContDiffHolderMap k r E F) := by
  let T : supportedIn (k := k) (r := r) (F := F) K → BoundedContDiffHolderMap k s E F :=
    fun f => ofLE hsr.le (f : BoundedContDiffHolderMap k r E F)
  have hSc : IsCompact (closure (T '' Metric.closedBall 0 1)) := by
    refine IsSeqCompact.isCompact fun y hy => ?_
    have hy' : ∀ n : ℕ, ∃ f ∈ Metric.closedBall (0 : supportedIn (k := k) (r := r) (F := F) K) 1,
        dist (y n) (T f) < 1 / ((n : ℝ) + 1) := fun n => by
      obtain ⟨b, ⟨f, hf, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 (hy n) (1 / ((n : ℝ) + 1))
        Nat.one_div_pos_of_nat
      exact ⟨f, hf, hb⟩
    choose f hf hfy using hy'
    have hfM : ∀ n, ‖((f n : supportedIn (k := k) (r := r) (F := F) K) :
        BoundedContDiffHolderMap k r E F)‖ ≤ 1 := fun n => by
      exact mem_closedBall_zero_iff.1 (hf n)
    obtain ⟨g, φ, hφ, hg⟩ := exists_subseq_tendsto_ofLE hr hsr hK
      (fun n => ((f n : supportedIn (k := k) (r := r) (F := F) K) :
        BoundedContDiffHolderMap k r E F))
      (fun n => mem_supportedIn.1 (f n).2) hfM
    have hmem : ∀ n, T (f (φ n)) ∈ T '' Metric.closedBall 0 1 := fun n =>
      ⟨f (φ n), hf (φ n), rfl⟩
    have hgS : g ∈ closure (T '' Metric.closedBall 0 1) :=
      mem_closure_of_tendsto hg (Eventually.of_forall hmem)
    refine ⟨g, hgS, φ, hφ, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n => dist (T (f (φ n))) g) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hg
    have h3 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1) + dist (T (f (φ n))) g) atTop (𝓝 0) := by
      have := h1.add h2
      rwa [add_zero] at this
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h3
    exact (dist_triangle _ _ _).trans (add_le_add (hfy (φ n)).le le_rfl)
  exact (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, _, hSc, subset_closure⟩

end BoundedContDiffHolderMap

end SGPT.Foundations.Analysis.Pending
