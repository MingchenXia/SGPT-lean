import SGPT.Foundations.Analysis.Pending.ManifoldSchauderHigher

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Regularity in the global Schauder theory on a compact complex manifold

The regularity clause of blueprint `bou:schauder-global`: for an operator `L` given in every chart `e_i` of a Hölder atlas
by `L_i v = a_i : D²v + Dv(β_i) + c_i v` with coefficients in `C^{k,r}_b` (`a_i` symmetric, `λ`-elliptic), if
`u ∈ C^{2,r}(M)` and `L u = g ∈ C^{k,r}(M)` on the chart domains, then `u ∈ C^{k+2,r}(M)` (`exists_holderMap_of_ellipticOp_eq`).
Together with `ManifoldSchauderHigher.exists_norm_le` this is `bou:schauder-global` for every `k`.

Proof.  In a chart, `v = u ∘ e_i⁻¹` is `C^{2,r}` near every point of the chart target and solves `a_i : D²v = g̃` with
`g̃ = g ∘ e_i⁻¹ - Dv(β_i) - c_i v`; if `v` is `C^{j+2,r}` there (`j < k`), then `g̃` is `C^{j+1,r}`, and the interior regularity
for `a : D²v = g` (`LinearRegularity.holderAt_of_hessTrace_eq`, difference quotients) makes `v` `C^{j+3,r}` (`holderAt_of_ellipticOp_eq`).
A function that is `C^{m,r}` near every point and has compact support lies in `C^{m,r}_b` (`exists_of_holderAt`: a Lebesgue number of
a finite cover by the local representatives), so every local representative `(χ_i u) ∘ e_i⁻¹` of `u` lies in `C^{k+2,r}_b`
(`exists_holderMap_of_holderAt`).

## Main results

* `exists_of_holderAt` (local-to-global for compactly supported germs);
* `exists_holderMap_of_holderAt` (a function `C^{m,r}` in every chart lies in `C^{m,r}(M)`);
* `holderAt_of_ellipticOp_eq` (local bootstrap with lower-order terms);
* **`exists_holderMap_of_ellipticOp_eq`** (the regularity clause of `bou:schauder-global`).

TN.5, blueprint `bou:schauder-global`.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldSchauderRegularity

open BoundedContDiffHolderMap EllipticMeanValue SchauderBlowup SchauderWholeSpace LinearRegularity HolderGerm

/-! ### Local-to-global for compactly supported germs -/

section LocalGlobal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ} {r : ℝ≥0}

/-- **A compactly supported function that is `C^{m,r}` near every point lies in `C^{m,r}_b`.** -/
theorem exists_of_holderAt {f : E → F} (hc : HasCompactSupport f) (h : ∀ z, HolderAt m r f z) :
    ∃ w : BoundedContDiffHolderMap m r E F, ⇑w = f := by
  classical
  have hcd : ContDiff ℝ m f := contDiff_iff_contDiffAt.2 fun z => (h z).contDiffAt
  have hbd : ∀ i ≤ m, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := fun i hi =>
    (hcd.continuous_iteratedFDeriv (by exact_mod_cast hi)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  -- local Hölder data
  have hloc : ∀ z, ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∃ C : ℝ≥0, ∀ x ∈ U, ∀ y ∈ U, dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y) ≤ C * dist x y ^ (r : ℝ) := by
    intro z
    obtain ⟨w, hw⟩ := h z
    have hDw := hw.iteratedFDeriv (𝕜 := ℝ) m
    obtain ⟨U, hUD, hUo, hzU⟩ := _root_.eventually_nhds_iff.1 hDw
    obtain ⟨C, hC⟩ := w.memHolder
    exact ⟨U, hUo, hzU, C, fun x hx y hy => by
      rw [← hUD x hx, ← hUD y hy]
      exact hC.dist_le x y⟩
  choose U hUo hzU C hC using hloc
  set K := tsupport f with hK
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hUo fun z _ => mem_iUnion.2 ⟨z, hzU z⟩
  have hcov : K ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨j, hj⟩, hxj⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hc (fun j : t => hUo j) hcov
  obtain ⟨B, hB⟩ := hbd m le_rfl
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set H : ℝ := ∑ j ∈ t, (C j : ℝ) + 2 * B / δ ^ (r : ℝ) with hH
  have hδr : 0 < δ ^ (r : ℝ) := Real.rpow_pos_of_pos hδ _
  have hH0 : 0 ≤ H := by positivity
  have hCle : ∀ j ∈ t, (C j : ℝ) ≤ H := fun j hj =>
    (Finset.single_le_sum (f := fun j => (C j : ℝ)) (fun _ _ => NNReal.coe_nonneg _) hj).trans
      (le_add_of_nonneg_right (by positivity))
  have hzero : ∀ x ∉ K, iteratedFDeriv ℝ m f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (tsupport_iteratedFDeriv_subset m h')
  have hnear : ∀ x ∈ K, ∀ y, dist x y < δ → dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y) ≤ H * dist x y ^ (r : ℝ) := by
    intro x hx y hxy
    obtain ⟨⟨j, hj⟩, hball⟩ := hleb x hx
    have hxU : x ∈ U j := hball (mem_ball_self hδ)
    have hyU : y ∈ U j := hball (by rw [mem_ball, dist_comm]; exact hxy)
    exact (hC j x hxU y hyU).trans (mul_le_mul_of_nonneg_right (hCle j hj) (Real.rpow_nonneg dist_nonneg _))
  refine ⟨⟨f, hcd, hbd, ⟨H.toNNReal, HolderWith.of_dist_le fun x y => ?_⟩⟩, rfl⟩
  rw [Real.coe_toNNReal _ hH0]
  rcases lt_or_ge (dist x y) δ with hxy | hxy
  · by_cases hx : x ∈ K
    · exact hnear x hx y hxy
    by_cases hy : y ∈ K
    · rw [dist_comm, dist_comm x y]
      exact hnear y hy x (by rwa [dist_comm])
    have e1 : iteratedFDeriv ℝ m f x = 0 := hzero x hx
    have e2 : iteratedFDeriv ℝ m f y = 0 := hzero y hy
    rw [e1, e2, dist_self]
    positivity
  · have h1 : dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y) ≤ 2 * B := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hB x, hB y])
    have h2 : δ ^ (r : ℝ) ≤ dist x y ^ (r : ℝ) := Real.rpow_le_rpow hδ.le hxy r.coe_nonneg
    calc dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y) ≤ 2 * B := h1
      _ = 2 * B / δ ^ (r : ℝ) * δ ^ (r : ℝ) := by field_simp
      _ ≤ 2 * B / δ ^ (r : ℝ) * dist x y ^ (r : ℝ) := by gcongr
      _ ≤ H * dist x y ^ (r : ℝ) := by
          gcongr
          rw [hH]
          linarith [Finset.sum_nonneg (fun j (_ : j ∈ t) => NNReal.coe_nonneg (C j))]

end LocalGlobal

/-! ### Membership in `C^{m,r}(M)` from the charts -/

section Manifold

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {m : ℕ} {r : ℝ≥0} {F : Type} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A function that is `C^{m,r}` near every point of every chart target lies in `C^{m,r}(M)`** (`r ≤ 1`). -/
theorem exists_holderMap_of_holderAt (hr : r ≤ 1) {u : M → F}
    (h : ∀ i, ∀ z ∈ (A.chart i).val.target, HolderAt m r (fun x => u ((A.chart i).val.symm x)) z) :
    ∃ w : A.HolderMap m r F, ⇑w = u := by
  refine ⟨⟨u, fun i => ?_⟩, rfl⟩
  set e := A.chart i with he
  set K := e.val '' tsupport (A.χ i) with hK
  have hKc : IsCompact K := A.isCompact_image_tsupport i
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩; exact e.val.map_source (A.tsupport_subset i hy)
  obtain ⟨hχs, -, -⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e
    (A.chartSmooth i) (A.isCompact_tsupport i) (A.tsupport_subset i)
  have hsupp : support (A.localRep i u) ⊆ K := fun z hz => by
    by_contra h'
    exact hz (HolderAtlas.localRep_eq_zero_of_notMem u h')
  refine exists_of_holderAt (HasCompactSupport.of_support_subset_isCompact hKc hsupp) fun z => ?_
  by_cases hzt : z ∈ e.val.target
  · have hχ : HolderAt m r (e.val.target.indicator (A.χ i ∘ e.val.symm)) z :=
      holderAt_of_contDiffAt hr ((contDiff_infty.1 hχs _).contDiffAt)
    refine (hχ.smul hr (h i z hzt)).congr ?_
    filter_upwards [e.val.open_target.mem_nhds hzt] with x hx
    rw [HolderAtlas.localRep_of_mem u hx, indicator_of_mem hx, comp_apply]
  · have hzK : z ∉ K := fun h' => hzt (hKt h')
    refine (holderAt_zero (k := m) (r := r) (z := z)).congr ?_
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hzK] with x hx
    exact (HolderAtlas.localRep_eq_zero_of_notMem u hx).symm

end Manifold

/-! ### The local bootstrap with lower-order terms -/

section Bootstrap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {r : ℝ≥0}

/-- **Interior regularity for `L v = g` with lower-order terms**: on an open `U`, if the coefficients are `C^{k,r}`
(`a` symmetric and `λ`-elliptic on `U`), `g` is `C^{k,r}` and `v` is `C^{2,r}` near every point of `U`, and
`a : D²v + Dv(β) + c v = g` on `U`, then `v` is `C^{k+2,r}` near every point of `U`. -/
theorem holderAt_of_ellipticOp_eq (hr0 : 0 < r) (hr1 : r < 1) {U : Set E} (hU : IsOpen U) {lam : ℝ} (hlam : 0 < lam)
    {a : E → E →L[ℝ] E} {β : E → E} {c g v : E → ℝ} (hsymm : ∀ z ∈ U, ∀ u w, ⟪a z u, w⟫ = ⟪u, a z w⟫)
    (hell : ∀ z ∈ U, ∀ w, lam * ‖w‖ ^ 2 ≤ ⟪a z w, w⟫) (k : ℕ)
    (ha : ∀ z ∈ U, HolderAt k r a z) (hβ : ∀ z ∈ U, HolderAt k r β z) (hc : ∀ z ∈ U, HolderAt k r c z)
    (hg : ∀ z ∈ U, HolderAt k r g z) (hv : ∀ z ∈ U, HolderAt 2 r v z)
    (heq : ∀ z ∈ U, ellipticOp b a β c v z = g z) : ∀ z ∈ U, HolderAt (k + 2) r v z := by
  have hr1' : r ≤ 1 := hr1.le
  have hpos : ∀ z ∈ U, ∀ w, w ≠ 0 → 0 < ⟪a z w, w⟫ := fun z hz w hw =>
    lt_of_lt_of_le (by have := norm_pos_iff.2 hw; positivity) (hell z hz w)
  -- the principal part of the equation
  set G : E → ℝ := fun x => g x - fderiv ℝ v x (β x) - c x * v x with hG
  have hprin : ∀ z ∈ U, hessTrace b (a z) (fderiv ℝ (fderiv ℝ v) z) = G z := by
    intro z hz
    have := heq z hz
    simp only [ellipticOp] at this
    simp only [hG]
    linarith
  -- bootstrap: `v` is `C^{j+2,r}` for `j ≤ k`
  have key : ∀ j, j ≤ k → ∀ z ∈ U, HolderAt (j + 2) r v z := by
    intro j
    induction j with
    | zero => exact fun _ => hv
    | succ j ih =>
      intro hjk
      have hvj := ih (by omega)
      have hGj : ∀ z ∈ U, HolderAt (j + 1) r G z := by
        intro z hz
        have h1 : HolderAt (j + 1) r g z := (hg z hz).of_le hr1' (by omega)
        have h2 : HolderAt (j + 1) r (fderiv ℝ v) z := (hvj z hz).derivative
        have h3 : HolderAt (j + 1) r β z := (hβ z hz).of_le hr1' (by omega)
        have h4 : HolderAt (j + 1) r c z := (hc z hz).of_le hr1' (by omega)
        have h5 : HolderAt (j + 1) r v z := (hvj z hz).of_le hr1' (by omega)
        exact (h1.sub (h2.bilinear hr1' (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) h3)).sub (h4.mul hr1' h5)
      have := holderAt_of_hessTrace_eq b hr0 hr1 hU hsymm hpos (j + 1) (by omega) G v
        (fun z hz => (ha z hz).of_le hr1' (by omega)) hGj (fun z hz => hvj z hz) hprin
      exact this
  exact key k le_rfl

end Bootstrap

/-! ### The regularity clause on the manifold -/

section Regularity

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (A : HolderAtlas n M) {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n))

/-- **Regularity** (blueprint `bou:schauder-global`, the regularity clause): for an operator given in every chart of the
atlas by coefficients `(a_i, β_i, c_i)` in `C^{k,r}_b` (`a_i` symmetric, `λ`-elliptic), if `u ∈ C^{2,r}(M)` and `L u = g`
with `g ∈ C^{k,r}(M)` on every chart domain, then `u ∈ C^{k+2,r}(M)`. -/
theorem exists_holderMap_of_ellipticOp_eq {lam : ℝ} {r : ℝ≥0} (hlam : 0 < lam) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ)
    (a : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) (ComplexModel n →L[ℝ] ComplexModel n))
    (β : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) (ComplexModel n))
    (c : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) ℝ)
    (hsymm : ∀ i x u v, ⟪a i x u, v⟫ = ⟪u, a i x v⟫) (hell : ∀ i x v, lam * ‖v‖ ^ 2 ≤ ⟪a i x v, v⟫)
    (u : A.HolderMap 2 r ℝ) (g : A.HolderMap k r ℝ)
    (hrep : ∀ i, ∀ z ∈ (A.chart i).val.target,
      g ((A.chart i).val.symm z) = ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) :
    ∃ w : A.HolderMap (k + 2) r ℝ, ⇑w = ⇑u := by
  have hr1' : r ≤ 1 := hr1.le
  refine exists_holderMap_of_holderAt hr1' fun i z hz => ?_
  exact holderAt_of_ellipticOp_eq b hr0 hr1 (A.chart i).val.open_target hlam
    (fun z _ => hsymm i z) (fun z _ => hell i z) k (fun z _ => HolderGerm.BoundedContDiffHolderMap.holderAt (a i) z)
    (fun z _ => HolderGerm.BoundedContDiffHolderMap.holderAt (β i) z)
    (fun z _ => HolderGerm.BoundedContDiffHolderMap.holderAt (c i) z) (fun z hz => holderAt_comp_symm hr1' g (A.chart i) hz)
    (fun z hz => holderAt_comp_symm hr1' u (A.chart i) hz) (fun z hz => (hrep i z hz).symm) z hz

end Regularity

end SGPT.Foundations.Analysis.Pending.ManifoldSchauderRegularity
