import SGPT.Foundations.Analysis.Pending.SchauderHigherOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Global Schauder estimates of every order on a compact complex manifold

Let `A` be a Hölder atlas of a complex manifold `M` (charts `e_i` with a chart-smooth partition of unity `χ_i`),
`b` an orthonormal basis of the real inner product space `ComplexModel n`, `0 < r < 1` and `k ∈ ℕ`.  A second-order
operator `L` on `M` is given chartwise: in the chart `e_i` it reads `L_i v = a_i : D²v + Dv(β_i) + c_i v`
(`SchauderWholeSpace.ellipticOp`) on `e_i(tsupport χ_i)`, with coefficients `a_i, β_i, c_i ∈ C^{k,r}_b` on the whole model
space, `a_i` symmetric and `λ`-elliptic.

**Main result** `exists_norm_le` (blueprint `bou:schauder-global`, the estimate): there is `C` such that every
`u ∈ C^{k+2,r}(M)` with `|u| ≤ S` and `L u = g ∈ C^{k,r}(M)` satisfies `‖u‖_{C^{k+2,r}(M)} ≤ C (‖g‖_{C^{k,r}(M)} + S)`.

Proof, by induction on `k`.  `k = 0` is `ManifoldSchauder.exists_norm_le`.  For `k + 1`, in each chart the local piece
`f_i = (χ_i u) ∘ e_i⁻¹ = χ̃_i v_i` (`v_i = σ_i · (u ∘ e_i⁻¹)`, `σ_i = 1` near `e_i(tsupport χ_i)`) solves
`L_i f_i = χ̃_i (g ∘ e_i⁻¹) + R_i` with the first-order remainder `R_i` of the product rule (`ManifoldSchauder.remainder`),
which lies in `C^{k+1,r}_b` with norm `≤ K ‖v_i‖_{C^{k+2,r}_b} ≤ K' ‖u‖_{C^{k+2,r}(M)}` (`remainderMap`); the whole-space
estimate of order `k + 1` (`SchauderHigherOrder.exists_norm_le`) bounds `‖f_i‖_{C^{k+3,r}_b}`, and the case `k` bounds
`‖u‖_{C^{k+2,r}(M)}` by `‖g‖_{C^{k,r}(M)} + S`.  No interpolation is needed beyond `k = 0`.

## Main definitions and results

* `HolderAtlas.HolderMap.lowerMap` (`C^{k+1,r}(M) ⊆ C^{k,r}(M)`, norm `≤ (k + 3) ‖u‖`);
* `crossMap`, `remainderMap` (the remainder of the product rule in `C^{k,r}_b`) and `exists_norm_remainderMap_le`;
* `exists_chart_estimate_succ` (one chart) and **`exists_norm_le`**.

TN.5, blueprint `bou:schauder-global`.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending

namespace HolderAtlas.HolderMap

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {A : HolderAtlas n M} {k : ℕ} {r : ℝ≥0} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inclusion `C^{k+1,r}(M, F) ⊆ C^{k,r}(M, F)` (`r ≤ 1`). -/
def lowerMap (hr : r ≤ 1) (u : A.HolderMap (k + 1) r F) : A.HolderMap k r F :=
  ⟨u, fun a => ⟨BoundedContDiffHolderMap.lowerMap hr (u.rep a), by
    rw [BoundedContDiffHolderMap.coe_lowerMap, coe_rep]⟩⟩

@[simp]
theorem coe_lowerMap (hr : r ≤ 1) (u : A.HolderMap (k + 1) r F) : ⇑(lowerMap hr u) = ⇑u :=
  rfl

theorem norm_lowerMap_le (hr : r ≤ 1) (u : A.HolderMap (k + 1) r F) : ‖lowerMap hr u‖ ≤ (k + 3) * ‖u‖ := by
  rw [norm_def, norm_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have he : (lowerMap hr u).rep a = BoundedContDiffHolderMap.lowerMap hr (u.rep a) :=
    BoundedContDiffHolderMap.ext fun z => by
      rw [coe_rep, BoundedContDiffHolderMap.coe_lowerMap, coe_rep]
      rfl
  rw [he]
  exact BoundedContDiffHolderMap.norm_lowerMap_le hr _

end HolderAtlas.HolderMap

namespace ManifoldSchauderHigher

open BoundedContDiffHolderMap EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceSolvability
  LinearRegularity ManifoldSchauder SchauderHigherOrder

/-! ### The remainder of the product rule in `C^{k,r}_b` -/

section Remainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {k : ℕ} {r : ℝ≥0} (hr : r ≤ 1)

/-- `x ↦ A(x) : (p(x) ⊗ q(x) + q(x) ⊗ p(x))` (`ManifoldSchauder.crossTerm`) in `C^{k,r}_b`. -/
def crossMap (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E)) (p q : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) :
    BoundedContDiffHolderMap k r E ℝ :=
  ∑ i, (bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) p)
      (bilinear hr pairBil q (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)) +
    bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) q)
      (bilinear hr pairBil p (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)))

theorem coe_crossMap (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (p q : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) (x : E) :
    crossMap b hr A p q x = crossTerm b (A x) (p x) (q x) := by
  rw [crossMap, coe_sum, Finset.sum_apply]
  simp [crossTerm]

/-- `‖x ↦ f(x) v‖ ≤ 2^(k+3) (k+3) ‖f‖` for a unit vector `v`. -/
theorem norm_clmMap_apply_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {v : E} (hv : ‖v‖ = 1)
    (f : BoundedContDiffHolderMap k r E (E →L[ℝ] G)) :
    ‖clmMap hr (ContinuousLinearMap.apply ℝ G v) f‖ ≤ 2 ^ (k + 3) * (k + 3) * ‖f‖ := by
  have h1 : ‖ContinuousLinearMap.apply ℝ G v‖ ≤ 1 := (norm_apply_le' v).trans hv.le
  calc ‖clmMap hr (ContinuousLinearMap.apply ℝ G v) f‖ ≤
        2 ^ (k + 3) * (k + 3) * ‖ContinuousLinearMap.apply ℝ G v‖ * ‖f‖ := norm_clmMap_le hr _ _
    _ ≤ 2 ^ (k + 3) * (k + 3) * 1 * ‖f‖ := by gcongr
    _ = _ := by ring

/-- One term of `crossMap`. -/
theorem norm_crossTerm_le (i : ι) (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (f g : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) :
    ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) f)
      (bilinear hr pairBil g (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A))‖ ≤
      (2 ^ (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖f‖ * ‖g‖ := by
  have hb : ‖b i‖ = 1 := b.orthonormal.1 i
  have e1 := norm_bilinear_le hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) f)
    (bilinear hr pairBil g (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A))
  have e2 := norm_bilinear_le hr (pairBil (E := E)) g (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)
  have hm : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hpb : ‖(pairBil (E := E))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hf := norm_clmMap_apply_le hr hb f
  have hA := norm_clmMap_apply_le hr hb A
  have f2 : ‖bilinear hr pairBil g (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)‖ ≤
      2 ^ (k + 3) * ‖g‖ * (2 ^ (k + 3) * (k + 3) * ‖A‖) := by
    refine e2.trans ?_
    calc 2 ^ (k + 3) * ‖(pairBil (E := E))‖ * ‖g‖ * ‖clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A‖ ≤
          2 ^ (k + 3) * 1 * ‖g‖ * (2 ^ (k + 3) * (k + 3) * ‖A‖) := by gcongr
      _ = _ := by ring
  refine e1.trans ?_
  calc 2 ^ (k + 3) * ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) f‖ *
        ‖bilinear hr pairBil g (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)‖ ≤
        2 ^ (k + 3) * 1 * (2 ^ (k + 3) * (k + 3) * ‖f‖) * (2 ^ (k + 3) * ‖g‖ * (2 ^ (k + 3) * (k + 3) * ‖A‖)) := by
        gcongr
    _ = _ := by ring

theorem exists_norm_crossMap_le (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (p : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ), ‖crossMap b hr A p q‖ ≤ K * ‖q‖ := by
  refine ⟨Fintype.card ι * (2 * ((2 ^ (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖p‖)), by positivity,
    fun q => ?_⟩
  rw [crossMap]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) p)
      (bilinear hr pairBil q (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)) +
    bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (clmMap hr (ContinuousLinearMap.apply ℝ ℝ (b i)) q)
      (bilinear hr pairBil p (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A))‖ ≤
      2 * ((2 ^ (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖p‖) * ‖q‖ := by
    intro i
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_crossTerm_le b hr i A p q
    have h2 := norm_crossTerm_le b hr i A q p
    have : (2 ^ (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖q‖ * ‖p‖ =
        (2 ^ (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖p‖ * ‖q‖ := by ring
    rw [this] at h2
    linarith
  refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The remainder `R = v (A : D²χ + Dχ(β)) + A : (Dχ ⊗ Dv + Dv ⊗ Dχ)` of the product rule `L(χ v) = χ L v + R`
(`ManifoldSchauder.remainder`), in `C^{k,r}_b`, with `Dχ`, `D²χ` given as elements `p`, `Q` of `C^{k,r}_b`. -/
def remainderMap (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E)) (β : BoundedContDiffHolderMap k r E E)
    (p : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ))
    (v : BoundedContDiffHolderMap (k + 1) r E ℝ) : BoundedContDiffHolderMap k r E ℝ :=
  bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr v) (hessTraceMap b hr A Q + bilinear hr pairBil p β) +
    crossMap b hr A p v.fderivMap

theorem coe_remainderMap (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E)) (β : BoundedContDiffHolderMap k r E E)
    {χ : E → ℝ} (p : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ)) (hp : ⇑p = fderiv ℝ χ)
    (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ)) (hQ : ⇑Q = fderiv ℝ (fderiv ℝ χ))
    (v : BoundedContDiffHolderMap (k + 1) r E ℝ) (x : E) :
    remainderMap b hr A β p Q v x = remainder b A β χ v x := by
  simp only [remainderMap, coe_add, Pi.add_apply, coe_bilinear, coe_lowerMap, ContinuousLinearMap.mul_apply',
    coe_hessTraceMap, ContinuousLinearMap.id_apply, coe_crossMap, coe_fderivMap, remainder, hp, hQ]

theorem exists_norm_remainderMap_le (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (β : BoundedContDiffHolderMap k r E E) (p : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ))
    (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : BoundedContDiffHolderMap (k + 1) r E ℝ, ‖remainderMap b hr A β p Q v‖ ≤ K * ‖v‖ := by
  obtain ⟨Kc, hKc0, hKc⟩ := exists_norm_crossMap_le b hr A p
  set W := hessTraceMap b hr A Q + bilinear hr pairBil p β with hW
  refine ⟨2 ^ (k + 3) * ((k + 3) * ‖W‖) + Kc, by positivity, fun v => ?_⟩
  have e1 := norm_bilinear_le hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr v) W
  have e2 := norm_lowerMap_le hr v
  have e3 : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have e4 := hKc v.fderivMap
  have e5 := norm_fderivMap_le v
  have hv0 := norm_nonneg v
  have hW0 := norm_nonneg W
  have t1 : ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr v) W‖ ≤ 2 ^ (k + 3) * ((k + 3) * ‖W‖) * ‖v‖ := by
    refine e1.trans ?_
    calc 2 ^ (k + 3) * ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖lowerMap hr v‖ * ‖W‖ ≤
          2 ^ (k + 3) * 1 * ((k + 3) * ‖v‖) * ‖W‖ := by gcongr
      _ = _ := by ring
  have t2 : ‖crossMap b hr A p v.fderivMap‖ ≤ Kc * ‖v‖ := e4.trans (by gcongr)
  calc ‖remainderMap b hr A β p Q v‖ ≤ ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr v) W‖ +
        ‖crossMap b hr A p v.fderivMap‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Remainder

/-! ### The estimate on the manifold -/

section Manifold

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (A : HolderAtlas n M) {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n))

/-- **The estimate of order `k + 1` in one chart**: `‖(χ_i u) ∘ e_i⁻¹‖_{C^{k+3,r}_b} ≤ K_g ‖g‖_{C^{k+1,r}(M)} +
K_u ‖u‖_{C^{k+2,r}(M)} + K_s S` for `L_i` with coefficients in `C^{k+1,r}_b`. -/
theorem exists_chart_estimate_succ (i : Fin A.m) {lam : ℝ} {r : ℝ≥0} (hlam : 0 < lam) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) (a : BoundedContDiffHolderMap (k + 1) r (ComplexModel n) (ComplexModel n →L[ℝ] ComplexModel n))
    (β : BoundedContDiffHolderMap (k + 1) r (ComplexModel n) (ComplexModel n))
    (c : BoundedContDiffHolderMap (k + 1) r (ComplexModel n) ℝ)
    (hsymm : ∀ x u v, ⟪a x u, v⟫ = ⟪u, a x v⟫) (hell : ∀ x v, lam * ‖v‖ ^ 2 ≤ ⟪a x v, v⟫) :
    ∃ Kg Ku Ks : ℝ, 0 ≤ Kg ∧ 0 ≤ Ku ∧ 0 ≤ Ks ∧
      ∀ (u : A.HolderMap (k + 1 + 2) r ℝ) (g : A.HolderMap (k + 1) r ℝ) (S : ℝ), 0 ≤ S → (∀ y, |u y| ≤ S) →
      (∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
        g ((A.chart i).val.symm z) = ellipticOp b a β c (fun w => u ((A.chart i).val.symm w)) z) →
      ‖u.rep i‖ ≤ Kg * ‖g‖ + Ku * ‖HolderAtlas.HolderMap.lowerMap hr1.le u‖ + Ks * S := by
  classical
  have hr1' : r ≤ 1 := hr1.le
  set e := A.chart i with he
  set K := e.val '' tsupport (A.χ i) with hK
  have hKc : IsCompact K := A.isCompact_image_tsupport i
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩; exact e.val.map_source (A.tsupport_subset i hy)
  set χt := e.val.target.indicator (A.χ i ∘ e.val.symm) with hχt_def
  obtain ⟨hχs, hχc, hχt⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e
    (A.chartSmooth i) (A.isCompact_tsupport i) (A.tsupport_subset i)
  have hsupp : ∀ z, χt z ≠ 0 → z ∈ K := by
    intro z hz
    by_cases hzt : z ∈ e.val.target
    · rw [hχt_def, indicator_of_mem hzt, comp_apply] at hz
      exact ⟨e.val.symm z, subset_tsupport _ hz, e.val.right_inv hzt⟩
    · exact absurd (indicator_of_notMem hzt _) hz
  obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hKc e.val.open_target hKt
  obtain ⟨σ, hσs, hσc, hσt, hσ1⟩ :=
    exists_contDiff_eq_one_of_isCompact hK'c e.val.open_target hK't
  obtain ⟨Cv, hCv⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := k + 2) (r := r)
    (F := ℝ) hr1' e (contDiff_infty.1 hσs _) hσc hσt
  obtain ⟨Ch, hCh⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := k + 1) (r := r)
    (F := ℝ) hr1' e (contDiff_infty.1 hχs _) hχc hχt
  -- `Dχ̃`, `D²χ̃` in `C^{k+1,r}_b`
  have hχ4 : ContDiff ℝ ((k + 1 + 1 + 1 + 1 : ℕ)) χt := contDiff_infty.1 hχs _
  have hDχ : ContDiff ℝ ((k + 1 + 1 : ℕ)) (fderiv ℝ χt) :=
    (hχ4.fderiv_right (m := ((k + 1 + 1 + 1 : ℕ))) (by push_cast; exact le_rfl)).of_le
      (by exact_mod_cast (by omega : k + 1 + 1 ≤ k + 1 + 1 + 1))
  have hD2χ : ContDiff ℝ ((k + 1 + 1 : ℕ)) (fderiv ℝ (fderiv ℝ χt)) :=
    (hχ4.fderiv_right (m := ((k + 1 + 1 + 1 : ℕ))) (by push_cast; exact le_rfl)).fderiv_right
      (by push_cast; exact le_rfl)
  set pχ := ofHasCompactSupport (k := k + 1) hr1' (fderiv ℝ χt) hDχ (hχc.fderiv (𝕜 := ℝ)) with hpχ
  set Qχ := ofHasCompactSupport (k := k + 1) hr1' (fderiv ℝ (fderiv ℝ χt)) hD2χ
    ((hχc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)) with hQχ
  obtain ⟨Kr, hKr0, hKr⟩ := exists_norm_remainderMap_le b hr1' a β pχ Qχ
  obtain ⟨Cw, hCw0, hW⟩ := SchauderHigherOrder.exists_norm_le b hlam hr0 hr1 (k + 1) a β c hsymm hell
  obtain ⟨K₀, -, -, -, hK₀0, -, hχ0, -⟩ := exists_bounds_of_hasCompactSupport hχs hχc
  refine ⟨Cw * |Ch|, Cw * (Kr * |Cv|), Cw * K₀, by positivity, by positivity, by positivity,
    fun u g S hS0 hu hrep => ?_⟩
  obtain ⟨v, hv, hvn⟩ := hCv (HolderAtlas.HolderMap.lowerMap hr1' u)
  obtain ⟨h, hh, hhn⟩ := hCh g
  have hh' : ∀ z, h z = χt z * g (e.val.symm z) := fun z => by rw [hh z]; rfl
  set f := u.rep i with hf_def
  -- `f = χ̃ · (u ∘ e⁻¹) = χ̃ · v`
  have hfu : ∀ z, f z = χt z * u (e.val.symm z) := by
    intro z
    rw [hf_def, HolderAtlas.HolderMap.coe_rep]
    by_cases hzt : z ∈ e.val.target
    · rw [HolderAtlas.localRep_of_mem _ hzt, hχt_def, indicator_of_mem hzt, comp_apply, smul_eq_mul]
    · rw [HolderAtlas.localRep_of_notMem _ hzt, hχt_def, indicator_of_notMem hzt, zero_mul]
  have hfv : ∀ z, f z = χt z * v z := by
    intro z
    rw [hfu z, hv z, smul_eq_mul, HolderAtlas.HolderMap.coe_lowerMap]
    by_cases hz0 : χt z = 0
    · simp [hz0]
    · rw [hσ1 z (interior_subset (hKK' (hsupp z hz0))), one_mul]
  have hfeq : ⇑f = fun z => χt z * v z := funext hfv
  have hv2 : ContDiff ℝ 2 ⇑v := v.contDiff.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hχ2' : ContDiff ℝ 2 χt := contDiff_infty.1 hχs 2
  -- the equation for `f`
  have hL : ∀ z, ellipticOp b a β c f z = h z + remainder b a β χt v z := by
    intro z
    rw [hfeq, ellipticOp_mul_eq b a β c hχ2' hv2, hh' z]
    congr 1
    by_cases hz0 : χt z = 0
    · rw [hz0, zero_mul, zero_mul]
    · have hzK := hsupp z hz0
      rw [hrep z hzK]
      congr 1
      refine ellipticOp_congr b a β c ?_
      filter_upwards [isOpen_interior.mem_nhds (hKK' hzK)] with w hw
      rw [hv w, hσ1 w (interior_subset hw), one_smul, HolderAtlas.HolderMap.coe_lowerMap]
  set G := h + remainderMap b hr1' a β pχ Qχ v with hG
  have hGeq : ∀ z, G z = ellipticOp b a β c f z := by
    intro z
    rw [hL z, hG, coe_add, Pi.add_apply, coe_remainderMap b hr1' a β pχ (coe_ofHasCompactSupport _ _ _ _) Qχ
      (coe_ofHasCompactSupport _ _ _ _) v z]
  have hfA : ∀ z, |f z| ≤ K₀ * S := fun z => by
    rw [hfu z, abs_mul]; exact mul_le_mul (hχ0 z) (hu _) (abs_nonneg _) hK₀0
  have hfn := hW f G (K₀ * S) (by positivity) hfA hGeq
  have hGn : ‖G‖ ≤ |Ch| * ‖g‖ + Kr * (|Cv| * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖) := by
    have e1 : ‖h‖ ≤ |Ch| * ‖g‖ := hhn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    have e2 : ‖v‖ ≤ |Cv| * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ :=
      hvn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc ‖G‖ ≤ ‖h‖ + ‖remainderMap b hr1' a β pχ Qχ v‖ := norm_add_le _ _
      _ ≤ |Ch| * ‖g‖ + Kr * ‖v‖ := add_le_add e1 (hKr v)
      _ ≤ _ := by gcongr
  calc ‖f‖ ≤ Cw * (‖G‖ + K₀ * S) := hfn
    _ ≤ Cw * (|Ch| * ‖g‖ + Kr * (|Cv| * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖) + K₀ * S) := by gcongr
    _ = Cw * |Ch| * ‖g‖ + Cw * (Kr * |Cv|) * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ + Cw * K₀ * S := by ring

/-- **The global Schauder estimate of every order** on a compact complex manifold (blueprint `bou:schauder-global`, the
estimate): for a Hölder atlas `A`, `0 < r < 1` and `k ∈ ℕ`, and an operator given chartwise by coefficients
`(a_i, β_i, c_i)` in `C^{k,r}_b` (`a_i` symmetric, `λ`-elliptic) on `e_i(tsupport χ_i)`, there is `C` such that every
`u ∈ C^{k+2,r}(M)` with `|u| ≤ S` and `g = L u ∈ C^{k,r}(M)` satisfy `‖u‖_{C^{k+2,r}(M)} ≤ C (‖g‖_{C^{k,r}(M)} + S)`. -/
theorem exists_norm_le {lam : ℝ} {r : ℝ≥0} (hlam : 0 < lam) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ∀ (a : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) (ComplexModel n →L[ℝ] ComplexModel n))
      (β : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) (ComplexModel n))
      (c : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) ℝ),
      (∀ i x u v, ⟪a i x u, v⟫ = ⟪u, a i x v⟫) → (∀ i x v, lam * ‖v‖ ^ 2 ≤ ⟪a i x v, v⟫) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.HolderMap (k + 2) r ℝ) (g : A.HolderMap k r ℝ) (S : ℝ), 0 ≤ S →
        (∀ y, |u y| ≤ S) →
        (∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
          g ((A.chart i).val.symm z) = ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) →
        ‖u‖ ≤ C * (‖g‖ + S) := by
  have hr1' : r ≤ 1 := hr1.le
  induction k with
  | zero =>
    intro a β c hsymm hell
    set Λ : ℝ := ∑ i, 2 * (‖a i‖ + ‖β i‖ + ‖c i‖) with hΛ
    have hle : ∀ i, 2 * (‖a i‖ + ‖β i‖ + ‖c i‖) ≤ Λ := fun i =>
      Finset.single_le_sum (f := fun i => 2 * (‖a i‖ + ‖β i‖ + ‖c i‖)) (fun j _ => by positivity)
        (Finset.mem_univ i)
    have ha : ∀ i, IsEllipticCoeff (⇑(a i)) lam Λ r := fun i =>
      { symm := hsymm i
        elliptic := hell i
        bound := fun x => (( a i).norm_apply_le x).trans (by
          linarith [hle i, norm_nonneg (β i), norm_nonneg (c i), norm_nonneg (a i)])
        holder := fun x y => (norm_sub_le_of_zero hr1' (a i) x y).trans (by
          gcongr
          linarith [hle i, norm_nonneg (β i), norm_nonneg (c i)]) }
    have hβc : ∀ i, IsLowerCoeff (⇑(β i)) (⇑(c i)) Λ r := fun i =>
      { bound_β := fun x => ((β i).norm_apply_le x).trans (by
          linarith [hle i, norm_nonneg (β i), norm_nonneg (c i), norm_nonneg (a i)])
        holder_β := fun x y => (norm_sub_le_of_zero hr1' (β i) x y).trans (by
          gcongr
          linarith [hle i, norm_nonneg (a i), norm_nonneg (c i)])
        bound_c := fun x => by
          rw [← Real.norm_eq_abs]
          exact ((c i).norm_apply_le x).trans (by
            linarith [hle i, norm_nonneg (β i), norm_nonneg (c i), norm_nonneg (a i)])
        holder_c := fun x y => by
          rw [← Real.norm_eq_abs]
          refine (norm_sub_le_of_zero hr1' (c i) x y).trans ?_
          gcongr
          linarith [hle i, norm_nonneg (a i), norm_nonneg (β i)] }
    obtain ⟨C, hC0, hC⟩ := ManifoldSchauder.exists_norm_le A b (Λ := Λ) hlam hr0 hr1
    exact ⟨C, hC0, fun u g S hS hu hrep => hC (fun i => ⇑(a i)) (fun i => ⇑(β i)) (fun i => ⇑(c i)) ha hβc
      u g S hS hu hrep⟩
  | succ k ih =>
    intro a β c hsymm hell
    obtain ⟨C₁, hC₁0, hk⟩ := ih (fun i => lowerMap hr1' (a i)) (fun i => lowerMap hr1' (β i))
      (fun i => lowerMap hr1' (c i)) hsymm hell
    choose Kg Ku Ks hKg hKu hKs hest using
      fun i => exists_chart_estimate_succ A b i hlam hr0 hr1 k (a i) (β i) (c i) (hsymm i) (hell i)
    set SKg := ∑ i, Kg i with hSKg
    set SKu := ∑ i, Ku i with hSKu
    set SKs := ∑ i, Ks i with hSKs
    have hSKg0 : 0 ≤ SKg := Finset.sum_nonneg fun i _ => hKg i
    have hSKu0 : 0 ≤ SKu := Finset.sum_nonneg fun i _ => hKu i
    have hSKs0 : 0 ≤ SKs := Finset.sum_nonneg fun i _ => hKs i
    refine ⟨SKg + SKu * C₁ * (k + 3) + SKu * C₁ + SKs, by positivity, fun u g S hS hu hrep => ?_⟩
    have hsum : ‖u‖ ≤ SKg * ‖g‖ + SKu * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ + SKs * S := by
      calc ‖u‖ = ∑ i, ‖u.rep i‖ := HolderAtlas.HolderMap.norm_def u
        _ ≤ ∑ i, (Kg i * ‖g‖ + Ku i * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ + Ks i * S) :=
            Finset.sum_le_sum fun i _ => hest i u g S hS hu (hrep i)
        _ = SKg * ‖g‖ + SKu * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ + SKs * S := by
            simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hSKg, hSKu, hSKs]
    have hlow : ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ ≤ C₁ * (‖HolderAtlas.HolderMap.lowerMap hr1' g‖ + S) :=
      hk (HolderAtlas.HolderMap.lowerMap hr1' u) (HolderAtlas.HolderMap.lowerMap hr1' g) S hS hu
        (fun i z hz => hrep i z hz)
    have hg' : ‖HolderAtlas.HolderMap.lowerMap hr1' g‖ ≤ (k + 3) * ‖g‖ := by
      have := HolderAtlas.HolderMap.norm_lowerMap_le hr1' g
      exact_mod_cast this
    have hg0 := norm_nonneg g
    have hl0 := norm_nonneg (HolderAtlas.HolderMap.lowerMap hr1' u)
    have h1 : SKu * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ ≤ SKu * (C₁ * ((k + 3) * ‖g‖ + S)) := by
      refine mul_le_mul_of_nonneg_left (hlow.trans ?_) hSKu0
      gcongr
    have h2 : 0 ≤ SKu * C₁ * (k + 3) * S := by positivity
    have h3 : 0 ≤ SKu * C₁ * ‖g‖ := by positivity
    have h4 : 0 ≤ SKg * S := by positivity
    have h5 : 0 ≤ SKs * ‖g‖ := by positivity
    calc ‖u‖ ≤ SKg * ‖g‖ + SKu * ‖HolderAtlas.HolderMap.lowerMap hr1' u‖ + SKs * S := hsum
      _ ≤ SKg * ‖g‖ + SKu * (C₁ * ((k + 3) * ‖g‖ + S)) + SKs * S := by linarith
      _ ≤ (SKg + SKu * C₁ * (k + 3) + SKu * C₁ + SKs) * (‖g‖ + S) := by
          nlinarith [h2, h3, h4, h5]

end Manifold

end ManifoldSchauderHigher

end SGPT.Foundations.Analysis.Pending
