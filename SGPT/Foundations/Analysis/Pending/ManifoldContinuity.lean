import SGPT.Foundations.Analysis.Pending.ManifoldParametrix
import SGPT.Foundations.Analysis.Pending.MethodOfContinuity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `L - s` is invertible on a compact complex manifold for every `s > 0`

Setting as in `ManifoldParametrix.exists_ellipticOp_sub_eq_of_large`: a Hölder atlas `A` of a compact
complex manifold `M`, `0 < r < 1`, an operator `L` given chartwise by whole-space coefficients
`(a_i, β_i, c_i)` in the Schauder class `(λ, Λ, r)` with `c_i ≤ 0` on open sets
`U_i ⊇ e_i(tsupport χ_i)` of the chart targets, realizable (`hreal`).

* `exists_mem_of_chartRel`: `L` maps `C^{2,r}(M)` into `C^{0,r}(M)`, `‖L u‖ ≤ C ‖u‖` (the local
  representative of `L u` is `χ̃_i · L_i(σ_i (u ∘ e_i⁻¹))`, a product of bounded Hölder functions).
* `chartOp`: hence `L` is a linear map `C^{2,r}(M) → C^{0,r}(M)` (`chartOp_rel`, `norm_chartOp_le`); the
  partner of `u` in the chart relation is unique (`eq_of_chartRel`).
* `exists_ellipticOp_sub_eq` (blueprint `bou:kahler-laplacian-solvability`, (2) without the Fredholm
  step): for every `s > 0` and `f ∈ C^{0,r}(M)` there is `u ∈ C^{2,r}(M)` with `L u - s u = f`.
  Proof: the method of continuity (`MethodOfContinuity.surjective_of_continuity`) from `L - μ₀`,
  onto by the parametrix, to `L - s`, with the uniform estimate
  `‖u‖ ≤ C (1 + 1/s) ‖(L - s') u‖` for `s' ∈ [s, μ₀]` (`ManifoldSchauder.exists_norm_le` for the
  coefficients `(a_i, β_i, c_i - s')` and the maximum principle
  `ManifoldMaxPrinciple.mul_abs_le_of_chartOp_sub`).  Uniqueness: `eq_of_ellipticOp_sub_eq`.

TN.4 B5 linear track L4(b).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldContinuity

open FirstPass EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple
  ManifoldSchauder ManifoldParametrix HolderAtlas.HolderMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n)) {r : ℝ≥0}

/-- The sup norm is bounded by the Hölder norm. -/
theorem abs_apply_le_norm {k : ℕ} (g : A.HolderMap k r ℝ) (y : M) : |g y| ≤ ‖g‖ := by
  have hsum : g y = ∑ a, A.χ a y * g y := by rw [← Finset.sum_mul, A.sum_eq_one, one_mul]
  rw [hsum, norm_def]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  by_cases hy : y ∈ (A.chart a).val.source
  · have := HolderAtlas.localRep_chart (A := A) (g : M → ℝ) hy
    rw [smul_eq_mul] at this
    rw [← this, ← coe_rep, ← Real.norm_eq_abs]
    exact (g.rep a).norm_apply_le _
  · rw [HolderAtlas.χ_eq_zero_of_notMem A hy, zero_mul, abs_zero]
    exact norm_nonneg _

/-- `L` scales on functions that are `C²` near the point. -/
theorem ellipticOp_smul_of_contDiffAt (a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
    (β : ComplexModel n → ComplexModel n) (c : ComplexModel n → ℝ) (k : ℝ)
    {f : ComplexModel n → ℝ} {x : ComplexModel n} (hf : ContDiffAt ℝ 2 f x) :
    ellipticOp b a β c (fun y => k * f y) x = k * ellipticOp b a β c f x := by
  have hf1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => k * f y) =ᶠ[𝓝 x] fun y => k • fderiv ℝ f y := by
    filter_upwards [hf1] with y hfy
    exact (hfy.hasFDerivAt.const_mul k).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (fun y => k * f y)) x = k • fderiv ℝ (fderiv ℝ f) x := by
    rw [hev.fderiv_eq]; exact fderiv_const_smul hDf k
  simp only [ellipticOp]
  rw [h2, hev.eq_of_nhds, hessTrace_smul_right]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `u ∘ e⁻¹` is `C²` near every point of a chart target. -/
theorem contDiffAt_comp_symm (hr : r ≤ 1) (u : A.HolderMap 2 r ℝ) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ContDiffAt ℝ 2 (fun w => u (e.val.symm w)) z := by
  obtain ⟨v, hv⟩ := ManifoldMaxPrinciple.exists_local_rep hr u e hz
  exact (WholeSpaceSolvability.contDiff_two v).contDiffAt.congr_of_eventuallyEq hv.symm

/-- **Uniqueness of `L u`**: two functions that are `L u` chartwise on `e_i(tsupport χ_i)` coincide. -/
theorem eq_of_chartRel
    {a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n}
    {β : Fin A.m → ComplexModel n → ComplexModel n} {c : Fin A.m → ComplexModel n → ℝ}
    {u g g' : M → ℝ}
    (hg : ∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), g ((A.chart i).val.symm z) =
      ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z)
    (hg' : ∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), g' ((A.chart i).val.symm z) =
      ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) :
    g = g' := by
  funext y
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, A.χ i y ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
  have hys : y ∈ (A.chart i).val.source := A.tsupport_subset i (subset_tsupport _ hi)
  have hz : (A.chart i).val y ∈ (A.chart i).val '' tsupport (A.χ i) :=
    ⟨y, subset_tsupport _ hi, rfl⟩
  have h1 := hg i _ hz
  have h2 := hg' i _ hz
  rw [(A.chart i).val.left_inv hys] at h1 h2
  rw [h1, h2]

/-- **`L` maps `C^{2,r}(M)` into `C^{0,r}(M)`**, with `‖L u‖ ≤ C ‖u‖` uniformly over the coefficients
bounded by `Λ` (`a_i` bounded and `r`-Hölder, `(β_i, c_i)` in `IsLowerCoeff`). -/
theorem exists_mem_of_chartRel (hr0 : 0 < r) (hr1 : r < 1) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
        (β : Fin A.m → ComplexModel n → ComplexModel n) (c : Fin A.m → ComplexModel n → ℝ),
        (∀ i x, ‖a i x‖ ≤ Λ) → (∀ i x y, ‖a i x - a i y‖ ≤ Λ * ‖x - y‖ ^ (r : ℝ)) →
        (∀ i, IsLowerCoeff (β i) (c i) Λ r) →
      ∀ (u : A.HolderMap 2 r ℝ) (g : M → ℝ),
        (∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), g ((A.chart i).val.symm z) =
          ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) →
        ∃ G : A.HolderMap 0 r ℝ, ⇑G = g ∧ ‖G‖ ≤ C * ‖u‖ := by
  classical
  have hr1' : r ≤ 1 := hr1.le
  -- chart by chart
  have key : ∀ j : Fin A.m, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ (a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
        (β : ComplexModel n → ComplexModel n) (c : ComplexModel n → ℝ),
        (∀ x, ‖a x‖ ≤ Λ) → (∀ x y, ‖a x - a y‖ ≤ Λ * ‖x - y‖ ^ (r : ℝ)) →
        IsLowerCoeff β c Λ r →
      ∀ (u : A.HolderMap 2 r ℝ) (g : M → ℝ),
        (∀ z ∈ (A.chart j).val '' tsupport (A.χ j), g ((A.chart j).val.symm z) =
          ellipticOp b a β c (fun w => u ((A.chart j).val.symm w)) z) →
        ∃ h : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ,
          ⇑h = A.localRep j g ∧ ‖h‖ ≤ Cj * ‖u‖ := by
    intro j
    set e := A.chart j with he
    set K := e.val '' tsupport (A.χ j) with hK
    have hKc : IsCompact K := A.isCompact_image_tsupport j
    have hKt : K ⊆ e.val.target := by
      rintro _ ⟨y, hy, rfl⟩; exact e.val.map_source (A.tsupport_subset j hy)
    obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hKc e.val.open_target hKt
    obtain ⟨σ, hσs, hσc, hσt, hσ1⟩ :=
      exists_contDiff_eq_one_of_isCompact hK'c e.val.open_target hK't
    obtain ⟨Cv, hCv⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 2) (r := r)
      (F := ℝ) hr1' e (contDiff_infty.1 hσs 3) hσc hσt
    obtain ⟨hχs, hχc, -⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e
      (A.chartSmooth j) (A.isCompact_tsupport j) (A.tsupport_subset j)
    set χt := e.val.target.indicator (A.χ j ∘ e.val.symm) with hχt
    obtain ⟨K₀, K₁, -, -, hK₀0, -, hχ0, hχ1, -, -, -⟩ :=
      exists_bounds_of_hasCompactSupport hχs hχc
    have hχ2 : ContDiff ℝ 2 χt := contDiff_infty.1 hχs 2
    have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hχ1 0)
    set d : ℝ := (Fintype.card ι : ℝ) with hd
    set Cq : ℝ := K₀ * ((d + 2) * |Λ|) + ((K₁ + 2 * K₀) * ((d + 2) * |Λ|) +
      K₀ * ((2 * d + 16) * |Λ|)) with hCq
    refine ⟨Cq * |Cv|, by positivity, fun a β c hab hah hβc u g hg => ?_⟩
    have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hab 0)
    obtain ⟨v, hv, hvn⟩ := hCv u
    have hv2 := WholeSpaceSolvability.contDiff_two v
    -- the local representative is `χ̃ · L v`
    have hrep : ∀ z, A.localRep j g z = χt z * ellipticOp b a β c v z := by
      intro z
      by_cases hzt : z ∈ e.val.target
      · rw [HolderAtlas.localRep_of_mem _ hzt, smul_eq_mul]
        have hχz : χt z = A.χ j (e.val.symm z) := by rw [hχt, indicator_of_mem hzt, comp_apply]
        rw [hχz]
        by_cases h0 : A.χ j (e.val.symm z) = 0
        · rw [h0, zero_mul, zero_mul]
        · have hzK : z ∈ K := ⟨e.val.symm z, subset_tsupport _ h0, e.val.right_inv hzt⟩
          rw [hg z hzK]
          congr 1
          refine ellipticOp_congr b a β c ?_
          filter_upwards [isOpen_interior.mem_nhds (hKK' hzK)] with w hw
          rw [hv w, hσ1 w (interior_subset hw), one_smul]
      · rw [HolderAtlas.localRep_of_notMem _ hzt, hχt, indicator_of_notMem hzt, zero_mul]
    -- bounds for `χ̃ · L v`
    have hL0 := WholeSpaceSolvability.abs_ellipticOp_le b a β c hab hβc v
    have hL1 := WholeSpaceSolvability.abs_ellipticOp_sub_le b hr1' a β c hab hah hβc v
    have hχL : ∀ x y, |χt x - χt y| ≤ (K₁ + 2 * K₀) * ‖x - y‖ ^ (r : ℝ) := fun x y => by
      have := norm_sub_le_rpow_of_lipschitz_of_bound (Y := ℝ) (g := χt) hK₁0 r.coe_nonneg
        (by exact_mod_cast hr1') (fun x y => by
          rw [Real.norm_eq_abs]; exact abs_sub_le_of_fderiv hχ2 hχ1 x y)
        (fun x => by rw [Real.norm_eq_abs]; exact hχ0 x) x y
      rwa [Real.norm_eq_abs] at this
    have hvn' : ‖v‖ ≤ |Cv| * ‖u‖ :=
      hvn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    have hdΛ : (d + 2) * Λ ≤ (d + 2) * |Λ| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have hdΛ' : (2 * d + 16) * Λ ≤ (2 * d + 16) * |Λ| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    set F₀ := K₀ * ((d + 2) * |Λ| * ‖v‖) with hF₀
    set M₀ := (K₁ + 2 * K₀) * ((d + 2) * |Λ| * ‖v‖) + K₀ * ((2 * d + 16) * |Λ| * ‖v‖) with hM₀
    have hqF : ∀ x, |χt x * ellipticOp b a β c v x| ≤ F₀ := fun x => by
      rw [abs_mul]
      refine mul_le_mul (hχ0 x) ((hL0 x).trans ?_) (abs_nonneg _) hK₀0
      exact mul_le_mul_of_nonneg_right hdΛ (norm_nonneg _)
    have hM₀0 : 0 ≤ M₀ := by positivity
    have hqM : ∀ x y, |χt x * ellipticOp b a β c v x - χt y * ellipticOp b a β c v y| ≤
        M₀ * ‖x - y‖ ^ (r : ℝ) := fun x y => by
      have hp0 : 0 ≤ ‖x - y‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
      have := abs_mul_sub_mul_le (hχL x y)
        ((hL0 x).trans (mul_le_mul_of_nonneg_right hdΛ (norm_nonneg _))) (hχ0 y)
        ((hL1 x y).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdΛ' (norm_nonneg _)) hp0))
      refine this.trans (le_of_eq ?_)
      rw [hM₀]; ring
    refine ⟨ofHolderZero hr0 (fun x => χt x * ellipticOp b a β c v x) hqF hM₀0 hqM,
      funext fun z => (hrep z).symm, ?_⟩
    refine (norm_ofHolderZero_le hr0 _ hqF hM₀0 hqM).trans ?_
    have : F₀ + M₀ = Cq * ‖v‖ := by rw [hF₀, hM₀, hCq]; ring
    rw [this]
    calc Cq * ‖v‖ ≤ Cq * (|Cv| * ‖u‖) := mul_le_mul_of_nonneg_left hvn' (by positivity)
      _ = Cq * |Cv| * ‖u‖ := by ring
  choose C hC0 hC using key
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j,
    fun a β c hab hah hβc u g hg => ?_⟩
  choose h hh hhn using fun j => hC j (a j) (β j) (c j) (hab j) (hah j) (hβc j) u g (hg j)
  refine ⟨⟨g, fun j => ⟨h j, hh j⟩⟩, rfl, ?_⟩
  rw [norm_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have : (⟨g, fun j => ⟨h j, hh j⟩⟩ : A.HolderMap 0 r ℝ).rep j = h j :=
    BoundedContDiffHolderMap.ext fun z => by rw [coe_rep, hh j]; rfl
  rw [this]
  exact hhn j

/-- Two functions on `M` agreeing on every `e_i⁻¹(e_i(tsupport χ_i))` agree. -/
theorem funext_chart {F G : M → ℝ}
    (h : ∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
      F ((A.chart i).val.symm z) = G ((A.chart i).val.symm z)) : F = G := by
  funext y
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, A.χ i y ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
  have hys : y ∈ (A.chart i).val.source := A.tsupport_subset i (subset_tsupport _ hi)
  have := h i _ ⟨y, subset_tsupport _ hi, rfl⟩
  rwa [(A.chart i).val.left_inv hys] at this

/-- **`L` as a bounded linear map** `C^{2,r}(M) → C^{0,r}(M)` (given realizability). -/
theorem exists_chartOp (hr0 : 0 < r) (hr1 : r < 1) {Λ : ℝ}
    (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
    (β : Fin A.m → ComplexModel n → ComplexModel n) (c : Fin A.m → ComplexModel n → ℝ)
    (hab : ∀ i x, ‖a i x‖ ≤ Λ) (hah : ∀ i x y, ‖a i x - a i y‖ ≤ Λ * ‖x - y‖ ^ (r : ℝ))
    (hβc : ∀ i, IsLowerCoeff (β i) (c i) Λ r) (U : Fin A.m → Set (ComplexModel n))
    (hKU : ∀ i, (A.chart i).val '' tsupport (A.χ i) ⊆ U i)
    (hUt : ∀ i, U i ⊆ (A.chart i).val.target)
    (hreal : ∀ u : A.HolderMap 2 r ℝ, ∃ g : M → ℝ, ∀ i, ∀ z ∈ U i,
      g ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) :
    ∃ T : A.HolderMap 2 r ℝ →ₗ[ℝ] A.HolderMap 0 r ℝ, ∃ CT : ℝ, 0 ≤ CT ∧
      (∀ u, ‖T u‖ ≤ CT * ‖u‖) ∧
      ∀ u, ∀ i, ∀ z ∈ U i, T u ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z := by
  have hr1' : r ≤ 1 := hr1.le
  obtain ⟨C, hC0, hC⟩ := exists_mem_of_chartRel (A := A) b hr0 hr1 Λ
  have hG : ∀ u : A.HolderMap 2 r ℝ, ∃ G : A.HolderMap 0 r ℝ,
      (∀ i, ∀ z ∈ U i, G ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z) ∧
      ‖G‖ ≤ C * ‖u‖ := by
    intro u
    obtain ⟨g, hg⟩ := hreal u
    obtain ⟨G, hGg, hGn⟩ := hC a β c hab hah hβc u g fun i z hz => hg i z (hKU i hz)
    exact ⟨G, fun i z hz => by rw [hGg]; exact hg i z hz, hGn⟩
  choose Top hTrel hTn using hG
  have hrelK : ∀ u i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), Top u ((A.chart i).val.symm z) =
      ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z :=
    fun u i z hz => hTrel u i z (hKU i hz)
  refine ⟨{ toFun := Top, map_add' := fun u v => ?_, map_smul' := fun k u => ?_ }, C, hC0,
    hTn, hTrel⟩
  · ext y
    have := congrFun (eq_of_chartRel (A := A) b (u := ⇑(u + v)) (hrelK (u + v))
      (g' := ⇑(Top u + Top v)) fun i z hz => by
        have hzt := (hUt i) (hKU i hz)
        rw [HolderAtlas.HolderMap.coe_add, Pi.add_apply, hrelK u i z hz, hrelK v i z hz,
          ← ellipticOp_add_of_contDiffAt b _ _ _ (contDiffAt_comp_symm hr1' u _ hzt)
            (contDiffAt_comp_symm hr1' v _ hzt)]
        rfl) y
    exact this
  · ext y
    have := congrFun (eq_of_chartRel (A := A) b (u := ⇑(k • u)) (hrelK (k • u))
      (g' := ⇑(k • Top u)) fun i z hz => by
        have hzt := (hUt i) (hKU i hz)
        rw [HolderAtlas.HolderMap.coe_smul, Pi.smul_apply, smul_eq_mul, hrelK u i z hz,
          ← ellipticOp_smul_of_contDiffAt b _ _ _ k (contDiffAt_comp_symm hr1' u _ hzt)]
        rfl) y
    simpa using this

/-- **`L - s` is onto `C^{0,r}(M)` for every `s > 0`** (`c_i ≤ 0`; blueprint
`bou:kahler-laplacian-solvability`, the continuity in the parameter). -/
theorem exists_ellipticOp_sub_eq [CompactSpace M] {lam Λ : ℝ} (hlam : 0 < lam) (hr0 : 0 < r)
    (hr1 : r < 1)
    (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
    (β : Fin A.m → ComplexModel n → ComplexModel n) (c : Fin A.m → ComplexModel n → ℝ)
    (ha : ∀ i, IsEllipticCoeff (a i) lam Λ r) (hβc : ∀ i, IsLowerCoeff (β i) (c i) Λ r)
    (hc : ∀ i x, c i x ≤ 0) (U : Fin A.m → Set (ComplexModel n)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, (A.chart i).val '' tsupport (A.χ i) ⊆ U i)
    (hUt : ∀ i, U i ⊆ (A.chart i).val.target)
    (hreal : ∀ u : A.HolderMap 2 r ℝ, ∃ g : M → ℝ, ∀ i, ∀ z ∈ U i,
      g ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z)
    {s : ℝ} (hs : 0 < s) (f : A.HolderMap 0 r ℝ) :
    ∃ u : A.HolderMap 2 r ℝ, ∀ i, ∀ z ∈ U i,
      ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z -
        s * u ((A.chart i).val.symm z) = f ((A.chart i).val.symm z) := by
  have hr1' : r ≤ 1 := hr1.le
  obtain ⟨T, CT, -, -, hTrel⟩ := exists_chartOp (A := A) b hr0 hr1 a β c
    (fun i => (ha i).bound) (fun i => (ha i).holder) hβc U hKU hUt hreal
  obtain ⟨μ₀, hμ₀1, hpar⟩ := exists_ellipticOp_sub_eq_of_large (A := A) b hlam hr0 hr1 a β c ha
    hβc hc U hU hKU hUt hreal
  set μ₁ := max μ₀ s with hμ₁
  have hμ₁0 : 0 ≤ μ₁ := (zero_le_one.trans hμ₀1).trans (le_max_left _ _)
  have hsμ₁ : s ≤ μ₁ := le_max_right _ _
  set ι' : A.HolderMap 2 r ℝ →ₗ[ℝ] A.HolderMap 0 r ℝ :=
    (toZeroCLM (A := A) (F := ℝ) (k := 2) hr1' (by norm_num)).toLinearMap with hι'
  have hι'apply : ∀ u y, ι' u y = u y := fun u y => rfl
  have hι'n : ∀ u, ‖ι' u‖ ≤ 3 * ‖u‖ := fun u => norm_toZero_le hr1' (by norm_num) u
  set T₀ := T - μ₁ • ι' with hT₀
  set T₁ := T - s • ι' with hT₁
  -- the relation of `T u - s' u` with the coefficients `(a, β, c - s')`
  have hTrelK : ∀ u i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i), T u ((A.chart i).val.symm z) =
      ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z :=
    fun u i z hz => hTrel u i z (hKU i hz)
  -- `T₀` is onto by the parametrix
  have h0 : Function.Surjective T₀ := by
    intro g
    obtain ⟨u, hu⟩ := hpar μ₁ (le_max_left _ _) g
    refine ⟨u, ?_⟩
    ext y
    have := congrFun (funext_chart (A := A) (F := ⇑(T₀ u)) (G := ⇑g) fun i z hz => by
      rw [hT₀, LinearMap.sub_apply, LinearMap.smul_apply, HolderAtlas.HolderMap.coe_sub,
        Pi.sub_apply, HolderAtlas.HolderMap.coe_smul, Pi.smul_apply, hι'apply,
        hTrelK u i z hz, smul_eq_mul]
      exact hu i z (hKU i hz)) y
    exact this
  -- the uniform estimate
  obtain ⟨CS, hCS0, hCS⟩ := ManifoldSchauder.exists_norm_le A b (Λ := Λ + μ₁) hlam hr0 hr1
  set C' := CS * (1 + 1 / s) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hest : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ C' * ‖T₀ u + t • (T₁ u - T₀ u)‖ := by
    intro t ht u
    set s' := μ₁ - t * (μ₁ - s) with hs'
    have hs's : s ≤ s' := by
      rw [hs']; nlinarith [ht.2, sub_nonneg.2 hsμ₁]
    have hs'μ : s' ≤ μ₁ := by
      rw [hs']; nlinarith [ht.1, sub_nonneg.2 hsμ₁]
    have hs'0 : 0 < s' := hs.trans_le hs's
    set G := T₀ u + t • (T₁ u - T₀ u) with hG
    have hGy : ∀ y, G y = T u y - s' * u y := fun y => by
      simp only [hG, hT₀, hT₁, LinearMap.sub_apply, LinearMap.smul_apply,
        HolderAtlas.HolderMap.coe_add, HolderAtlas.HolderMap.coe_sub,
        HolderAtlas.HolderMap.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hι'apply, hs']
      ring
    -- the maximum principle: `|u| ≤ ‖G‖ / s`
    have hmax : ∀ y, |u y| ≤ ‖G‖ / s := fun y => by
      have h1 := ManifoldMaxPrinciple.mul_abs_le_of_chartOp_sub b hr1' (fun i => (ha i).symm)
        (fun i x v => le_trans (mul_nonneg hlam.le (sq_nonneg ‖v‖)) ((ha i).elliptic x v))
        hc hs'0 u (T u) (hTrelK u) (F := ‖G‖) (fun y' => by
          rw [← hGy]; exact abs_apply_le_norm G y') y
      rw [le_div_iff₀ hs]
      have h3 : s * |u y| ≤ s' * |u y| := mul_le_mul_of_nonneg_right hs's (abs_nonneg _)
      linarith
    -- the Schauder estimate with the coefficients `(a, β, c - s')`
    have hcls : ∀ i, IsEllipticCoeff (a i) lam (Λ + μ₁) r := fun i =>
      ⟨(ha i).symm, (ha i).elliptic, fun x => ((ha i).bound x).trans (by linarith),
        fun x y => ((ha i).holder x y).trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg (norm_nonneg _) _))⟩
    have hclw : ∀ i, IsLowerCoeff (β i) (fun x => c i x - s') (Λ + μ₁) r := fun i =>
      ⟨fun x => ((hβc i).bound_β x).trans (by linarith),
        fun x y => ((hβc i).holder_β x y).trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg (norm_nonneg _) _)),
        fun x => (abs_sub _ _).trans (by rw [abs_of_pos hs'0]; linarith [(hβc i).bound_c x]),
        fun x y => by
          rw [show c i x - s' - (c i y - s') = c i x - c i y by ring]
          exact ((hβc i).holder_c x y).trans (mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (norm_nonneg _) _))⟩
    have hS0 : 0 ≤ ‖G‖ / s := by positivity
    have h2 := hCS a β (fun i x => c i x - s') hcls hclw u G (‖G‖ / s) hS0 hmax
      fun i z hz => by
        rw [hGy, hTrelK u i z hz]
        simp only [ellipticOp]
        ring
    calc ‖u‖ ≤ CS * (‖G‖ + ‖G‖ / s) := h2
      _ = C' * ‖G‖ := by rw [hC']; ring
  have hK : ∀ u, ‖T₁ u - T₀ u‖ ≤ (3 * (μ₁ - s)) * ‖u‖ := fun u => by
    have e : T₁ u - T₀ u = (μ₁ - s) • ι' u := by
      rw [hT₀, hT₁]; simp only [LinearMap.sub_apply, LinearMap.smul_apply]; module
    rw [e, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hsμ₁)]
    calc (μ₁ - s) * ‖ι' u‖ ≤ (μ₁ - s) * (3 * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hι'n u) (sub_nonneg.2 hsμ₁)
      _ = 3 * (μ₁ - s) * ‖u‖ := by ring
  have h1 := MethodOfContinuity.surjective_of_continuity T₀ T₁ hC'0
    (by linarith [sub_nonneg.2 hsμ₁]) hK hest h0
  obtain ⟨u, hu⟩ := h1 f
  refine ⟨u, fun i z hz => ?_⟩
  have := congrArg (fun F : A.HolderMap 0 r ℝ => F ((A.chart i).val.symm z)) hu
  simp only [hT₁, LinearMap.sub_apply, LinearMap.smul_apply, HolderAtlas.HolderMap.coe_sub,
    HolderAtlas.HolderMap.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hι'apply] at this
  rw [← hTrel u i z hz]
  exact this

end SGPT.Foundations.Analysis.Pending.ManifoldContinuity
