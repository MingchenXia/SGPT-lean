import SGPT.Foundations.Analysis.Pending.ManifoldSchauder
import SGPT.Foundations.Analysis.Pending.ManifoldHolderPushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The maximum principle for `L - μ` on a compact complex manifold

Let `A` be a Hölder atlas of a compact complex manifold `M`, `b` an orthonormal basis of the real
inner product space `ComplexModel n`, and `L` an operator given chartwise, as in
`ManifoldSchauder.exists_norm_le`: in the chart `e_i` it reads
`a_i : D² + D(·)(β_i) + c_i` on `e_i(tsupport χ_i)`, now only with `a_i(z)` symmetric positive
semidefinite and `c_i ≤ 0`.  For `μ > 0` and `u ∈ C^{2,r}(M)` with `|L u - μ u| ≤ F` on `M`:
`μ |u| ≤ F` on `M` (`mul_abs_le_of_chartOp_sub`).

Proof: at a maximum point `y₀` of `u` (compactness, `HolderMap.continuous`) pick a chart with
`χ_i(y₀) ≠ 0`; `u ∘ e_i⁻¹` agrees near `e_i(y₀)` with a `C²` function (`exists_local_rep`) having a
local maximum there, so its gradient vanishes and `a_i : D²(u ∘ e_i⁻¹) ≤ 0`
(`IsLocalMax.fderiv_fderiv_nonpos`, `WholeSpaceMaxPrinciple.hessTrace_nonpos`); hence
`L u(y₀) ≤ c_i u(y₀)` and `μ u(y₀) ≤ μ u(y₀) - L u(y₀) ≤ F` when `u(y₀) ≥ 0`.  Apply this to `-u` too.

TN.4 B5 linear track L4 (blueprint `bou:kahler-laplacian-solvability`: injectivity of
`Δ_ω - 1` and the bound `sup |u| ≤ sup |(Δ_ω - s) u| / s` of the method of continuity).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldMaxPrinciple

open FirstPass EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple
  ManifoldSchauder

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (ComplexModel n)) {r : ℝ≥0}

/-- Near a point of a chart target, `u ∘ e⁻¹` agrees with an element of `C^{2,r}_b` (`r ≤ 1`). -/
theorem exists_local_rep (hr : r ≤ 1) (u : A.HolderMap 2 r ℝ) (e : ComplexChart n M)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ v : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ,
      ⇑v =ᶠ[𝓝 z₀] fun w => u (e.val.symm w) := by
  obtain ⟨K', hK'c, hzK', hK't⟩ := exists_compact_between isCompact_singleton e.val.open_target
    (singleton_subset_iff.2 hz₀)
  obtain ⟨σ, hσs, hσc, hσt, hσ1⟩ :=
    exists_contDiff_eq_one_of_isCompact hK'c e.val.open_target hK't
  obtain ⟨C, hC⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 2) (r := r)
    (F := ℝ) hr e (contDiff_infty.1 hσs 3) hσc hσt
  obtain ⟨v, hv, -⟩ := hC u
  refine ⟨v, ?_⟩
  filter_upwards [isOpen_interior.mem_nhds (hzK' rfl)] with w hw
  rw [hv w, hσ1 w (interior_subset hw), one_smul]

/-- One half of the maximum principle: `μ u ≤ F`. -/
theorem mul_le_of_chartOp_sub [CompactSpace M] (hr : r ≤ 1)
    {a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n}
    {β : Fin A.m → ComplexModel n → ComplexModel n} {c : Fin A.m → ComplexModel n → ℝ}
    (hsymm : ∀ i x v w, ⟪a i x v, w⟫ = ⟪v, a i x w⟫) (hpos : ∀ i x v, 0 ≤ ⟪a i x v, v⟫)
    (hc : ∀ i x, c i x ≤ 0) {μ F : ℝ} (hμ : 0 < μ) (u : A.HolderMap 2 r ℝ) (g : M → ℝ)
    (hrep : ∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
      g ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z)
    (hF : ∀ y, |g y - μ * u y| ≤ F) (y : M) : μ * u y ≤ F := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF y)
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, mem_univ y⟩
    (HolderAtlas.HolderMap.continuous u).continuousOn
  have hmax : ∀ y', u y' ≤ u y₀ := fun y' => hy₀ (mem_univ y')
  by_cases hu0 : u y₀ ≤ 0
  · exact (mul_le_mul_of_nonneg_left (hmax y) hμ.le).trans
      ((mul_nonpos_of_nonneg_of_nonpos hμ.le hu0).trans hF0)
  rw [not_le] at hu0
  -- a chart around the maximum point
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, A.χ i y₀ ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
  set e := A.chart i with he
  have hy₀s : y₀ ∈ e.val.source := A.tsupport_subset i (subset_tsupport _ hi)
  set z₀ := e.val y₀ with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hy₀s
  have hz₀K : z₀ ∈ e.val '' tsupport (A.χ i) := ⟨y₀, subset_tsupport _ hi, rfl⟩
  have hsy : e.val.symm z₀ = y₀ := e.val.left_inv hy₀s
  obtain ⟨v, hv⟩ := exists_local_rep (A := A) hr u e hz₀t
  have hv2 : ContDiff ℝ 2 ⇑v := WholeSpaceSolvability.contDiff_two v
  have hvmax : IsLocalMax (⇑v) z₀ := by
    filter_upwards [hv, e.val.open_target.mem_nhds hz₀t] with w hw _
    rw [hw, hv.eq_of_nhds, hsy]
    exact hmax _
  -- the first- and second-order conditions
  have hD : fderiv ℝ v z₀ = 0 := hvmax.fderiv_eq_zero
  have hD2 : hessTrace b (a i z₀) (fderiv ℝ (fderiv ℝ v) z₀) ≤ 0 :=
    hessTrace_nonpos b (hsymm i z₀) (hpos i z₀) fun h =>
      hvmax.fderiv_fderiv_nonpos hv2.contDiffAt h
  have hg : g y₀ ≤ c i z₀ * u y₀ := by
    have h1 := hrep i z₀ hz₀K
    rw [hsy, ← ellipticOp_congr b (a i) (β i) (c i) hv, ellipticOp, hD,
      zero_apply, hv.eq_of_nhds, hsy] at h1
    linarith
  have hμu : μ * u y₀ ≤ F := by
    have h1 := (le_abs_self _).trans (hF y₀)
    have h2 : c i z₀ * u y₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hc i z₀) hu0.le
    have h3 := neg_le_abs (g y₀ - μ * u y₀)
    linarith [hF y₀]
  exact (mul_le_mul_of_nonneg_left (hmax y) hμ.le).trans hμu

/-- **The maximum principle for `L - μ` on a compact manifold**: `μ |u| ≤ F` when
`|L u - μ u| ≤ F` (`a_i` symmetric positive semidefinite, `c_i ≤ 0`, `μ > 0`). -/
theorem mul_abs_le_of_chartOp_sub [CompactSpace M] (hr : r ≤ 1)
    {a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n}
    {β : Fin A.m → ComplexModel n → ComplexModel n} {c : Fin A.m → ComplexModel n → ℝ}
    (hsymm : ∀ i x v w, ⟪a i x v, w⟫ = ⟪v, a i x w⟫) (hpos : ∀ i x v, 0 ≤ ⟪a i x v, v⟫)
    (hc : ∀ i x, c i x ≤ 0) {μ F : ℝ} (hμ : 0 < μ) (u : A.HolderMap 2 r ℝ) (g : M → ℝ)
    (hrep : ∀ i, ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
      g ((A.chart i).val.symm z) =
        ellipticOp b (a i) (β i) (c i) (fun w => u ((A.chart i).val.symm w)) z)
    (hF : ∀ y, |g y - μ * u y| ≤ F) (y : M) : μ * |u y| ≤ F := by
  have h1 := mul_le_of_chartOp_sub b hr hsymm hpos hc hμ u g hrep hF y
  have h2 := mul_le_of_chartOp_sub b hr hsymm hpos hc hμ (-u) (fun y => -g y)
    (fun i z hz => by
      simp only [HolderAtlas.HolderMap.coe_neg, Pi.neg_apply]
      rw [ellipticOp_neg, hrep i z hz])
    (fun y' => by
      simp only [HolderAtlas.HolderMap.coe_neg, Pi.neg_apply]
      rw [show -g y' - μ * -u y' = -(g y' - μ * u y') by ring, abs_neg]
      exact hF y') y
  simp only [HolderAtlas.HolderMap.coe_neg, Pi.neg_apply] at h2
  rcases abs_cases (u y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

end SGPT.Foundations.Analysis.Pending.ManifoldMaxPrinciple
