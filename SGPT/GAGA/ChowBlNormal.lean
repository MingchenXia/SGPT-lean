import SGPT.GAGA.ChowBlLocal

/-!
# Normal coordinates of a blow-up: the derivative computations


Chart-level lemmas for the immersion of the blow-up embedding.  `C` is flattened near `x₀` by
`Φ ∘ e` onto `ℂᵏ × 0`; `NormalIdx n k` are the normal indices `k ≤ l`; `σⱼ = monomial k j` is the
`j`-th monomial chart of the blow-up of `ℂⁿ` along `ℂᵏ × 0` and `γⱼ = e⁻¹ ∘ Φ⁻¹ ∘ σⱼ`
(`monoBase`).  For generators `g_q = ∑_l b_{ql} t_l` of `𝓘_C` (`t_l` the normal coordinates),
`g_q ∘ γⱼ = wⱼ · ũ_q` with `ũ_q(w) = ∑_l b_{ql}(γⱼ w) ŵ_l`, `ŵ_l = w_l` (`l ≠ j`), `ŵ_j = 1`
(`genFun_monoBase_eq`).

* `fderiv_monomial_eq_zero`: a vector killed by `dσⱼ(w₀)`, `w₀ⱼ = 0`, has zero coordinates
  outside the normal indices `≠ j`;
* `fderiv_tildeU_apply`: along such a vector `ξ`, `dũ(w₀) ξ = B(x₀) ξ'` (`ξ'` the normal part of
  `ξ` with `ξ'_j = 0`).
* chart helpers: `mfderiv_eq_fderiv_chart`, `differentiableAt_chart_of_mdifferentiableAt`,
  `eventually_differentiableAt_chart`, `liftedOpen_extChartAt_symm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

universe u

/-! ### Charts -/

section Charts

variable {n : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]

/-- The manifold derivative between `SGPT.Foundations.Analysis` manifolds is the derivative of the
chart expression. -/
theorem mfderiv_eq_fderiv_chart {f : Y → M} {p : Y}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f p) :
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f p =
      fderiv ℂ (fun z => chartAt (ComplexModel n) (f p) (f ((chartAt (ComplexModel n) p).symm z)))
        (chartAt (ComplexModel n) p p) := by
  rw [hf.mfderiv]
  simp [fderivWithin_univ]
  rfl

theorem differentiableAt_chart_of_mdifferentiableAt {f : Y → M} {p : Y}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f p) :
    DifferentiableAt ℂ
      (fun z => chartAt (ComplexModel n) (f p) (f ((chartAt (ComplexModel n) p).symm z)))
      (chartAt (ComplexModel n) p p) := by
  have := hf.differentiableWithinAt_writtenInExtChartAt
  rw [modelWithCornersSelf_coe, Set.range_id, differentiableWithinAt_univ] at this
  exact this

/-- Finitely many functions holomorphic at `p` are differentiable, read in the chart at `p`,
near `e p`. -/
theorem eventually_differentiableAt_chart [IsComplexManifold n Y] {ι : Type} [Fintype ι]
    {f : Y → ι → ℂ} {p : Y} (hf : ∀ k, HolomorphicAt n (fun y => f y k) p) :
    ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p),
      DifferentiableAt ℂ (fun z => f ((chartAt (ComplexModel n) p).symm z)) z := by
  have h : ∀ k, OkaRelationSheaf.HolAt (fun z => f ((chartAt (ComplexModel n) p).symm z) k)
      (chartAt (ComplexModel n) p p) := fun k =>
    CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ p) (hf k)
  filter_upwards [eventually_all.2 h] with z hz
  exact differentiableAt_pi.mpr hz

/-- The inverse chart of a lifted open set. -/
theorem liftedOpen_extChartAt_symm {S : TopologicalSpace.Opens (ComplexModel n)}
    (q₀ : LiftedOpen.{u} S) (w : ComplexModel n) (hw : w ∈ S) :
    (extChartAt 𝓘(ℂ, ComplexModel n) q₀).symm w = LiftedOpen.mk S w hw := by
  have hsrc : LiftedOpen.mk S w hw ∈ (extChartAt 𝓘(ℂ, ComplexModel n) q₀).source := by
    rw [extChartAt_source]
    exact mem_chart_source _ (LiftedOpen.mk S w hw)
  have := (extChartAt 𝓘(ℂ, ComplexModel n) q₀).left_inv hsrc
  rw [LiftedOpen.extChartAt_eq] at this
  exact this

/-- The coordinates of the derivative of a map into `ℂⁿ`. -/
theorem fderiv_coord_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ComplexModel n} {z : E} (hf : DifferentiableAt ℂ f z) (v : E) (i : Fin n) :
    fderiv ℂ f z v i = fderiv ℂ (fun y => f y i) z v := by
  have h : (fun y => f y i) = (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) ∘ f := rfl
  rw [h, fderiv_comp z (EuclideanSpace.proj i).differentiableAt hf,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

end Charts

/-! ### Normal coordinates -/

section Normal

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {x₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)} {k : ℕ}

/-- The normal indices `k ≤ l`. -/
abbrev NormalIdx (n k : ℕ) := {l : Fin n // k ≤ l.1}

/-- `ŵ`: the normal coordinates of `w`, with `1` at `j`. -/
def hatW (j : NormalIdx n k) (w : ComplexModel n) (l : NormalIdx n k) : ℂ :=
  if l = j then 1 else w l.1

variable (Φ k) in
/-- `γⱼ = e⁻¹ ∘ Φ⁻¹ ∘ σⱼ`: the base point of the `j`-th monomial chart. -/
def monoBase (j : NormalIdx n k) (w : ComplexModel n) : M :=
  (chartAt (ComplexModel n) x₀).symm (Φ.invFun (monomial k j.1 w))

variable (Φ k) in
/-- `ũ_q(w) = ∑_l b_{ql}(γⱼ w) ŵ_l`. -/
def tildeU {κ : Type} [Fintype κ] (j : NormalIdx n k) (b : κ → NormalIdx n k → M → ℂ)
    (w : ComplexModel n) (q : κ) : ℂ :=
  ∑ l, b q l (monoBase Φ k j w) * hatW j w l

/-- The normal coordinates of `γⱼ(w)` are `wⱼ ŵ_l`. -/
theorem flatCoord_monoBase (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (j : NormalIdx n k) {w : ComplexModel n} (hw : monomial k j.1 w ∈ Φ.target)
    (l : NormalIdx n k) : flatCoord Φ l.1 (monoBase Φ k j w) = w j.1 * hatW j w l := by
  have h := (flatInverse_mem Φ hw hΦsrc).2
  show (Φ.toFun (chartAt (ComplexModel n) x₀ (monoBase Φ k j w))) l.1 = _
  rw [monoBase, h, monomial_apply, hatW]
  by_cases hl : l = j
  · subst hl; simp
  · have hne : l.1 ≠ j.1 := fun h => hl (Subtype.ext h)
    rw [if_pos ⟨l.2, hne⟩, if_neg hl]
    ring

/-- `g_q ∘ γⱼ = wⱼ ũ_q` for `g_q = ∑ b_{ql} t_l`. -/
theorem genFun_monoBase_eq (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    {κ : Type} [Fintype κ] {g : κ → M → ℂ} {b : κ → NormalIdx n k → M → ℂ}
    (j : NormalIdx n k) {w : ComplexModel n} (hw : monomial k j.1 w ∈ Φ.target)
    (hb : ∀ q, g q (monoBase Φ k j w) =
      ∑ l, b q l (monoBase Φ k j w) * flatCoord Φ l.1 (monoBase Φ k j w)) (q : κ) :
    g q (monoBase Φ k j w) = w j.1 * tildeU Φ k j b w q := by
  rw [hb q, tildeU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [flatCoord_monoBase hΦsrc j hw l]
  ring

/-- **The kernel of `dσⱼ`** at a point with `wⱼ = 0` lies in the normal directions `≠ j`. -/
theorem fderiv_monomial_eq_zero {j : Fin n} {w₀ ξ : ComplexModel n}
    (h0 : fderiv ℂ (monomial k j) w₀ ξ = 0) (i : Fin n) (hi : ¬(k ≤ i.1 ∧ i ≠ j)) :
    ξ i = 0 := by
  have h1 := fderiv_coord_apply ((contDiff_monomial k j).differentiable (by simp) w₀) ξ i
  rw [h0] at h1
  have h2 : (fun w => monomial k j w i) = fun w : ComplexModel n => w i := by
    funext w; simp [monomial_apply, hi]
  rw [h2] at h1
  have h3 : fderiv ℂ (fun w : ComplexModel n => w i) w₀ ξ = ξ i := by
    have : (fun w : ComplexModel n => w i) = (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) :=
      rfl
    rw [this, ContinuousLinearMap.fderiv]
    rfl
  rw [h3] at h1
  simpa using h1.symm

/-- **The derivative of `ũ`** at `w₀` (`σⱼ(w₀) = Φ(e x₀) = 0`) along `ξ ∈ ker dσⱼ(w₀)`:
`dũ_q(w₀) ξ = ∑_{l ≠ j} b_{ql}(x₀) ξ_l`. -/
theorem fderiv_tildeU_apply (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x₀ x₀) = 0)
    {κ : Type} [Fintype κ] {b : κ → NormalIdx n k → M → ℂ}
    (hb : ∀ q l, HolomorphicAt n (b q l) x₀) (j : NormalIdx n k) {w₀ ξ : ComplexModel n}
    (hw₀ : monomial k j.1 w₀ = 0) (hξ : fderiv ℂ (monomial k j.1) w₀ ξ = 0) (q : κ) :
    HasFDerivAt (fun w => tildeU Φ k j b w q)
      (fderiv ℂ (fun w => tildeU Φ k j b w q) w₀) w₀ ∧
    fderiv ℂ (fun w => tildeU Φ k j b w q) w₀ ξ =
      ∑ l, b q l x₀ * (if l = j then 0 else ξ l.1) := by
  classical
  have h0T : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← hΦ0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = chartAt (ComplexModel n) x₀ x₀ := by
    rw [← hΦ0]; exact Φ.left_inv _ Φ.center_mem_source
  have hbase0 : monoBase Φ k j w₀ = x₀ := by
    rw [monoBase, hw₀, hinv0]
    exact (chartAt (ComplexModel n) x₀).left_inv (mem_chart_source _ x₀)
  -- the coefficient functions `w ↦ b_{ql}(γⱼ w)`
  have hB : ∀ l, HasFDerivAt (fun w => b q l (monoBase Φ k j w))
      ((fderiv ℂ (fun u => b q l ((chartAt (ComplexModel n) x₀).symm (Φ.invFun u))) 0).comp
        (fderiv ℂ (monomial k j.1) w₀)) w₀ := by
    intro l
    have hout : DifferentiableAt ℂ
        (fun u => b q l ((chartAt (ComplexModel n) x₀).symm (Φ.invFun u))) 0 := by
      have h1 : OkaRelationSheaf.HolAt
          (fun z => b q l ((chartAt (ComplexModel n) x₀).symm z))
          (chartAt (ComplexModel n) x₀ x₀) :=
        CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x₀) (hb q l)
      have h2 : DifferentiableAt ℂ Φ.invFun 0 :=
        Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0T)
      have h3 := h1.self_of_nhds
      rw [← hinv0] at h3
      exact h3.comp 0 h2
    have hin : HasFDerivAt (monomial k j.1) (fderiv ℂ (monomial k j.1) w₀) w₀ :=
      ((contDiff_monomial k j.1).differentiable (by simp) w₀).hasFDerivAt
    rw [← hw₀] at hout
    have := hout.hasFDerivAt.comp w₀ hin
    rw [hw₀] at this
    exact this
  have hH : ∀ l, HasFDerivAt (fun w : ComplexModel n => hatW j w l)
      (if l = j then 0 else (EuclideanSpace.proj l.1 : ComplexModel n →L[ℂ] ℂ)) w₀ := by
    intro l
    by_cases hl : l = j
    · simp only [hatW, hl, if_true]
      exact hasFDerivAt_const 1 w₀
    · simp only [hatW, hl, if_false]
      exact (EuclideanSpace.proj l.1 : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
  have hsum : HasFDerivAt (fun w => tildeU Φ k j b w q)
      (∑ l, (b q l (monoBase Φ k j w₀) •
          (if l = j then 0 else (EuclideanSpace.proj l.1 : ComplexModel n →L[ℂ] ℂ)) +
        hatW j w₀ l • ((fderiv ℂ (fun u => b q l ((chartAt (ComplexModel n) x₀).symm
          (Φ.invFun u))) 0).comp (fderiv ℂ (monomial k j.1) w₀)))) w₀ := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hB l).mul (hH l))
    simpa [tildeU] using this
  refine ⟨hsum.differentiableAt.hasFDerivAt, ?_⟩
  rw [hsum.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hξ, map_zero, hbase0, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · simp [hl]
  · simp [hl]

end Normal

end SGPT.GAGA.ChowBl
