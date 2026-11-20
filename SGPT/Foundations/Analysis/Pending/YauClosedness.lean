import SGPT.Foundations.Analysis.Pending.YauSmoothOpenness

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Limits of solutions of the `ε`-continuity path (closedness)

Let `A` be a Kähler background on a compact complex manifold `Y`, `F` chart-smooth.  A sequence of
chart-smooth solutions `φ_j` of
`(A + ddᶜφ_j)^N = e^{t_j F + ε_j φ_j + κ_j} A^N`, `A + ddᶜφ_j` Kähler,
with `t_j → t₀`, `ε_j → ε₀`, `κ_j → κ₀` and **bounded in `C^{2,r}(Y)`** has a limit: there is a
chart-smooth `φ₀` with `A + ddᶜφ₀` Kähler and `(A + ddᶜφ₀)^N = e^{t₀F + ε₀φ₀ + κ₀} A^N`
(`exists_smooth_of_tendsto`, blueprint `bou:yau-closedness`).  Proof:

* compactness of `C^{2,r}(Y) ⊂ C^{2,s}(Y)`, `s = r/2` (`HolderAtlas.HolderMap.exists_subseq_tendsto_ofLE`);
* convergence in `C^{2,s}(Y)` gives pointwise convergence of the values (`tendsto_apply`) and of the
  complex Hessians in **every** chart (`tendsto_complexHessian`: a cut-off equal to `1` near the point
  and the chart-independence estimate `HolderAtlas.HolderMap.exists_smul_comp_symm`);
* the equation in determinant form `det(H_A + Hess φ_j) = e^{G_j} det H_A` (`det_eq_of_density`)
  passes to the limit; the limit of positive definite matrices is positive semidefinite, and its
  determinant `e^{G₀} det H_A` is positive, so it is positive definite (`posDef_of_tendsto`,
  `limit_of_tendsto`);
* the limit `U ∈ C^{2,s}(Y)` solves `ma A U = (t₀F + κ₀) + ε₀U` (`ma_eq_of_det_eq`), hence is
  chart-smooth by the regularity bootstrap (`MongeAmpereRegularity.chartSmooth_of_ma_eq`).

The uniform `C^{2,r}` bound itself (TN-CLASSICAL's `T2`, the statement under discussion) is a hypothesis here.

TN.4 B5, N5 = P3(c) of the the proof of Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.YauClosedness

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder ManifoldTubePositivity
  PositiveClasses

/-! ### Limits of positive definite matrices -/

/-- A limit of positive definite matrices with nonzero determinant is positive definite. -/
theorem posDef_of_tendsto {n : ℕ} {P : ℕ → Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : ∀ j, (P j).PosDef) (hPQ : Tendsto P atTop (𝓝 Q)) (hdet : Q.det ≠ 0) : Q.PosDef := by
  have hQ : Q.IsHermitian := by
    have h1 : Tendsto (fun j => (P j)ᴴ) atTop (𝓝 Qᴴ) :=
      ((continuous_id.matrix_conjTranspose).tendsto Q).comp hPQ
    have h2 : (fun j => (P j)ᴴ) = P := funext fun j => (hP j).1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hPQ
  have hsemi : Q.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hQ fun x => ?_
    have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => star x ⬝ᵥ (M *ᵥ x) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact ge_of_tendsto ((hc.tendsto Q).comp hPQ) (Eventually.of_forall fun j =>
      (hP j).posSemidef.dotProduct_mulVec_nonneg x)
  exact hsemi.posDef_iff_det_ne_zero.mpr hdet

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Convergence in `C^{2,s}(Y)` -/

/-- Convergence in `C^{k,s}(Y)` gives pointwise convergence. -/
theorem tendsto_apply {HA : HolderAtlas N Y} {k : ℕ} {s : ℝ≥0} {v : ℕ → HA.HolderMap k s ℝ}
    {U : HA.HolderMap k s ℝ} (hv : Tendsto v atTop (𝓝 U)) (y : Y) :
    Tendsto (fun j => v j y) atTop (𝓝 (U y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hv ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hv
  have h := ManifoldContinuity.abs_apply_le_norm (v j - U) y
  rw [HolderAtlas.HolderMap.coe_sub, Pi.sub_apply] at h
  rwa [Real.norm_eq_abs]

/-- **Convergence in `C^{2,s}(Y)` gives convergence of the complex Hessians in every chart.** -/
theorem tendsto_complexHessian {HA : HolderAtlas N Y} {s : ℝ≥0} (hs : s ≤ 1)
    {v : ℕ → HA.HolderMap 2 s ℝ} {U : HA.HolderMap 2 s ℝ} (hv : Tendsto v atTop (𝓝 U))
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) :
    Tendsto (fun j => complexHessian (fun x => v j (e.val.symm x)) z) atTop
      (𝓝 (complexHessian (fun x => U (e.val.symm x)) z)) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp e.val.open_target z hz
  have hKt : closedBall z (ρ / 2) ⊆ e.val.target :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨σ, hσs, hσc, hσt, hσ1, -⟩ :=
    exists_cutoff (isCompact_closedBall z (ρ / 2)) e.val.open_target hKt
  obtain ⟨C, hC⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := HA) (k := 2) (F := ℝ) hs e
    (contDiff_infty.1 hσs (2 + 1)) hσc hσt
  choose w hw hwn using hC
  have hloc : ∀ ψ : HA.HolderMap 2 s ℝ, (⇑(w ψ)) =ᶠ[𝓝 z] fun x => ψ (e.val.symm x) := by
    intro ψ
    filter_upwards [ball_mem_nhds z (half_pos hρ)] with x hx
    rw [hw ψ x, hσ1 x (ball_subset_closedBall hx), smul_eq_mul, one_mul]
  have hk : ∀ ψ : HA.HolderMap 2 s ℝ,
      complexHessian (fun x => ψ (e.val.symm x)) z = complexHessian (w ψ) z := fun ψ =>
    (complexHessian_congr' (hloc ψ)).symm
  have hsub : ∀ j, w (v j) - w U = w (v j - U) := fun j =>
    BoundedContDiffHolderMap.ext fun x => by
      rw [BoundedContDiffHolderMap.coe_sub, Pi.sub_apply, hw, hw, hw,
        HolderAtlas.HolderMap.coe_sub, Pi.sub_apply, smul_sub]
  have hT : Tendsto (fun j => kfun (w (v j)) z) atTop (𝓝 (kfun (w U) z)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun j => C * ‖v j - U‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hv).const_mul C
      rwa [mul_zero] at this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) h0
    calc ‖kfun (w (v j)) z - kfun (w U) z‖ ≤ ‖w (v j) - w U‖ := norm_kfun_sub_le' _ _ z
      _ = ‖w (v j - U)‖ := by rw [hsub]
      _ ≤ C * ‖v j - U‖ := hwn _
  simp only [hk]
  exact hT

/-! ### The equation in determinant form -/

section Kahler

variable (A : KahlerBackground N Y)

/-- The coefficient matrix `H_A + complexHessian φ` of a Kähler form `A + ddᶜφ` is positive
definite in every chart. -/
theorem posDef_of_isKahler {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler) (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) :
    (normalizedHermitianMatrix (A.form.val.coeff e z) +
      complexHessian (fun x => φ (e.val.symm x)) z).PosDef := by
  rw [← YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ hz]
  exact posDef_coeff hK.1 hz

/-- **The density form in determinant form**: `(A + ddᶜφ)^N = e^G A^N` reads
`det(H_A + complexHessian φ) = e^G det H_A` in every chart. -/
theorem det_eq_of_density {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) {G : Y → ℝ}
    (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) :
    (normalizedHermitianMatrix (A.form.val.coeff e z) +
      complexHessian (fun x => φ (e.val.symm x)) z).det.re =
      Real.exp (G (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re := by
  have h11 : IsOneOne ((A.form + ddcClosedForm φ hφ).val.coeff e z) := (hK.1 e z hz).1
  have hA11 : IsOneOne (A.form.val.coeff e z) := (A.isKahler.1 e z hz).1
  have hd := hdens e z hz
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det h11,
    ConcentrationMassComparison.actualTopPowerDensity_eq_det hA11,
    YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ hz] at hd
  have hc : (0 : ℝ) < N.factorial / Real.pi ^ N := by positivity
  refine mul_left_cancel₀ hc.ne' ?_
  rw [hd]
  ring

/-- `ma A u = G` from the determinant form in every chart. -/
theorem ma_eq_of_det_eq {u G : Y → ℝ}
    (hdet : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => u (e.val.symm x)) z).det.re =
        Real.exp (G (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re)
    (y : Y) : ma A.form.val u y = G y := by
  set e := complexChartAt (n := N) y with he
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  have hpos : 0 < (normalizedHermitianMatrix (A.form.val.coeff e (e.val y))).det.re :=
    (Complex.pos_iff.mp (posDef_coeff A.isKahler.1 hz).det_pos).1
  have h := hdet e (e.val y) hz
  rw [e.val.left_inv (mem_complexChartAt_source y)] at h
  simp only [ma, maChart, ← he]
  rw [h, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  ring

/-- **Passing to the limit in the equation**: if `v_j → U` in `C^{2,s}(Y)`, every `v_j` has
`H_A + complexHessian v_j > 0` and `det(H_A + complexHessian v_j) = e^{G_j} det H_A` in every chart,
and `G_j → G₀` pointwise, then `H_A + complexHessian U > 0` and
`det(H_A + complexHessian U) = e^{G₀} det H_A` in every chart. -/
theorem limit_of_tendsto {HA : HolderAtlas N Y} {s : ℝ≥0} (hs : s ≤ 1)
    {v : ℕ → HA.HolderMap 2 s ℝ} {U : HA.HolderMap 2 s ℝ} (hv : Tendsto v atTop (𝓝 U))
    {G : ℕ → Y → ℝ} {G₀ : Y → ℝ} (hG : ∀ y, Tendsto (fun j => G j y) atTop (𝓝 (G₀ y)))
    (hpos : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => v j (e.val.symm x)) z).PosDef)
    (hdet : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => v j (e.val.symm x)) z).det.re =
        Real.exp (G j (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re) :
    (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => U (e.val.symm x)) z).PosDef) ∧
    (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => U (e.val.symm x)) z).det.re =
        Real.exp (G₀ (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re) := by
  have key : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => U (e.val.symm x)) z).det.re =
        Real.exp (G₀ (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re := by
    intro e z hz
    have hP := (tendsto_complexHessian hs hv e hz).const_add
      (normalizedHermitianMatrix (A.form.val.coeff e z))
    have h1 := ((Complex.continuous_re.comp (continuous_id.matrix_det)).tendsto _).comp hP
    have h2 : Tendsto (fun j => Real.exp (G j (e.val.symm z)) *
        (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re) atTop
        (𝓝 (Real.exp (G₀ (e.val.symm z)) *
          (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re)) :=
      ((Real.continuous_exp.tendsto _).comp (hG _)).mul_const _
    refine tendsto_nhds_unique h1 ?_
    refine h2.congr fun j => ?_
    exact (hdet j e z hz).symm
  refine ⟨fun e z hz => ?_, key⟩
  have hP := (tendsto_complexHessian hs hv e hz).const_add
    (normalizedHermitianMatrix (A.form.val.coeff e z))
  refine posDef_of_tendsto (fun j => hpos j e z hz) hP fun h0 => ?_
  have hre := key e z hz
  rw [h0, Complex.zero_re] at hre
  have hA : 0 < (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re :=
    (Complex.pos_iff.mp (posDef_coeff A.isKahler.1 hz).det_pos).1
  have := mul_pos (Real.exp_pos (G₀ (e.val.symm z))) hA
  linarith

end Kahler

/-! ### Closedness -/

/-- **Limits of bounded sequences of solutions** (blueprint `bou:yau-closedness`): let `φ_j` be
chart-smooth solutions of `(A + ddᶜφ_j)^N = e^{t_j F + ε_j φ_j + κ_j} A^N` with `A + ddᶜφ_j` Kähler,
`t_j → t₀`, `ε_j → ε₀`, `κ_j → κ₀`, and `‖φ_j‖_{C^{2,r}(Y)} ≤ C`.  Then there is a chart-smooth `φ₀`
with `A + ddᶜφ₀` Kähler and `(A + ddᶜφ₀)^N = e^{t₀F + ε₀φ₀ + κ₀} A^N`. -/
theorem exists_smooth_of_tendsto (A : KahlerBackground N Y) {HA : HolderAtlas N Y} {r : ℝ≥0}
    (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ} (hF : ChartSmooth (n := N) F)
    {t ε κ : ℕ → ℝ} {t₀ ε₀ κ₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (hε : Tendsto ε atTop (𝓝 ε₀)) (hκ : Tendsto κ atTop (𝓝 κ₀))
    (φ : ℕ → Y → ℝ) (hφ : ∀ j, ChartSmooth (n := N) (φ j))
    (hK : ∀ j, (A.form + ddcClosedForm (φ j) (hφ j)).val.IsKahler)
    (hdens : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm (φ j) (hφ j)).val.coeff e z) =
        Real.exp (t j * F (e.val.symm z) + ε j * φ j (e.val.symm z) + κ j) *
          actualTopPowerDensity (A.form.val.coeff e z))
    {C : ℝ} (hC : ∀ j, ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le (φ j) (hφ j)‖ ≤ C) :
    ∃ (φ₀ : Y → ℝ) (hφ₀ : ChartSmooth (n := N) φ₀),
      (A.form + ddcClosedForm φ₀ hφ₀).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ₀ hφ₀).val.coeff e z) =
          Real.exp (t₀ * F (e.val.symm z) + ε₀ * φ₀ (e.val.symm z) + κ₀) *
            actualTopPowerDensity (A.form.val.coeff e z) := by
  set s : ℝ≥0 := r / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos hr0 two_pos
  have hsr : s < r := by rw [hsdef]; exact NNReal.half_lt_self hr0.ne'
  have hs1 : s < 1 := hsr.trans hr1
  obtain ⟨U, σ, hσ, hU⟩ := HolderAtlas.HolderMap.exists_subseq_tendsto_ofLE hr1.le hsr
    (fun j => HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le (φ j) (hφ j)) hC
  set v : ℕ → HA.HolderMap 2 s ℝ := fun j => HolderAtlas.HolderMap.ofLE hsr.le
    (HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le (φ (σ j)) (hφ (σ j))) with hvdef
  have hvU : Tendsto v atTop (𝓝 U) := hU
  have hcoe : ∀ j, ⇑(v j) = φ (σ j) := fun j => rfl
  set G : ℕ → Y → ℝ := fun j y => t (σ j) * F y + ε (σ j) * φ (σ j) y + κ (σ j) with hGdef
  set G₀ : Y → ℝ := fun y => t₀ * F y + ε₀ * U y + κ₀ with hG₀def
  have hG : ∀ y, Tendsto (fun j => G j y) atTop (𝓝 (G₀ y)) := by
    intro y
    have hy : Tendsto (fun j => φ (σ j) y) atTop (𝓝 (U y)) := tendsto_apply hvU y
    have ht' := ht.comp hσ.tendsto_atTop
    have hε' := hε.comp hσ.tendsto_atTop
    have hκ' := hκ.comp hσ.tendsto_atTop
    exact ((ht'.mul_const (F y)).add (hε'.mul hy)).add hκ'
  have hpos : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => v j (e.val.symm x)) z).PosDef :=
    fun j e z hz => posDef_of_isKahler A (hφ (σ j)) (hK (σ j)) e hz
  have hdet : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => v j (e.val.symm x)) z).det.re =
        Real.exp (G j (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re :=
    fun j e z hz => det_eq_of_density A (hφ (σ j)) (G := G j) (hK (σ j)) (hdens (σ j)) e hz
  obtain ⟨hposU, hdetU⟩ := limit_of_tendsto A hs1.le hvU hG hpos hdet
  -- `U` solves the equation with `F' = t₀F + κ₀`, `t = 1`, `ε = ε₀`
  set F' : Y → ℝ := fun y => t₀ * F y + κ₀ with hF'def
  have hF' : ChartSmooth (n := N) F' := fun e => (contDiffOn_const.mul (hF e)).add contDiffOn_const
  have hma : ∀ y, ma A.form.val ⇑U y = G₀ y := ma_eq_of_det_eq A hdetU
  have hma' : ∀ y, ma A.form.val ⇑U y = 1 * F' y + ε₀ * U y := fun y => by
    rw [hma y, hG₀def, hF'def]
    ring
  have hUs : ChartSmooth (n := N) ⇑U :=
    MongeAmpereRegularity.chartSmooth_of_ma_eq A hs0 hs1 hF' U hposU hma'
  have hKU := YauSmoothOpenness.isKahler_of_posDef A hUs hposU
  exact ⟨⇑U, hUs, hKU, fun e z hz =>
    YauSmoothOpenness.density_eq_of_ma_eq A hUs (G := G₀) hKU hma e z hz⟩

end SGPT.Foundations.Analysis.Pending.YauClosedness
