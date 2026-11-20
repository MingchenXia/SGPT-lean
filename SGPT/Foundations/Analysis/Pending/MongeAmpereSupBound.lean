import SGPT.Foundations.Analysis.Pending.AubinYauEstimate

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The `C⁰` estimate at fixed `ε` on the `ε`-continuity path of Yau's theorem

Let `Y` be a compact complex manifold of dimension `N` with a Kähler form `A`, `ε > 0`, and `φ` a
chart-smooth function with `A_φ = A + ddᶜφ` Kähler and

`A_φ^N = e^{H + εφ} A^N`  (chart densities, `|H| ≤ B`).

Then `ε |φ| ≤ B` on `Y` (`abs_le_of_mongeAmpere_eq_exp`).

This is step P3(a) of N5 (closedness of the `ε`-continuity path at fixed `ε`, used with `H = tF`)
in TN23's the proof of Yau's theorem; statement the statement under discussion (T1),
split settled in C-0063.  Textbook: the maximum principle step of the continuity method,
Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.4 (the `C⁰` bound for the
`ε`-perturbed equation); Błocki, LNM 2038, §5.

## Proof

At a maximum point `y₀` of `φ`, in the preferred chart `e` at `y₀` and with a local potential `ρ`
of `A`, put `P = (ρ_{jk̄})(z₀)` and `Q = (∂²(φ ∘ e⁻¹)/∂z_j∂z̄_k)(z₀)`, `z₀ = e(y₀)`.  Then `P > 0`,
`P + Q > 0`, `det(P + Q) = e^{G(y₀)} det P` with `G = H + εφ` (`exists_potential_hessian`), and
`Re tr(P⁻¹Q) ≤ 0` (maximum principle in trace form,
`AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos`), i.e. `tr(P⁻¹(P + Q)) ≤ N`.  In the common
frame of `P` and `P + Q` (`AubinYauMatrixBounds.exists_frame`), `∑ λ_k ≤ N` gives `∏ λ_k ≤ 1` by
`log x ≤ x - 1` (`prod_le_one_of_sum_le`), i.e. `det(P + Q) ≤ det P` (`re_det_le_of_trace_le`), so
`G(y₀) ≤ 0` (`add_le_zero_of_isMax`).  Symmetrically `G ≥ 0` at a minimum point
(`zero_le_add_of_isMin`).  Hence `-B ≤ -H(y₂) ≤ εφ(y₂) ≤ εφ ≤ εφ(y₁) ≤ -H(y₁) ≤ B`.
-/

open Set Filter Matrix
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereSupBound

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian AubinYauLocalStep AubinYauEstimate
  ManifoldTubePositivity

noncomputable section

/-! ### Determinants of two positive definite matrices -/

section Matrix

variable {n : ℕ}

/-- `∑ λ_k ≤ n` with all `λ_k > 0` forces `∏ λ_k ≤ 1` (via `log x ≤ x - 1`). -/
theorem prod_le_one_of_sum_le {lam : Fin n → ℝ} (hlam : ∀ k, 0 < lam k)
    (h : ∑ k, lam k ≤ n) : ∏ k, lam k ≤ 1 := by
  have hlog : Real.log (∏ k, lam k) ≤ 0 := by
    rw [Real.log_prod fun k _ => (hlam k).ne']
    calc ∑ k, Real.log (lam k) ≤ ∑ k, (lam k - 1) :=
          Finset.sum_le_sum fun k _ => Real.log_le_sub_one_of_pos (hlam k)
      _ = ∑ k, lam k - n := by simp [Finset.sum_sub_distrib]
      _ ≤ 0 := by linarith
  have hpos : 0 < ∏ k, lam k := Finset.prod_pos fun k _ => hlam k
  calc ∏ k, lam k = Real.exp (Real.log (∏ k, lam k)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlog
    _ = 1 := Real.exp_zero

/-- `∑ λ_k⁻¹ ≤ n` with all `λ_k > 0` forces `1 ≤ ∏ λ_k`. -/
theorem one_le_prod_of_sum_inv_le {lam : Fin n → ℝ} (hlam : ∀ k, 0 < lam k)
    (h : ∑ k, (lam k)⁻¹ ≤ n) : 1 ≤ ∏ k, lam k := by
  have h1 := prod_le_one_of_sum_le (lam := fun k => (lam k)⁻¹) (fun k => inv_pos.mpr (hlam k)) h
  rw [Finset.prod_inv_distrib] at h1
  have hpos : 0 < ∏ k, lam k := Finset.prod_pos fun k _ => hlam k
  exact (inv_le_one₀ hpos).mp h1

/-- `Re tr(G⁻¹ G') ≤ n` for positive definite `G, G'` gives `det G' ≤ det G`. -/
theorem re_det_le_of_trace_le {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hG' : G'.PosDef) (h : (G⁻¹ * G').trace.re ≤ n) : G'.det.re ≤ G.det.re := by
  obtain ⟨lam, hlam, -, htr, hdet, -⟩ := AubinYauMatrixBounds.exists_frame hG hG'
  have hsum : ∑ k, lam k ≤ n := by
    rw [htr, Complex.re_sum] at h
    simpa using h
  have hprod := prod_le_one_of_sum_le hlam hsum
  have hG0 : 0 < G.det.re := (Complex.pos_iff.mp hG.det_pos).1
  have hdet' : G'.det.re = (∏ k, lam k) * G.det.re := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  rw [hdet']
  nlinarith

/-- `Re tr(G'⁻¹ G) ≤ n` for positive definite `G, G'` gives `det G ≤ det G'`. -/
theorem re_det_le_of_trace_inv_le {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hG' : G'.PosDef) (h : (G'⁻¹ * G).trace.re ≤ n) : G.det.re ≤ G'.det.re := by
  obtain ⟨lam, hlam, htr, -, hdet, -⟩ := AubinYauMatrixBounds.exists_frame hG hG'
  have hsum : ∑ k, (lam k)⁻¹ ≤ n := by
    rw [htr, Complex.re_sum] at h
    simpa [← Complex.ofReal_inv] using h
  have hprod := one_le_prod_of_sum_inv_le hlam hsum
  have hG0 : 0 < G.det.re := (Complex.pos_iff.mp hG.det_pos).1
  have hdet' : G'.det.re = (∏ k, lam k) * G.det.re := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  rw [hdet']
  nlinarith

end Matrix

/-! ### The maximum principle for the Monge–Ampère equation -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The equation at a point, in the preferred chart**: for `A_φ^N = e^G A^N` and `y₀ ∈ Y`, with
`e` the preferred chart at `y₀` and `ψ = φ ∘ e⁻¹`, there is a positive definite `P` (the complex
Hessian of a local potential of `A` at `e(y₀)`) with `P + ψ_{jk̄}(e(y₀))` positive definite and
`det(P + ψ_{jk̄}(e(y₀))) = e^{G(y₀)} det P`. -/
theorem exists_potential_hessian (A : PositiveClasses.KahlerBackground N Y) {φ G : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    (y₀ : Y) :
    ∃ P : Matrix (Fin N) (Fin N) ℂ, P.PosDef ∧
      (P + complexHessian (fun w => φ ((complexChartAt (n := N) y₀).val.symm w))
        ((complexChartAt (n := N) y₀).val y₀)).PosDef ∧
      (P + complexHessian (fun w => φ ((complexChartAt (n := N) y₀).val.symm w))
        ((complexChartAt (n := N) y₀).val y₀)).det.re = Real.exp (G y₀) * P.det.re := by
  set e := complexChartAt (n := N) y₀ with he
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  obtain ⟨W, ρ, hzW, hpot⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials A.form e (e.val y₀) hz
  have hρ2 : ContDiffAt ℝ 2 ρ (e.val y₀) := contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hzW
  have hψ2 : ContDiffAt ℝ 2 (fun w => φ (e.val.symm w)) (e.val y₀) :=
    contDiffAt_two_of_contDiffOn e.val.open_target (hφ e) hz
  have hu2 : ContDiffAt ℝ 2 (fun w => ρ w + φ (e.val.symm w)) (e.val y₀) := hρ2.add hψ2
  have hA' := coeff_line_eq_leviForm A hpot hzW
  have hB' := coeff_add_line_eq_leviForm A hφ hpot hzW
  have hGm : (complexHessian ρ (e.val y₀)).PosDef := posDef_complexHessian hρ2 fun w hw =>
    leviForm_pos_of_isKahler A.isKahler hz hA' hw
  have hGm' : (complexHessian (fun w => ρ w + φ (e.val.symm w)) (e.val y₀)).PosDef :=
    posDef_complexHessian hu2 fun w hw => leviForm_pos_of_isKahler hK hz hB' hw
  have hsplit := complexHessian_fun_add hρ2 hψ2
  refine ⟨complexHessian ρ (e.val y₀), hGm, hsplit ▸ hGm', ?_⟩
  rw [← hsplit, re_det_complexHessian_eq_exp A hφ hdens hpot hzW, e.val.left_inv hy]

theorem isUnit_det_of_posDef {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) : IsUnit P.det :=
  isUnit_iff_ne_zero.mpr hP.det_pos.ne'

/-- **At a maximum point of `φ`**: `A_φ^N = e^G A^N` forces `G ≤ 0` there. -/
theorem le_zero_of_isMax (A : PositiveClasses.KahlerBackground N Y) {φ G : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    {y₀ : Y} (hmax : ∀ y, φ y ≤ φ y₀) : G y₀ ≤ 0 := by
  obtain ⟨P, hP, hPQ, hdet⟩ := exists_potential_hessian A hφ hK hdens y₀
  set e := complexChartAt (n := N) y₀ with he
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  set Q := complexHessian (fun w => φ (e.val.symm w)) (e.val y₀) with hQ
  have hψ2 : ContDiffAt ℝ 2 (fun w => φ (e.val.symm w)) (e.val y₀) :=
    contDiffAt_two_of_contDiffOn e.val.open_target (hφ e) hz
  have hloc : IsLocalMax (fun w => φ (e.val.symm w)) (e.val y₀) :=
    Eventually.of_forall fun w => by
      change φ (e.val.symm w) ≤ φ (e.val.symm (e.val y₀))
      rw [e.val.left_inv hy]
      exact hmax _
  have htr := AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos hψ2 hloc hP.posSemidef.inv
  have h1 : (P⁻¹ * (P + Q)).trace.re ≤ N := by
    rw [Matrix.mul_add, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hP), trace_add, trace_one,
      Complex.add_re]
    simp only [Fintype.card_fin, Complex.natCast_re]
    linarith
  have h2 := re_det_le_of_trace_le hP hPQ h1
  rw [hdet] at h2
  have hP0 : 0 < P.det.re := (Complex.pos_iff.mp hP.det_pos).1
  have h3 : Real.exp (G y₀) ≤ Real.exp 0 := by
    rw [Real.exp_zero]
    nlinarith
  exact Real.exp_le_exp.mp h3

/-- **At a minimum point of `φ`**: `A_φ^N = e^G A^N` forces `0 ≤ G` there. -/
theorem zero_le_of_isMin (A : PositiveClasses.KahlerBackground N Y) {φ G : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    {y₀ : Y} (hmin : ∀ y, φ y₀ ≤ φ y) : 0 ≤ G y₀ := by
  obtain ⟨P, hP, hPQ, hdet⟩ := exists_potential_hessian A hφ hK hdens y₀
  set e := complexChartAt (n := N) y₀ with he
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  set Q := complexHessian (fun w => φ (e.val.symm w)) (e.val y₀) with hQ
  have hψ2 : ContDiffAt ℝ 2 (fun w => φ (e.val.symm w)) (e.val y₀) :=
    contDiffAt_two_of_contDiffOn e.val.open_target (hφ e) hz
  have hneg2 : ContDiffAt ℝ 2 (fun w => -1 * φ (e.val.symm w)) (e.val y₀) :=
    contDiffAt_const.mul hψ2
  have hloc : IsLocalMax (fun w => -1 * φ (e.val.symm w)) (e.val y₀) :=
    Eventually.of_forall fun w => by
      change -1 * φ (e.val.symm w) ≤ -1 * φ (e.val.symm (e.val y₀))
      rw [e.val.left_inv hy]
      linarith [hmin (e.val.symm w)]
  have htr := AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos hneg2 hloc
    hPQ.posSemidef.inv
  rw [complexHessian_const_mul hψ2 (-1)] at htr
  have h1 : ((P + Q)⁻¹ * P).trace.re ≤ N := by
    have hPeq : (P + Q)⁻¹ * P = 1 + (P + Q)⁻¹ * (((-1 : ℝ) : ℂ) • Q) := by
      have h := Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hPQ)
      rw [Matrix.mul_add] at h
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, Matrix.mul_neg, ← h]
      abel
    rw [hPeq, trace_add, trace_one, Complex.add_re]
    simp only [Fintype.card_fin, Complex.natCast_re]
    linarith
  have h2 := re_det_le_of_trace_inv_le hP hPQ h1
  rw [hdet] at h2
  have hP0 : 0 < P.det.re := (Complex.pos_iff.mp hP.det_pos).1
  have h3 : Real.exp 0 ≤ Real.exp (G y₀) := by
    rw [Real.exp_zero]
    nlinarith
  exact Real.exp_le_exp.mp h3

/-- **The `C⁰` estimate at fixed `ε`** (step P3(a) of N5 of Yau's theorem; I-0831 C-0062 T1): on a
compact complex manifold with a Kähler form `A`, if `A + ddᶜφ` is Kähler and
`(A + ddᶜφ)^N = e^{H + εφ} A^N` in every chart with `ε > 0` and `|H| ≤ B`, then `ε |φ| ≤ B`. -/
theorem abs_le_of_mongeAmpere_eq_exp {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y]
    (A : PositiveClasses.KahlerBackground N Y) {φ H : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    {ε B : ℝ} (hε : 0 < ε) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (H (e.val.symm z) + ε * φ (e.val.symm z)) *
          actualTopPowerDensity (A.form.val.coeff e z))
    (hH : ∀ y, |H y| ≤ B) : ∀ y, ε * |φ y| ≤ B := by
  intro y
  have hφc : Continuous φ := YauUniformEstimate.continuous_of_chartSmooth hφ
  obtain ⟨y₁, -, hy₁⟩ := isCompact_univ.exists_isMaxOn ⟨y, mem_univ y⟩ hφc.continuousOn
  obtain ⟨y₂, -, hy₂⟩ := isCompact_univ.exists_isMinOn ⟨y, mem_univ y⟩ hφc.continuousOn
  have h1 : H y₁ + ε * φ y₁ ≤ 0 := le_zero_of_isMax (G := fun x => H x + ε * φ x) A hφ hK hdens
    (y₀ := y₁) fun x => hy₁ (mem_univ x)
  have h2 : 0 ≤ H y₂ + ε * φ y₂ := zero_le_of_isMin (G := fun x => H x + ε * φ x) A hφ hK hdens
    (y₀ := y₂) fun x => hy₂ (mem_univ x)
  have hm1 : ε * φ y ≤ ε * φ y₁ := mul_le_mul_of_nonneg_left (hy₁ (mem_univ y)) hε.le
  have hm2 : ε * φ y₂ ≤ ε * φ y := mul_le_mul_of_nonneg_left (hy₂ (mem_univ y)) hε.le
  have hb1 := (abs_le.mp (hH y₁)).1
  have hb2 := (abs_le.mp (hH y₂)).2
  rw [← abs_of_pos hε, ← abs_mul, abs_le]
  constructor <;> linarith

end Manifold

end

end SGPT.Foundations.Analysis.Pending.MongeAmpereSupBound
