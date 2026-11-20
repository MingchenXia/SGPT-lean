import SGPT.Foundations.Analysis.Pending.CalabiCutoffEstimate
import SGPT.Foundations.Analysis.Pending.AubinYauEstimate

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The third-order (Calabi) estimate for the complex Monge–Ampère equation (N4)

Let `Y` be a complex manifold of dimension `N` with a Kähler form `A`, `F` chart-smooth, `C₀ ∈ ℝ`, `e` a
chart and `K ⊆ e.target` compact. There is `C` such that for every chart-smooth `φ` with
`A_φ = A + ddᶜφ` Kähler, `A_φ^N = e^{tF + εφ + κ} A^N` in the chart `e` (`t, ε ∈ [0, 1]`, `κ ∈ ℝ`) and
`C₀⁻¹ A ≤ A_φ ≤ C₀ A` in the chart `e`, the real derivative of every entry of the complex Hessian of
`φ ∘ e⁻¹` is bounded by `C` on `K` (`exists_norm_fderiv_complexHessian_le`; the statement agreed with
TN23, the statement under discussion / C-0059: it is what the closedness step N5 consumes).

## Proof

* Cover `K` by finitely many balls `ball p R_p` with a local potential `ρ_p` of `A` on
  `closedBall p (8 R_p)` (`exists_piece`); on `ball p (4 R_p)`, `u = ρ_p + φ ∘ e⁻¹` (made globally smooth
  by a cutoff) solves `log det(u_{jk̄}) = f + εu` with `f = tF − ερ_p + log det(ρ_{p,jk̄}) + κ`, whose
  second and third derivatives are bounded uniformly in `t, ε, κ, φ`; `C₀` and the bounds of `ρ_p` give
  `tr H, tr H⁻¹ ≤ Λ_p`.
* `CalabiCutoffEstimate.exists_sum_frob_dH_le` bounds the third derivatives of `u` on `closedBall p R_p`;
  subtracting those of `ρ_p` and `‖D H_{jk}‖ ≤ 2N |∂H|` (`norm_fderiv_complexHessian_le`) give the bound.

TN.4 B5, nonlinear track N4 (d), blueprint `bou:yau-c3-estimate`
.
-/

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.CalabiThirdOrderEstimate

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity
  CalabiFlatLaplacian CalabiFlatInequality CalabiLinearChange CalabiCutoffEstimate
  AubinYauEstimate AubinYauUniformConstants SemiconcaveHessian ManifoldTubePositivity
  RelativeEigenvalueMax

noncomputable section

/-! ### Local lemmas -/

section Local

variable {N : ℕ}

/-- `‖D H_{jk}‖ ≤ 2N |∂H|` for the complex Hessian of a smooth function. -/
theorem norm_fderiv_complexHessian_le {g : ComplexModel N → ℝ} (hg : ContDiff ℝ ∞ g)
    (z : ComplexModel N) (j k : Fin N) :
    ‖fderiv ℝ (fun w => complexHessian g w j k) z‖ ≤ 2 * N * √(∑ m, frob (dH g m z)) := by
  set B : ℝ := √(∑ m, frob (dH g m z)) with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hB : ∀ m a b, ‖dH g m z a b‖ ≤ B := fun m a b =>
    (norm_entry_le _ a b).trans (Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun m => frob (dH g m z)) (fun _ _ => frob_nonneg _)
        (Finset.mem_univ m)))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hsplit : fderiv ℝ (fun w => complexHessian g w j k) z w =
      wirt (-I) w (fun w => complexHessian g w j k) z +
        wirt I w (fun w => complexHessian g w j k) z := by
    simp only [wirt]
    ring
  have h1 : wirt (-I) w (fun w => complexHessian g w j k) z = ∑ b, w b * dH g b z j k := by
    rw [wirt_negI_sum_dir]
    rfl
  have hH : (fun y => complexHessian g y j k) = fun y => starRingEnd ℂ (complexHessian g y k j) := by
    funext y
    have := congrFun (congrFun (isHermitian_complexHessian hg y) j) k
    rw [conjTranspose_apply] at this
    rw [← this]
    rfl
  have h2 : wirt I w (fun w => complexHessian g w j k) z =
      ∑ a, star (w a) * starRingEnd ℂ (dH g a z k j) := by
    rw [wirt_I_sum_dir]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [hH, wirt_I_conj (differentiable_complexHessian_apply hg k j z)]
    rfl
  rw [hsplit, h1, h2]
  have hw : ∀ b, ‖w b‖ ≤ ‖w‖ := fun b => PiLp.norm_apply_le w b
  calc ‖∑ b, w b * dH g b z j k + ∑ a, star (w a) * starRingEnd ℂ (dH g a z k j)‖
      ≤ ∑ b, ‖w b‖ * B + ∑ a, ‖w a‖ * B := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hB b j k) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          rw [norm_mul, norm_star, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (hB a k j) (norm_nonneg _)
    _ ≤ ∑ _b : Fin N, ‖w‖ * B + ∑ _a : Fin N, ‖w‖ * B := by
        gcongr with b _ a _
        · exact hw b
        · exact hw a
    _ = 2 * N * B * ‖w‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem frob_smul_le {s : ℝ} (hs : |s| ≤ 1) (A : Mat N) : frob ((s : ℂ) • A) ≤ frob A := by
  unfold frob
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h1 : |s| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
  exact mul_le_of_le_one_left (sq_nonneg _) h1

theorem frob_comb_le {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) (A B C : Mat N) :
    frob ((s : ℂ) • A + (t : ℂ) • B + C) ≤ 4 * frob A + 4 * frob B + 2 * frob C := by
  have h1 := frob_add_le ((s : ℂ) • A + (t : ℂ) • B) C
  have h2 := frob_add_le ((s : ℂ) • A) ((t : ℂ) • B)
  have h3 := frob_smul_le hs A
  have h4 := frob_smul_le ht B
  linarith

/-- The complex Hessian of `s a + t b + c + κ`. -/
theorem complexHessian_comb {a b c : ComplexModel N → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c) (s t κ : ℝ) :
    complexHessian (fun z => s * a z + t * b z + c z + κ) =
      fun z => (s : ℂ) • complexHessian a z + (t : ℂ) • complexHessian b z + complexHessian c z := by
  have hab : ContDiff ℝ ∞ (fun z => s * a z + t * b z + c z) :=
    ((contDiff_const.mul ha).add (contDiff_const.mul hb)).add hc
  rw [complexHessian_add_const hab κ]
  funext z
  have h2 : ∀ {g : ComplexModel N → ℝ}, ContDiff ℝ ∞ g → ∀ y, ContDiffAt ℝ 2 g y :=
    fun hg y => AubinYauLocalStep.contDiffAt_two hg y
  rw [AubinYauLocalStep.complexHessian_fun_add
      (h2 ((contDiff_const.mul ha).add (contDiff_const.mul hb)) z) (h2 hc z),
    AubinYauLocalStep.complexHessian_fun_add (h2 (contDiff_const.mul ha) z)
      (h2 (contDiff_const.mul hb) z),
    AubinYauLocalStep.complexHessian_const_mul (h2 ha z),
    AubinYauLocalStep.complexHessian_const_mul (h2 hb z)]

theorem dH_comb {a b c : ComplexModel N → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (s t κ : ℝ) (m : Fin N) (z : ComplexModel N) :
    dH (fun z => s * a z + t * b z + c z + κ) m z =
      (s : ℂ) • dH a m z + (t : ℂ) • dH b m z + dH c m z := by
  unfold dH
  rw [complexHessian_comb ha hb hc]
  ext i j
  simp only [wirtM_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have da := differentiable_complexHessian_apply ha i j z
  have db := differentiable_complexHessian_apply hb i j z
  have dc := differentiable_complexHessian_apply hc i j z
  rw [wirt_add ((da.const_mul _).fun_add (db.const_mul _)) dc,
    wirt_add (da.const_mul _) (db.const_mul _), wirt_const_mul _ da, wirt_const_mul _ db]

/-- Uniform bounds of the second and third derivatives on a compact set. -/
theorem exists_frob_bound {g : ComplexModel N → ℝ} (hg : ContDiff ℝ ∞ g)
    {S : Set (ComplexModel N)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ S, frob (complexHessian g z) ≤ B ∧ ∑ m, frob (dH g m z) ≤ B := by
  have hc : Continuous (fun z => frob (complexHessian g z) + ∑ m, frob (dH g m z)) := by
    unfold frob
    refine Continuous.add ?_ ?_
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((contDiff_complexHessian_apply hg a b).continuous.norm).pow 2
    · exact continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun a _ =>
        continuous_finsetSum _ fun b _ => (((mSmooth_dH hg m) a b).continuous.norm).pow 2
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hB z hz
  rw [Real.norm_eq_abs] at h
  have h1 := frob_nonneg (complexHessian g z)
  have h2 : 0 ≤ ∑ m, frob (dH g m z) := Finset.sum_nonneg fun _ _ => frob_nonneg _
  have h3 := le_abs_self (frob (complexHessian g z) + ∑ m, frob (dH g m z))
  constructor <;> linarith [le_max_left B 0]

theorem re_star_dotProduct_self (x : Fin N → ℂ) : (star x ⬝ᵥ x).re = ∑ j, ‖x j‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end Local

/-! ### Charts -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **A chart piece** at a point `p` of `e.target`: a local potential `ρ` of `A` on
`W ⊇ closedBall p (8R)`, globally smooth `ρ'`, `F'`, `Lg` equal to `ρ`, `F ∘ e⁻¹`, `log det H(ρ')` near
`p`, and two-sided bounds of the Levi form of `ρ'` on `closedBall p (2R)`. -/
theorem exists_chart_piece (hN : 0 < N) (A : PositiveClasses.KahlerBackground N Y) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) (e : ComplexChart N Y) {p : ComplexModel N}
    (hp : p ∈ e.val.target) :
    ∃ (W : Set (ComplexModel N)) (ρ ρ' F' Lg : ComplexModel N → ℝ) (R : ℝ), 0 < R ∧
      IsSmoothLocalPotential A.form.val e W ρ ∧ closedBall p (8 * R) ⊆ W ∧
      ContDiff ℝ ∞ ρ' ∧ EqOn ρ' ρ (ball p (6 * R)) ∧
      ContDiff ℝ ∞ F' ∧ EqOn F' (fun w => F (e.val.symm w)) (ball p (4 * R)) ∧
      ContDiff ℝ ∞ Lg ∧
        EqOn Lg (fun w => Real.log (complexHessian ρ' w).det.re) (ball p (4 * R)) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ z ∈ closedBall p (2 * R), ∀ w : ComplexModel N,
        c * ‖w‖ ^ 2 ≤ leviForm ρ' z w ∧ leviForm ρ' z w ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨W, ρ, hpW, hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials A.form e p hp
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp hpot.1 p hpW
  set R := R₀ / 16 with hRdef
  have hR : 0 < R := by positivity
  have h8 : closedBall p (8 * R) ⊆ W :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hball
  obtain ⟨ρ', hρ', hρ'eq⟩ := exists_contDiff_eqOn_ball hpot.1 hpot.2.2.1
    (by positivity : 0 < 6 * R) (by linarith : 6 * R < 8 * R) h8
  have hW6 : ball p (6 * R) ⊆ W :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans h8)
  have hlevi : ∀ z ∈ ball p (6 * R), ∀ v, v ≠ 0 → 0 < leviForm ρ' z v := by
    intro z hz v hv
    have hgerm : ρ' =ᶠ[𝓝 z] ρ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hρ'eq
    rw [leviForm_congr hgerm]
    exact leviForm_pos_of_isKahler A.isKahler (hpot.2.1 (hW6 hz))
      (coeff_line_eq_leviForm A hpot (hW6 hz)) hv
  obtain ⟨F', hF', hF'eq⟩ := exists_contDiff_eqOn_ball e.val.open_target (hF e)
    (by positivity : 0 < 4 * R) (by linarith : 4 * R < 8 * R) (h8.trans hpot.2.1)
  have hdetpos : ∀ z ∈ ball p (6 * R), 0 < (complexHessian ρ' z).det.re := by
    intro z hz
    have hpd : (complexHessian ρ' z).PosDef :=
      AubinYauLocalStep.posDef_complexHessian (AubinYauLocalStep.contDiffAt_two hρ' z)
        (hlevi z hz)
    exact (Complex.pos_iff.mp hpd.det_pos).1
  have hLgon : ContDiffOn ℝ ∞ (fun w => Real.log (complexHessian ρ' w).det.re)
      (ball p (6 * R)) := by
    have hD : ContDiff ℝ ∞ (fun w => (complexHessian ρ' w).det.re) :=
      Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hρ')
    exact fun z hz => (hD.contDiffAt.log (hdetpos z hz).ne').contDiffWithinAt
  obtain ⟨Lg, hLg, hLgeq⟩ := exists_contDiff_eqOn_ball isOpen_ball hLgon
    (by positivity : 0 < 4 * R) (by linarith : 4 * R < 5 * R)
    (closedBall_subset_ball (by linarith))
  obtain ⟨c, C, _, _, hc, hC, _, _, hbd⟩ := exists_uniform_constants hN hρ' isOpen_ball
    (isCompact_closedBall p (2 * R)) (closedBall_subset_ball (by linarith)) hlevi
  exact ⟨W, ρ, ρ', F', Lg, R, hR, hpot, h8, hρ', hρ'eq, hF', hF'eq, hLg, hLgeq, c, C, hc, hC,
    fun z hz w => ⟨(hbd z hz).1 w, (hbd z hz).2.1 w⟩⟩

/-- **The hypotheses of the ball estimate** for `u = ρ + φ ∘ e⁻¹` (made globally smooth) on a chart
piece: positivity, `tr H, tr H⁻¹ ≤ Λ`, the equation `log det H = f + εu` with
`f = tF' - ερ' + Lg + κ`, and the bounds of the derivatives of `f`. -/
theorem ball_hyps (hN : 0 < N) (A : PositiveClasses.KahlerBackground N Y) {F : Y → ℝ}
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ ρ' F' Lg : ComplexModel N → ℝ}
    {p : ComplexModel N} {R : ℝ} (hpot : IsSmoothLocalPotential A.form.val e W ρ)
    (h8 : closedBall p (8 * R) ⊆ W) (hρ' : ContDiff ℝ ∞ ρ') (hρ'eq : EqOn ρ' ρ (ball p (6 * R)))
    (hF' : ContDiff ℝ ∞ F') (hF'eq : EqOn F' (fun w => F (e.val.symm w)) (ball p (4 * R)))
    (hLg : ContDiff ℝ ∞ Lg)
    (hLgeq : EqOn Lg (fun w => Real.log (complexHessian ρ' w).det.re) (ball p (4 * R)))
    {c Cρ : ℝ} (hc : 0 < c) (hCρ : 0 ≤ Cρ) (hbd : ∀ z ∈ closedBall p (2 * R), ∀ w : ComplexModel N,
      c * ‖w‖ ^ 2 ≤ leviForm ρ' z w ∧ leviForm ρ' z w ≤ Cρ * ‖w‖ ^ 2)
    {BF Bρ BL : ℝ}
    (hBF : ∀ z ∈ closedBall p (2 * R), frob (complexHessian F' z) ≤ BF ∧ ∑ m, frob (dH F' m z) ≤ BF)
    (hBρ : ∀ z ∈ closedBall p (2 * R), frob (complexHessian ρ' z) ≤ Bρ ∧ ∑ m, frob (dH ρ' m z) ≤ Bρ)
    (hBL : ∀ z ∈ closedBall p (2 * R), frob (complexHessian Lg z) ≤ BL ∧ ∑ m, frob (dH Lg m z) ≤ BL)
    (C₀ : ℝ) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) {t ε κ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hε : ε ∈ Icc (0 : ℝ) 1) (hKa : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ z ∈ e.val.target,
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
          actualTopPowerDensity (A.form.val.coeff e z))
    (hC₀ : ∀ z ∈ e.val.target, ∀ v : ComplexModel N,
      (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] ≤
          C₀ * A.form.val.coeff e z ![v, Complex.I • v] ∧
        A.form.val.coeff e z ![v, Complex.I • v] ≤
          C₀ * (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v])
    {u : ComplexModel N → ℝ} (hu : ContDiff ℝ ∞ u)
    (hueq : EqOn u (fun w => ρ w + φ (e.val.symm w)) (ball p (4 * R))) :
    ∀ z ∈ ball p (2 * R), (complexHessian u z).PosDef ∧
      (complexHessian u z).trace.re ≤ N * max C₀ 1 * (Cρ + 1 / c) + 1 ∧
      ((complexHessian u z)⁻¹).trace.re ≤ N * max C₀ 1 * (Cρ + 1 / c) + 1 ∧
      Real.log (complexHessian u z).det.re = (t * F' z + (-ε) * ρ' z + Lg z + κ) + ε * u z ∧
      frob (complexHessian (fun z => t * F' z + (-ε) * ρ' z + Lg z + κ) z) ≤
        4 * BF + 4 * Bρ + 2 * BL ∧
      ∑ m, frob (dH (fun z => t * F' z + (-ε) * ρ' z + Lg z + κ) m z) ≤
        4 * BF + 4 * Bρ + 2 * BL := by
  intro z hz
  have hR : 0 < R := by
    by_contra h
    have h := not_lt.mp h
    have := mem_ball.mp hz
    have := dist_nonneg (x := z) (y := p)
    linarith
  have hz4 : z ∈ ball p (4 * R) := ball_subset_ball (by linarith) hz
  have hz6 : z ∈ ball p (6 * R) := ball_subset_ball (by linarith) hz
  have hzc : z ∈ closedBall p (2 * R) := ball_subset_closedBall hz
  have hzW : z ∈ W := h8 (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
  have hzt : z ∈ e.val.target := hpot.2.1 hzW
  have hgu : u =ᶠ[𝓝 z] fun w => ρ w + φ (e.val.symm w) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz4) hueq
  have hgρ : ρ' =ᶠ[𝓝 z] ρ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz6) hρ'eq
  have hLu : ∀ v, leviForm u z v =
      Real.pi * (A.form + ddcClosedForm φ hφ).val.coeff e z (line v) := by
    intro v
    rw [leviForm_congr hgu, coeff_add_line_eq_leviForm A hφ hpot hzW]
    field_simp
  have hLρ : ∀ v, leviForm ρ' z v = Real.pi * A.form.val.coeff e z (line v) := by
    intro v
    rw [leviForm_congr hgρ, coeff_line_eq_leviForm A hpot hzW]
    field_simp
  have hpi := Real.pi_pos
  have hBpos : ∀ v, v ≠ 0 → 0 < leviForm u z v := fun v hv => by
    rw [hLu]; exact mul_pos hpi ((hKa.1 e z hzt).2 v hv)
  have hpos : (complexHessian u z).PosDef :=
    AubinYauLocalStep.posDef_complexHessian (AubinYauLocalStep.contDiffAt_two hu z) hBpos
  -- the two-sided bound in Levi forms
  have hup : ∀ v, leviForm u z v ≤ C₀ * leviForm ρ' z v := fun v => by
    rw [hLu, hLρ]; have := (hC₀ z hzt v).1; nlinarith
  have hlow : ∀ v, leviForm ρ' z v ≤ C₀ * leviForm u z v := fun v => by
    rw [hLu, hLρ]; have := (hC₀ z hzt v).2; nlinarith
  have hu0 : ∀ v, 0 ≤ leviForm u z v := fun v => by
    rcases eq_or_ne v 0 with rfl | hv
    · have := hBpos; simp [leviForm]
    · exact (hBpos v hv).le
  set C₀' : ℝ := max C₀ 1 with hC₀'
  have hC₀1 : 1 ≤ C₀' := le_max_right _ _
  have hupper : ∀ v, leviForm u z v ≤ C₀' * Cρ * ‖v‖ ^ 2 := by
    intro v
    have h1 := hup v
    have h2 := (hbd z hzc v).2
    have h3 := (hbd z hzc v).1
    have hρ0 : 0 ≤ leviForm ρ' z v := le_trans (by positivity) h3
    calc leviForm u z v ≤ C₀ * leviForm ρ' z v := h1
      _ ≤ C₀' * leviForm ρ' z v := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0
      _ ≤ C₀' * (Cρ * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = C₀' * Cρ * ‖v‖ ^ 2 := by ring
  have hlower : ∀ v, c * ‖v‖ ^ 2 ≤ C₀' * leviForm u z v := by
    intro v
    calc c * ‖v‖ ^ 2 ≤ leviForm ρ' z v := (hbd z hzc v).1
      _ ≤ C₀ * leviForm u z v := hlow v
      _ ≤ C₀' * leviForm u z v := mul_le_mul_of_nonneg_right (le_max_left _ _) (hu0 v)
  -- traces
  have hq : ∀ x : Fin N → ℂ, (star x ⬝ᵥ (complexHessian u z *ᵥ x)).re =
      leviForm u z (coordCombination x) := re_quad_complexHessian (AubinYauLocalStep.contDiffAt_two hu z)
  have hone : ∀ x : Fin N → ℂ, (star x ⬝ᵥ ((1 : Mat N) *ᵥ x)).re = ‖coordCombination x‖ ^ 2 := by
    intro x
    rw [Matrix.one_mulVec, re_star_dotProduct_self, AubinYauLocalStep.norm_sq_coordCombination]
  have htr1 : (complexHessian u z).trace.re ≤ N * (C₀' * Cρ) := by
    have h := re_trace_inv_mul_le_of_quad_le (G := (1 : Mat N)) (G' := complexHessian u z)
      Matrix.PosDef.one hpos (c := C₀' * Cρ) (fun x => by rw [hq, hone]; exact hupper _)
    rwa [inv_one, Matrix.one_mul] at h
  have htr2 : ((complexHessian u z)⁻¹).trace.re ≤ N * (C₀' / c) := by
    have h := re_trace_inv_mul_le_of_quad_le (G := complexHessian u z) (G' := (1 : Mat N))
      hpos Matrix.PosDef.one (c := C₀' / c) (fun x => by
        rw [hq, hone, div_mul_eq_mul_div, le_div_iff₀ hc]
        have := hlower (coordCombination x)
        linarith)
    rwa [Matrix.mul_one] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ1 : (N : ℝ) * (C₀' * Cρ) ≤ N * C₀' * (Cρ + 1 / c) + 1 := by
    have : 0 ≤ (N : ℝ) * C₀' * (1 / c) := by positivity
    nlinarith
  have hΛ2 : (N : ℝ) * (C₀' / c) ≤ N * C₀' * (Cρ + 1 / c) + 1 := by
    have : 0 ≤ (N : ℝ) * C₀' * Cρ := by positivity
    have e : (N : ℝ) * (C₀' / c) = N * C₀' * (1 / c) := by ring
    nlinarith
  -- the equation
  have hdetu : (complexHessian u z).det.re =
      Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) * (complexHessian ρ' z).det.re := by
    rw [AubinYauUniformConstants.complexHessian_congr hgu,
      YauUniformEstimate.re_det_complexHessian_eq hφ hpot hzW, hdens z hzt,
      AubinYauUniformConstants.complexHessian_congr hgρ, re_det_complexHessian_potential A hpot hzW]
    ring
  have hρpos : 0 < (complexHessian ρ' z).det.re := by
    have hpd : (complexHessian ρ' z).PosDef :=
      AubinYauLocalStep.posDef_complexHessian (AubinYauLocalStep.contDiffAt_two hρ' z)
        fun v hv => lt_of_lt_of_le (by have := norm_pos_iff.mpr hv; positivity) (hbd z hzc v).1
    exact (Complex.pos_iff.mp hpd.det_pos).1
  have hlog : Real.log (complexHessian u z).det.re =
      (t * F' z + (-ε) * ρ' z + Lg z + κ) + ε * u z := by
    rw [hdetu, Real.log_mul (Real.exp_pos _).ne' hρpos.ne', Real.log_exp, hF'eq hz4, hLgeq hz4,
      hueq hz4, hρ'eq hz6]
    ring
  -- the right-hand side
  have hts : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hεs : |-ε| ≤ 1 := by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hε.1], hε.2⟩
  have hH := congrFun (complexHessian_comb hF' hρ' hLg t (-ε) κ) z
  refine ⟨hpos, htr1.trans hΛ1, htr2.trans hΛ2, hlog, ?_, ?_⟩
  · rw [hH]
    refine (frob_comb_le hts hεs _ _ _).trans ?_
    linarith [(hBF z hzc).1, (hBρ z hzc).1, (hBL z hzc).1]
  · simp only [dH_comb hF' hρ' hLg t (-ε) κ]
    calc ∑ m, frob ((t : ℂ) • dH F' m z + ((-ε : ℝ) : ℂ) • dH ρ' m z + dH Lg m z)
        ≤ ∑ m, (4 * frob (dH F' m z) + 4 * frob (dH ρ' m z) + 2 * frob (dH Lg m z)) :=
          Finset.sum_le_sum fun m _ => frob_comb_le hts hεs _ _ _
      _ = 4 * ∑ m, frob (dH F' m z) + 4 * ∑ m, frob (dH ρ' m z) + 2 * ∑ m, frob (dH Lg m z) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 4 * BF + 4 * Bρ + 2 * BL := by
          linarith [(hBF z hzc).2, (hBρ z hzc).2, (hBL z hzc).2]

/-- **The third-order (Calabi) estimate** (N4 of Yau's theorem; statement I-0831 C-0058, confirmed by
TN23 in C-0059): for a chart `e` and a compact `K ⊆ e.target` there is one constant `C` bounding, on `K`,
the real derivative of every entry of the complex Hessian of `φ ∘ e⁻¹`, for every chart-smooth `φ` with
`A + ddᶜφ` Kähler, `(A + ddᶜφ)^N = e^{tF + εφ + κ} A^N` (`t, ε ∈ [0, 1]`, `κ ∈ ℝ`) and
`C₀⁻¹ A ≤ A + ddᶜφ ≤ C₀ A`, the last two in the chart `e`. -/
theorem exists_norm_fderiv_complexHessian_le {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y]
    (A : PositiveClasses.KahlerBackground N Y) (F : Y → ℝ) (hF : ChartSmooth (n := N) F)
    (C₀ : ℝ) (e : ComplexChart N Y) {K : Set (ComplexModel N)} (hK : IsCompact K)
    (hKe : K ⊆ e.val.target) :
    ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ z ∈ e.val.target,
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ z ∈ e.val.target, ∀ v : ComplexModel N,
        (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] ≤
            C₀ * A.form.val.coeff e z ![v, Complex.I • v] ∧
          A.form.val.coeff e z ![v, Complex.I • v] ≤
            C₀ * (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v]) →
      ∀ z ∈ K, ∀ j k : Fin N,
        ‖fderiv ℝ (fun w => complexHessian (fun w' => φ (e.val.symm w')) w j k) z‖ ≤ C := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, fun φ hφ t ε κ _ _ _ _ _ z _ j => j.elim0⟩
  -- a chart piece at every point of `K`
  have hpiece : ∀ p : K, ∃ (W : Set (ComplexModel N)) (ρ ρ' F' Lg : ComplexModel N → ℝ) (R : ℝ),
      0 < R ∧ IsSmoothLocalPotential A.form.val e W ρ ∧ closedBall (p : ComplexModel N) (8 * R) ⊆ W ∧
      ContDiff ℝ ∞ ρ' ∧ EqOn ρ' ρ (ball (p : ComplexModel N) (6 * R)) ∧
      ContDiff ℝ ∞ F' ∧ EqOn F' (fun w => F (e.val.symm w)) (ball (p : ComplexModel N) (4 * R)) ∧
      ContDiff ℝ ∞ Lg ∧ EqOn Lg (fun w => Real.log (complexHessian ρ' w).det.re)
        (ball (p : ComplexModel N) (4 * R)) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ z ∈ closedBall (p : ComplexModel N) (2 * R),
        ∀ w : ComplexModel N, c * ‖w‖ ^ 2 ≤ leviForm ρ' z w ∧ leviForm ρ' z w ≤ C * ‖w‖ ^ 2 :=
    fun p => exists_chart_piece hN A hF e (hKe p.2)
  choose W ρ ρ' F' Lg R hR hpot h8 hρ' hρ'eq hF' hF'eq hLg hLgeq c Cρ hc hCρ hbd using hpiece
  have hBF := fun p : K => exists_frob_bound (hF' p) (isCompact_closedBall (p : ComplexModel N) (2 * R p))
  have hBρ := fun p : K => exists_frob_bound (hρ' p) (isCompact_closedBall (p : ComplexModel N) (2 * R p))
  have hBL := fun p : K => exists_frob_bound (hLg p) (isCompact_closedBall (p : ComplexModel N) (2 * R p))
  choose BF hBF0 hBF using hBF
  choose Bρ hBρ0 hBρ using hBρ
  choose BL hBL0 hBL using hBL
  have hcore := fun p : K => exists_sum_frob_dH_le (p : ComplexModel N) (hR p)
    (N * max C₀ 1 * (Cρ p + 1 / c p) + 1) (4 * BF p + 4 * Bρ p + 2 * BL p)
  choose Cc hCc using hcore
  -- a finite subcover
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun p : K => ball (p : ComplexModel N) (R p))
    (fun p => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hR _)⟩)
  refine ⟨∑ p ∈ T, (2 * N * √(Cc p) + 2 * N * √(Bρ p)), ?_⟩
  intro φ hφ t ε κ ht hε hKa hdens hC₀ z hz j k
  obtain ⟨p, hpT, hzp⟩ : ∃ p ∈ T, z ∈ ball (p : ComplexModel N) (R p) := by
    have := hT hz
    rw [mem_iUnion₂] at this
    obtain ⟨p, hp, h⟩ := this
    exact ⟨p, hp, h⟩
  have hRp := hR p
  -- the potential of `A_φ` near `p`, made globally smooth
  have hu_on : ContDiffOn ℝ ∞ (fun w => ρ p w + φ (e.val.symm w)) (W p) :=
    (hpot p).2.2.1.add ((hφ e).mono (hpot p).2.1)
  obtain ⟨u, hu, hueq⟩ := exists_contDiff_eqOn_ball (hpot p).1 hu_on
    (by positivity : 0 < 4 * R p) (by linarith : 4 * R p < 8 * R p) (h8 p)
  have hyps := ball_hyps hN A (hpot p) (h8 p) (hρ' p) (hρ'eq p) (hF' p) (hF'eq p) (hLg p)
    (hLgeq p) (hc p) (hCρ p) (hbd p) (hBF p) (hBρ p) (hBL p) C₀ hφ ht hε hKa hdens hC₀ hu hueq
  have hfs : ContDiff ℝ ∞ (fun w => t * F' p w + (-ε) * ρ' p w + Lg p w + κ) :=
    (((contDiff_const.mul (hF' p)).add (contDiff_const.mul (hρ' p))).add (hLg p)).add contDiff_const
  have hbound := hCc p u (fun w => t * F' p w + (-ε) * ρ' p w + Lg p w + κ) ε hu hfs hε.1 hε.2
    hyps z (ball_subset_closedBall hzp)
  -- the Hessian of `φ ∘ e⁻¹` near `z`
  have hz4 : z ∈ ball (p : ComplexModel N) (4 * R p) := ball_subset_ball (by linarith) hzp
  have hgerm : (fun w => complexHessian (fun w' => φ (e.val.symm w')) w j k) =ᶠ[𝓝 z]
      fun w => complexHessian u w j k - complexHessian (ρ' p) w j k := by
    filter_upwards [isOpen_ball.mem_nhds hz4] with w hw
    have h1 : (fun w' => φ (e.val.symm w')) =ᶠ[𝓝 w] fun y => u y + (-1) * ρ' p y := by
      filter_upwards [isOpen_ball.mem_nhds hw] with y hy
      rw [hueq hy, hρ'eq p (ball_subset_ball (by linarith) hy)]
      ring
    rw [AubinYauUniformConstants.complexHessian_congr h1,
      AubinYauLocalStep.complexHessian_fun_add (AubinYauLocalStep.contDiffAt_two hu w)
        (contDiffAt_const.mul (AubinYauLocalStep.contDiffAt_two (hρ' p) w)),
      AubinYauLocalStep.complexHessian_const_mul (AubinYauLocalStep.contDiffAt_two (hρ' p) w)]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hgerm.fderiv_eq, fderiv_fun_sub (differentiable_complexHessian_apply hu j k z)
    (differentiable_complexHessian_apply (hρ' p) j k z)]
  have hρb : ∑ m, frob (dH (ρ' p) m z) ≤ Bρ p :=
    (hBρ p z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hzp))).2
  have hN0 : (0 : ℝ) ≤ 2 * N := by positivity
  calc ‖fderiv ℝ (fun w => complexHessian u w j k) z -
        fderiv ℝ (fun w => complexHessian (ρ' p) w j k) z‖
      ≤ ‖fderiv ℝ (fun w => complexHessian u w j k) z‖ +
          ‖fderiv ℝ (fun w => complexHessian (ρ' p) w j k) z‖ := norm_sub_le _ _
    _ ≤ 2 * N * √(∑ m, frob (dH u m z)) + 2 * N * √(∑ m, frob (dH (ρ' p) m z)) :=
        add_le_add (norm_fderiv_complexHessian_le hu z j k)
          (norm_fderiv_complexHessian_le (hρ' p) z j k)
    _ ≤ 2 * N * √(Cc p) + 2 * N * √(Bρ p) :=
        add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) hN0)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hρb) hN0)
    _ ≤ ∑ q ∈ T, (2 * N * √(Cc q) + 2 * N * √(Bρ q)) :=
        Finset.single_le_sum (f := fun q => 2 * N * √(Cc q) + 2 * N * √(Bρ q))
          (fun q _ => by positivity) hpT

end Manifold

end

end SGPT.Foundations.Analysis.Pending.CalabiThirdOrderEstimate
