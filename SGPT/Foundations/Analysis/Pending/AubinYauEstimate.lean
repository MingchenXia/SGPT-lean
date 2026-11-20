import SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants
import SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax
import SGPT.Foundations.Analysis.Pending.YauUniformEstimate

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The second-order (Aubin–Yau) estimate for the complex Monge–Ampère equation (Błocki)

Let `Y` be a compact complex manifold of dimension `N` with a Kähler form `A`, and `Bφ, BG, L ∈ ℝ`.
There is `C > 0` such that for chart-smooth `φ, G` with `A_φ = A + ddᶜφ` Kähler,
`A_φ^N = e^G A^N` (chart densities), `osc φ ≤ Bφ`, `|G| ≤ BG` and `ddᶜG ≥ -L·A`:
`A_φ ≤ C·A` and `A ≤ C·A_φ` on every complex line in every chart
(`exists_le_smul_of_mongeAmpere_eq_exp`).

This is Theorem 5.13 of Z. Błocki, *The Calabi–Yau theorem*, LNM 2038
(`lnm2038-monge-ampere:page-0222`–`page-0224`) in the nondegenerate case `f = e^G`, i.e. the `C²`
estimate (N3) of Yau's theorem (the second-order Monge–Ampère estimate; statement
the statement under discussion).

## Proof

* `RelativeEigenvalueMax.exists_max_log_ratio_add`: `log η - κφ` attains its maximum `M` at `y`,
  `η` the largest eigenvalue of `A_φ` relative to `A`, realised in a chart at `y` by `|ζ| = 1`.
* In a chart ball around `y` with a local potential `ρ` of `A` (made globally smooth by a cutoff,
  `AubinYauUniformConstants.exists_contDiff_eqOn_ball`), `u = ρ + φ ∘ e⁻¹` is a local potential of
  `A_φ`; `α̃ = log u_{ζζ̄} - log ρ_{ζζ̄} - κ(u - ρ) ≤ log η - κφ ≤ M` near the chart point of `y`,
  with equality there.
* `AubinYauLocalStep.re_trace_inv_le_of_isLocalMax` with the uniform constants of finitely many
  chart balls (`AubinYauUniformConstants.exists_uniform_constants`) and
  `(log det u_{jk̄})_{ζζ̄} = G_{ζζ̄} + (log det ρ_{jk̄})_{ζζ̄}`: `tr (u_{jk̄})⁻¹ ≤ κN` at `y`.
* The endgame (`AubinYauMatrixBounds`): `η(y) ≤ Λ`, hence `η ≤ Λ e^{κ Bφ}` everywhere, hence both
  inequalities.
-/

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.AubinYauEstimate

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian AubinYauLocalStep
  AubinYauUniformConstants RelativeEigenvalueMax ManifoldTubePositivity

noncomputable section

/-! ### Matrices -/

section Matrix

variable {n : ℕ}

/-- `G' ≤ c G` (positive definite) gives `tr(G⁻¹ G') ≤ n c`. -/
theorem re_trace_inv_mul_le_of_quad_le {G G' : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hG' : G'.PosDef) {c : ℝ}
    (h : ∀ x, (star x ⬝ᵥ (G' *ᵥ x)).re ≤ c * (star x ⬝ᵥ (G *ᵥ x)).re) :
    (G⁻¹ * G').trace.re ≤ n * c := by
  classical
  obtain ⟨R, hdet, hGR, lam, -, hG'R⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hG' hG
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hRu
  have hSG : (star R) * G = R⁻¹ := by
    calc (star R) * G = (star R) * G * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * G * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ := by rw [hGR, Matrix.one_mul]
  have hGinv : G⁻¹ = R * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSG, hRR]
  have htr : (G⁻¹ * G').trace = ∑ k, (lam k : ℂ) := by
    rw [hGinv, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc (star R),
      hG'R, trace_diagonal]
  have hk : ∀ k, lam k ≤ c := by
    intro k
    have hx := h (R *ᵥ Pi.single k 1)
    rw [AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec,
      AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec, hG'R, hGR] at hx
    simpa [dotProduct, mulVec_diagonal, Pi.single_apply] using hx
  rw [htr, Complex.re_sum]
  simp only [Complex.ofReal_re]
  calc ∑ k, lam k ≤ ∑ _k : Fin n, c := Finset.sum_le_sum fun k _ => hk k
    _ = n * c := by simp

end Matrix

/-! ### Charts with local potentials -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem contDiffAt_two_of_contDiffOn {f : ComplexModel N → ℝ} {W : Set (ComplexModel N)}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) {z : ComplexModel N} (hz : z ∈ W) :
    ContDiffAt ℝ 2 f z :=
  (hf.contDiffAt (hW.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The background form on a complex line, through a local potential. -/
theorem coeff_line_eq_leviForm (A : PositiveClasses.KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {z : ComplexModel N} (hz : z ∈ W)
    (v : ComplexModel N) :
    A.form.val.coeff e z (line v) = leviForm ρ z v / Real.pi := by
  rw [← hpot.2.2.2 hz, smoothDDC_complexDiagonal_eq_leviForm
    (contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hz)]

/-- `A + ddᶜφ` on a complex line, through the local potential `ρ + φ ∘ e⁻¹`. -/
theorem coeff_add_line_eq_leviForm (A : PositiveClasses.KahlerBackground N Y) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) {e : ComplexChart N Y} {W : Set (ComplexModel N)}
    {ρ : ComplexModel N → ℝ} (hpot : IsSmoothLocalPotential A.form.val e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) (v : ComplexModel N) :
    (A.form + ddcClosedForm φ hφ).val.coeff e z (line v) =
      leviForm (fun w => ρ w + φ (e.val.symm w)) z v / Real.pi := by
  have hρ : ContDiffOn ℝ ∞ ρ W := hpot.2.2.1
  have hψ : ContDiffOn ℝ ∞ (fun w => φ (e.val.symm w)) W := (hφ e).mono hpot.2.1
  have hcoeff : (A.form + ddcClosedForm φ hφ).val.coeff e z =
      smoothDDC (fun w => ρ w + φ (e.val.symm w)) z := by
    rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff, smoothDDC_add hpot.1 hρ hψ hz,
      hpot.2.2.2 hz]
  rw [hcoeff, smoothDDC_complexDiagonal_eq_leviForm
    (contDiffAt_two_of_contDiffOn hpot.1 (hρ.add hψ) hz)]

/-- `ddᶜG` on a complex line. -/
theorem ddc_coeff_line_eq_leviForm {G : Y → ℝ} (hG : ChartSmooth (n := N) G)
    {e : ComplexChart N Y} {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    (ddcClosedForm G hG).val.coeff e z (line v) =
      leviForm (fun w => G (e.val.symm w)) z v / Real.pi := by
  rw [ddcClosedForm_coeff, smoothDDC_complexDiagonal_eq_leviForm
    (contDiffAt_two_of_contDiffOn e.val.open_target (hG e) hz)]

/-- The chart density of `A` is `(N!/πᴺ) det` of the complex Hessian of a local potential. -/
theorem re_det_complexHessian_potential (A : PositiveClasses.KahlerBackground N Y)
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {z : ComplexModel N} (hz : z ∈ W) :
    (complexHessian ρ z).det.re =
      Real.pi ^ N / N.factorial * actualTopPowerDensity (A.form.val.coeff e z) := by
  have hzt : z ∈ e.val.target := hpot.2.1 hz
  have h11 : IsOneOne (A.form.val.coeff e z) := A.form.property.2 e z hzt
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det h11, ← hpot.2.2.2 hz,
    normalizedHermitianMatrix_smoothDDC (contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hz)]
  have hpi : (0 : ℝ) < Real.pi ^ N := pow_pos Real.pi_pos N
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  field_simp

/-- The Monge–Ampère equation in terms of the complex Hessians of local potentials. -/
theorem re_det_complexHessian_eq_exp (A : PositiveClasses.KahlerBackground N Y) {φ G : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ)
    (hdens : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {z : ComplexModel N} (hz : z ∈ W) :
    (complexHessian (fun w => ρ w + φ (e.val.symm w)) z).det.re =
      Real.exp (G (e.val.symm z)) * (complexHessian ρ z).det.re := by
  rw [YauUniformEstimate.re_det_complexHessian_eq hφ hpot hz, hdens e z (hpot.2.1 hz),
    re_det_complexHessian_potential A hpot hz]
  ring

/-- Positivity of the Levi form of a local potential of a Kähler form. -/
theorem leviForm_pos_of_isKahler {a : SmoothRealForm N Y 2} (ha : a.IsKahler)
    {e : ComplexChart N Y} {z : ComplexModel N} (hz : z ∈ e.val.target) {f : ComplexModel N → ℝ}
    (hf : ∀ v, a.coeff e z (line v) = leviForm f z v / Real.pi) {v : ComplexModel N}
    (hv : v ≠ 0) : 0 < leviForm f z v := by
  have h := (ha.1 e z hz).2 v hv
  have h' : 0 < leviForm f z v / Real.pi := by rw [← hf v]; exact h
  exact (div_pos_iff_of_pos_right Real.pi_pos).mp h'

/-- The quadratic form of a complex Hessian at the conjugate vector is the Levi form. -/
theorem re_quad_complexHessian_star {f : ComplexModel N → ℝ} {z : ComplexModel N}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexModel N) :
    (star (fun d => star (v d)) ⬝ᵥ (complexHessian f z *ᵥ fun d => star (v d))).re =
      leviForm f z v := by
  rw [dotProduct_mulVec_complexHessian_eq_leviForm hf, coordCombination_star, Complex.ofReal_re]

theorem re_quad_complexHessian {f : ComplexModel N → ℝ} {z : ComplexModel N}
    (hf : ContDiffAt ℝ 2 f z) (x : Fin N → ℂ) :
    (star x ⬝ᵥ (complexHessian f z *ᵥ x)).re = leviForm f z (coordCombination x) := by
  rw [dotProduct_mulVec_complexHessian_eq_leviForm hf, Complex.ofReal_re]

/-- **A chart piece** around `p`: a local potential `ρ` of `A` on `W ⊇ closedBall (4R)`, a globally
smooth `ρ'` equal to `ρ` on `ball (2R)`, and the uniform constants of `ρ'` on `closedBall R`. -/
theorem exists_piece (hN : 0 < N) (A : PositiveClasses.KahlerBackground N Y) (p : Y) :
    ∃ (W : Set (ComplexModel N)) (ρ ρ' : ComplexModel N → ℝ) (R : ℝ), 0 < R ∧
      IsSmoothLocalPotential A.form.val (complexChartAt (n := N) p) W ρ ∧
      closedBall ((complexChartAt (n := N) p).val p) (4 * R) ⊆ W ∧
      ContDiff ℝ ∞ ρ' ∧ EqOn ρ' ρ (ball ((complexChartAt (n := N) p).val p) (2 * R)) ∧
      ∃ c C M K₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ M ∧ 0 ≤ K₁ ∧
        ∀ z ∈ closedBall ((complexChartAt (n := N) p).val p) R,
          (∀ w, c * ‖w‖ ^ 2 ≤ leviForm ρ' z w) ∧ (∀ w, leviForm ρ' z w ≤ C * ‖w‖ ^ 2) ∧
          (∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 → ∀ w,
            leviForm (fun y => leviForm ρ' y ζ) z w ≤ M * ‖w‖ ^ 2) ∧
          (∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 →
            -K₁ ≤ leviForm (fun y => Real.log (complexHessian ρ' y).det.re) z ζ) := by
  set e := complexChartAt (n := N) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  have hzp : e.val p ∈ e.val.target := e.val.map_source hp
  obtain ⟨W, ρ, hzW, hpot⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials A.form e (e.val p) hzp
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp hpot.1 (e.val p) hzW
  set R := R₀ / 8 with hRdef
  have hR : 0 < R := by positivity
  have h4 : closedBall (e.val p) (4 * R) ⊆ W :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hball
  obtain ⟨ρ', hρ', hρ'eq⟩ := exists_contDiff_eqOn_ball hpot.1 hpot.2.2.1
    (by positivity : 0 < 2 * R) (by linarith : 2 * R < 4 * R) h4
  have hVW : ball (e.val p) (2 * R) ⊆ W :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans h4
  have hlevi : ∀ z ∈ ball (e.val p) (2 * R), ∀ v, v ≠ 0 → 0 < leviForm ρ' z v := by
    intro z hz v hv
    have hgerm : ρ' =ᶠ[𝓝 z] ρ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hρ'eq
    rw [leviForm_congr hgerm]
    exact leviForm_pos_of_isKahler A.isKahler (hpot.2.1 (hVW hz))
      (coeff_line_eq_leviForm A hpot (hVW hz)) hv
  obtain ⟨c, C, M, K₁, hc, hC, hM, hK₁, hbd⟩ := exists_uniform_constants hN hρ' isOpen_ball
    (isCompact_closedBall _ _) (closedBall_subset_ball (by linarith)) hlevi
  exact ⟨W, ρ, ρ', R, hR, hpot, h4, hρ', hρ'eq, c, C, M, K₁, hc, hC, hM, hK₁, hbd⟩

/-! ### The estimate -/

/-- **The `C²` estimate** (Błocki, LNM 2038 Theorem 5.13 in the nondegenerate case,
`lnm2038-monge-ampere:page-0222`–`page-0224`): on a compact complex manifold `Y` with a Kähler form
`A`, for all `Bφ, BG, L` there is `C > 0` such that every chart-smooth `φ` with `A_φ = A + ddᶜφ` Kähler,
`A_φ^N = e^G A^N`, `osc φ ≤ Bφ`, `|G| ≤ BG` and `ddᶜG ≥ -L·A` satisfies `A_φ ≤ C·A` and
`A ≤ C·A_φ` on every complex line in every chart. -/
theorem exists_le_smul_of_mongeAmpere_eq_exp {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y]
    [ConnectedSpace Y] (A : PositiveClasses.KahlerBackground N Y) (Bφ BG L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (G : Y → ℝ)
      (hG : ChartSmooth (n := N) G),
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ e z, z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ x y, φ x - φ y ≤ Bφ) → (∀ x, |G x| ≤ BG) →
      (∀ e z, z ∈ e.val.target → ∀ v : ComplexModel N,
        -L * A.form.val.coeff e z ![v, Complex.I • v] ≤
          (ddcClosedForm G hG).val.coeff e z ![v, Complex.I • v]) →
      ∀ e z, z ∈ e.val.target → ∀ v : ComplexModel N,
        (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] ≤
            C * A.form.val.coeff e z ![v, Complex.I • v] ∧
          A.form.val.coeff e z ![v, Complex.I • v] ≤
            C * (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] := by
  classical
  -- trivial cases
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨1, one_pos, fun φ hφ G hG _ _ _ _ _ e z hz v =>
      (hY.false (e.val.symm z)).elim⟩
  have hzero : ∀ (β : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ), β (line 0) = 0 := fun β =>
    β.map_coord_zero (0 : Fin 2) (by simp [line])
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨1, one_pos, fun φ hφ G hG _ _ _ _ _ e z hz v => ?_⟩
    subst hN
    have hv : v = 0 := Subsingleton.elim _ _
    subst hv
    have h1 := hzero ((A.form + ddcClosedForm φ hφ).val.coeff e z)
    have h2 := hzero (A.form.val.coeff e z)
    simp only [line] at h1 h2
    rw [h1, h2]
    simp
  -- the finite atlas of chart pieces and its constants
  choose W ρ ρ' R hR hpot hWball hρ' hρ'eq c C M K₁ hc hC hM hK₁ hbd using exists_piece hN A
  set e : Y → ComplexChart N Y := fun p => complexChartAt (n := N) p with hedef
  set O : Y → Set Y := fun p => (e p).val.source ∩ (e p).val ⁻¹' ball ((e p).val p) (R p)
    with hOdef
  have hO : ∀ p, IsOpen (O p) := fun p => (e p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => ⟨mem_complexChartAt_source p, mem_ball_self (hR p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  set K0 : Y → ℝ := fun p => max L 0 * C p + K₁ p with hK0def
  have hK0 : ∀ p, 0 ≤ K0 p := fun p => by
    simp only [hK0def]; have := hC p; have := hK₁ p; positivity
  set κ : ℝ := ∑ p ∈ t, (K0 p + M p / c p + 1) / c p with hκdef
  have hterm : ∀ p, 0 ≤ (K0 p + M p / c p + 1) / c p := fun p => by
    have := hK0 p; have := hM p; have := hc p; positivity
  have hκ0 : 0 ≤ κ := Finset.sum_nonneg fun p _ => hterm p
  have hκp : ∀ p ∈ t, K0 p + M p / c p + 1 ≤ κ * c p := by
    intro p hp
    have h1 : (K0 p + M p / c p + 1) / c p ≤ κ :=
      Finset.single_le_sum (f := fun p => (K0 p + M p / c p + 1) / c p) (fun q _ => hterm q) hp
    rw [div_le_iff₀ (hc p)] at h1
    exact h1
  set Λ : ℝ := ∑ p ∈ t, Real.exp BG * (C p * κ * N) ^ (N - 1) with hΛdef
  have hΛterm : ∀ p, 0 ≤ Real.exp BG * (C p * κ * N) ^ (N - 1) := fun p => by
    have := hC p; positivity
  set C₁ : ℝ := Λ * Real.exp (κ * Bφ) with hC₁def
  set C₂ : ℝ := (N * C₁) ^ (N - 1) / Real.exp (-BG) with hC₂def
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro φ hφ G hG hKa hdens hosc hGb hddc
  set Aφ := A.form + ddcClosedForm φ hφ with hAφdef
  have hApos : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 →
      0 < A.form.val.coeff e z (line v) := fun e z hz v hv => (A.isKahler.1 e z hz).2 v hv
  have hBpos : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 →
      0 < Aφ.val.coeff e z (line v) := fun e z hz v hv => (hKa.1 e z hz).2 v hv
  have hφc : Continuous φ := YauUniformEstimate.continuous_of_chartSmooth hφ
  -- STEP 1: the maximum of `log η - κ φ`
  obtain ⟨y, Mx, hbound, hattain⟩ := exists_max_log_ratio_add hN A.form.val Aφ.val hApos hBpos
    (f := fun x => -κ * φ x) (continuous_const.mul hφc)
  obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, y ∈ O p := by
    have := ht (mem_univ y)
    rw [mem_iUnion₂] at this
    obtain ⟨p, hp, hyp⟩ := this
    exact ⟨p, hp, hyp⟩
  obtain ⟨ζ, hζ1, hζ⟩ := hattain (e p) hyp.1
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  set z₀ := (e p).val y with hz₀def
  set V := ball ((e p).val p) (2 * R p) with hVdef
  have hz₀B : z₀ ∈ ball ((e p).val p) (R p) := hyp.2
  have hz₀V : z₀ ∈ V := ball_subset_ball (by linarith [hR p]) hz₀B
  have hz₀K : z₀ ∈ closedBall ((e p).val p) (R p) := ball_subset_closedBall hz₀B
  have hVW : V ⊆ W p :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [hR p]))).trans
      (hWball p)
  -- STEP 2: the local potential of `A_φ` in the chart, globally smooth near `z₀`
  set ψ : ComplexModel N → ℝ := fun w => φ ((e p).val.symm w) with hψdef
  have hu_on : ContDiffOn ℝ ∞ (fun w => ρ p w + ψ w) (W p) :=
    (hpot p).2.2.1.add ((hφ (e p)).mono (hpot p).2.1)
  obtain ⟨u', hu', hu'eq⟩ := exists_contDiff_eqOn_ball (hpot p).1 hu_on
    (by linarith [hR p] : 0 < 2 * R p) (by linarith [hR p] : 2 * R p < 4 * R p) (hWball p)
  have hgermu : ∀ z ∈ V, u' =ᶠ[𝓝 z] fun w => ρ p w + ψ w := fun z hz =>
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hu'eq
  have hgermρ : ∀ z ∈ V, ρ' p =ᶠ[𝓝 z] ρ p := fun z hz =>
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (hρ'eq p)
  have hLu : ∀ z ∈ V, ∀ v, leviForm u' z v = Real.pi * Aφ.val.coeff (e p) z (line v) := by
    intro z hz v
    rw [leviForm_congr (hgermu z hz), coeff_add_line_eq_leviForm A hφ (hpot p) (hVW hz)]
    field_simp
    rfl
  have hLρ : ∀ z ∈ V, ∀ v, leviForm (ρ' p) z v = Real.pi * A.form.val.coeff (e p) z (line v) := by
    intro z hz v
    rw [leviForm_congr (hgermρ z hz), coeff_line_eq_leviForm A (hpot p) (hVW hz)]
    field_simp
  have hzt : ∀ z ∈ V, z ∈ (e p).val.target := fun z hz => (hpot p).2.1 (hVW hz)
  -- STEP 3: the comparison function has a local maximum at `z₀`
  set α : ComplexModel N → ℝ := fun z => Real.log (leviForm u' z ζ) -
    Real.log (leviForm (ρ' p) z ζ) - κ * (u' z - ρ' p z) with hαdef
  have hαV : ∀ z ∈ V, α z = Real.log (Aφ.val.coeff (e p) z (line ζ) /
      A.form.val.coeff (e p) z (line ζ)) + (-κ * φ ((e p).val.symm z)) := by
    intro z hz
    have ha := hApos (e p) z (hzt z hz) ζ hζ0
    have hb := hBpos (e p) z (hzt z hz) ζ hζ0
    have hdiff : u' z - ρ' p z = φ ((e p).val.symm z) := by
      rw [hu'eq hz, hρ'eq p hz]; simp only [hψdef]; ring
    simp only [hαdef]
    rw [hLu z hz, hLρ z hz, hdiff, Real.log_div hb.ne' ha.ne',
      Real.log_mul Real.pi_pos.ne' hb.ne', Real.log_mul Real.pi_pos.ne' ha.ne']
    ring
  have hαz₀ : α z₀ = Mx := by
    rw [hαV z₀ hz₀V, (e p).val.left_inv hyp.1]
    exact hζ
  have hmax : IsLocalMax α z₀ := by
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhds hz₀V) fun z hz => ?_
    rw [hαz₀, hαV z hz]
    exact hbound (e p) z (hzt z hz) ζ hζ0
  -- STEP 4: the hypotheses of the local step at `z₀`
  have hz₀t : z₀ ∈ (e p).val.target := hzt z₀ hz₀V
  have hposu : ∀ z ∈ V, (complexHessian u' z).PosDef := fun z hz =>
    posDef_complexHessian (contDiffAt_two hu' z) fun v hv => by
      rw [hLu z hz v]; exact mul_pos Real.pi_pos (hBpos _ _ (hzt z hz) v hv)
  have hposρ : ∀ z ∈ V, (complexHessian (ρ' p) z).PosDef := fun z hz =>
    posDef_complexHessian (contDiffAt_two (hρ' p) z) fun v hv => by
      rw [hLρ z hz v]; exact mul_pos Real.pi_pos (hApos _ _ (hzt z hz) v hv)
  set Gt : ComplexModel N → ℝ := fun w => G ((e p).val.symm w) with hGtdef
  set Dρ : ComplexModel N → ℝ := fun w => (complexHessian (ρ' p) w).det.re with hDρdef
  have hdetV : ∀ z ∈ V, (complexHessian u' z).det.re = Real.exp (Gt z) * Dρ z := by
    intro z hz
    show (complexHessian u' z).det.re = Real.exp (Gt z) * (complexHessian (ρ' p) z).det.re
    rw [complexHessian_congr (hgermu z hz), complexHessian_congr (hgermρ z hz)]
    exact re_det_complexHessian_eq_exp A hφ hdens (hpot p) (hVW hz)
  have hDρpos : ∀ z ∈ V, 0 < Dρ z := fun z hz => (Complex.pos_iff.mp (hposρ z hz).det_pos).1
  have hlogV : (fun w => Real.log (complexHessian u' w).det.re) =ᶠ[𝓝 z₀]
      fun w => Gt w + Real.log (Dρ w) := by
    filter_upwards [isOpen_ball.mem_nhds hz₀V] with z hz
    rw [hdetV z hz, Real.log_mul (Real.exp_pos _).ne' (hDρpos z hz).ne', Real.log_exp]
  have hGt2 : ContDiffAt ℝ 2 Gt z₀ :=
    contDiffAt_two_of_contDiffOn (e p).val.open_target (hG (e p)) hz₀t
  have hDρc : ContDiff ℝ ∞ Dρ :=
    Complex.reCLM.contDiff.comp (WirtingerLogDet.contDiff_det_complexHessian (hρ' p))
  have hlog2 : ContDiffAt ℝ 2 (fun w => Real.log (Dρ w)) z₀ :=
    (contDiffAt_two hDρc z₀).log (hDρpos z₀ hz₀V).ne'
  have hlevisum : leviForm (fun w => Real.log (complexHessian u' w).det.re) z₀ ζ =
      leviForm Gt z₀ ζ + leviForm (fun w => Real.log (Dρ w)) z₀ ζ := by
    rw [leviForm_congr hlogV]
    exact leviForm_add hGt2 hlog2 ζ
  have hGlow : -L * leviForm (ρ' p) z₀ ζ ≤ leviForm Gt z₀ ζ := by
    have h := hddc (e p) z₀ hz₀t ζ
    have h1 : A.form.val.coeff (e p) z₀ (line ζ) = leviForm (ρ' p) z₀ ζ / Real.pi := by
      rw [hLρ z₀ hz₀V]; field_simp
    have h2 := ddc_coeff_line_eq_leviForm hG hz₀t ζ
    change -L * A.form.val.coeff (e p) z₀ (line ζ) ≤ (ddcClosedForm G hG).val.coeff (e p) z₀
      (line ζ) at h
    rw [h1, h2] at h
    have hpi := Real.pi_pos
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hpi] at h
    exact h
  have hLρC : leviForm (ρ' p) z₀ ζ ≤ C p := by
    have := (hbd p z₀ hz₀K).2.1 ζ; rw [hζ1] at this; simpa using this
  have hLρ0 : 0 ≤ leviForm (ρ' p) z₀ ζ := by
    have := (hbd p z₀ hz₀K).1 ζ; rw [hζ1] at this
    have hcp := hc p
    nlinarith
  have hdet : -K0 p ≤ leviForm (fun w => Real.log (complexHessian u' w).det.re) z₀ ζ := by
    rw [hlevisum]
    have h3 := (hbd p z₀ hz₀K).2.2.2 ζ hζ1.le
    have h4 : -(max L 0 * C p) ≤ -L * leviForm (ρ' p) z₀ ζ := by
      have hL := le_max_left L 0
      have hL0 := le_max_right L 0
      nlinarith
    simp only [hK0def]
    simp only [hDρdef] at h3 ⊢
    linarith
  have htrace := re_trace_inv_le_of_isLocalMax hu' (hρ' p) hζ1 (hposu z₀ hz₀V) (hc p) (hK0 p)
    (hM p) ((hbd p z₀ hz₀K).1) ((hbd p z₀ hz₀K).2.2.1 ζ hζ1.le) hdet (hκp p hpt) hmax
  -- STEP 5: the endgame at `z₀`: `η(y) ≤ Λ`
  have hGm := hposρ z₀ hz₀V
  have hGm' := hposu z₀ hz₀V
  have hK : ((complexHessian u' z₀)⁻¹ * complexHessian (ρ' p) z₀).trace.re ≤ C p * κ * N := by
    have h := re_trace_mul_complexHessian_le hGm'.posSemidef.inv (contDiffAt_two (hρ' p) z₀)
      (hbd p z₀ hz₀K).2.1
    calc ((complexHessian u' z₀)⁻¹ * complexHessian (ρ' p) z₀).trace.re
        ≤ C p * ((complexHessian u' z₀)⁻¹).trace.re := h
      _ ≤ C p * (κ * N) := mul_le_mul_of_nonneg_left htrace (hC p)
      _ = C p * κ * N := by ring
  have hD : (complexHessian u' z₀).det.re ≤ Real.exp BG * (complexHessian (ρ' p) z₀).det.re := by
    rw [hdetV z₀ hz₀V]
    have hGy : Gt z₀ ≤ BG := by
      simp only [hGtdef, hz₀def, (e p).val.left_inv hyp.1]
      exact (le_abs_self _).trans (hGb y)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hGy) (hDρpos z₀ hz₀V).le
  have hq := AubinYauMatrixBounds.quad_le_of_trace_inv_le hGm hGm' hK hD (fun d => star (ζ d))
  rw [re_quad_complexHessian_star (contDiffAt_two hu' z₀),
    re_quad_complexHessian_star (contDiffAt_two (hρ' p) z₀)] at hq
  have hLρpos : 0 < leviForm (ρ' p) z₀ ζ := by
    rw [hLρ z₀ hz₀V]; exact mul_pos Real.pi_pos (hApos _ _ hz₀t ζ hζ0)
  have hLupos : 0 < leviForm u' z₀ ζ := by
    rw [hLu z₀ hz₀V]; exact mul_pos Real.pi_pos (hBpos _ _ hz₀t ζ hζ0)
  have hΛp : Real.exp BG * (C p * κ * N) ^ (N - 1) ≤ Λ :=
    Finset.single_le_sum (f := fun p => Real.exp BG * (C p * κ * N) ^ (N - 1))
      (fun q _ => hΛterm q) hpt
  have hratio0 : Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) =
      leviForm u' z₀ ζ / leviForm (ρ' p) z₀ ζ := by
    rw [hLu z₀ hz₀V, hLρ z₀ hz₀V, mul_div_mul_left _ _ Real.pi_pos.ne']
  have hratio : Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) ≤ Λ := by
    rw [hratio0, div_le_iff₀ hLρpos]
    calc leviForm u' z₀ ζ ≤ Real.exp BG * (C p * κ * N) ^ (N - 1) * leviForm (ρ' p) z₀ ζ := hq
      _ ≤ Λ * leviForm (ρ' p) z₀ ζ := mul_le_mul_of_nonneg_right hΛp hLρpos.le
  have hratiopos : 0 < Aφ.val.coeff (e p) z₀ (line ζ) / A.form.val.coeff (e p) z₀ (line ζ) := by
    rw [hratio0]; exact div_pos hLupos hLρpos
  have hΛpos : 0 < Λ := hratiopos.trans_le hratio
  have hMx : Mx ≤ Real.log Λ - κ * φ y := by
    rw [← hαz₀, hαV z₀ hz₀V, (e p).val.left_inv hyp.1]
    have := Real.log_le_log hratiopos hratio
    linarith
  -- STEP 6: `A_φ ≤ C₁ A` everywhere
  have hAnn : ∀ (e' : ComplexChart N Y) z, z ∈ e'.val.target → ∀ v,
      0 ≤ A.form.val.coeff e' z (line v) := by
    intro e' z hz v
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, hzero]
    · exact (hApos e' z hz v hv).le
  have hBnn : ∀ (e' : ComplexChart N Y) z, z ∈ e'.val.target → ∀ v,
      0 ≤ Aφ.val.coeff e' z (line v) := by
    intro e' z hz v
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, hzero]
    · exact (hBpos e' z hz v hv).le
  have hfirst : ∀ (e' : ComplexChart N Y) z, z ∈ e'.val.target → ∀ v,
      Aφ.val.coeff e' z (line v) ≤ C₁ * A.form.val.coeff e' z (line v) := by
    intro e' z hz v
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, hzero, hzero, mul_zero]
    have ha := hApos e' z hz v hv
    have hb := hBpos e' z hz v hv
    have h1 := hbound e' z hz v hv
    have h2 := hosc (e'.val.symm z) y
    have hlog : Real.log (Aφ.val.coeff e' z (line v) / A.form.val.coeff e' z (line v)) ≤
        Real.log Λ + κ * Bφ := by
      have : κ * (φ (e'.val.symm z) - φ y) ≤ κ * Bφ := mul_le_mul_of_nonneg_left h2 hκ0
      linarith
    have hle : Aφ.val.coeff e' z (line v) / A.form.val.coeff e' z (line v) ≤ C₁ := by
      have := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log (div_pos hb ha), Real.exp_add, Real.exp_log hΛpos] at this
      exact this
    rwa [div_le_iff₀ ha] at hle
  -- STEP 7: `A ≤ C₂ A_φ` everywhere (traces and determinants in any chart)
  have hsecond : ∀ (e' : ComplexChart N Y) z, z ∈ e'.val.target → ∀ v,
      A.form.val.coeff e' z (line v) ≤ C₂ * Aφ.val.coeff e' z (line v) := by
    intro e' z hz v
    obtain ⟨W', ρ'', hzW', hpot'⟩ :=
      LocalPotentials.closedRealOneOne_hasLocalPotentials A.form e' z hz
    have hρ''2 : ContDiffAt ℝ 2 ρ'' z := contDiffAt_two_of_contDiffOn hpot'.1 hpot'.2.2.1 hzW'
    have hu''2 : ContDiffAt ℝ 2 (fun w => ρ'' w + φ (e'.val.symm w)) z :=
      contDiffAt_two_of_contDiffOn hpot'.1 (hpot'.2.2.1.add ((hφ e').mono hpot'.2.1)) hzW'
    have hA' := coeff_line_eq_leviForm A hpot' hzW'
    have hB' := coeff_add_line_eq_leviForm A hφ hpot' hzW'
    have hGm : (complexHessian ρ'' z).PosDef := posDef_complexHessian hρ''2 fun w hw =>
      leviForm_pos_of_isKahler A.isKahler hz hA' hw
    have hGm' : (complexHessian (fun w => ρ'' w + φ (e'.val.symm w)) z).PosDef :=
      posDef_complexHessian hu''2 fun w hw => leviForm_pos_of_isKahler hKa hz hB' hw
    have hquad : ∀ x, (star x ⬝ᵥ (complexHessian (fun w => ρ'' w + φ (e'.val.symm w)) z *ᵥ x)).re ≤
        C₁ * (star x ⬝ᵥ (complexHessian ρ'' z *ᵥ x)).re := by
      intro x
      rw [re_quad_complexHessian hu''2, re_quad_complexHessian hρ''2]
      have h := hfirst e' z hz (coordCombination x)
      rw [hA', hB'] at h
      have hpi := Real.pi_pos
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hpi] at h
      exact h
    have htr := re_trace_inv_mul_le_of_quad_le hGm hGm' hquad
    have hdet : Real.exp (-BG) * (complexHessian ρ'' z).det.re ≤
        (complexHessian (fun w => ρ'' w + φ (e'.val.symm w)) z).det.re := by
      rw [re_det_complexHessian_eq_exp A hφ hdens hpot' hzW']
      have hGz : -BG ≤ G (e'.val.symm z) := by
        have := hGb (e'.val.symm z); rw [abs_le] at this; exact this.1
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hGz)
        (Complex.pos_iff.mp hGm.det_pos).1.le
    have hq2 := (AubinYauMatrixBounds.quad_le_of_trace_le hGm hGm' htr hdet (Real.exp_pos _)
      (fun d => star (v d))).2
    rw [re_quad_complexHessian_star hρ''2, re_quad_complexHessian_star hu''2] at hq2
    rw [hA', hB', mul_div_assoc']
    exact div_le_div_of_nonneg_right hq2 Real.pi_pos.le
  intro e' z hz v
  have ha := hAnn e' z hz v
  have hb := hBnn e' z hz v
  constructor
  · exact (hfirst e' z hz v).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) ha)
  · exact (hsecond e' z hz v).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) hb)

end Manifold

end

end SGPT.Foundations.Analysis.Pending.AubinYauEstimate
