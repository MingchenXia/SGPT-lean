import SGPT.Trace.OTExt4Grad
import SGPT.Okounkov.TranscendentalSkodaKernel

/-!
# A Ricci lower bound for the chart densities of a smooth volume

Blueprint `claude-ot-ext5.tex`, node `claude-ot-ext5:ricci`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `thm:compact-submanifold-extension` ("choose `b_K ≥ 0` with
`c₁(K_X^{-1}, h_{K^{-1},ω}) ≥ -b_K ω`", `lem:hermitian-form-comparison`), in the chart form used by
`CompactTwistedL2CorrectionStatement`: for a smooth positive volume `μ` on a compact Kähler manifold
there is `b_K ≥ 0` with

`Levi(log ρ_c)(v) ≤ b_K ω_c(v, iv)`

for **every** chart `c` and every density `ρ_c` of `μ` in `c` (`Levi(-log ρ_c)` is the curvature
of the metric of `K_X^{-1}` induced by `μ`, times `π`).

* `det_restrictScalars_eq_norm_sq`: `det_ℝ A = |det_ℂ A|²` for `ℂ`-linear `A`;
* `chartDensity_chg`: the transformation law `ρ_c = |J|² ρ_{c'} ∘ (c' ∘ c⁻¹)` of chart densities,
  `J = det_ℂ D(c' ∘ c⁻¹)` (`jac`), from the change of variables formula and the comparison of
  integrals over small balls (`eqOn_of_setIntegral_closedBall_eq`);
* `leviForm_log_norm_sq_eq_zero`: `log |J|²` is pluriharmonic;
* `exists_leviForm_log_chartDensity_le`: the Ricci lower bound.  Near every point `x` the function
  `log ρ_e ∘ e` (for the chart `e` at `x`) is extended to a global smooth function `H`; the Kähler
  domination of `ddᶜ(-H)` near `x` in every chart (`exists_nhds_smoothDDC_domination`) and the
  transformation law give the bound near `x` in every chart; finitely many points suffice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Manifold ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Trace.TwistedL2 SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

variable {n : ℕ}

/-! ### Jacobians -/

/-- `det_ℂ A = det (linMat A)`. -/
theorem linearMap_det_eq_det_linMat (A : ComplexModel n →L[ℂ] ComplexModel n) :
    LinearMap.det (A : ComplexModel n →ₗ[ℂ] ComplexModel n) = (linMat A).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

/-- `det_ℝ A = |det_ℂ A|²` for a `ℂ`-linear map `A` of `ℂⁿ`. -/
theorem det_restrictScalars_eq_norm_sq (A : ComplexModel n →L[ℂ] ComplexModel n) :
    (A.restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n).det = ‖(linMat A).det‖ ^ 2 := by
  rw [← linearMap_det_eq_det_linMat, ← Complex.normSq_eq_norm_sq]
  have h := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ)
    (f := (A : ComplexModel n →ₗ[ℂ] ComplexModel n))
  rw [Algebra.norm_complex_eq] at h
  exact h

/-- The determinant of a matrix with holomorphic entries is holomorphic. -/
theorem differentiableAt_det_of_entries {k : ℕ} {f : ComplexModel n → Matrix (Fin k) (Fin k) ℂ}
    {z : ComplexModel n} (hf : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) z) :
    DifferentiableAt ℂ (fun y => (f y).det) z := by
  have heq : (fun y => (f y).det) = fun y => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [heq]
  exact DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i y => f y (σ i) i)
      fun i _ => (hf _ _).hasFDerivAt).differentiableAt

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The complex Jacobian `J = det_ℂ D(c' ∘ c⁻¹)` of a coordinate change. -/
def jac (c c' : ComplexChart n X) (z : ComplexModel n) : ℂ := (linMat (fderiv ℂ (chg c c') z)).det

theorem contDiffOn_chg (c c' : ComplexChart n X) : ContDiffOn ℂ ∞ (chg c c') (ovl c c') :=
  contDiffOn_of_differentiableOn_complex (differentiableOn_chg c c') (isOpen_ovl c c')

theorem differentiableAt_jac {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    DifferentiableAt ℂ (jac c c') z := by
  refine differentiableAt_det_of_entries fun i j => ?_
  have h1 : DifferentiableAt ℂ (fun y => fderiv ℂ (chg c c') y (coordVec j)) z :=
    (differentiableOn_fderiv_apply_of_isOpen (differentiableOn_chg c c') (isOpen_ovl c c')
      (coordVec j)).differentiableAt ((isOpen_ovl c c').mem_nhds hz)
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp z h1

theorem jac_ne_zero {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    jac c c' z ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_linMat_fderiv_chg hz)).ne_zero

theorem injOn_chg (c c' : ComplexChart n X) : InjOn (chg c c') (ovl c c') := by
  intro y hy y' hy' h
  have h' := congrArg c'.val.symm h
  rw [symm_chg hy, symm_chg hy'] at h'
  exact c.val.symm.injOn hy.1 hy'.1 h'

/-- **`log |J|²` is pluriharmonic.** -/
theorem leviForm_log_norm_sq_eq_zero {J : ComplexModel n → ℂ} {z : ComplexModel n}
    (hJ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ J y) (hJz : J z ≠ 0) (v : ComplexModel n) :
    leviForm (fun y => Real.log (‖J y‖ ^ 2)) z v = 0 := by
  have hpos : 0 < SGPT.Foundations.Analysis.generatorNormSq (fun _ : Fin 1 => J) z := by
    simp [SGPT.Foundations.Analysis.generatorNormSq, norm_pos_iff.mpr hJz]
  have h := SGPT.Okounkov.TranscendentalSkoda.leviForm_log_normSq (G := fun _ : Fin 1 => J)
    (fun _ => hJ) hpos v
  simp only [SGPT.Foundations.Analysis.generatorNormSq, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton] at h
  rw [h, norm_mul, Complex.norm_conj, mul_pow]
  ring

/-! ### Integrals over small balls -/

/-- Two continuous functions on an open set with the same integrals over all closed balls in it
agree there. -/
theorem eqOn_of_setIntegral_closedBall_eq {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f g : ComplexModel n → ℝ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ z r, 0 < r → closedBall z r ⊆ U →
      ∫ y in closedBall z r, f y = ∫ y in closedBall z r, g y) : EqOn f g U := by
  have key : ∀ f g : ComplexModel n → ℝ, ContinuousOn f U → ContinuousOn g U →
      (∀ z r, 0 < r → closedBall z r ⊆ U →
        ∫ y in closedBall z r, f y = ∫ y in closedBall z r, g y) →
      ∀ z ∈ U, f z ≤ g z := by
    intro f g hf hg h z hz
    by_contra hlt
    rw [not_le] at hlt
    set d := f z - g z with hd
    have hd0 : 0 < d := by linarith
    have hcont : ContinuousAt (fun y => f y - g y) z := (hf.sub hg).continuousAt (hU.mem_nhds hz)
    have hev : ∀ᶠ y in 𝓝 z, y ∈ U ∧ d / 2 < f y - g y :=
      Filter.Eventually.and (hU.mem_nhds hz : ∀ᶠ y in 𝓝 z, y ∈ U)
        (hcont.eventually (lt_mem_nhds (by linarith)))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set B := closedBall z (r / 2) with hB
    have hBb : B ⊆ ball z r := closedBall_subset_ball (by linarith)
    have hBU : B ⊆ U := fun y hy => (hball y (hBb hy)).1
    have hBc : IsCompact B := isCompact_closedBall _ _
    have hfi : IntegrableOn f B := (hf.mono hBU).integrableOn_compact hBc
    have hgi : IntegrableOn g B := (hg.mono hBU).integrableOn_compact hBc
    have heq := h z (r / 2) (by positivity) hBU
    have hvol : 0 < volume.real B := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos volume z (by positivity)).ne'
        (measure_closedBall_lt_top (x := z) (r := r / 2)).ne
    have hpos : 0 < ∫ y in B, (f y - g y) := by
      calc (0 : ℝ) < ∫ _ in B, d / 2 := by
            rw [setIntegral_const, smul_eq_mul]; positivity
        _ ≤ ∫ y in B, (f y - g y) :=
            setIntegral_mono_on (integrableOn_const (measure_closedBall_lt_top).ne) (hfi.sub hgi)
              measurableSet_closedBall fun y hy => (hball y (hBb hy)).2.le
    rw [integral_sub hfi hgi, heq, sub_self] at hpos
    exact lt_irrefl _ hpos
  intro z hz
  exact le_antisymm (key f g hf hg h z hz) (key g f hg hf (fun z r hr hB => (h z r hr hB).symm) z hz)

/-! ### The transformation law of chart densities -/

variable [MeasurableSpace X] [BorelSpace X]

/-- **Transformation law of chart densities**: `ρ_c = |J|² · ρ_{c'} ∘ (c' ∘ c⁻¹)` on the overlap. -/
theorem chartDensity_chg {μ : Measure X} {c c' : ComplexChart n X} {ρ ρ' : ComplexModel n → ℝ}
    (hρ : IsChartDensity μ c ρ) (hρ' : IsChartDensity μ c' ρ') {z : ComplexModel n}
    (hz : z ∈ ovl c c') : ρ z = ‖jac c c' z‖ ^ 2 * ρ' (chg c c' z) := by
  have hcont1 : ContinuousOn ρ (ovl c c') := hρ.1.continuousOn.mono fun y hy => hy.1
  have hchgc : ContinuousOn (chg c c') (ovl c c') := (differentiableOn_chg c c').continuousOn
  have hcont2 : ContinuousOn (fun y => ‖jac c c' y‖ ^ 2 * ρ' (chg c c' y)) (ovl c c') := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuous_norm.comp_continuousOn fun y hy =>
        (differentiableAt_jac hy).continuousAt.continuousWithinAt).pow 2
    · exact hρ'.1.continuousOn.comp hchgc fun y hy => c'.val.map_source hy.2
  refine eqOn_of_setIntegral_closedBall_eq (isOpen_ovl c c') hcont1 hcont2 (fun y r hr hB => ?_) hz
  set B := closedBall y r
  have hBc : IsCompact B := isCompact_closedBall _ _
  -- the volume
  have h1 := setIntegral_chg hρ hρ' hBc hB (G := fun _ => (1 : ℂ)) continuousOn_const
  simp only [mul_one] at h1
  have h1' : ∫ w in chg c c' '' B, ρ' w = ∫ w in B, ρ w := by exact_mod_cast h1
  -- the change of variables formula
  have h2 := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
    (f := chg c c') (f' := fun w => (fderiv ℂ (chg c c') w).restrictScalars ℝ)
    (fun w hw => ((differentiableAt_chg (hB hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((injOn_chg c c').mono hB) ρ'
  rw [← h1', h2]
  refine setIntegral_congr_fun measurableSet_closedBall fun w _ => ?_
  rw [det_restrictScalars_eq_norm_sq, smul_eq_mul, abs_of_nonneg (by positivity)]
  rfl

/-! ### The Ricci lower bound -/

/-- A chart-smooth function equal to `1` near `x` with support in the open `U ∋ x`. -/
theorem exists_chartSmooth_eq_one [CompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x ∈ U) :
    ∃ χ : X → ℝ, ChartSmooth (n := n) χ ∧ tsupport χ ⊆ U ∧
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, χ y = 1 := by
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  obtain ⟨η, hη, -, hsum, hsupp⟩ := SGPT.Trace.OTExt4.exists_chartSmooth_partition (n := n)
    (fun b : Bool => if b then U else tᶜ)
    (fun b => by cases b <;> simp [hU, htc.isOpen_compl])
    (fun y => by
      by_cases hy : y ∈ t
      · exact ⟨true, by simpa using htU hy⟩
      · exact ⟨false, by simpa using hy⟩)
  refine ⟨η true, hη true, by simpa using hsupp true, interior t, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr ht, interior_subset.trans htU, fun y hy => ?_⟩
  have h0 : η false y = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hsupp false h
    simp only [Bool.false_eq_true, ite_false, mem_compl_iff] at this
    exact this (interior_subset hy)
  have := hsum y
  rw [Fintype.sum_bool] at this
  linarith

open Classical in
/-- `χ · (log ρ ∘ e)` on the chart source of `e`, extended by `0`. -/
def localLogExt (e : ComplexChart n X) (ρ : ComplexModel n → ℝ) (χ : X → ℝ) (x : X) : ℝ :=
  if x ∈ e.val.source then χ x * Real.log (ρ (e.val x)) else 0

omit [MeasurableSpace X] [BorelSpace X] in
theorem chartSmooth_localLogExt {e : ComplexChart n X} {ρ : ComplexModel n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ e.val.target) (hρpos : ∀ z ∈ e.val.target, 0 < ρ z) {χ : X → ℝ}
    (hχ : ChartSmooth (n := n) χ) (hχe : tsupport χ ⊆ e.val.source) :
    ChartSmooth (n := n) (localLogExt e ρ χ) := by
  intro c z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have hχz : ContDiffAt ℝ ∞ (fun y => χ (c.val.symm y)) z :=
    (hχ c).contDiffAt (c.val.open_target.mem_nhds hz)
  by_cases hzs : c.val.symm z ∈ tsupport χ
  · have hzo : z ∈ ovl c e := ⟨hz, hχe hzs⟩
    have hev : (fun y => localLogExt e ρ χ (c.val.symm y)) =ᶠ[𝓝 z]
        fun y => χ (c.val.symm y) * Real.log (ρ (chg c e y)) := by
      filter_upwards [(isOpen_ovl c e).mem_nhds hzo] with y hy
      have hy2 : c.val.symm y ∈ e.val.source := hy.2
      simp [localLogExt, hy2, chg]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine hχz.mul (ContDiffAt.log ?_ (hρpos _ (e.val.map_source hzo.2)).ne')
    · exact (hρ.contDiffAt (e.val.open_target.mem_nhds (e.val.map_source hzo.2))).comp z
        ((contDiffOn_chg c e).contDiffAt ((isOpen_ovl c e).mem_nhds hzo) |>.restrict_scalars ℝ)
  · have hev : (fun y => localLogExt e ρ χ (c.val.symm y)) =ᶠ[𝓝 z] fun _ => 0 := by
      have hopen : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (tsupport χ)ᶜ) :=
        c.val.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl
      filter_upwards [hopen.mem_nhds ⟨hz, hzs⟩] with y hy
      have h0 : χ (c.val.symm y) = 0 := image_eq_zero_of_notMem_tsupport hy.2
      simp only [localLogExt, h0, zero_mul, ite_self]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The Ricci lower bound** (FPT: `c₁(K_X^{-1}, h_{K^{-1},ω}) ≥ -b_K ω`, in charts): for a smooth
positive volume `μ` on a compact Kähler manifold there is `b_K ≥ 0` with
`Levi(log ρ)(v) ≤ b_K ω(v, iv)` for every chart `c`, every density `ρ` of `μ` in `c`, every point
of the chart and every vector. -/
theorem exists_leviForm_log_chartDensity_le [CompactSpace X] (ωb : KahlerBackground n X)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ bK : ℝ, 0 ≤ bK ∧ ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        leviForm (fun y => Real.log (ρ y)) z v ≤ bK * kahlerQuad ωb c z v := by
  have hloc : ∀ x : X, ∃ B : ℝ, 0 < B ∧ ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
        ∀ z ∈ c.val.target, c.val.symm z ∈ V → ∀ v : ComplexModel n,
          leviForm (fun y => Real.log (ρ y)) z v ≤ Real.pi * B * kahlerQuad ωb c z v := by
    intro x
    set e := complexChartAt (n := n) x with he
    obtain ⟨ρe, hρe⟩ := hμ e
    have hρe' : IsChartDensity μ e ρe := hρe
    obtain ⟨χ, hχ, hχe, V₀, hV₀o, hxV₀, hV₀e, hχ1⟩ :=
      exists_chartSmooth_eq_one (n := n) e.val.open_source (mem_complexChartAt_source x)
    set H := localLogExt e ρe χ with hH
    have hHs : ChartSmooth (n := n) H := chartSmooth_localLogExt hρe'.1 hρe'.2.1 hχ hχe
    have hHn : ChartSmooth (n := n) (fun y => -H y) := fun c => (hHs c).neg
    obtain ⟨B, hB, V₁, hV₁o, hxV₁, hdom⟩ := exists_nhds_smoothDDC_domination ωb hHn x
    refine ⟨B, hB, V₀ ∩ V₁, hV₀o.inter hV₁o, ⟨hxV₀, hxV₁⟩, fun c ρ hρ z hz hzV v => ?_⟩
    have hzo : z ∈ ovl c e := ⟨hz, hV₀e hzV.1⟩
    set O := ovl c e ∩ c.val.symm ⁻¹' V₀ with hO
    have hOo : IsOpen O := (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
      (isOpen_ovl c e) hV₀o
    have hzO : z ∈ O := ⟨hzo, hzV.1⟩
    -- the decomposition `log ρ = H ∘ c⁻¹ + log |J|²` near `z`
    have hev : (fun y => Real.log (ρ y)) =ᶠ[𝓝 z]
        (fun y => H (c.val.symm y)) + fun y => Real.log (‖jac c e y‖ ^ 2) := by
      filter_upwards [hOo.mem_nhds hzO] with y hy
      have hyt : chg c e y ∈ e.val.target := e.val.map_source hy.1.2
      rw [Pi.add_apply, chartDensity_chg hρ hρe' hy.1,
        Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr (jac_ne_zero hy.1)))
          (hρe'.2.1 _ hyt).ne']
      simp only [hH, localLogExt, if_pos (hV₀e hy.2), hχ1 _ hy.2, one_mul, chg]
      ring
    have hH2 : ContDiffAt ℝ 2 (fun y => H (c.val.symm y)) z :=
      ((hHs c).contDiffAt (c.val.open_target.mem_nhds hz)).of_le (by norm_cast)
    have hJev : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (jac c e) y := by
      filter_upwards [(isOpen_ovl c e).mem_nhds hzo] with y hy
      exact differentiableAt_jac hy
    have hJ2 : ContDiffAt ℝ 2 (fun y => Real.log (‖jac c e y‖ ^ 2)) z := by
      have hJc : ContDiffAt ℂ 2 (jac c e) z :=
        (contDiffAt_of_differentiableOn_complex (U := ovl c e) (fun y hy =>
          (differentiableAt_jac hy).differentiableWithinAt) (isOpen_ovl c e) hzo).of_le
          (by norm_cast)
      refine ContDiffAt.log ?_ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (jac_ne_zero hzo)))
      exact ((contDiff_norm_sq ℝ).contDiffAt (x := jac c e z)).comp z (hJc.restrict_scalars ℝ)
    rw [leviForm_congr_ev hev v, leviForm_add hH2 hJ2,
      leviForm_log_norm_sq_eq_zero hJev (jac_ne_zero hzo), add_zero]
    -- the domination
    have hd := hdom c z hz hzV.2 v
    rw [smoothDDC_complexDiagonal_eq_leviForm hH2.neg v] at hd
    have hneg : leviForm (fun y => -H (c.val.symm y)) z v = -leviForm (fun y => H (c.val.symm y)) z v :=
      leviForm_neg (fun y => H (c.val.symm y)) z v
    rw [hneg] at hd
    have hpi := Real.pi_pos
    have : leviForm (fun y => H (c.val.symm y)) z v / Real.pi ≤ B * kahlerQuad ωb c z v := by
      rw [neg_div] at hd; linarith
    rw [div_le_iff₀ hpi] at this
    linarith
  choose B hB V hVo hxV hbd using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  set S : ℝ := ∑ x ∈ t, B x with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => (hB x).le
  refine ⟨Real.pi * S, by positivity, fun c ρ hρ z hz v => ?_⟩
  obtain ⟨x, hxt, hzx⟩ : ∃ x ∈ t, c.val.symm z ∈ V x := by
    simpa using ht (mem_univ (c.val.symm z))
  have h := hbd x c ρ hρ z hz hzx v
  have hkq : 0 ≤ kahlerQuad ωb c z v := kahlerQuad_nonneg ωb c hz v
  have hBS : B x ≤ S := Finset.single_le_sum (f := B) (fun y _ => (hB y).le) hxt
  have : Real.pi * B x * kahlerQuad ωb c z v ≤ Real.pi * S * kahlerQuad ωb c z v :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBS Real.pi_pos.le) hkq
  linarith

end SGPT.Trace.OTExt5
