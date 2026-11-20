import SGPT.Foundations.Analysis.Pending.CalabiThirdOrderEstimate
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
import SGPT.Foundations.Analysis.Pending.ManifoldSchauder
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.SemiconcaveHessianBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The uniform `C^{2,r}` bound along the continuity path of Yau's theorem

Let `Y` be a compact connected complex manifold of dimension `N` with a Kähler form `A`, a Hölder
atlas `HA`, `0 < r < 1`, `F` chart-smooth and `S, K ∈ ℝ`.  There is `C` such that every chart-smooth
`φ` with `A_φ = A + ddᶜφ` Kähler,

`A_φ^N = e^{tF + εφ + κ} A^N`  (chart densities; `t, ε ∈ [0, 1]`, `|κ| ≤ K`)

and `|φ| ≤ S` satisfies `‖φ‖_{C^{2,r}(Y)} ≤ C` (`exists_norm_ofChartSmooth_le`).

This is step P3(b) of N5 of Yau's theorem (TN23's plan
the proof of Yau's theorem), statement the statement under discussion (T2), split settled
in C-0063, confirmed by TN23 in C-0065.  Textbook: Székelyhidi, *An Introduction to Extremal Kähler
Metrics*, §3.4 (the `C^{2,α}` estimate from the `C²` and `C³` estimates and Schauder theory).

## Proof

* `C²` (N3, `AubinYauEstimate.exists_le_smul_of_mongeAmpere_eq_exp`) with `G = tF + εφ + κ`:
  `|G| ≤ sup|F| + S + K` and `ddᶜG = t ddᶜF + ε ddᶜφ ≥ -(L_F + 1) A` (`KahlerDomination`), so
  `C₀⁻¹ A ≤ A_φ ≤ C₀ A` with `C₀` independent of `φ`.
* Hence the entries of the complex Hessian `Q = (∂²(φ ∘ e⁻¹)/∂z_j∂z̄_k)` are bounded on every compact
  subset of a chart target (polarization, `norm_complexHessian_entry_le_of_leviForm`).
* `C³` (N4, `CalabiThirdOrderEstimate.exists_norm_fderiv_complexHessian_le`) bounds `‖D Q_{jk}‖` on
  the compact sets `e_i(tsupport χ_i)` of the atlas.
* The Laplacian of `A` applied to `φ` reads `Re tr(H_A⁻¹ Q)` in every chart
  (`KahlerLaplacianChart.laplacian_eq`), so its local representatives `(χ_i Δ_A φ) ∘ e_i⁻¹` have
  uniformly bounded values and derivatives (`chart_bound`), hence are uniformly Lipschitz and
  bounded, hence uniformly bounded in `C^{0,r}_b` (`norm_le_of_lipschitz`): `‖Δ_A φ‖_{C^{0,r}(Y)}`
  is bounded independently of `φ`.
* The global Schauder estimate (`ManifoldSchauder.exists_norm_le`) for the realizable Laplacian
  (`KahlerLaplacianChart.exists_atlas_coeff`, `laplacian_eq_ellipticOp`):
  `‖φ‖_{C^{2,r}} ≤ C_S (‖Δ_A φ‖_{C^{0,r}} + S)`.
-/

noncomputable section

open Set Filter Topology Metric Function Matrix
open scoped NNReal ContDiff Manifold ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.YauHolderBound

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian AubinYauEstimate ManifoldTubePositivity
  KahlerLaplacianChart

/-! ### Euclidean lemmas -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded Lipschitz function in `C^{0,r}_b` has norm at most `L + 3M`. -/
theorem norm_le_of_lipschitz {r : ℝ≥0} (hr : r ≤ 1) (f : BoundedContDiffHolderMap 0 r E ℝ)
    {L M : ℝ} (hL0 : 0 ≤ L) (hM : ∀ x, |f x| ≤ M)
    (hL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) : ‖f‖ ≤ L + 3 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hhol : ∀ x y, ‖f x - f y‖ ≤ (L + 2 * M) * ‖x - y‖ ^ (r : ℝ) :=
    SchauderWholeSpace.norm_sub_le_rpow_of_lipschitz_of_bound hL0 r.2 hr
      (fun x y => by rw [Real.norm_eq_abs]; exact hL x y)
      (fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have hH : HolderWith (Real.toNNReal (L + 2 * M)) r (iteratedFDeriv ℝ 0 ⇑f) := by
    refine HolderWith.of_dist_le fun x y => ?_
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.dist_map,
      dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact hhol x y
  have h1 := f.iteratedFDerivHolder.norm_le_of_holderWith (C := Real.toNNReal (L + 2 * M))
    (by rw [BoundedContDiffHolderMap.coe_iteratedFDerivHolder]; exact hH)
  rw [BoundedContDiffHolderMap.iteratedFDerivHolder_toBoundedContinuousFunction,
    Real.coe_toNNReal _ (by positivity)] at h1
  have h0 : ‖f.iteratedFDerivBCF 0‖ ≤ M :=
    (BoundedContinuousFunction.norm_le hM0).2 fun x => by
      rw [BoundedContDiffHolderMap.coe_iteratedFDerivBCF _ le_rfl, norm_iteratedFDeriv_zero,
        Real.norm_eq_abs]
      exact hM x
  rw [BoundedContDiffHolderMap.norm_def, Finset.range_zero, Finset.sum_empty, zero_add]
  linarith

/-- A function differentiable everywhere with `‖Df‖ ≤ L` is `L`-Lipschitz. -/
theorem abs_sub_le_of_norm_fderiv_le {f : E → ℝ} (hf : Differentiable ℝ f) {L : ℝ}
    (h : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (x y : E) : |f x - f y| ≤ L * ‖x - y‖ := by
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z) (fun z _ => h z)
    (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

end Euclidean

/-! ### The derivative of `σ · Re tr(P Q)` -/

section TraceDerivative

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem re_trace_mul_eq (P Q : Matrix (Fin n) (Fin n) ℂ) :
    (P * Q).trace.re = ∑ j, ∑ k, (P j k * Q k j).re := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum]

theorem hasFDerivAt_re_trace_mul {P Q : E → Matrix (Fin n) (Fin n) ℂ} {z : E}
    {P' Q' : Fin n → Fin n → E →L[ℝ] ℂ} (hP : ∀ j k, HasFDerivAt (fun w => P w j k) (P' j k) z)
    (hQ : ∀ j k, HasFDerivAt (fun w => Q w j k) (Q' j k) z) :
    HasFDerivAt (fun w => (P w * Q w).trace.re)
      (∑ j, ∑ k, Complex.reCLM.comp (P z j k • Q' k j + Q z k j • P' j k)) z := by
  simp_rw [re_trace_mul_eq]
  refine HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ => ?_
  exact Complex.reCLM.hasFDerivAt.comp z ((hP j k).mul (hQ k j))

theorem norm_re_trace_mul_le {P Q : Matrix (Fin n) (Fin n) ℂ} {a b : ℝ}
    (hP : ∀ j k, ‖P j k‖ ≤ a) (hQ : ∀ j k, ‖Q j k‖ ≤ b) :
    |(P * Q).trace.re| ≤ n * (n * (a * b)) := by
  rw [re_trace_mul_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ j, |∑ k, (P j k * Q k j).re| ≤ n * (a * b) := by
    intro j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |(P j k * Q k j).re| ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ =>
          (Complex.abs_re_le_norm _).trans (by
            rw [norm_mul]
            exact mul_le_mul (hP j k) (hQ k j) (norm_nonneg _) ((norm_nonneg _).trans (hP j k)))
      _ = n * (a * b) := by simp
  calc ∑ j, |∑ k, (P j k * Q k j).re| ≤ ∑ _j : Fin n, n * (a * b) := Finset.sum_le_sum fun j _ => h j
    _ = n * (n * (a * b)) := by simp

theorem norm_sum_reCLM_comp_le {P Q : Matrix (Fin n) (Fin n) ℂ}
    {P' Q' : Fin n → Fin n → E →L[ℝ] ℂ} {a a' b b' : ℝ} (hP : ∀ j k, ‖P j k‖ ≤ a)
    (hP' : ∀ j k, ‖P' j k‖ ≤ a') (hQ : ∀ j k, ‖Q j k‖ ≤ b) (hQ' : ∀ j k, ‖Q' j k‖ ≤ b') :
    ‖∑ j, ∑ k, Complex.reCLM.comp (P j k • Q' k j + Q k j • P' j k)‖ ≤
      n * (n * (a * b' + b * a')) := by
  have hterm : ∀ j k, ‖Complex.reCLM.comp (P j k • Q' k j + Q k j • P' j k)‖ ≤ a * b' + b * a' := by
    intro j k
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.reCLM_norm, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have ha := (norm_nonneg _).trans (hP j k)
    have hb := (norm_nonneg _).trans (hQ k j)
    exact add_le_add (mul_le_mul (hP j k) (hQ' k j) (norm_nonneg _) ha)
      (mul_le_mul (hQ k j) (hP' j k) (norm_nonneg _) hb)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖∑ k, Complex.reCLM.comp (P j k • Q' k j + Q k j • P' j k)‖
      ≤ ∑ _j : Fin n, n * (a * b' + b * a') := Finset.sum_le_sum fun j _ => by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k, ‖Complex.reCLM.comp (P j k • Q' k j + Q k j • P' j k)‖
            ≤ ∑ _k : Fin n, (a * b' + b * a') := Finset.sum_le_sum fun k _ => hterm j k
          _ = n * (a * b' + b * a') := by rw [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
    _ = n * (n * (a * b' + b * a')) := by simp

/-- **Pointwise bounds for `σ · Re tr(P Q)`**: if `f` agrees near `z` with
`w ↦ σ w · Re tr(P(w) Q(w))`, with `σ`, the entries of `P` and `Q` differentiable at `z`, then `f`
is differentiable at `z`, with value and derivative bounded through bounds on `σ`, `P`, `Q` and their
derivatives at `z`. -/
theorem bounds_of_eventuallyEq {f σ : E → ℝ} {P Q : E → Matrix (Fin n) (Fin n) ℂ} {z : E}
    (hf : f =ᶠ[𝓝 z] fun w => σ w * (P w * Q w).trace.re) (hσ : DifferentiableAt ℝ σ z)
    (hP : ∀ j k, DifferentiableAt ℝ (fun w => P w j k) z)
    (hQ : ∀ j k, DifferentiableAt ℝ (fun w => Q w j k) z) {c c₃ c₄ : ℝ}
    (hσb : |σ z| ≤ c) (hσd : ‖fderiv ℝ σ z‖ ≤ c) (hPb : ∀ j k, ‖P z j k‖ ≤ c)
    (hPd : ∀ j k, ‖fderiv ℝ (fun w => P w j k) z‖ ≤ c) (hQb : ∀ j k, ‖Q z j k‖ ≤ c₃)
    (hQd : ∀ j k, ‖fderiv ℝ (fun w => Q w j k) z‖ ≤ c₄) :
    DifferentiableAt ℝ f z ∧ |f z| ≤ c * (n * (n * (c * c₃))) ∧
      ‖fderiv ℝ f z‖ ≤ c * (n * (n * (c * c₄ + c₃ * c))) + n * (n * (c * c₃)) * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hσb
  have hT := hasFDerivAt_re_trace_mul (fun j k => (hP j k).hasFDerivAt)
    (fun j k => (hQ j k).hasFDerivAt)
  have hg := hσ.hasFDerivAt.mul hT
  have hfd := hg.congr_of_eventuallyEq hf
  have hval : |(P z * Q z).trace.re| ≤ n * (n * (c * c₃)) := norm_re_trace_mul_le hPb hQb
  refine ⟨hfd.differentiableAt, ?_, ?_⟩
  · rw [hf.self_of_nhds, abs_mul]
    exact mul_le_mul hσb hval (abs_nonneg _) hc
  · rw [hfd.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hD := norm_sum_reCLM_comp_le hPb hPd hQb hQd
    exact add_le_add (mul_le_mul hσb hD (norm_nonneg _) hc)
      (mul_le_mul hval hσd (norm_nonneg _) ((abs_nonneg _).trans hval))

end TraceDerivative

/-! ### Chart-level bounds -/

section Chart

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The local representative of `σ · Re tr(P Q)`**: a function `f` vanishing off a compact `K` and
equal to `σ · Re tr(P Q)` on an open `U ⊇ K` is differentiable everywhere, with value and derivative
bounded through bounds of `σ`, `P`, `Q` and their derivatives on `K`. -/
theorem chart_bound {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f σ : E → ℝ} {P Q : E → Matrix (Fin n) (Fin n) ℂ}
    (hfU : ∀ z ∈ U, f z = σ z * (P z * Q z).trace.re) (hf0 : ∀ z ∉ K, f z = 0) {c c₃ c₄ : ℝ}
    (hc : 0 ≤ c) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄)
    (hσ : ∀ z ∈ K, DifferentiableAt ℝ σ z ∧ |σ z| ≤ c ∧ ‖fderiv ℝ σ z‖ ≤ c)
    (hP : ∀ z ∈ K, ∀ j k, DifferentiableAt ℝ (fun w => P w j k) z ∧ ‖P z j k‖ ≤ c ∧
      ‖fderiv ℝ (fun w => P w j k) z‖ ≤ c)
    (hQ : ∀ z ∈ K, ∀ j k, DifferentiableAt ℝ (fun w => Q w j k) z ∧ ‖Q z j k‖ ≤ c₃ ∧
      ‖fderiv ℝ (fun w => Q w j k) z‖ ≤ c₄) :
    Differentiable ℝ f ∧ (∀ x, |f x| ≤ c * (n * (n * (c * c₃)))) ∧
      ∀ x, ‖fderiv ℝ f x‖ ≤ c * (n * (n * (c * c₄ + c₃ * c))) + n * (n * (c * c₃)) * c := by
  have hM0 : 0 ≤ c * (n * (n * (c * c₃))) := by positivity
  have hL0 : 0 ≤ c * (n * (n * (c * c₄ + c₃ * c))) + n * (n * (c * c₃)) * c := by positivity
  have key : ∀ x, DifferentiableAt ℝ f x ∧ |f x| ≤ c * (n * (n * (c * c₃))) ∧
      ‖fderiv ℝ f x‖ ≤ c * (n * (n * (c * c₄ + c₃ * c))) + n * (n * (c * c₃)) * c := by
    intro x
    by_cases hx : x ∈ K
    · have hf : f =ᶠ[𝓝 x] fun w => σ w * (P w * Q w).trace.re :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hfU
      exact bounds_of_eventuallyEq hf (hσ x hx).1 (fun j k => (hP x hx j k).1)
        (fun j k => (hQ x hx j k).1) (hσ x hx).2.1 (hσ x hx).2.2 (fun j k => (hP x hx j k).2.1)
        (fun j k => (hP x hx j k).2.2) (fun j k => (hQ x hx j k).2.1)
        (fun j k => (hQ x hx j k).2.2)
    · have hf : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun w hw => hf0 w hw
      have hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x := (hasFDerivAt_const 0 x).congr_of_eventuallyEq hf
      refine ⟨hd.differentiableAt, ?_, ?_⟩
      · rw [hf0 x hx, abs_zero]; exact hM0
      · rw [hd.fderiv, norm_zero]; exact hL0
  exact ⟨fun x => (key x).1, fun x => (key x).2.1, fun x => (key x).2.2⟩

/-- A function smooth on an open `U` is differentiable at the points of a compact `K ⊆ U`, with
values and derivatives bounded there. -/
theorem exists_bound_of_contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {g : E → F}
    (hg : ContDiffOn ℝ ∞ g U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ K, DifferentiableAt ℝ g z ∧ ‖g z‖ ≤ c ∧ ‖fderiv ℝ g z‖ ≤ c := by
  obtain ⟨c₁, hc₁⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKU)
  obtain ⟨c₂, hc₂⟩ := hK.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU)
  refine ⟨max (max c₁ c₂) 0, le_max_right _ _, fun z hz => ⟨?_, ?_, ?_⟩⟩
  · exact (hg.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)
  · exact (hc₁ z hz).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hc₂ z hz).trans ((le_max_right _ _).trans (le_max_left _ _))

end Chart

/-! ### Entries of complex Hessians -/

section Entries

variable {n : ℕ}

/-- The entries of `H⁻¹` through the Laplacian coefficient `lapCoeff H = ¼ conj(H⁻¹)`. -/
theorem inv_apply_eq_lapCoeff (H : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    H⁻¹ j k = 4 * starRingEnd ℂ ((lapCoeff H (coordinateVector k)) j) := by
  simp only [lapCoeff, _root_.smul_apply, matCLM_coordinateVector]
  simp [coordinateVector, Pi.single_apply, Finset.sum_apply, map_ofNat]

/-- A continuous real-linear functional reading `H⁻¹ j k` off `lapCoeff H`. -/
def invEntryCLM (j k : Fin n) : (ComplexModel n →L[ℝ] ComplexModel n) →L[ℝ] ℂ :=
  (4 : ℝ) • (Complex.conjCLE.toContinuousLinearMap.comp
    (((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ (ComplexModel n) (coordinateVector k))))

theorem invEntryCLM_lapCoeff (H : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    invEntryCLM j k (lapCoeff H) = H⁻¹ j k := by
  rw [inv_apply_eq_lapCoeff]
  simp [invEntryCLM]

/-- **Polarization**: a pointwise bound `|u_{vv̄}| ≤ c ‖v‖²` of the Levi form bounds every entry of
the complex Hessian by `4c`. -/
theorem norm_complexHessian_entry_le_of_leviForm {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, |leviForm u z v| ≤ c * ‖v‖ ^ 2) (j k : Fin n) :
    ‖complexHessian u z j k‖ ≤ 4 * c := by
  set T := fderiv ℝ (fderiv ℝ u) z with hT
  set J : ComplexModel n →L[ℝ] ComplexModel n :=
    ((Complex.I : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ with hJ
  have hJv : ∀ v, J v = Complex.I • v := fun v => rfl
  set B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ := T + T.bilinearComp J J with hB
  have hBv : ∀ v w, B v w = T v w + T (Complex.I • v) (Complex.I • w) := fun v w => rfl
  have hsymmT : ∀ v w, T v w = T w v := fun v w =>
    (hu.isSymmSndFDerivAt (by simp)) v w
  have hsymm : ∀ v w, B v w = B w v := fun v w => by rw [hBv, hBv, hsymmT v w, hsymmT (_ • v)]
  have hBvv : ∀ v, |B v v| ≤ (4 * c) * ‖v‖ ^ 2 := by
    intro v
    have h1 : B v v = 4 * leviForm u z v := by
      rw [hBv, leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv]
      ring
    rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h v) (by norm_num)
  have hpol := abs_apply_le_of_abs_apply_self_le hsymm (by positivity) hBvv
  have hej : ‖coordinateVector (n := n) j‖ = 1 := by simp [coordinateVector]
  have hek : ‖coordinateVector (n := n) k‖ = 1 := by simp [coordinateVector]
  have hIek : ‖Complex.I • coordinateVector (n := n) k‖ = 1 := by
    rw [norm_smul, Complex.norm_I, one_mul, hek]
  have h1 := hpol (coordinateVector j) (coordinateVector k)
  have h2 := hpol (coordinateVector j) (Complex.I • coordinateVector k)
  rw [hej, hek, mul_one, mul_one] at h1
  rw [hej, hIek, mul_one, mul_one] at h2
  have hentry : complexHessian u z j k =
      ((B (coordinateVector j) (coordinateVector k) : ℝ) : ℂ) / 4 +
        Complex.I * ((B (coordinateVector j) (Complex.I • coordinateVector k) : ℝ) : ℂ) / 4 := by
    rw [hBv, hBv, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    simp only [complexHessian, realHessian_eq_fderiv, hT]
    push_cast
    ring
  rw [hentry]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_ofNat]
  linarith

end Entries

/-! ### On the manifold -/

section Manifold

open AubinYauUniformConstants

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The entries of the inverse coefficient matrix of a Hermitian form are smooth on chart targets. -/
theorem contDiffOn_inv_apply {g : SmoothRealForm N Y 2} (hg : g.IsHermitian) (e : ComplexChart N Y)
    (j k : Fin N) :
    ContDiffOn ℝ ∞ (fun z => (normalizedHermitianMatrix (g.coeff e z))⁻¹ j k) e.val.target := by
  have h := contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun z hz =>
    isUnit_iff_ne_zero.mpr (posDef_coeff hg hz).det_pos.ne'
  exact ((invEntryCLM j k).contDiff.comp_contDiffOn h).congr fun z _ =>
    (invEntryCLM_lapCoeff _ j k).symm

/-- The entries of the complex Hessian of a function smooth on an open set are differentiable there. -/
theorem differentiableAt_complexHessian_apply {ψ : ComplexModel N → ℝ} {U : Set (ComplexModel N)}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) {z : ComplexModel N} (hz : z ∈ U) (j k : Fin N) :
    DifferentiableAt ℝ (fun w => complexHessian ψ w j k) z := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨ψ', hψ', heq⟩ := exists_contDiff_eqOn_ball hU hψ (by positivity : 0 < R / 4)
    (by linarith : R / 4 < R / 2) ((closedBall_subset_ball (by linarith)).trans hball)
  have hloc : (fun w => complexHessian ψ w j k) =ᶠ[𝓝 z] fun w => complexHessian ψ' w j k := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < R / 4))] with w hw
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) heq)]
  exact (WirtingerLogDet.differentiable_complexHessian_apply hψ' j k z).congr_of_eventuallyEq hloc

/-- The Laplacian of `A` read in a chart: `Δ_A φ (e⁻¹ z) = Re tr(H_A(z)⁻¹ (φ ∘ e⁻¹)_{jk̄}(z))`. -/
theorem laplacian_symm_eq {g : SmoothRealForm N Y 2} (hg : g.IsHermitian) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) :
    laplacian g φ (e.val.symm z) = ((normalizedHermitianMatrix (g.coeff e z))⁻¹ *
      complexHessian (fun w => φ (e.val.symm w)) z).trace.re := by
  have hu : ∀ e : ComplexChart N Y, ContDiffOn ℝ 2 (fun w => φ (e.val.symm w)) e.val.target :=
    fun e => (hφ e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [laplacian_eq hg hu (e.val.map_target hz), e.val.right_inv hz]
  rfl

theorem coeff_line_nonneg {g : SmoothRealForm N Y 2} (hg : g.IsHermitian) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    0 ≤ g.coeff e z ![v, Complex.I • v] := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [(g.coeff e z).map_coord_zero (0 : Fin 2) (by simp)]
  · exact ((hg e z hz).2 v hv).le

theorem coeff_line_le (β : CoordinateRealTwoForm N) (v : ComplexModel N) :
    β ![v, Complex.I • v] ≤ ‖β‖ * ‖v‖ ^ 2 := by
  have h := β.le_opNorm ![v, Complex.I • v]
  rw [Fin.prod_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul, Complex.norm_I, one_mul] at h
  calc β ![v, Complex.I • v] ≤ ‖β ![v, Complex.I • v]‖ := Real.le_norm_self _
    _ ≤ ‖β‖ * (‖v‖ * ‖v‖) := h
    _ = ‖β‖ * ‖v‖ ^ 2 := by ring

theorem leviForm_lincomb {f g : ComplexModel N → ℝ} {z : ComplexModel N}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (a b c : ℝ) (v : ComplexModel N) :
    leviForm (fun w => a * f w + b * g w + c) z v = a * leviForm f z v + b * leviForm g z v := by
  have hfun : (fun w => a * f w + b * g w + c) = (a • f + b • g) + fun _ => c := by
    funext w; simp [smul_eq_mul]
  have h1 : ContDiffAt ℝ 2 (a • f) z := hf.const_smul a
  have h2 : ContDiffAt ℝ 2 (b • g) z := hg.const_smul b
  have h12 : ContDiffAt ℝ 2 (a • f + b • g) z := h1.add h2
  rw [hfun, leviForm_add (v := fun _ => c) h12 contDiffAt_const, leviForm_add h1 h2,
    leviForm_smul hf, leviForm_smul hg, leviForm_const, add_zero]

/-- **Entry bound from the `C²` estimate**: if `A + ddᶜφ ≤ C₀ A` on complex lines at `z` and
`A + ddᶜφ` is Kähler, the entries of `(φ ∘ e⁻¹)_{jk̄}(z)` are at most `4π(1 + |C₀|) ‖A_e(z)‖`. -/
theorem norm_complexHessian_entry_le_of_two_sided (A : PositiveClasses.KahlerBackground N Y)
    {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    {C₀ : ℝ} {e : ComplexChart N Y} {z : ComplexModel N} (hz : z ∈ e.val.target)
    (hb : ∀ v : ComplexModel N, (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] ≤
      C₀ * A.form.val.coeff e z ![v, Complex.I • v]) (j k : Fin N) :
    ‖complexHessian (fun w => φ (e.val.symm w)) z j k‖ ≤
      4 * (Real.pi * (1 + |C₀|) * ‖A.form.val.coeff e z‖) := by
  have hψ2 : ContDiffAt ℝ 2 (fun w => φ (e.val.symm w)) z :=
    contDiffAt_two_of_contDiffOn e.val.open_target (hφ e) hz
  refine norm_complexHessian_entry_le_of_leviForm hψ2 (by positivity) (fun v => ?_) j k
  have hsplit : (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] =
      A.form.val.coeff e z ![v, Complex.I • v] + leviForm (fun w => φ (e.val.symm w)) z v /
        Real.pi := by
    rw [← ddc_coeff_line_eq_leviForm hφ hz v, ClosedRealOneOneForm.coeff_add]
    rfl
  have h1 := hb v
  have h2 := coeff_line_nonneg hK.1 hz v
  have h3 := coeff_line_nonneg A.isKahler.1 hz v
  have h4 := coeff_line_le (A.form.val.coeff e z) v
  rw [hsplit] at h1 h2
  have hpi := Real.pi_pos
  set L := leviForm (fun w => φ (e.val.symm w)) z v with hLdef
  set a := A.form.val.coeff e z ![v, Complex.I • v]
  have hL : L = Real.pi * (L / Real.pi) := by field_simp
  have hC : C₀ ≤ |C₀| := le_abs_self C₀
  have ha0 : 0 ≤ ‖A.form.val.coeff e z‖ * ‖v‖ ^ 2 := by positivity
  rw [abs_le]
  constructor
  · -- `L / π ≥ -a ≥ -‖A‖ ‖v‖²`
    have : -(‖A.form.val.coeff e z‖ * ‖v‖ ^ 2) ≤ L / Real.pi := by linarith
    have h5 : -(Real.pi * (1 + |C₀|) * ‖A.form.val.coeff e z‖ * ‖v‖ ^ 2) ≤
        -(Real.pi * ‖A.form.val.coeff e z‖ * ‖v‖ ^ 2) := by
      have : 0 ≤ Real.pi * |C₀| * ‖A.form.val.coeff e z‖ * ‖v‖ ^ 2 := by positivity
      nlinarith
    rw [hL]
    nlinarith
  · -- `L / π ≤ (C₀ - 1) a ≤ |C₀| ‖A‖ ‖v‖²`
    have h6 : L / Real.pi ≤ (C₀ - 1) * a := by linarith
    have h7 : (C₀ - 1) * a ≤ |C₀| * (‖A.form.val.coeff e z‖ * ‖v‖ ^ 2) := by
      have : (C₀ - 1) * a ≤ |C₀| * a := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
    rw [hL]
    have h8 : L / Real.pi ≤ (1 + |C₀|) * (‖A.form.val.coeff e z‖ * ‖v‖ ^ 2) := by nlinarith
    calc Real.pi * (L / Real.pi) ≤ Real.pi * ((1 + |C₀|) * (‖A.form.val.coeff e z‖ * ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h8 hpi.le
      _ = Real.pi * (1 + |C₀|) * ‖A.form.val.coeff e z‖ * ‖v‖ ^ 2 := by ring

end Manifold

/-! ### The uniform `C^{2,r}` bound -/

section Main

open SchauderBlowup SchauderWholeSpace

/-- **The uniform `C^{2,r}` bound along the continuity path** (step P3(b) of N5 of Yau's theorem;
I-0831 C-0062 T2): on a compact connected complex manifold `Y` with a Kähler form `A` and a Hölder
atlas `HA`, for `0 < r < 1`, a chart-smooth `F` and `S, K ∈ ℝ` there is `C` with
`‖φ‖_{C^{2,r}(Y)} ≤ C` for every chart-smooth `φ` with `A + ddᶜφ` Kähler,
`(A + ddᶜφ)^N = e^{tF + εφ + κ} A^N` in every chart (`t, ε ∈ [0, 1]`, `|κ| ≤ K`) and `|φ| ≤ S`. -/
theorem exists_norm_ofChartSmooth_le {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y]
    (A : PositiveClasses.KahlerBackground N Y) (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r)
    (hr1 : r < 1) {F : Y → ℝ} (hF : ChartSmooth (n := N) F) (S K : ℝ) :
    ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 → |κ| ≤ K →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ y, |φ y| ≤ S) →
      ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ‖ ≤ C := by
  classical
  -- constants independent of `φ`
  obtain ⟨LF, hLF0, hLF⟩ := KahlerDomination.exists_isSemipositive_add_smul
    (ddcClosedForm F hF).val A.form.val A.isKahler.1
  obtain ⟨BF, hBF⟩ := isCompact_univ.exists_bound_of_continuousOn
    (YauUniformEstimate.continuous_of_chartSmooth hF).continuousOn
  set S' := max S 0 with hS'
  set K' := max K 0 with hK'
  obtain ⟨C₀, -, hN3⟩ := exists_le_smul_of_mongeAmpere_eq_exp A (2 * S') (BF + S' + K') (LF + 1)
  choose C4 hC4 using fun i => CalabiThirdOrderEstimate.exists_norm_fderiv_complexHessian_le A F hF
    C₀ (HA.chart i) (HA.isCompact_image_tsupport i) (image_tsupport_subset_target HA i)
  choose cσ hcσ0 hcσ using fun i => exists_bound_of_contDiffOn (HA.chart i).val.open_target
    (HA.isCompact_image_tsupport i) (image_tsupport_subset_target HA i)
    (HA.chartSmooth i (HA.chart i))
  choose cP hcP0 hcP using fun i (j k : Fin N) => exists_bound_of_contDiffOn
    (HA.chart i).val.open_target (HA.isCompact_image_tsupport i)
    (image_tsupport_subset_target HA i) (contDiffOn_inv_apply A.isKahler.1 (HA.chart i) j k)
  choose cA hcA0 hcA using fun i => exists_bound_of_contDiffOn (HA.chart i).val.open_target
    (HA.isCompact_image_tsupport i) (image_tsupport_subset_target HA i)
    (A.form.val.smooth (HA.chart i))
  set c : Fin HA.m → ℝ := fun i => cσ i + ∑ j, ∑ k, cP i j k with hc
  set c₃ : Fin HA.m → ℝ := fun i => 4 * (Real.pi * (1 + |C₀|) * cA i) with hc₃
  set c₄ : Fin HA.m → ℝ := fun i => max (C4 i) 0 with hc₄
  set M : Fin HA.m → ℝ := fun i => c i * (N * (N * (c i * c₃ i))) with hM
  set L : Fin HA.m → ℝ := fun i =>
    c i * (N * (N * (c i * c₄ i + c₃ i * c i))) + N * (N * (c i * c₃ i)) * c i with hL
  set G₀ : ℝ := ∑ i, (L i + 3 * M i) with hG₀
  have hc0 : ∀ i, 0 ≤ c i := fun i => add_nonneg (hcσ0 i)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hcP0 i j k)
  have hc₃0 : ∀ i, 0 ≤ c₃ i := fun i => by have := hcA0 i; positivity
  have hc₄0 : ∀ i, 0 ≤ c₄ i := fun i => le_max_right _ _
  have hσc : ∀ i, cσ i ≤ c i := fun i => le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hcP0 i j k)
  have hPc : ∀ i j k, cP i j k ≤ c i := by
    intro i j k
    have h1 : cP i j k ≤ ∑ k', cP i j k' :=
      Finset.single_le_sum (f := fun k' => cP i j k') (fun k' _ => hcP0 i j k') (Finset.mem_univ k)
    have h2 : ∑ k', cP i j k' ≤ ∑ j', ∑ k', cP i j' k' :=
      Finset.single_le_sum (f := fun j' => ∑ k', cP i j' k')
        (fun j' _ => Finset.sum_nonneg fun k' _ => hcP0 i j' k') (Finset.mem_univ j)
    have h3 := hcσ0 i
    simp only [hc]
    linarith
  -- the Schauder estimate for the Laplacian of `A`
  obtain ⟨lam, Λ, a, U, hlam, hΛ, ha, -, hKU, hUt, heq⟩ :=
    exists_atlas_coeff A.isKahler.1 HA (r := r) r.2 hr1.le
  obtain ⟨CS, hCS0, hCS⟩ := ManifoldSchauder.exists_norm_le HA realBasis (Λ := Λ) hlam hr0 hr1
  refine ⟨CS * (G₀ + S'), ?_⟩
  intro φ hφ t ε κ ht hε hκ hK hdens hS
  set u := HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ with hu
  set g := laplacianCLM A.isKahler.1 HA hr0 hr1 u with hg
  have hgφ : ∀ y, g y = laplacian A.form.val φ y := fun y => by
    rw [hg, laplacianCLM_apply]
    rfl
  -- the `C²` estimate for this `φ`
  set G : Y → ℝ := fun y => t * F y + ε * φ y + κ with hGdef
  have hGs : ChartSmooth (n := N) G := fun e =>
    ((contDiffOn_const.mul (hF e)).add (contDiffOn_const.mul (hφ e))).add contDiffOn_const
  have hSφ : ∀ y, |φ y| ≤ S' := fun y => (hS y).trans (le_max_left _ _)
  have hosc : ∀ x y, φ x - φ y ≤ 2 * S' := by
    intro x y
    have h1 := (abs_le.mp (hSφ x)).2
    have h2 := (abs_le.mp (hSφ y)).1
    linarith
  have hGb : ∀ x, |G x| ≤ BF + S' + K' := by
    intro x
    have hFx : |F x| ≤ BF := by have := hBF x (mem_univ x); rwa [Real.norm_eq_abs] at this
    have h1 : |t * F x| ≤ BF := by
      rw [abs_mul, abs_of_nonneg ht.1]
      calc t * |F x| ≤ 1 * |F x| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
        _ ≤ BF := by rw [one_mul]; exact hFx
    have h2 : |ε * φ x| ≤ S' := by
      rw [abs_mul, abs_of_nonneg hε.1]
      calc ε * |φ x| ≤ 1 * |φ x| := mul_le_mul_of_nonneg_right hε.2 (abs_nonneg _)
        _ ≤ S' := by rw [one_mul]; exact hSφ x
    have h3 : |κ| ≤ K' := hκ.trans (le_max_left _ _)
    have h4 : |t * F x + ε * φ x + κ| ≤ |t * F x| + |ε * φ x| + |κ| :=
      (abs_add_le _ _).trans (by linarith [abs_add_le (t * F x) (ε * φ x)])
    change |t * F x + ε * φ x + κ| ≤ BF + S' + K'
    linarith
  have hddc : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
      -(LF + 1) * A.form.val.coeff e z ![v, Complex.I • v] ≤
        (ddcClosedForm G hGs).val.coeff e z ![v, Complex.I • v] := by
    intro e z hz v
    have hF2 := contDiffAt_two_of_contDiffOn e.val.open_target (hF e) hz
    have hφ2 := contDiffAt_two_of_contDiffOn e.val.open_target (hφ e) hz
    have hGl : (ddcClosedForm G hGs).val.coeff e z ![v, Complex.I • v] =
        t * (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] +
          ε * (ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] := by
      have e1 := ddc_coeff_line_eq_leviForm hGs hz v
      have e2 := ddc_coeff_line_eq_leviForm hF hz v
      have e3 := ddc_coeff_line_eq_leviForm hφ hz v
      have e4 : leviForm (fun w => G (e.val.symm w)) z v =
          t * leviForm (fun w => F (e.val.symm w)) z v +
            ε * leviForm (fun w => φ (e.val.symm w)) z v :=
        leviForm_lincomb hF2 hφ2 t ε κ v
      change (ddcClosedForm G hGs).val.coeff e z (RelativeEigenvalueMax.line v) =
        t * (ddcClosedForm F hF).val.coeff e z (RelativeEigenvalueMax.line v) +
          ε * (ddcClosedForm φ hφ).val.coeff e z (RelativeEigenvalueMax.line v)
      rw [e1, e2, e3, e4]
      ring
    have hFl := hLF e z hz v
    have hA := coeff_line_nonneg A.isKahler.1 hz v
    have hAφ := coeff_line_nonneg hK.1 hz v
    have hsplit : (A.form + ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] =
        A.form.val.coeff e z ![v, Complex.I • v] +
          (ddcClosedForm φ hφ).val.coeff e z ![v, Complex.I • v] := by
      rw [ClosedRealOneOneForm.coeff_add]
      rfl
    rw [hsplit] at hAφ
    rw [hGl]
    nlinarith [mul_nonneg ht.1 hFl, mul_nonneg (sub_nonneg.mpr ht.2) (mul_nonneg hLF0.le hA),
      mul_nonneg hε.1 hAφ, mul_nonneg (sub_nonneg.mpr hε.2) hA]
  have hb := hN3 φ hφ G hGs hK hdens hosc hGb hddc
  -- the local representatives of `Δ_A φ`
  have hrepb : ∀ i, ‖g.rep i‖ ≤ L i + 3 * M i := by
    intro i
    have hKc := HA.isCompact_image_tsupport i
    have hKt := image_tsupport_subset_target HA i
    have hfU : ∀ z ∈ (HA.chart i).val.target, (g.rep i) z =
        HA.χ i ((HA.chart i).val.symm z) *
          ((normalizedHermitianMatrix (A.form.val.coeff (HA.chart i) z))⁻¹ *
            complexHessian (fun w => φ ((HA.chart i).val.symm w)) z).trace.re := by
      intro z hz
      rw [HolderAtlas.HolderMap.coe_rep, HolderAtlas.localRep_of_mem _ hz, hgφ,
        laplacian_symm_eq A.isKahler.1 hφ hz, smul_eq_mul]
    have hf0 : ∀ z ∉ (HA.chart i).val '' tsupport (HA.χ i), (g.rep i) z = 0 := fun z hz => by
      rw [HolderAtlas.HolderMap.coe_rep]
      exact HolderAtlas.localRep_eq_zero_of_notMem _ hz
    have hσ : ∀ z ∈ (HA.chart i).val '' tsupport (HA.χ i),
        DifferentiableAt ℝ (fun w => HA.χ i ((HA.chart i).val.symm w)) z ∧
          |HA.χ i ((HA.chart i).val.symm z)| ≤ c i ∧
          ‖fderiv ℝ (fun w => HA.χ i ((HA.chart i).val.symm w)) z‖ ≤ c i := by
      intro z hz
      obtain ⟨h1, h2, h3⟩ := hcσ i z hz
      rw [Real.norm_eq_abs] at h2
      exact ⟨h1, h2.trans (hσc i), h3.trans (hσc i)⟩
    have hP : ∀ z ∈ (HA.chart i).val '' tsupport (HA.χ i), ∀ j k,
        DifferentiableAt ℝ
          (fun w => (normalizedHermitianMatrix (A.form.val.coeff (HA.chart i) w))⁻¹ j k) z ∧
        ‖(normalizedHermitianMatrix (A.form.val.coeff (HA.chart i) z))⁻¹ j k‖ ≤ c i ∧
        ‖fderiv ℝ
          (fun w => (normalizedHermitianMatrix (A.form.val.coeff (HA.chart i) w))⁻¹ j k) z‖ ≤
            c i := by
      intro z hz j k
      obtain ⟨h1, h2, h3⟩ := hcP i j k z hz
      exact ⟨h1, h2.trans (hPc i j k), h3.trans (hPc i j k)⟩
    have hQ : ∀ z ∈ (HA.chart i).val '' tsupport (HA.χ i), ∀ j k,
        DifferentiableAt ℝ
          (fun w => complexHessian (fun w' => φ ((HA.chart i).val.symm w')) w j k) z ∧
        ‖complexHessian (fun w' => φ ((HA.chart i).val.symm w')) z j k‖ ≤ c₃ i ∧
        ‖fderiv ℝ
          (fun w => complexHessian (fun w' => φ ((HA.chart i).val.symm w')) w j k) z‖ ≤
            c₄ i := by
      intro z hz j k
      refine ⟨differentiableAt_complexHessian_apply (HA.chart i).val.open_target
        (hφ (HA.chart i)) (hKt hz) j k, ?_, ?_⟩
      · refine (norm_complexHessian_entry_le_of_two_sided A hφ hK (hKt hz)
          (fun v => (hb (HA.chart i) z (hKt hz) v).1) j k).trans ?_
        have hA := (hcA i z hz).2.1
        have : Real.pi * (1 + |C₀|) * ‖A.form.val.coeff (HA.chart i) z‖ ≤
            Real.pi * (1 + |C₀|) * cA i :=
          mul_le_mul_of_nonneg_left hA (by positivity)
        simp only [hc₃]
        linarith
      · exact (hC4 i φ hφ t ε κ ht hε hK (fun z hz => hdens (HA.chart i) z hz)
          (fun z hz v => hb (HA.chart i) z hz v) z hz j k).trans (le_max_left _ _)
    obtain ⟨hdiff, hval, hder⟩ := chart_bound (HA.chart i).val.open_target hKc hKt hfU hf0
      (hc0 i) (hc₃0 i) (hc₄0 i) hσ hP hQ
    have hL0 : 0 ≤ L i := by
      have := hc0 i; have := hc₃0 i; have := hc₄0 i
      simp only [hL]
      positivity
    exact norm_le_of_lipschitz hr1.le (g.rep i) hL0 hval (abs_sub_le_of_norm_fderiv_le hdiff hder)
  have hgnorm : ‖g‖ ≤ G₀ := by
    rw [HolderAtlas.HolderMap.norm_def]
    exact Finset.sum_le_sum fun i _ => hrepb i
  have hrep : ∀ i, ∀ z ∈ (HA.chart i).val '' tsupport (HA.χ i),
      g ((HA.chart i).val.symm z) = ellipticOp realBasis (a i) ((fun _ _ => 0) i)
        ((fun _ _ => 0) i) (fun w => u ((HA.chart i).val.symm w)) z := by
    intro i z hz
    rw [hg, laplacianCLM_apply]
    exact laplacian_eq_ellipticOp realBasis A.isKahler.1 hr1.le u i (hUt i) (heq i) (hKU i hz)
  have hmain := hCS a (fun _ _ => 0) (fun _ _ => 0) ha (fun _ => isLowerCoeff_zero hΛ) u g S'
    (le_max_right _ _) hSφ hrep
  calc ‖u‖ ≤ CS * (‖g‖ + S') := hmain
    _ ≤ CS * (G₀ + S') := mul_le_mul_of_nonneg_left (by linarith) hCS0

end Main

end SGPT.Foundations.Analysis.Pending.YauHolderBound
