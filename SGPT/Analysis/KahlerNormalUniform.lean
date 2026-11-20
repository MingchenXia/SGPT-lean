import SGPT.Analysis.KahlerNormalCoordinates

/-!
# Kähler normal coordinates: uniform bounds

Lane TOS-C11 (`claude-tos-c11`, node `tos-c11:normal-coordinates-uniform`).  Source: Xia,
*Foundations of pluripotential theory*, `lem:kahler-normal-coordinates-uniform`, second part:
for a compact subset `K` of the domain and every order `q`, the derivatives of order `q` at `0` of
the coefficients of the form in normal coordinates centred at `z₀` are bounded independently of
`z₀ ∈ K`.

* `exists_pos_le_apply_I_smul` — uniform positivity `a(z)(u, iu) ≥ m ‖u‖²` on `K`.
* `kahlerNormal_bound` — `‖A‖ ≤ C` and `‖c‖ ≤ C` for every `z₀ ∈ K`, every `ℂ`-linear `A` with
  `A^*a(z₀) = ω₀` and the quadratic coefficient `c` attached to it.
* `contDiffAt_iteratedFDeriv_param` — the iterated derivatives in `w` of a jointly smooth function
  of `(x, w)` are jointly smooth (parametric smoothness of iterated derivatives).
* `kahlerNormal_uniform_deriv` — for fixed vectors `u, v` and every `q`, the `q`-th derivative at
  `0` of `w ↦ (Φ^*a)(w)(u, v)` is bounded independently of `z₀ ∈ K` and of the normalizing `A`
  (in particular of a unitary change of the normalization).  The coefficient matrix of `Φ^*a` has
  the entries `π((Φ^*a)(eⱼ, i eₖ) - i (Φ^*a)(eⱼ, eₖ))`, so its derivatives are bounded too.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.Analysis.KahlerNormal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Uniform positivity and bounds for `A` and `c` -/

theorem twoForm_norm_apply_le (α : CoordinateRealTwoForm n) (x y : ComplexModel n) :
    |α ![x, y]| ≤ ‖α‖ * ‖x‖ * ‖y‖ := by
  have h := α.le_opNorm ![x, y]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← Real.norm_eq_abs]
  calc ‖α ![x, y]‖ ≤ ‖α‖ * (‖x‖ * ‖y‖) := h
    _ = ‖α‖ * ‖x‖ * ‖y‖ := by ring

theorem twoForm_apply_I_smul_smul (α : CoordinateRealTwoForm n) (r : ℝ) (u : ComplexModel n) :
    α ![r • u, Complex.I • (r • u)] = r ^ 2 * α ![u, Complex.I • u] := by
  rw [smul_comm Complex.I r u, twoForm_smul_left, twoForm_smul_right]
  ring

/-- **Uniform positivity** on a compact set: `a(z)(u, iu) ≥ m ‖u‖²` for `z ∈ K`. -/
theorem exists_pos_le_apply_I_smul {U : Set (ComplexModel n)}
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContinuousOn a U)
    (hpos : ∀ z ∈ U, IsStrictlyPositive (a z)) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K, ∀ u, m * ‖u‖ ^ 2 ≤ a z ![u, Complex.I • u] := by
  set S : Set (ComplexModel n × ComplexModel n) := K ×ˢ sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  set g : ComplexModel n × ComplexModel n → ℝ := fun p => a p.1 ![p.2, Complex.I • p.2]
  have hg : ContinuousOn g S := by
    have h1 : ContinuousOn (fun p : ComplexModel n × ComplexModel n => a p.1) S :=
      ha.comp continuousOn_fst fun p hp => hKU hp.1
    have h2 : Continuous (fun p : ComplexModel n × ComplexModel n =>
        (![p.2, Complex.I • p.2] : Fin 2 → ComplexModel n)) := by
      refine continuous_pi fun i => ?_
      fin_cases i
      · simpa using (continuous_snd : Continuous fun p : ComplexModel n × ComplexModel n => p.2)
      · have : Continuous fun p : ComplexModel n × ComplexModel n => Complex.I • p.2 :=
          continuous_snd.const_smul Complex.I
        simpa using this
    have hev : Continuous fun p : CoordinateRealTwoForm n × (Fin 2 → ComplexModel n) => p.1 p.2 :=
      continuous_eval
    exact hev.comp_continuousOn (h1.prodMk h2.continuousOn)
  have key : ∀ m : ℝ, (∀ p ∈ S, m ≤ g p) → ∀ z ∈ K, ∀ u, m * ‖u‖ ^ 2 ≤ a z ![u, Complex.I • u] := by
    intro m hm z hz u
    by_cases hu : u = 0
    · subst u
      rw [smul_zero, (a z).map_coord_zero (0 : Fin 2) (by simp)]
      simp
    · have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hmem : (z, ‖u‖⁻¹ • u) ∈ S := ⟨hz, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu'.ne']⟩
      have h := hm _ hmem
      have heq : u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hu'.ne', one_smul]
      calc m * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 * g (z, ‖u‖⁻¹ • u) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left h (by positivity)
        _ = a z ![u, Complex.I • u] := by
            conv_rhs => rw [heq]
            rw [twoForm_apply_I_smul_smul]
  by_cases hne : S.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne hg
    have hp₀ne : p₀.2 ≠ 0 := by
      intro h
      have := hp₀.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    exact ⟨g p₀, hpos _ (hKU hp₀.1) _ hp₀ne, key _ fun p hp => hmin hp⟩
  · refine ⟨1, one_pos, key 1 fun p hp => (hne ⟨p, hp⟩).elim⟩

/-- **Uniform bounds for `A` and `c`.**  On a compact `K ⊆ U` there is `C` such that for every
`z₀ ∈ K`, every `ℂ`-linear `A` with `a(z₀)(A ·, A ·) = ω₀` and the attached quadratic coefficient
`c` (`⟪v, c(p, u)⟫ = π ∂_p H(u, v)`), `‖A‖ ≤ C`, `‖c(p, u)‖ ≤ C ‖p‖ ‖u‖` and `‖c‖ ≤ C`. -/
theorem kahlerNormal_bound {U : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ 1 a U)
    (hpos : ∀ z ∈ U, IsStrictlyPositive (a z)) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z₀ ∈ K, ∀ A : ComplexModel n →L[ℂ] ComplexModel n,
      (∀ x y, a z₀ ![A x, A y] = flatForm n ![x, y]) →
      ‖A‖ ≤ C ∧ ∀ c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n,
        (∀ p x y, inner ℂ y (c p x) = (Real.pi : ℂ) * dHol (normalizedDeriv a z₀ A) p x y) →
        (∀ p x, ‖c p x‖ ≤ C * ‖p‖ * ‖x‖) ∧ ‖c‖ ≤ C := by
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul ha.continuousOn hpos hK hKU
  have hfc : ContinuousOn (fderiv ℝ a) U := ha.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (f := fun z => fderiv ℝ a z) (hfc.mono hKU)
  set CA : ℝ := (Real.pi * m)⁻¹.sqrt
  have hCA : 0 ≤ CA := Real.sqrt_nonneg _
  set Cc : ℝ := 2 * Real.pi * (max D 0) * CA ^ 3
  have hCc : 0 ≤ Cc := by positivity
  refine ⟨max CA Cc, le_max_of_le_left hCA, fun z₀ hz₀ A hA => ?_⟩
  -- the bound for `A`
  have hAx : ∀ x, ‖A x‖ ≤ CA * ‖x‖ := by
    intro x
    have h1 := hmK z₀ hz₀ (A x)
    rw [← map_smul, hA, flatForm_apply_I_smul_self] at h1
    have h2 : ‖A x‖ ^ 2 ≤ (Real.pi * m)⁻¹ * ‖x‖ ^ 2 := by
      rw [mul_inv, mul_comm Real.pi⁻¹, mul_assoc]
      rw [le_inv_mul_iff₀ hm]
      exact h1
    calc ‖A x‖ = Real.sqrt (‖A x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.pi * m)⁻¹ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = CA * ‖x‖ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hAn : ‖A‖ ≤ CA := A.opNorm_le_bound hCA hAx
  refine ⟨hAn.trans (le_max_left _ _), fun c hc => ?_⟩
  -- the bound for `β`
  set β := normalizedDeriv a z₀ A
  have hDz : ‖fderiv ℝ a z₀‖ ≤ max D 0 := (hD z₀ hz₀).trans (le_max_left _ _)
  have hβ : ∀ q x y, |β q ![x, y]| ≤ max D 0 * CA ^ 3 * ‖q‖ * ‖x‖ * ‖y‖ := by
    intro q x y
    rw [normalizedDeriv_apply]
    calc |fderiv ℝ a z₀ (A q) ![A x, A y]| ≤ ‖fderiv ℝ a z₀ (A q)‖ * ‖A x‖ * ‖A y‖ :=
          twoForm_norm_apply_le _ _ _
      _ ≤ (max D 0 * (CA * ‖q‖)) * (CA * ‖x‖) * (CA * ‖y‖) := by
          gcongr
          · exact ((fderiv ℝ a z₀).le_opNorm _).trans (mul_le_mul hDz (hAx q) (norm_nonneg _)
              (le_max_right _ _))
          · exact hAx x
          · exact hAx y
      _ = max D 0 * CA ^ 3 * ‖q‖ * ‖x‖ * ‖y‖ := by ring
  have hdHol : ∀ p x y, ‖dHol β p x y‖ ≤ 2 * (max D 0 * CA ^ 3) * ‖p‖ * ‖x‖ * ‖y‖ := by
    intro p x y
    have hIx : ‖Complex.I • y‖ = ‖y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have hIp : ‖Complex.I • p‖ = ‖p‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have e1 := hβ p x (Complex.I • y)
    have e2 := hβ (Complex.I • p) x y
    have e3 := hβ p x y
    have e4 := hβ (Complex.I • p) x (Complex.I • y)
    rw [hIx] at e1 e4
    rw [hIp] at e2 e4
    have hre : |(dHol β p x y).re| ≤ max D 0 * CA ^ 3 * ‖p‖ * ‖x‖ * ‖y‖ := by
      rw [dHol_re, abs_div, abs_two]
      have := abs_sub (β p ![x, Complex.I • y]) (β (Complex.I • p) ![x, y])
      linarith
    have him : |(dHol β p x y).im| ≤ max D 0 * CA ^ 3 * ‖p‖ * ‖x‖ * ‖y‖ := by
      rw [dHol_im, abs_div, abs_neg, abs_two]
      have := abs_add_le (β p ![x, y]) (β (Complex.I • p) ![x, Complex.I • y])
      linarith
    calc ‖dHol β p x y‖ ≤ |(dHol β p x y).re| + |(dHol β p x y).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by linarith
  have hcpx : ∀ p x, ‖c p x‖ ≤ Cc * ‖p‖ * ‖x‖ := by
    intro p x
    have h1 : ‖c p x‖ ^ 2 ≤ Real.pi * (2 * (max D 0 * CA ^ 3) * ‖p‖ * ‖x‖ * ‖c p x‖) := by
      have hi := hc p x (c p x)
      have : ‖c p x‖ ^ 2 = ‖inner ℂ (c p x) (c p x)‖ := by
        rw [inner_self_eq_norm_sq_to_K]
        simp
      rw [this, hi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_left (hdHol p x (c p x)) Real.pi_pos.le
    by_cases h0 : ‖c p x‖ = 0
    · rw [h0]; positivity
    · have hpos' : 0 < ‖c p x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have : ‖c p x‖ * ‖c p x‖ ≤ (Cc * ‖p‖ * ‖x‖) * ‖c p x‖ := by
        rw [← sq]; calc ‖c p x‖ ^ 2 ≤ _ := h1
          _ = (Cc * ‖p‖ * ‖x‖) * ‖c p x‖ := by ring
      exact le_of_mul_le_mul_right this hpos'
  refine ⟨fun p x => (hcpx p x).trans ?_, ?_⟩
  · gcongr
    exact le_max_right _ _
  · refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left hCA) fun p => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    exact (hcpx p x).trans (by gcongr; exact le_max_right _ _)

/-! ### Parametric smoothness of iterated derivatives -/

/-- If `G` is smooth on an open set `O ⊆ P × E`, then `(x, w) ↦ D_w^q G(x, w)` is smooth on `O`. -/
theorem contDiffAt_iteratedFDeriv_param {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : P × E → F} {O : Set (P × E)} (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O) (q : ℕ) :
    ∀ y ∈ O, ContDiffAt ℝ ∞ (fun y : P × E => iteratedFDeriv ℝ q (fun w => G (y.1, w)) y.2) y := by
  induction q with
  | zero =>
    intro y hy
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Prod.mk.eta]
    exact (hG.contDiffAt (hO.mem_nhds hy)).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E F).symm : F →L[ℝ] E [×0]→L[ℝ] F)
  | succ q ih =>
    intro y hy
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hmap : ContDiff ℝ ∞ (fun p : (P × E) × E => (p.1.1, p.2)) := by fun_prop
    have h1 : ContDiffAt ℝ ∞ (fun y : P × E => iteratedFDeriv ℝ q (fun w => G (y.1, w)) y.2)
        (y.1, y.2) := ih (y.1, y.2) hy
    have hf0 : ContDiffAt ℝ ∞ ((fun y : P × E => iteratedFDeriv ℝ q (fun w => G (y.1, w)) y.2) ∘
        fun p : (P × E) × E => (p.1.1, p.2)) (y, y.2) := h1.comp (y, y.2) hmap.contDiffAt
    have hf : ContDiffAt ℝ ∞ (Function.uncurry fun (y : P × E) (w : E) =>
        iteratedFDeriv ℝ q (fun w => G (y.1, w)) w) (y, y.2) := hf0
    have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)
    have hfd := hf.fderiv contDiffAt_snd hinf
    exact hfd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) => E) F).symm :
        _ →L[ℝ] E [×(q + 1)]→L[ℝ] F)

/-! ### The coefficients in normal coordinates as a smooth function of the data -/

/-- Real data of normal coordinates: centre `z₀`, linear part `A`, quadratic part `c`. -/
abbrev NormalData (n : ℕ) := ComplexModel n × (ComplexModel n →L[ℝ] ComplexModel n) ×
  (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n)

/-- `z₀ + A (w - ½ c(w, w))` for real data. -/
def normalPoint (x : NormalData n) (w : ComplexModel n) : ComplexModel n :=
  x.1 + x.2.1 (w - (1 / 2 : ℝ) • x.2.2 w w)

/-- The coefficient `a(Φ w)(DΦ(w) u, DΦ(w) v)` as a function of the data and of `w`. -/
def normalCoeffFun (a : ComplexModel n → CoordinateRealTwoForm n) (u v : ComplexModel n)
    (y : NormalData n × ComplexModel n) : ℝ :=
  a (normalPoint y.1 y.2) ![y.1.2.1 (u - y.1.2.2 y.2 u), y.1.2.1 (v - y.1.2.2 y.2 v)]

/-- Evaluation of a two-form through two curryings. -/
theorem twoForm_apply_eq_curry (α : CoordinateRealTwoForm n) (x y : ComplexModel n) :
    α ![x, y] = (α.curryLeft x).curryLeft y ![] := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.curryLeft_apply_apply]

theorem contDiff_normalPoint :
    ContDiff ℝ ∞ (fun y : NormalData n × ComplexModel n => normalPoint y.1 y.2) := by
  unfold normalPoint; fun_prop

theorem contDiffOn_normalCoeffFun {U : Set (ComplexModel n)}
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U) (u v : ComplexModel n) :
    ContDiffOn ℝ ∞ (normalCoeffFun a u v) {y | normalPoint y.1 y.2 ∈ U} := by
  have hX : ContDiff ℝ ∞ (fun y : NormalData n × ComplexModel n => y.1.2.1 (u - y.1.2.2 y.2 u)) := by
    fun_prop
  have hY : ContDiff ℝ ∞ (fun y : NormalData n × ComplexModel n => y.1.2.1 (v - y.1.2.2 y.2 v)) := by
    fun_prop
  have h0 : ContDiffOn ℝ ∞ (fun y : NormalData n × ComplexModel n => a (normalPoint y.1 y.2))
      {y | normalPoint y.1 y.2 ∈ U} := ha.comp contDiff_normalPoint.contDiffOn fun y hy => hy
  have h1 := ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ)
    (n := 1)).toContinuousLinearMap.contDiff.comp_contDiffOn h0).clm_apply hX.contDiffOn
  have h2 := ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ)
    (n := 0)).toContinuousLinearMap.contDiff.comp_contDiffOn h1).clm_apply hY.contDiffOn
  have h3 := (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ
    (![] : Fin 0 → ComplexModel n)).contDiff.comp_contDiffOn h2
  refine h3.congr fun y _ => ?_
  exact twoForm_apply_eq_curry _ _ _

set_option maxHeartbeats 1600000 in
/-- **Uniform bounds for the derivatives in normal coordinates** (FPT
`lem:kahler-normal-coordinates-uniform`, second part).  Let `a` be a smooth field of strictly
positive closed real `(1,1)`-forms on an open `U ⊆ ℂⁿ`, `K ⊆ U` compact, `q ∈ ℕ` and `u, v` fixed
vectors.  There is `C` such that for every `z₀ ∈ K`, every `ℂ`-linear `A` with
`a(z₀)(A ·, A ·) = ω₀` and the attached quadratic coefficient `c`, the `q`-th derivative at `0` of
`w ↦ (Φ^*a)(w)(u, v)`, `Φ = normalCoord z₀ A c`, has norm at most `C`. -/
theorem kahlerNormal_uniform_deriv {U : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (a z))
    (hcl : ∀ z ∈ U, extDeriv a z = 0) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) (q : ℕ) (u v : ComplexModel n) :
    ∃ C : ℝ, ∀ z₀ ∈ K, ∀ A : ComplexModel n →L[ℂ] ComplexModel n,
      (∀ x y, a z₀ ![A x, A y] = flatForm n ![x, y]) →
      ∀ c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n,
        (∀ p x y, inner ℂ y (c p x) = (Real.pi : ℂ) * dHol (normalizedDeriv a z₀ A) p x y) →
        ‖iteratedFDeriv ℝ q (fun w => pullbackField (normalCoord z₀ A c) a w ![u, v]) 0‖ ≤ C := by
  obtain ⟨C0, hC0, hb⟩ := kahlerNormal_bound hU (ha.of_le (by simp)) hpos hK hKU
  have hO : IsOpen {y : NormalData n × ComplexModel n | normalPoint y.1 y.2 ∈ U} :=
    hU.preimage contDiff_normalPoint.continuous
  have hH := contDiffAt_iteratedFDeriv_param hO (contDiffOn_normalCoeffFun ha u v) q
  have : FiniteDimensional ℝ (ComplexModel n →L[ℝ] ComplexModel n) := inferInstance
  have : FiniteDimensional ℝ (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) :=
    inferInstance
  have : ProperSpace (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) :=
    FiniteDimensional.proper_real (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n)
  have hKp : IsCompact (K ×ˢ ((closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n) C0) ×ˢ
      (closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) C0))) :=
    hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hcont : ContinuousOn (fun x : NormalData n =>
      iteratedFDeriv ℝ q (fun w => normalCoeffFun a u v (x, w)) 0)
      (K ×ˢ ((closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n) C0) ×ˢ
      (closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) C0))) := by
    intro x hx
    have hxO : normalPoint (x, (0 : ComplexModel n)).1 (x, (0 : ComplexModel n)).2 ∈ U := by
      simpa [normalPoint] using hKU hx.1
    have hc1 : ContinuousAt (fun x : NormalData n => (x, (0 : ComplexModel n))) x :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hcomp : ContinuousAt ((fun y : NormalData n × ComplexModel n =>
        iteratedFDeriv ℝ q (fun w => normalCoeffFun a u v (y.1, w)) y.2) ∘
        fun x : NormalData n => (x, (0 : ComplexModel n))) x :=
      ContinuousAt.comp (hH _ hxO).continuousAt hc1
    exact hcomp.continuousWithinAt
  obtain ⟨C, hC⟩ := hKp.exists_bound_of_continuousOn (f := fun x : NormalData n =>
      iteratedFDeriv ℝ q (fun w => normalCoeffFun a u v (x, w)) 0) hcont
  refine ⟨C, fun z₀ hz₀ A hA c hc => ?_⟩
  have hz₀U := hKU hz₀
  have ha0 : DifferentiableAt ℝ a z₀ :=
    (ha.contDiffAt (hU.mem_nhds hz₀U)).differentiableAt (by simp)
  have h11ev : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z) :=
    Filter.mem_of_superset (hU.mem_nhds hz₀U) fun z hz => h11 z hz
  have hsymm := (kahlerNormal_of_normalizing z₀ A c ha0 h11ev (hcl z₀ hz₀U) hA hc).1
  obtain ⟨hAn, hcb⟩ := hb z₀ hz₀ A hA
  obtain ⟨hcpx, -⟩ := hcb c hc
  obtain ⟨cR, hcR⟩ : ∃ cR : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n,
      ∀ p x, cR p x = c p x :=
    ⟨ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel n) (ComplexModel n) ℝ ℝ ∘L
      c.restrictScalars ℝ, fun p x => rfl⟩
  have hx : ((z₀, A.restrictScalars ℝ, cR) : NormalData n) ∈
      K ×ˢ ((closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n) C0) ×ˢ
      (closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) C0)) := by
    have h1 : ‖A.restrictScalars ℝ‖ ≤ C0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun y => ?_
      exact (A.le_opNorm y).trans (by gcongr)
    have h2 : ‖cR‖ ≤ C0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun p => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      rw [hcR]
      exact hcpx p y
    refine ⟨hz₀, ?_, ?_⟩
    · rw [mem_closedBall]
      exact (dist_zero_right _).le.trans h1
    · rw [mem_closedBall]
      exact (dist_zero_right cR).le.trans h2
  have hfun : (fun w => pullbackField (normalCoord z₀ A c) a w ![u, v]) =
      fun w => normalCoeffFun a u v ((z₀, A.restrictScalars ℝ, cR), w) := by
    funext w
    have hhalf : ((1 / 2 : ℂ)) • c w w = (1 / 2 : ℝ) • c w w := by
      rw [← Complex.coe_smul]; norm_num
    rw [pullbackField, fderiv_normalCoord z₀ A c hsymm, compContinuousLinearMap_apply_two]
    simp only [normalCoeffFun, normalPoint, normalCoord, hcR, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, _root_.sub_apply, ContinuousLinearMap.id_apply, hhalf]
  rw [hfun]
  exact hC _ hx

/-! ### Kähler forms of the library -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Kähler normal coordinates for a Kähler form of the library**, in a chart `e` of the atlas, at
a point `z₀` of the chart target (FPT `lem:kahler-normal-coordinates-uniform`, applied to the
coefficients `h` of `κ` in a chart). -/
theorem exists_kahlerNormalCoordinates_of_isKahler {κ : SmoothRealForm n M 2} (hκ : κ.IsKahler)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ (A : ComplexModel n ≃L[ℂ] ComplexModel n)
      (c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n)
      (Ψ : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n)),
      (∀ p u, c p u = c u p) ∧
      ⇑Ψ = normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c ∧ 0 ∈ Ψ.source ∧
      Ψ 0 = z₀ ∧ (∀ w ∈ Ψ.source, DifferentiableAt ℂ Ψ w) ∧
      (∀ z ∈ Ψ.target, DifferentiableAt ℂ Ψ.symm z) ∧
      pullbackField (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c) (κ.coeff e) 0 =
        flatForm n ∧
      normalizedHermitianMatrix (pullbackField
        (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c) (κ.coeff e) 0) = 1 ∧
      HasFDerivAt (pullbackField (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c)
        (κ.coeff e)) (0 : ComplexModel n →L[ℝ] CoordinateRealTwoForm n) 0 :=
  exists_kahlerNormalCoordinates e.val.open_target
    ((κ.smooth e).differentiableOn (by simp)) (fun z hz => (hκ.1 e z hz).1)
    (fun z hz => (hκ.1 e z hz).2) (fun z hz => hκ.2 e z hz) hz₀

/-- **Uniform bounds** for a Kähler form of the library on a compact subset `K` of a chart target:
`‖A‖, ‖c‖ ≤ C` and, for fixed `u, v` and every order `q`, the `q`-th derivative at `0` of the
coefficient `w ↦ (Φ^*κ)(w)(u, v)` is bounded independently of the centre `z₀ ∈ K` and of the
normalizing `A`. -/
theorem kahlerNormal_uniform_of_isKahler {κ : SmoothRealForm n M 2} (hκ : κ.IsKahler)
    (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ e.val.target) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z₀ ∈ K, ∀ A : ComplexModel n →L[ℂ] ComplexModel n,
      (∀ x y, κ.coeff e z₀ ![A x, A y] = flatForm n ![x, y]) →
      ‖A‖ ≤ C ∧ ∀ c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n,
        (∀ p x y, inner ℂ y (c p x) =
          (Real.pi : ℂ) * dHol (normalizedDeriv (κ.coeff e) z₀ A) p x y) →
        (∀ p x, ‖c p x‖ ≤ C * ‖p‖ * ‖x‖) ∧ ‖c‖ ≤ C) ∧
    ∀ (q : ℕ) (u v : ComplexModel n), ∃ C : ℝ, ∀ z₀ ∈ K,
      ∀ A : ComplexModel n →L[ℂ] ComplexModel n,
      (∀ x y, κ.coeff e z₀ ![A x, A y] = flatForm n ![x, y]) →
      ∀ c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n,
        (∀ p x y, inner ℂ y (c p x) =
          (Real.pi : ℂ) * dHol (normalizedDeriv (κ.coeff e) z₀ A) p x y) →
        ‖iteratedFDeriv ℝ q (fun w => pullbackField (normalCoord z₀ A c) (κ.coeff e) w ![u, v])
          0‖ ≤ C :=
  ⟨kahlerNormal_bound e.val.open_target ((κ.smooth e).of_le (by simp))
      (fun z hz => (hκ.1 e z hz).2) hK hKU,
    fun q u v => kahlerNormal_uniform_deriv e.val.open_target (κ.smooth e)
      (fun z hz => (hκ.1 e z hz).1) (fun z hz => (hκ.1 e z hz).2) (fun z hz => hκ.2 e z hz)
      hK hKU q u v⟩

end Manifold

end SGPT.Analysis.KahlerNormal
