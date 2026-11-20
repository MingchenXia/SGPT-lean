import SGPT.Foundations.Analysis.Pending.WholeSpaceMaxPrinciple

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The parameter-dependent Schauder estimate for `L - μ` on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, `0 < α < 1`,
and `L u = a : D²u + Du(β) + c u` (`SchauderWholeSpace.ellipticOp`) with `a ∈ IsEllipticCoeff a λ Λ α`,
`(β, c) ∈ IsLowerCoeff β c Λ α` and `c ≤ 0`.  For `μ ≥ 1` put `f = L u - μ u` and
`N = [f]_α + μ^{α/2} |f|_0`.  Then, with `C` independent of `μ` and of the operator
(`exists_weighted_estimate`):

`[D²u]_α ≤ C N`,  `|D²u|_0 ≤ C μ^{-α/2} N`,  `|Du|_0 ≤ C μ^{-(1+α)/2} N`,  `μ |u|_0 ≤ |f|_0`.

Proof: the last bound is the maximum principle (`WholeSpaceMaxPrinciple`).  For the others rescale
by `σ = μ^{-1/2}`: `u'(y) = u(σ y)` solves `L' u' - u' = μ⁻¹ f(σ ·)` for the operator `L'` with
coefficients `a(σ ·)`, `σ β(σ ·)`, `μ⁻¹ c(σ ·)`, which lies in the class with constants
`(λ, Λ + 1, α)` for every `μ ≥ 1` (the Hölder constants only decrease); apply the `C⁰` Schauder
estimate (`SchauderWholeSpace.exists_schauder_estimate`) to `u'` and scale back.

With the interpolation `[g]_α ≤ (2|g|_0)^{1-α} |Dg|_0^α` (`norm_sub_le_rpow_of_min`) this makes
`‖Du‖_{C^α} + ‖u‖_{C^α} ≤ C μ^{-(1-α)/2} ‖f‖_{C^α}` small for large `μ`: the smallness of the
first-order remainder of the parametrix for `L - μ` on a compact manifold (design note
the linear elliptic estimates, L2.9; blueprint
`bou:kahler-laplacian-solvability`).
-/

noncomputable section

open Set Filter Topology Metric
open scoped RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.SchauderWeighted

open EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple

/-! ### Interpolation of a Hölder seminorm between two sup bounds -/

section Generic

variable {X : Type*} [NormedAddCommGroup X] {Y : Type*} [NormedAddCommGroup Y]

/-- `min (2K) (L t) ≤ (2K)^{1-α} L^α t^α`: a bounded Lipschitz map satisfies
`‖g x - g y‖ ≤ (2K)^{1-α} L^α ‖x - y‖^α`. -/
theorem norm_sub_le_rpow_of_min {g : X → Y} {L K α : ℝ} (hL0 : 0 ≤ L) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (hK : ∀ x, ‖g x‖ ≤ K) (x y : X) :
    ‖g x - g y‖ ≤ (2 * K) ^ (1 - α) * L ^ α * ‖x - y‖ ^ α := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  set t := ‖x - y‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have h1 : ‖g x - g y‖ ≤ 2 * K := (norm_sub_le _ _).trans (by linarith [hK x, hK y])
  have h2 : ‖g x - g y‖ ≤ L * t := hL x y
  -- `m ≤ A` and `m ≤ B` give `m ≤ A^{1-α} B^α`
  set m := ‖g x - g y‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have key : m ≤ (2 * K) ^ (1 - α) * (L * t) ^ α := by
    calc m = m ^ (1 - α) * m ^ α := by
          rw [← Real.rpow_add' hm0 (by norm_num : (1 - α) + α ≠ 0)]; norm_num
      _ ≤ (2 * K) ^ (1 - α) * (L * t) ^ α := by
          gcongr
  rwa [Real.mul_rpow hL0 ht0, ← mul_assoc] at key

omit [NormedAddCommGroup X] in
theorem norm_smul_sub_smul [NormedSpace ℝ Y] (c : ℝ) (y y' : Y) : ‖c • y - c • y'‖ = |c| * ‖y - y'‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]

end Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### Rescaling -/

section Rescale

variable {u : E → ℝ}

theorem fderiv_comp_smul (hu : Differentiable ℝ u) (σ : ℝ) (y : E) :
    fderiv ℝ (fun y => u (σ • y)) y = σ • fderiv ℝ u (σ • y) := by
  have h := (hu (σ • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul σ)
  refine (h.congr_fderiv ?_).fderiv
  ext v
  simp

theorem fderiv_fderiv_comp_smul (hu : ContDiff ℝ 2 u) (σ : ℝ) (y : E) :
    fderiv ℝ (fderiv ℝ fun y => u (σ • y)) y = (σ ^ 2) • fderiv ℝ (fderiv ℝ u) (σ • y) := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hf : fderiv ℝ (fun y => u (σ • y)) = fun y => σ • fderiv ℝ u (σ • y) :=
    funext fun y => fderiv_comp_smul hu1 σ y
  rw [hf]
  have h := ((hDu (σ • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul σ)).const_smul σ
  refine (h.congr_fderiv ?_).fderiv
  ext v w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

/-- **The rescaled operator**: with `σ² μ = 1`, the operator with coefficients `a(σ ·)`,
`σ β(σ ·)`, `μ⁻¹ c(σ ·) - 1` applied to `u(σ ·)` is `μ⁻¹ (L u - μ u)(σ ·)`. -/
theorem ellipticOp_rescale (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) (hu : ContDiff ℝ 2 u)
    {σ μ : ℝ} (hσμ : σ ^ 2 * μ = 1) (y : E) :
    ellipticOp b (fun y => a (σ • y)) (fun y => σ • β (σ • y)) (fun y => c (σ • y) / μ - 1)
        (fun y => u (σ • y)) y =
      μ⁻¹ * (ellipticOp b a β c u (σ • y) - μ * u (σ • y)) := by
  have hμ : μ ≠ 0 := by rintro rfl; simp at hσμ
  have hσ2 : σ ^ 2 = μ⁻¹ := by field_simp; linarith
  simp only [ellipticOp]
  rw [fderiv_fderiv_comp_smul hu, fderiv_comp_smul (hu.differentiable (by norm_num)),
    hessTrace_smul_right, hσ2]
  simp only [smul_apply, map_smul, smul_eq_mul]
  field_simp
  have h1 : μ * σ ^ 2 = 1 := by rw [mul_comm]; exact hσμ
  rw [h1]
  ring

end Rescale

/-! ### The weighted estimate -/

/-- **The parameter-dependent Schauder estimate on the whole space** (`μ ≥ 1`, `c ≤ 0`): with
`f = L u - μ u`, `|f| ≤ F`, `[f]_α ≤ M` and `N = M + μ^{α/2} F`:
`[D²u]_α ≤ C N`, `μ^{α/2} |D²u|_0 ≤ C N`, `μ^{(1+α)/2} |Du|_0 ≤ C N` and `μ |u|_0 ≤ F`, with
`C = C(b, λ, Λ, α)` independent of `μ` and of the operator in the class. -/
theorem exists_weighted_estimate {lam Λ α : ℝ} (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ),
      IsEllipticCoeff a lam Λ α → IsLowerCoeff β c Λ α → (∀ x, c x ≤ 0) →
      ∀ μ : ℝ, 1 ≤ μ → ∀ u : E → ℝ, ContDiff ℝ 2 u →
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) → (∃ A : ℝ, ∀ x, |u x| ≤ A) →
      ∀ M F : ℝ, 0 ≤ M →
      (∀ x, |ellipticOp b a β c u x - μ * u x| ≤ F) →
      (∀ x y, |(ellipticOp b a β c u x - μ * u x) - (ellipticOp b a β c u y - μ * u y)| ≤
        M * ‖x - y‖ ^ α) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        C * (M + μ ^ (α / 2) * F) * ‖x - y‖ ^ α) ∧
      (∀ x, μ ^ (α / 2) * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (M + μ ^ (α / 2) * F)) ∧
      (∀ x, μ ^ ((1 + α) / 2) * ‖fderiv ℝ u x‖ ≤ C * (M + μ ^ (α / 2) * F)) ∧
      (∀ x, μ * |u x| ≤ F) := by
  obtain ⟨C, hC, hS⟩ := exists_schauder_estimate (Λ := Λ + 1) b hlam hα0 hα1
  refine ⟨C, hC, ?_⟩
  intro a β c ha hβc hc μ hμ u hu hH hB hA M F hM hF hFH
  have hΛ : 0 ≤ Λ := nonneg_of_isEllipticCoeff ha
  have hμ0 : 0 < μ := by linarith
  -- the maximum principle
  have hpos : ∀ x v, 0 ≤ ⟪a x v, v⟫ := fun x v =>
    le_trans (mul_nonneg hlam.le (sq_nonneg ‖v‖)) (ha.elliptic x v)
  have hmax : ∀ x, μ * |u x| ≤ F :=
    mul_abs_le_of_ellipticOp_sub b ha.symm hpos ha.bound hβc.bound_β hc hμ0 hu hA hF
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  -- the scale
  set s : ℝ := Real.sqrt μ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hμ0
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hμ
  have hss : s ^ 2 = μ := Real.sq_sqrt hμ0.le
  set σ : ℝ := s⁻¹ with hσ
  have hσ0 : 0 < σ := inv_pos.2 hs0
  have hσ1 : σ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hσs : σ * s = 1 := inv_mul_cancel₀ hs0.ne'
  have hσμ : σ ^ 2 * μ = 1 := by rw [← hss, ← mul_pow, hσs, one_pow]
  have hσα : σ ^ α ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hα0.le
  have hσα0 : 0 < σ ^ α := Real.rpow_pos_of_pos hσ0 _
  have hsα : s ^ α = μ ^ (α / 2) := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hμ0.le]; ring_nf
  have hσsα : σ ^ α * s ^ α = 1 := by
    rw [← Real.mul_rpow hσ0.le hs0.le, hσs, Real.one_rpow]
  have hs1α : μ ^ ((1 + α) / 2) = s * s ^ α := by
    rw [hsα, hs, Real.sqrt_eq_rpow, ← Real.rpow_add hμ0]; ring_nf
  have hσxy : ∀ y y' : E, ‖σ • y - σ • y'‖ ^ α = σ ^ α * ‖y - y'‖ ^ α := fun y y' => by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hσ0.le,
      Real.mul_rpow hσ0.le (norm_nonneg _)]
  have hσsx : ∀ x : E, σ • (s • x) = x := fun x => by rw [smul_smul, hσs, one_smul]
  -- the rescaled operator and function
  set a' : E → E →L[ℝ] E := fun y => a (σ • y) with ha'_def
  set β' : E → E := fun y => σ • β (σ • y) with hβ'_def
  set c' : E → ℝ := fun y => c (σ • y) / μ - 1 with hc'_def
  set u' : E → ℝ := fun y => u (σ • y) with hu'_def
  have ha' : IsEllipticCoeff a' lam (Λ + 1) α := by
    refine ⟨fun y => ha.symm (σ • y), fun y => ha.elliptic (σ • y),
      fun y => (ha.bound (σ • y)).trans (by linarith), fun y y' => ?_⟩
    calc ‖a (σ • y) - a (σ • y')‖ ≤ Λ * ‖σ • y - σ • y'‖ ^ α := ha.holder _ _
      _ = Λ * σ ^ α * ‖y - y'‖ ^ α := by rw [hσxy, mul_assoc]
      _ ≤ (Λ + 1) * ‖y - y'‖ ^ α := by
          gcongr
          nlinarith
  have hβc' : IsLowerCoeff β' c' (Λ + 1) α := by
    refine ⟨fun y => ?_, fun y y' => ?_, fun y => ?_, fun y y' => ?_⟩
    · simp only [hβ'_def, norm_smul, Real.norm_of_nonneg hσ0.le]
      nlinarith [hβc.bound_β (σ • y), norm_nonneg (β (σ • y))]
    · simp only [hβ'_def, ← smul_sub, norm_smul, Real.norm_of_nonneg hσ0.le]
      have h := hβc.holder_β (σ • y) (σ • y')
      rw [hσxy] at h
      have hp : 0 ≤ ‖y - y'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
      have h3 : Λ * (σ ^ α * ‖y - y'‖ ^ α) ≤ Λ * ‖y - y'‖ ^ α :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hp hσα) hΛ
      calc σ * ‖β (σ • y) - β (σ • y')‖ ≤ 1 * (Λ * (σ ^ α * ‖y - y'‖ ^ α)) :=
            mul_le_mul hσ1 h (norm_nonneg _) zero_le_one
        _ ≤ (Λ + 1) * ‖y - y'‖ ^ α := by nlinarith
    · simp only [hc'_def]
      have h := hβc.bound_c (σ • y)
      have : |c (σ • y) / μ| ≤ Λ := by
        rw [abs_div, abs_of_pos hμ0, div_le_iff₀ hμ0]; nlinarith [abs_nonneg (c (σ • y))]
      calc |c (σ • y) / μ - 1| ≤ |c (σ • y) / μ| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ Λ + 1 := by rw [abs_one]; linarith
    · simp only [hc'_def]
      have h := hβc.holder_c (σ • y) (σ • y')
      rw [hσxy] at h
      have hp : 0 ≤ ‖y - y'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
      have e : c (σ • y) / μ - 1 - (c (σ • y') / μ - 1) = (c (σ • y) - c (σ • y')) / μ := by ring
      rw [e, abs_div, abs_of_pos hμ0, div_le_iff₀ hμ0]
      have h3 : Λ * (σ ^ α * ‖y - y'‖ ^ α) ≤ Λ * ‖y - y'‖ ^ α :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hp hσα) hΛ
      have h4 : (Λ + 1) * ‖y - y'‖ ^ α ≤ (Λ + 1) * ‖y - y'‖ ^ α * μ :=
        le_mul_of_one_le_right (by positivity) hμ
      nlinarith
  have hu' : ContDiff ℝ 2 u' := hu.comp (contDiff_const_smul σ)
  have hD2u' : ∀ y, fderiv ℝ (fderiv ℝ u') y = (σ ^ 2) • fderiv ℝ (fderiv ℝ u) (σ • y) :=
    fun y => fderiv_fderiv_comp_smul hu σ y
  have hDu' : ∀ y, fderiv ℝ u' y = σ • fderiv ℝ u (σ • y) :=
    fun y => fderiv_comp_smul (hu.differentiable (by norm_num)) σ y
  have hH' : ∃ H : ℝ, ∀ y y', ‖fderiv ℝ (fderiv ℝ u') y - fderiv ℝ (fderiv ℝ u') y'‖ ≤
      H * ‖y - y'‖ ^ α := by
    obtain ⟨H, hH⟩ := hH
    refine ⟨σ ^ 2 * H * σ ^ α, fun y y' => ?_⟩
    rw [hD2u', hD2u', norm_smul_sub_smul (Y := E →L[ℝ] E →L[ℝ] ℝ),
      abs_of_nonneg (by positivity)]
    calc σ ^ 2 * ‖fderiv ℝ (fderiv ℝ u) (σ • y) - fderiv ℝ (fderiv ℝ u) (σ • y')‖
        ≤ σ ^ 2 * (H * (σ ^ α * ‖y - y'‖ ^ α)) := by
          gcongr; rw [← hσxy]; exact hH _ _
      _ = σ ^ 2 * H * σ ^ α * ‖y - y'‖ ^ α := by ring
  have hB' : ∃ B : ℝ, ∀ y, ‖fderiv ℝ (fderiv ℝ u') y‖ ≤ B := by
    obtain ⟨B, hB⟩ := hB
    refine ⟨σ ^ 2 * B, fun y => ?_⟩
    rw [hD2u', norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
  have hA' : ∀ y, |u' y| ≤ F / μ := fun y => by
    rw [le_div_iff₀ hμ0, mul_comm]; exact hmax (σ • y)
  set M'' : ℝ := σ ^ α * M / μ with hM''
  have hM''0 : 0 ≤ M'' := by positivity
  have hL' : ∀ y y', |ellipticOp b a' β' c' u' y - ellipticOp b a' β' c' u' y'| ≤
      M'' * ‖y - y'‖ ^ α := by
    intro y y'
    rw [ellipticOp_rescale b a β c hu hσμ, ellipticOp_rescale b a β c hu hσμ, ← mul_sub,
      abs_mul, abs_of_pos (inv_pos.2 hμ0)]
    have h := hFH (σ • y) (σ • y')
    rw [hσxy] at h
    rw [hM'', inv_mul_le_iff₀ hμ0]
    calc _ ≤ M * (σ ^ α * ‖y - y'‖ ^ α) := h
      _ = μ * (σ ^ α * M / μ * ‖y - y'‖ ^ α) := by field_simp
  obtain ⟨h1, h2, h3⟩ := hS a' β' c' ha' hβc' u' hu' hH' hB' (F / μ) M'' hM''0 hA' hL'
  -- scaling back
  have hkey : μ * (M'' + F / μ) * s ^ α = M + s ^ α * F := by
    rw [hM'']
    field_simp
    have : σ ^ α * s ^ α * M = M := by rw [hσsα, one_mul]
    nlinarith [this]
  have hD2x : ∀ x, fderiv ℝ (fderiv ℝ u') (s • x) = (σ ^ 2) • fderiv ℝ (fderiv ℝ u) x :=
    fun x => by rw [hD2u', hσsx]
  have hDx : ∀ x, fderiv ℝ u' (s • x) = σ • fderiv ℝ u x := fun x => by rw [hDu', hσsx]
  refine ⟨fun x x' => ?_, fun x => ?_, fun x => ?_, hmax⟩
  · have h := h1 (s • x) (s • x')
    rw [hD2x, hD2x, norm_smul_sub_smul (Y := E →L[ℝ] E →L[ℝ] ℝ),
      abs_of_nonneg (by positivity), ← smul_sub, norm_smul, Real.norm_of_nonneg hs0.le,
      Real.mul_rpow hs0.le (norm_nonneg _)] at h
    have hσ2 : σ ^ 2 = μ⁻¹ := by rw [← hss, hσ, inv_pow]
    rw [hσ2, inv_mul_le_iff₀ hμ0] at h
    rw [← hsα]
    calc _ ≤ μ * (C * (M'' + F / μ) * (s ^ α * ‖x - x'‖ ^ α)) := h
      _ = C * (μ * (M'' + F / μ) * s ^ α) * ‖x - x'‖ ^ α := by ring
      _ = C * (M + s ^ α * F) * ‖x - x'‖ ^ α := by rw [hkey]
  · have h := h2 (s • x)
    rw [hD2x, norm_smul_real (Y := E →L[ℝ] E →L[ℝ] ℝ), abs_of_nonneg (by positivity)] at h
    have hσ2 : σ ^ 2 = μ⁻¹ := by rw [← hss, hσ, inv_pow]
    rw [hσ2, inv_mul_le_iff₀ hμ0] at h
    rw [← hsα]
    calc s ^ α * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ s ^ α * (μ * (C * (M'' + F / μ))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * (μ * (M'' + F / μ) * s ^ α) := by ring
      _ = C * (M + s ^ α * F) := by rw [hkey]
  · have h := h3 (s • x)
    rw [hDx, norm_smul, Real.norm_of_nonneg hσ0.le, hσ, inv_mul_le_iff₀ hs0] at h
    rw [hs1α, ← hsα]
    calc s * s ^ α * ‖fderiv ℝ u x‖ ≤ s * s ^ α * (s * (C * (M'' + F / μ))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * (s ^ 2 * (M'' + F / μ) * s ^ α) := by ring
      _ = C * (M + s ^ α * F) := by rw [hss, hkey]

end SGPT.Foundations.Analysis.Pending.SchauderWeighted
