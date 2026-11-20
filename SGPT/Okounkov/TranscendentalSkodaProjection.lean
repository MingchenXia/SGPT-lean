import SGPT.Okounkov.TranscendentalSkodaAdjoint

/-!
# Skoda's theorem: the projection calculus of the kernel bundle

Blueprint `claude-tok-skoda`, node `skoda:projection-calculus`.

For a tuple `G` without common zeros, `P_S a = a - (G · a) ρ` (`kernelProj`) with the normal
direction `ρᵢ = Ḡᵢ / |G|²` (`normalDir`). This file proves:

* the pointwise algebra of `P_S`: linearity, `P_S a = a` on `S`, `P_S (a + c Ḡ) = P_S a`, the
  self-adjointness identities `∑ b̄ᵢ (P_S a)ᵢ = ∑ b̄ᵢ aᵢ` for `b ∈ S`, and the crude bound
  `|(P_S a)ᵢ| ≤ 2 ∑ₖ |aₖ|`;
* for `ℂ^R`-valued test forms `α` and their projection `P_S α` (`kernelProjForm`), which is again a
  test form: `P_S T*(P_S α) = P_S T* α` (`kernelProj_tstarForm_kernelProjForm`), and the formula
  `∂̄ (P_S α)ᵢ = P_S (∂̄ α)ᵢ - ((∂̄ρᵢ) ∧ (G · α))` (`dbarForm_kernelProjForm`);
* `∂̄` of a kernel-valued test function is kernel-valued (`sum_mul_dbarDir_of_inKernel`), and
  `∂̄ⱼ (Ḡₖ c) = conj (∂ⱼ Gₖ) c + Ḡₖ ∂̄ⱼ c` (`dbarDir_conj_mul`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open scoped Topology ComplexConjugate ContDiff

variable {n R : ℕ}

/-! ### Pointwise algebra -/

/-- The normal direction `ρᵢ = Ḡᵢ / |G|²` of the kernel bundle. -/
def normalDir (G : Fin R → ComplexModel n → ℂ) (i : Fin R) (x : ComplexModel n) : ℂ :=
  conj (G i x) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ)

theorem kernelProj_eq (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n) (a : Fin R → ℂ)
    (i : Fin R) : kernelProj G x a i = a i - normalDir G i x * ∑ k, G k x * a k := by
  simp only [kernelProj, normalDir]; ring

theorem sum_mul_normalDir (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) : ∑ i, G i x * normalDir G i x = 1 := by
  have h := sum_mul_skodaLift (D := {x}) (G := G) (fun z hz => by rw [hz]; exact hS)
    (fun _ => (1 : ℂ)) (mem_singleton x)
  simpa [skodaLift, normalDir] using h

theorem kernelProj_of_kernel (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    {a : Fin R → ℂ} (ha : ∑ k, G k x * a k = 0) : kernelProj G x a = a := by
  funext i; simp [kernelProj, ha]

theorem kernelProj_kernelProj (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) (a : Fin R → ℂ) :
    kernelProj G x (kernelProj G x a) = kernelProj G x a :=
  kernelProj_of_kernel G x (sum_mul_kernelProj G hS a)

theorem kernelProj_sub (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (a b : Fin R → ℂ) (i : Fin R) :
    kernelProj G x (fun k => a k - b k) i = kernelProj G x a i - kernelProj G x b i := by
  simp only [kernelProj_eq, mul_sub, Finset.sum_sub_distrib]; ring

theorem kernelProj_add (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (a b : Fin R → ℂ) (i : Fin R) :
    kernelProj G x (fun k => a k + b k) i = kernelProj G x a i + kernelProj G x b i := by
  simp only [kernelProj_eq, mul_add, Finset.sum_add_distrib]; ring

theorem kernelProj_smul (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n) (c : ℂ)
    (a : Fin R → ℂ) (i : Fin R) :
    kernelProj G x (fun k => c * a k) i = c * kernelProj G x a i := by
  simp only [kernelProj_eq]
  rw [show ∑ k, G k x * (c * a k) = c * ∑ k, G k x * a k by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
  ring

/-- `P_S (a + c Ḡ) = P_S a`. -/
theorem kernelProj_add_conj (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) (a : Fin R → ℂ) (c : ℂ) :
    kernelProj G x (fun k => a k + c * conj (G k x)) = kernelProj G x a := by
  funext i
  rw [kernelProj_add]
  have hc : kernelProj G x (fun k => c * conj (G k x)) i = 0 := by
    rw [kernelProj_smul]
    have h1 : ∑ k, G k x * conj (G k x) = ((generatorNormSq G x : ℝ) : ℂ) := by
      rw [generatorNormSq, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [kernelProj_eq, h1, normalDir, mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hS.ne', Complex.ofReal_one, mul_one, sub_self, mul_zero]
  rw [hc, add_zero]

/-- `P_S a = a + c Ḡ` for the scalar `c = -(G · a)/|G|²`. -/
theorem kernelProj_eq_add_conj (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (a : Fin R → ℂ) : ∃ c : ℂ, ∀ i, kernelProj G x a i = a i + c * conj (G i x) :=
  ⟨-((∑ k, G k x * a k) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ)), fun i => by
    rw [kernelProj_eq, normalDir]; ring⟩

/-- For `b ∈ S`: `∑ b̄ᵢ (P_S a)ᵢ = ∑ b̄ᵢ aᵢ`. -/
theorem sum_conj_mul_kernelProj (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    {b : Fin R → ℂ} (hb : ∑ k, G k x * b k = 0) (a : Fin R → ℂ) :
    ∑ i, conj (b i) * kernelProj G x a i = ∑ i, conj (b i) * a i := by
  simp only [kernelProj_eq, mul_sub, Finset.sum_sub_distrib, sub_eq_self]
  have h : ∑ i, conj (b i) * (normalDir G i x * ∑ k, G k x * a k) =
      (∑ k, G k x * a k) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ) *
        conj (∑ i, G i x * b i) := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [normalDir, map_mul]; ring
  rw [h, hb, map_zero, mul_zero]

/-- For `b ∈ S`: `∑ conj((P_S a)ᵢ) bᵢ = ∑ āᵢ bᵢ`. -/
theorem sum_conj_kernelProj_mul (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    {b : Fin R → ℂ} (hb : ∑ k, G k x * b k = 0) (a : Fin R → ℂ) :
    ∑ i, conj (kernelProj G x a i) * b i = ∑ i, conj (a i) * b i := by
  have h := congrArg conj (sum_conj_mul_kernelProj G x hb a)
  simp only [map_sum, map_mul, Complex.conj_conj] at h
  rw [← Finset.sum_congr rfl fun i _ => mul_comm (b i) (conj (kernelProj G x a i)),
    ← Finset.sum_congr rfl fun i _ => mul_comm (b i) (conj (a i))]
  exact h

theorem norm_mul_mul_inv_le_one (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (i k : Fin R) : ‖G i x‖ * ‖G k x‖ * (generatorNormSq G x)⁻¹ ≤ 1 := by
  have hle : ∀ l, ‖G l x‖ ^ 2 ≤ generatorNormSq G x := fun l =>
    Finset.single_le_sum (f := fun l => ‖G l x‖ ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ l)
  rcases (generatorNormSq_nonneg G x).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, mul_zero]; exact zero_le_one
  · rw [mul_inv_le_iff₀ hpos, one_mul]
    nlinarith [hle i, hle k, sq_nonneg (‖G i x‖ - ‖G k x‖)]

/-- The crude bound `|(P_S a)ᵢ| ≤ 2 ∑ₖ |aₖ|`. -/
theorem norm_kernelProj_le (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (a : Fin R → ℂ) (i : Fin R) : ‖kernelProj G x a i‖ ≤ 2 * ∑ k, ‖a k‖ := by
  have hsum : ‖normalDir G i x * ∑ k, G k x * a k‖ ≤ ∑ k, ‖a k‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [normalDir, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (generatorNormSq_nonneg G x))]
    have := norm_mul_mul_inv_le_one G x i k
    calc ‖G i x‖ * (generatorNormSq G x)⁻¹ * (‖G k x‖ * ‖a k‖)
        = (‖G i x‖ * ‖G k x‖ * (generatorNormSq G x)⁻¹) * ‖a k‖ := by ring
      _ ≤ 1 * ‖a k‖ := by gcongr
      _ = ‖a k‖ := one_mul _
  have hi : ‖a i‖ ≤ ∑ k, ‖a k‖ :=
    Finset.single_le_sum (f := fun k => ‖a k‖) (fun k _ => norm_nonneg _) (Finset.mem_univ i)
  rw [kernelProj_eq]
  calc ‖a i - normalDir G i x * ∑ k, G k x * a k‖
      ≤ ‖a i‖ + ‖normalDir G i x * ∑ k, G k x * a k‖ := norm_sub_le _ _
    _ ≤ 2 * ∑ k, ‖a k‖ := by linarith

theorem norm_normalDir_mul_le (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n)
    (i k : Fin R) : ‖normalDir G i x * G k x‖ ≤ 1 := by
  rw [normalDir, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (generatorNormSq_nonneg G x))]
  have := norm_mul_mul_inv_le_one G x i k
  calc ‖G i x‖ * (generatorNormSq G x)⁻¹ * ‖G k x‖
      = ‖G i x‖ * ‖G k x‖ * (generatorNormSq G x)⁻¹ := by ring
    _ ≤ 1 := this

/-! ### Smoothness and test forms -/

theorem contDiffOn_inv_generatorNormSq {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) :
    ContDiffOn ℝ ∞ (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) D :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((contDiffOn_generatorNormSq hD hG).inv fun z hz => (hpos z hz).ne')

theorem contDiffOn_conj_of_holo {D : Set (ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D) :
    ContDiffOn ℝ ∞ (fun y => conj (F y)) D :=
  Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_real_of_holo hD hF)

theorem contDiffOn_normalDir {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (i : Fin R) :
    ContDiffOn ℝ ∞ (normalDir G i) D :=
  (contDiffOn_conj_of_holo hD (hG i)).mul (contDiffOn_inv_generatorNormSq hD hG hpos)

theorem IsTestFunctionOn.sub' {D : Set (ComplexModel n)} {h₁ h₂ : ComplexModel n → ℂ}
    (h₁t : IsTestFunctionOn D h₁) (h₂t : IsTestFunctionOn D h₂) :
    IsTestFunctionOn D fun x => h₁ x - h₂ x := by
  have h := h₁t.add (h₂t.const_mul (-1))
  convert h using 1
  funext x; simp only [Pi.add_apply]; ring

theorem IsTestFunctionOn.finset_sum' {D : Set (ComplexModel n)} {ι : Type*} (s : Finset ι)
    {h : ι → ComplexModel n → ℂ} (ht : ∀ i ∈ s, IsTestFunctionOn D (h i)) :
    IsTestFunctionOn D fun x => ∑ i ∈ s, h i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact isTestFunctionOn_zero
  | insert a s ha ih =>
    have h1 := (ht a (Finset.mem_insert_self a s)).add
      (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))
    convert h1 using 1
    funext x; simp [Finset.sum_insert ha]

/-- The projection `P_S α` of a `ℂ^R`-valued `(0,1)`-form (rows `i`, form index `j`). -/
def kernelProjForm (G : Fin R → ComplexModel n → ℂ) (α : Fin R → Fin n → ComplexModel n → ℂ) :
    Fin R → Fin n → ComplexModel n → ℂ :=
  fun i j x => kernelProj G x (fun k => α k j x) i

theorem kernelProjForm_eq (G : Fin R → ComplexModel n → ℂ)
    (α : Fin R → Fin n → ComplexModel n → ℂ) (i : Fin R) (j : Fin n) :
    kernelProjForm G α i j = fun x => α i j x - normalDir G i x * ∑ k, G k x * α k j x := by
  funext x; exact kernelProj_eq G x _ i

/-- `P_S` of a test form is a test form. -/
theorem kernelProjForm_mem {L : Set (ComplexModel n)} (hL : IsOpen L)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) L)
    (hpos : ∀ z ∈ L, 0 < generatorNormSq G z) {α : Fin R → Fin n → ComplexModel n → ℂ}
    (hα : ∀ i, α i ∈ testForms L) (i : Fin R) : kernelProjForm G α i ∈ testForms L := by
  intro j
  rw [kernelProjForm_eq]
  refine IsTestFunctionOn.sub' (hα i j) ?_
  have h : (fun x => normalDir G i x * ∑ k, G k x * α k j x) =
      fun x => ∑ k, (normalDir G i x * G k x) * α k j x := by
    funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  exact IsTestFunctionOn.finset_sum' _ fun k _ => IsTestFunctionOn.mul_left hL
    ((contDiffOn_normalDir hL hG hpos i).mul (contDiffOn_real_of_holo hL (hG k))) (hα k j)

theorem inKernel_kernelProjForm (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) (α : Fin R → Fin n → ComplexModel n → ℂ) :
    InKernel G x fun i j => kernelProjForm G α i j x :=
  fun _ => sum_mul_kernelProj G hS _

/-! ### Wirtinger derivatives of the projection -/

theorem dDir_normalDir {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {x : ComplexModel n} (hx : x ∈ D)
    (i : Fin R) (v : ComplexModel n) :
    dDir v (normalDir G i) x =
      conj (G i x) * dDir v (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) x := by
  have hGx : DifferentiableAt ℂ (G i) x := (hG i).differentiableAt (hD.mem_nhds hx)
  have hcR : DifferentiableAt ℝ (fun y => conj (G i y)) x :=
    Complex.conjCLE.differentiableAt.comp x (hGx.restrictScalars ℝ)
  have hsR : DifferentiableAt ℝ (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) x :=
    ((contDiffOn_inv_generatorNormSq hD hG hpos).contDiffAt (hD.mem_nhds hx)).differentiableAt
      (by simp)
  have e : normalDir G i = fun y => conj (G i y) * (((generatorNormSq G y)⁻¹ : ℝ) : ℂ) := rfl
  rw [e, dDir_mul hcR hsR, dDir_conj (hGx.restrictScalars ℝ),
    SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt hGx, map_zero,
    zero_mul, zero_add]

/-- **Projection calculus (1)** (`skoda:projection-calculus`): `T*(P_S α)ᵢ = T* αᵢ + τ Ḡᵢ` for
one scalar `τ`, hence `P_S T*(P_S α) = P_S T* α`. -/
theorem exists_tstarForm_kernelProjForm {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (w₂ ψ₀ : ComplexModel n → ℝ)
    {α : Fin R → Fin n → ComplexModel n → ℂ} (hα : ∀ i j, ContDiff ℝ 1 (α i j))
    {x : ComplexModel n} (hx : x ∈ D) :
    ∃ τ : ℂ, ∀ i, tstarForm w₂ ψ₀ (kernelProjForm G α i) x =
      tstarForm w₂ ψ₀ (α i) x + τ * conj (G i x) := by
  set s : ComplexModel n → ℂ := fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ) with hs
  set c : Fin n → ComplexModel n → ℂ := fun j y => ∑ k, G k y * α k j y with hc
  have hGx : ∀ k, DifferentiableAt ℂ (G k) x := fun k => (hG k).differentiableAt (hD.mem_nhds hx)
  have hαd : ∀ k j, DifferentiableAt ℝ (α k j) x := fun k j =>
    ((hα k j).differentiable one_ne_zero) x
  have hcd : ∀ j, DifferentiableAt ℝ (c j) x := fun j => by
    simp only [hc]
    exact DifferentiableAt.fun_sum fun k _ => ((hGx k).restrictScalars ℝ).mul (hαd k j)
  have hρd : ∀ i, DifferentiableAt ℝ (normalDir G i) x := fun i =>
    ((contDiffOn_normalDir hD hG hpos i).contDiffAt (hD.mem_nhds hx)).differentiableAt
      (by simp)
  set τ : ℂ := ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ∑ j, (dDir (coordVec j) s x * c j x +
      s x * dDir (coordVec j) (c j) x - dDir (coordVec j) (fun y => ((w₂ y : ℝ) : ℂ)) x *
        (s x * c j x)) with hτ
  refine ⟨τ, fun i => ?_⟩
  have hρ : ∀ j, dDir (coordVec j) (normalDir G i) x = conj (G i x) * dDir (coordVec j) s x :=
    fun j => dDir_normalDir hD hG hpos hx i _
  have hdelta : ∀ j, deltaDir (coordVec j) w₂ (kernelProjForm G α i j) x =
      deltaDir (coordVec j) w₂ (α i j) x - conj (G i x) * (dDir (coordVec j) s x * c j x +
        s x * dDir (coordVec j) (c j) x - dDir (coordVec j) (fun y => ((w₂ y : ℝ) : ℂ)) x *
          (s x * c j x)) := by
    intro j
    have hfun : kernelProjForm G α i j = fun y => α i j y - normalDir G i y * c j y :=
      kernelProjForm_eq G α i j
    have hmul : DifferentiableAt ℝ (fun y => normalDir G i y * c j y) x := (hρd i).mul (hcd j)
    rw [hfun]
    simp only [deltaDir]
    rw [dDir_sub (hαd i j) hmul, dDir_mul (hρd i) (hcd j), hρ j]
    simp only [normalDir, hc, hs]
    ring
  simp only [tstarForm]
  rw [Finset.sum_congr rfl fun j _ => hdelta j, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [hτ]
  ring

theorem kernelProj_tstarForm_kernelProjForm {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (w₂ ψ₀ : ComplexModel n → ℝ)
    {α : Fin R → Fin n → ComplexModel n → ℂ} (hα : ∀ i j, ContDiff ℝ 1 (α i j))
    {x : ComplexModel n} (hx : x ∈ D) :
    kernelProj G x (fun i => tstarForm w₂ ψ₀ (kernelProjForm G α i) x) =
      kernelProj G x (fun i => tstarForm w₂ ψ₀ (α i) x) := by
  obtain ⟨τ, hτ⟩ := exists_tstarForm_kernelProjForm hD hG hpos w₂ ψ₀ hα hx
  simp_rw [hτ]
  exact kernelProj_add_conj G (hpos x hx) _ τ

/-- **Projection calculus (2)** (`skoda:projection-calculus`): for `cₗ = ∑ₖ Gₖ αₖₗ`,
`∂̄(P_S α)ᵢ = P_S(∂̄ α)ᵢ - (∂̄ⱼρᵢ cₗ - ∂̄ₗρᵢ cⱼ)`. -/
theorem dbarForm_kernelProjForm {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z)
    {α : Fin R → Fin n → ComplexModel n → ℂ} (hα : ∀ i j, ContDiff ℝ 1 (α i j))
    {x : ComplexModel n} (hx : x ∈ D) (i : Fin R) (p : Fin n × Fin n) :
    dbarForm (kernelProjForm G α i) p x =
      kernelProj G x (fun k => dbarForm (α k) p x) i -
        (dbarDir (coordVec p.1) (normalDir G i) x * ∑ k, G k x * α k p.2 x -
          dbarDir (coordVec p.2) (normalDir G i) x * ∑ k, G k x * α k p.1 x) := by
  have hGx : ∀ k, DifferentiableAt ℂ (G k) x := fun k => (hG k).differentiableAt (hD.mem_nhds hx)
  have hαd : ∀ k j, DifferentiableAt ℝ (α k j) x := fun k j =>
    ((hα k j).differentiable one_ne_zero) x
  have hcd : ∀ j, DifferentiableAt ℝ (fun y => ∑ k, G k y * α k j y) x := fun j =>
    DifferentiableAt.fun_sum fun k _ => ((hGx k).restrictScalars ℝ).mul (hαd k j)
  have hρd : DifferentiableAt ℝ (normalDir G i) x :=
    ((contDiffOn_normalDir hD hG hpos i).contDiffAt (hD.mem_nhds hx)).differentiableAt
      (by simp)
  have hdc : ∀ (v : ComplexModel n) j, dbarDir v (fun y => ∑ k, G k y * α k j y) x =
      ∑ k, G k x * dbarDir v (α k j) x := by
    intro v j
    rw [dbarDir_finset_sum (F := fun k y => G k y * α k j y) _
      fun k _ => ((hGx k).restrictScalars ℝ).mul (hαd k j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dbarDir_mul ((hGx k).restrictScalars ℝ) (hαd k j),
      SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt (hGx k),
      zero_mul, zero_add]
  have hterm : ∀ (v : ComplexModel n) j, dbarDir v (kernelProjForm G α i j) x =
      dbarDir v (α i j) x - (dbarDir v (normalDir G i) x * ∑ k, G k x * α k j x +
        normalDir G i x * ∑ k, G k x * dbarDir v (α k j) x) := by
    intro v j
    have hmul : DifferentiableAt ℝ (fun y => normalDir G i y * ∑ k, G k y * α k j y) x :=
      hρd.mul (hcd j)
    rw [kernelProjForm_eq, dbarDir_sub (hαd i j) hmul, dbarDir_mul hρd (hcd j), hdc v j]
  simp only [dbarForm]
  rw [hterm, hterm, kernelProj_eq]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- `∂̄ⱼ (Ḡₖ c) = conj (∂ⱼ Gₖ) c + Ḡₖ ∂̄ⱼ c`. -/
theorem dbarDir_conj_mul {D : Set (ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D) {c : ComplexModel n → ℂ}
    {x : ComplexModel n} (hx : x ∈ D) (hc : DifferentiableAt ℝ c x) (v : ComplexModel n) :
    dbarDir v (fun y => conj (F y) * c y) x =
      conj (dDir v F x) * c x + conj (F x) * dbarDir v c x := by
  have hFx : DifferentiableAt ℂ F x := hF.differentiableAt (hD.mem_nhds hx)
  have hcR : DifferentiableAt ℝ (fun y => conj (F y)) x :=
    Complex.conjCLE.differentiableAt.comp x (hFx.restrictScalars ℝ)
  rw [dbarDir_mul hcR hc, dbarDir_conj (hFx.restrictScalars ℝ)]

/-- `∂̄` of a kernel-valued test function is kernel-valued. -/
theorem sum_mul_dbarDir_of_inKernel {L : Set (ComplexModel n)} (hL : IsOpen L)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) L)
    {h : Fin R → ComplexModel n → ℂ} (hh : ∀ k, ContDiff ℝ 1 (h k))
    (hker : ∀ x ∈ L, ∑ k, G k x * h k x = 0) {x : ComplexModel n} (hx : x ∈ L)
    (v : ComplexModel n) : ∑ k, G k x * dbarDir v (h k) x = 0 := by
  have hGx : ∀ k, DifferentiableAt ℂ (G k) x := fun k => (hG k).differentiableAt (hL.mem_nhds hx)
  have hhd : ∀ k, DifferentiableAt ℝ (h k) x := fun k => ((hh k).differentiable one_ne_zero) x
  have h0 : dbarDir v (fun y => ∑ k, G k y * h k y) x = 0 := by
    have hev : (fun y => ∑ k, G k y * h k y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hL.mem_nhds hx) hker
    rw [dbarDir_congr hev, dbarDir_const]
  rw [dbarDir_finset_sum (F := fun k y => G k y * h k y) _
    fun k _ => ((hGx k).restrictScalars ℝ).mul (hhd k)] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dbarDir_mul ((hGx k).restrictScalars ℝ) (hhd k),
    SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt (hGx k),
    zero_mul, zero_add]

end SGPT.Okounkov.TranscendentalSkoda
