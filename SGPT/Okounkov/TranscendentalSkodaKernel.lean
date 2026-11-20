import SGPT.Okounkov.TranscendentalSkodaAlgebra
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Foundations.Analysis.Pending.HormanderInterface

/-!
# Skoda's theorem: the kernel bundle and the pointwise curvature estimates

Blueprint `claude-tok-skoda`, nodes `skoda:trace-rank`, `skoda:levi-log`, `skoda:curvature`.

A *tuple* is `G : Fin R → ℂⁿ → ℂ`. At a point `z`, a `ℂ^R`-valued `(0,1)`-covector is a matrix
`α : Fin R → Fin n → ℂ` (`α i j`: vector index `i`, form index `j`); it lies in the *kernel
bundle* (`InKernel G z α`) if every column is in `S_z = {a : ∑ᵢ Gᵢ(z) aᵢ = 0}`. We define

* `kernelPairing G z α = ∑ᵢ ∑ⱼ ∂ⱼGᵢ(z) αᵢⱼ` and the second fundamental form term
  `secondFundamental G z α = |kernelPairing G z α|² / |G(z)|²` (`B_z(α)` of the blueprint);
* `vectorLevi Φ z α = ∑ᵢ L_Φ(z)(αᵢ•)`, the Levi form of `Φ` summed over the rows.

The main result is **Skoda's curvature inequality** `secondFundamental_le_leviForm`:
`B_z(α) ≤ n · ∑ᵢ L_{log |G|²}(z)(αᵢ•)` for `α` in the kernel bundle, from the trace--rank
inequality `norm_sq_sum_dotProduct_le` and the Levi form of `log |G|²` (`leviForm_log_normSq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
open scoped Topology ComplexConjugate InnerProductSpace

variable {n R : ℕ}

/-! ### Definitions -/

/-- The covector `α` (columns `α • j`) lies in the kernel bundle `S_z = ker G(z)`. -/
def InKernel (G : Fin R → ComplexModel n → ℂ) (z : ComplexModel n) (α : Fin R → Fin n → ℂ) :
    Prop :=
  ∀ j, ∑ i, G i z * α i j = 0

/-- `∑ᵢ ∑ⱼ ∂ⱼGᵢ(z) αᵢⱼ`. -/
def kernelPairing (G : Fin R → ComplexModel n → ℂ) (z : ComplexModel n)
    (α : Fin R → Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, dDir (coordVec j) (G i) z * α i j

/-- The second fundamental form term `B_z(α) = |∑ᵢⱼ ∂ⱼGᵢ αᵢⱼ|² / |G|²`. -/
def secondFundamental (G : Fin R → ComplexModel n → ℂ) (z : ComplexModel n)
    (α : Fin R → Fin n → ℂ) : ℝ :=
  ‖kernelPairing G z α‖ ^ 2 / generatorNormSq G z

/-- The Levi form of `Φ` summed over the rows of `α`. -/
def vectorLevi (Φ : ComplexModel n → ℝ) (z : ComplexModel n) (α : Fin R → Fin n → ℂ) : ℝ :=
  ∑ i, leviForm Φ z (∑ j, α i j • coordVec j)

/-! ### The trace--rank inequality -/

/-- **Trace and rank** (`skoda:trace-rank`): for `w₁, …, wₙ ∈ ℂ^R` and an `R × n` matrix `α`,
`|∑ⱼ wⱼ · α•ⱼ|² ≤ n ∑ᵢ |∑ⱼ αᵢⱼ wⱼ|²` (`·` the bilinear dot product). -/
theorem norm_sq_sum_dotProduct_le (w : Fin n → EuclideanSpace ℂ (Fin R))
    (α : Fin R → Fin n → ℂ) :
    ‖∑ j, ∑ i, w j i * α i j‖ ^ 2 ≤ n * ∑ i, ‖∑ j, α i j • w j‖ ^ 2 := by
  classical
  set V : Submodule ℂ (EuclideanSpace ℂ (Fin R)) := Submodule.span ℂ (Set.range w) with hV
  set d := Module.finrank ℂ V with hd
  have hdn : d ≤ n := by
    have h := finrank_range_le_card (R := ℂ) w
    simpa [Set.finrank, Fintype.card_fin] using h
  set b := stdOrthonormalBasis ℂ V with hb
  -- the rows `ρᵢ = ∑ⱼ αᵢⱼ wⱼ` lie in `V`
  set ρ : Fin R → V := fun i =>
    ⟨∑ j, α i j • w j, Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩ with hρ
  have hρc : ∀ i, ((ρ i : V) : EuclideanSpace ℂ (Fin R)) = ∑ j, α i j • w j := fun i => rfl
  -- expansion in the orthonormal basis
  set c : Fin R → Fin (Module.finrank ℂ V) → ℂ := fun i l => ⟪(b l : V), ρ i⟫_ℂ with hc
  have hexp : ∀ i, ((ρ i : V) : EuclideanSpace ℂ (Fin R)) =
      ∑ l, c i l • ((b l : V) : EuclideanSpace ℂ (Fin R)) := by
    intro i
    conv_lhs => rw [← b.sum_repr' (ρ i)]
    simp [hc]
  have htrace : ∑ j, ∑ i, w j i * α i j =
      ∑ p : Fin R × Fin (Module.finrank ℂ V),
        c p.1 p.2 * ((b p.2 : V) : EuclideanSpace ℂ (Fin R)) p.1 := by
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := congrArg (fun v : EuclideanSpace ℂ (Fin R) => v i) (hexp i)
    simp only [hρc] at h
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hCS := normSq_sum_mul_le (fun p : Fin R × Fin (Module.finrank ℂ V) => c p.1 p.2)
    (fun p => ((b p.2 : V) : EuclideanSpace ℂ (Fin R)) p.1)
  rw [← htrace] at hCS
  have hpars : ∀ i, ∑ l, Complex.normSq (c i l) = ‖∑ j, α i j • w j‖ ^ 2 := by
    intro i
    have h := b.sum_sq_norm_inner_right (ρ i)
    rw [← Submodule.norm_coe, hρc] at h
    simpa [hc, Complex.normSq_eq_norm_sq] using h
  have hbasis : ∑ p : Fin R × Fin (Module.finrank ℂ V),
      Complex.normSq (((b p.2 : V) : EuclideanSpace ℂ (Fin R)) p.1) = d := by
    rw [Fintype.sum_prod_type_right]
    have : ∀ l, ∑ i, Complex.normSq (((b l : V) : EuclideanSpace ℂ (Fin R)) i) = 1 := by
      intro l
      have h1 : ‖((b l : V) : EuclideanSpace ℂ (Fin R))‖ = 1 := by
        rw [Submodule.norm_coe]; exact b.orthonormal.1 l
      have h2 := EuclideanSpace.norm_sq_eq ((b l : V) : EuclideanSpace ℂ (Fin R))
      rw [h1] at h2
      simp only [Complex.normSq_eq_norm_sq]
      linarith
    simp [this, hd]
  rw [Complex.normSq_eq_norm_sq, Fintype.sum_prod_type, hbasis] at hCS
  simp_rw [hpars] at hCS
  calc ‖∑ j, ∑ i, w j i * α i j‖ ^ 2 ≤ (∑ i, ‖∑ j, α i j • w j‖ ^ 2) * d := hCS
    _ ≤ (∑ i, ‖∑ j, α i j • w j‖ ^ 2) * n := by
        gcongr
    _ = n * ∑ i, ‖∑ j, α i j • w j‖ ^ 2 := by ring

/-! ### The Levi form of `log |G|²` -/

/-- For `f` complex differentiable at `x`, the Wirtinger derivative `∂_v f(x)` is `f'(x) v`. -/
theorem dDir_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    {x : E} (hf : DifferentiableAt ℂ f x) (v : E) : dDir v f x = fderiv ℂ f x v := by
  have h : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  simp only [dDir, h, ContinuousLinearMap.coe_restrictScalars', (fderiv ℂ f x).map_smul,
    smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `generatorNormSq G = ∑ᵢ normSq (Gᵢ)` as functions. -/
theorem generatorNormSq_eq_sum_normSq (G : Fin R → ComplexModel n → ℂ) :
    generatorNormSq G = fun y => ∑ i, Complex.normSq (G i y) := by
  funext y
  simp [generatorNormSq, Complex.normSq_eq_norm_sq]

/-- **The Levi form of `log |G|²`** (`skoda:levi-log`): with `ηᵢ = Gᵢ'(z) v` and
`S = |G(z)|² > 0`, `L_{log |G|²}(z)(v) = (S ∑ |ηᵢ|² - |∑ Ḡᵢ ηᵢ|²) / S²`. -/
theorem leviForm_log_normSq {G : Fin R → ComplexModel n → ℂ} {z : ComplexModel n}
    (hG : ∀ i, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G i) y) (hpos : 0 < generatorNormSq G z)
    (v : ComplexModel n) :
    leviForm (fun y => Real.log (generatorNormSq G y)) z v =
      (generatorNormSq G z * ∑ i, ‖fderiv ℂ (G i) z v‖ ^ 2 -
        ‖∑ i, conj (G i z) * fderiv ℂ (G i) z v‖ ^ 2) / generatorNormSq G z ^ 2 := by
  set S := generatorNormSq G with hSdef
  have hSf := generatorNormSq_eq_sum_normSq G
  have hterm : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (G i y)) z :=
    fun i => contDiffAt_normSq (hG i)
  have hS : ContDiffAt ℝ 2 S z := by
    rw [hSdef, hSf]
    exact ContDiffAt.sum fun i _ => hterm i
  rw [leviForm_log_of_pos hS hpos v]
  -- the Levi form of `S`
  have hone : ∀ i, (fun y => (fun _ : ComplexModel n => (1 : ℝ)) y ^ 2 *
      Complex.normSq (G i y)) = fun y => Complex.normSq (G i y) := by
    intro i; funext y; simp
  have hdelC : ∀ w : ComplexModel n, delC (fun _ : ComplexModel n => (1 : ℝ)) z w = 0 := by
    intro w; simp [delC]
  have hgamma : ∀ i (w : ComplexModel n),
      gammaTerm (fun _ : ComplexModel n => (1 : ℝ)) (G i) z w = fderiv ℂ (G i) z w := by
    intro i w; simp [gammaTerm, hdelC]
  have hLterm : ∀ i, leviForm (fun y => Complex.normSq (G i y)) z v =
      ‖fderiv ℂ (G i) z v‖ ^ 2 := by
    intro i
    have h := leviForm_sq_mul_normSq (c := fun _ : ComplexModel n => (1 : ℝ))
      contDiffAt_const (hG i) v
    rw [hone i] at h
    rw [h, hgamma, hdelC, Complex.normSq_eq_norm_sq]
    simp
  have hLS : leviForm S z v = ∑ i, ‖fderiv ℂ (G i) z v‖ ^ 2 := by
    rw [hSdef, hSf, leviForm_sum Finset.univ (fun i _ => hterm i) v]
    exact Finset.sum_congr rfl fun i _ => hLterm i
  -- the first derivatives of `S`
  have hdiff : ∀ i, DifferentiableAt ℝ (fun y => Complex.normSq (G i y)) z :=
    fun i => (hterm i).differentiableAt (by norm_num)
  have hdS : ∀ w, fderiv ℝ S z w = ∑ i, fderiv ℝ (fun y => Complex.normSq (G i y)) z w := by
    intro w
    rw [hSdef, hSf, fderiv_fun_sum fun i _ => hdiff i]
    simp
  have hcomb : ((fderiv ℝ S z v : ℝ) : ℂ) - Complex.I * ((fderiv ℝ S z (Complex.I • v) : ℝ) : ℂ) =
      2 * ∑ i, conj (G i z) * fderiv ℂ (G i) z v := by
    rw [hdS, hdS, Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := fderiv_sq_mul_normSq (c := fun _ : ComplexModel n => (1 : ℝ))
      contDiffAt_const (hG i) v
    rw [hone i, hgamma] at h
    rw [h]
    push_cast
    ring
  have hsq : (fderiv ℝ S z v) ^ 2 + (fderiv ℝ S z (Complex.I • v)) ^ 2 =
      4 * ‖∑ i, conj (G i z) * fderiv ℂ (G i) z v‖ ^ 2 := by
    have h := congrArg Complex.normSq hcomb
    have hl : Complex.normSq (((fderiv ℝ S z v : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ S z (Complex.I • v) : ℝ) : ℂ)) =
        (fderiv ℝ S z v) ^ 2 + (fderiv ℝ S z (Complex.I • v)) ^ 2 := by
      simp [Complex.normSq_apply]
      ring
    rw [hl, Complex.normSq_mul, show Complex.normSq 2 = 4 by norm_num,
      Complex.normSq_eq_norm_sq] at h
    exact h
  rw [hLS, hsq]
  field_simp

/-- `‖y - (⟪x, y⟫ / ‖x‖²) x‖² = ‖y‖² - |⟪x, y⟫|² / ‖x‖²`. -/
theorem norm_sq_sub_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (hx : x ≠ 0) :
    ‖y - (⟪x, y⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ)) • x‖ ^ 2 =
      ‖y‖ ^ 2 - ‖⟪x, y⟫_ℂ‖ ^ 2 / ‖x‖ ^ 2 := by
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  set c : ℂ := ⟪x, y⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ) with hc
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
  have hyx : ⟪y, x⟫_ℂ = conj ⟪x, y⟫_ℂ := by
    rw [← inner_conj_symm x y, RCLike.conj_conj]
  have hre : RCLike.re (c * ⟪y, x⟫_ℂ) = ‖⟪x, y⟫_ℂ‖ ^ 2 / ‖x‖ ^ 2 := by
    rw [hyx, hc, div_mul_eq_mul_div, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [show ((‖⟪x, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ) =
      ((‖⟪x, y⟫_ℂ‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hnc : ‖c‖ = ‖⟪x, y⟫_ℂ‖ / ‖x‖ ^ 2 := by
    rw [hc, norm_div, Complex.norm_real, Real.norm_of_nonneg hx2.le]
  rw [hre, hnc]
  field_simp
  ring

/-! ### Skoda's curvature inequality -/

/-- **Skoda's curvature inequality** (`skoda:curvature`): for `G` holomorphic near `z` with
`G(z) ≠ 0` and `α` in the kernel bundle at `z`, `B_z(α) ≤ n ∑ᵢ L_{log |G|²}(z)(αᵢ•)`. -/
theorem secondFundamental_le_leviForm {G : Fin R → ComplexModel n → ℂ} {z : ComplexModel n}
    (hG : ∀ i, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G i) y) (hpos : 0 < generatorNormSq G z)
    {α : Fin R → Fin n → ℂ} (hα : InKernel G z α) :
    secondFundamental G z α ≤
      n * vectorLevi (fun y => Real.log (generatorNormSq G y)) z α := by
  set S := generatorNormSq G z with hS
  set Gv : EuclideanSpace ℂ (Fin R) := WithLp.toLp 2 (fun i => G i z) with hGv
  have hGvS : ‖Gv‖ ^ 2 = S := by
    rw [EuclideanSpace.norm_sq_eq, hS, generatorNormSq]
  have hGv0 : Gv ≠ 0 := by
    intro h; rw [h, norm_zero] at hGvS; linarith [hGvS ▸ hpos]
  set dG : Fin n → EuclideanSpace ℂ (Fin R) := fun j =>
    WithLp.toLp 2 (fun i => fderiv ℂ (G i) z (coordVec j)) with hdG
  set c : Fin n → ℂ := fun j => ⟪Gv, dG j⟫_ℂ / ((‖Gv‖ ^ 2 : ℝ) : ℂ) with hc
  set w : Fin n → EuclideanSpace ℂ (Fin R) := fun j => dG j - c j • Gv with hw
  set η : Fin R → EuclideanSpace ℂ (Fin R) := fun i => ∑ j, α i j • dG j with hη
  -- the rows of `α` against the projected derivatives
  have hrow : ∀ i, ∑ j, α i j • w j =
      η i - (⟪Gv, η i⟫_ℂ / ((‖Gv‖ ^ 2 : ℝ) : ℂ)) • Gv := by
    intro i
    simp only [hw, hη, smul_sub, Finset.sum_sub_distrib, smul_smul, inner_sum,
      inner_smul_right, hc, Finset.sum_smul, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_div_assoc]
  -- the Levi form of each row
  have hlevi : ∀ i, leviForm (fun y => Real.log (generatorNormSq G y)) z
      (∑ j, α i j • coordVec j) = ‖∑ j, α i j • w j‖ ^ 2 / S := by
    intro i
    rw [leviForm_log_normSq hG hpos, hrow i, norm_sq_sub_proj Gv (η i) hGv0, hGvS]
    have hfd : ∀ i', fderiv ℂ (G i') z (∑ j, α i j • coordVec j) = (η i) i' := by
      intro i'
      simp [hη, hdG, map_sum, map_smul, WithLp.ofLp_sum]
    have hnη : ∑ i', ‖fderiv ℂ (G i') z (∑ j, α i j • coordVec j)‖ ^ 2 = ‖η i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i' _ => by rw [hfd]
    have hP : ∑ i', conj (G i' z) * fderiv ℂ (G i') z (∑ j, α i j • coordVec j) =
        ⟪Gv, η i⟫_ℂ := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i' _ => by
        rw [hfd]; simp [hGv, RCLike.inner_apply, mul_comm]
    rw [hnη, hP, ← hS]
    have hS0 : S ≠ 0 := hpos.ne'
    field_simp
  -- the trace term
  have hkp : kernelPairing G z α = ∑ j, ∑ i, w j i * α i j := by
    have h1 : kernelPairing G z α = ∑ j, ∑ i, dG j i * α i j := by
      rw [kernelPairing, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [dDir_eq_fderiv (hG i).self_of_nhds]
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hker : ∑ i, Gv i * α i j = 0 := hα j
    simp only [hw, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib]
    rw [show ∑ i, c j * Gv i * α i j = c j * ∑ i, Gv i * α i j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hker]
    simp
  have hP := norm_sq_sum_dotProduct_le w α
  rw [← hkp] at hP
  rw [secondFundamental, vectorLevi, ← hS]
  simp_rw [hlevi]
  rw [← Finset.sum_div, mul_div_assoc']
  exact div_le_div_of_nonneg_right hP hpos.le

end SGPT.Okounkov.TranscendentalSkoda
