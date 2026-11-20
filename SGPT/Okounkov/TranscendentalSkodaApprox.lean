import SGPT.Okounkov.TranscendentalSkodaHilbert

/-!
# Skoda's theorem: removing `∂̄ α` (Step 3 of the kernel-bundle estimate)

Blueprint `claude-tok-skoda`, node `skoda:twisted-hormander`, Step 3.

For a test form `α` let `β = π_W(α)` be its orthogonal projection onto the closed subspace `W` of
kernel-valued forms with weakly `∂̄`-closed rows. Testing against `h = P_S h + P_Q h` for vector
test functions (`P_S h` kernel-valued, `P_Q h = Ḡ c`) shows that every row of `β` satisfies
`T* βᵢ = γᵢ` weakly (`weak_tstar_rows`), with

`γ = P_S T* α + e^{-ψ₀} (∑ₖⱼ ∂ⱼGₖ βₖⱼ) ρ`, `ρ = Ḡ/|G|²` (`gammaFun`).

TN's density theorem (Hörmander's Lemma 4.1.3) applied row by row gives test forms `αₘ → β`
with `T* αₘ → γ` and `∂̄ αₘ → 0`; then `P_S T* αₘ → P_S γ = P_S T* α` and, by the projection
calculus, `∂̄ (P_S αₘ) → (∂̄ P_S) β = 0` (`exists_approx`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density
open scoped Topology ComplexConjugate ContDiff ENNReal InnerProductSpace

variable {n R : ℕ}

theorem contDiffOn_dDir {D : Set (ComplexModel n)} (hD : IsOpen D) {F : ComplexModel n → ℂ}
    (hF : ContDiffOn ℝ ∞ F D) (v : ComplexModel n) : ContDiffOn ℝ ∞ (dDir v F) D := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x) D := hF.fderiv_of_isOpen hD (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x v) D := h1.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (Complex.I • v)) D :=
    h1.clm_apply contDiffOn_const
  have : dDir v F = fun x => (fderiv ℝ F x v - Complex.I * fderiv ℝ F x (Complex.I • v)) / 2 :=
    rfl
  rw [this]
  exact (h2.sub (contDiffOn_const.mul h3)).div_const 2

namespace KernelL2Data

variable (d : KernelL2Data n R)

theorem ae_mem (w : ComplexModel n → ℝ) : ∀ᵐ x ∂(weightedVolume d.L w), x ∈ d.L :=
  ae_mem_weightedVolume d.isOpen w

/-- The rows `βᵢⱼ` of an element of `H₂`. -/
def rows (β : d.H₂) (i : Fin R) (j : Fin n) (x : ComplexModel n) : ℂ := (β i x) j

theorem memLp_rows (β : d.H₂) (i : Fin R) (j : Fin n) : MemLp (d.rows β i j) 2 d.μ₂ :=
  memLp_component (β i) j

theorem rows_inKernel {β : d.H₂} (hβ : β ∈ kernelSubmodule d.G d.μ₂) :
    ∀ᵐ x ∂d.μ₂, ∀ j, ∑ i, d.G i x * d.rows β i j x = 0 := by
  filter_upwards [hβ] with x hx j
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v j) hx
  simpa [rows] using h

theorem continuousOn_dDir_G (k : Fin R) (j : Fin n) :
    ContinuousOn (dDir (coordVec j) (d.G k)) d.L :=
  (contDiffOn_dDir d.isOpen (contDiffOn_real_of_holo d.isOpen (d.G_holo k)) _).continuousOn

/-- `K(β) = ∑ₖⱼ ∂ⱼGₖ βₖⱼ`. -/
def kerPair (β : d.H₂) (x : ComplexModel n) : ℂ :=
  kernelPairing d.G x fun k j => d.rows β k j x

/-- `e^{-ψ₀} K(β)`. -/
def expKerPair (β : d.H₂) (x : ComplexModel n) : ℂ :=
  ((Real.exp (-d.ψ₀ x) : ℝ) : ℂ) * d.kerPair β x

theorem aesm_rows_restrict (β : d.H₂) (k : Fin R) (j : Fin n) :
    AEStronglyMeasurable (d.rows β k j) (volume.restrict d.L) :=
  (aestronglyMeasurable_weightedVolume_iff d.isOpen d.w₂_cont).mp (d.memLp_rows β k j).1

theorem norm_kerPair_le (β : d.H₂) {x : ComplexModel n} (hx : x ∈ d.L) :
    ‖d.kerPair β x‖ ≤ d.CdG * ∑ k, ∑ j, ‖d.rows β k j x‖ := by
  rw [kerPair, kernelPairing, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (d.dG_bound x hx k j) (norm_nonneg _)

theorem memLp_expKerPair (β : d.H₂) : MemLp (d.expKerPair β) 2 d.μ₁ := by
  have hb : MemLp (fun x => d.CdG * ∑ k, ∑ j, ‖d.rows β k j x‖) 2 d.μ₂ :=
    (memLp_finsetSum _ fun k _ => memLp_finsetSum _ fun j _ =>
      (d.memLp_rows β k j).norm).const_mul _
  refine memLp_weightedVolume_of_sq_le d.isOpen d.w₁_cont d.w₂_cont ?_ hb fun x hx => ?_
  · have hK : AEStronglyMeasurable (d.kerPair β) (volume.restrict d.L) := by
      have e : d.kerPair β = fun x => ∑ k, ∑ j, dDir (coordVec j) (d.G k) x * d.rows β k j x :=
        rfl
      rw [e]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          ((d.continuousOn_dDir_G k j).aestronglyMeasurable d.isOpen.measurableSet).mul
            (d.aesm_rows_restrict β k j)
    exact (((Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
      d.ψ_smooth.continuousOn.neg)).aestronglyMeasurable d.isOpen.measurableSet)).mul hK
  · have hK := d.norm_kerPair_le β hx
    have hK0 : 0 ≤ ‖d.kerPair β x‖ := norm_nonneg _
    have hsq : ‖d.kerPair β x‖ ^ 2 ≤ ‖d.CdG * ∑ k, ∑ j, ‖d.rows β k j x‖‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      exact pow_le_pow_left₀ hK0 hK 2
    have he : ‖d.expKerPair β x‖ ^ 2 * Real.exp (-d.w₁ x) =
        ‖d.kerPair β x‖ ^ 2 * Real.exp (-(d.Φ x + d.χ x)) := by
      rw [expKerPair, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        mul_pow, ← Real.exp_nat_mul, mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
      congr 2
      simp only [w₁, w₃]
      push_cast
      ring
    rw [he]
    have hexp : Real.exp (-(d.Φ x + d.χ x)) ≤ Real.exp (-d.w₂ x) :=
      Real.exp_le_exp.mpr (by simp only [w₂, w₃]; linarith [d.ψ_nonneg x])
    calc ‖d.kerPair β x‖ ^ 2 * Real.exp (-(d.Φ x + d.χ x))
        ≤ ‖d.CdG * ∑ k, ∑ j, ‖d.rows β k j x‖‖ ^ 2 * Real.exp (-(d.Φ x + d.χ x)) :=
          mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)

/-- `γᵢ = (P_S T* α)ᵢ + e^{-ψ₀} K(β) ρᵢ`. -/
def gammaFun (α : Fin R → testForms d.L) (β : d.H₂) (i : Fin R) (x : ComplexModel n) : ℂ :=
  d.sTstar α i x + d.expKerPair β x * normalDir d.G i x

theorem memLp_gammaFun (α : Fin R → testForms d.L) (β : d.H₂) (i : Fin R) :
    MemLp (d.gammaFun α β i) 2 d.μ₁ := by
  refine (d.memLp_sTstar α i).add ?_
  refine (d.memLp_expKerPair β).of_le_mul (c := d.Cρ) ((d.memLp_expKerPair β).1.mul
    (d.aesm_of_continuousOn (contDiffOn_normalDir d.isOpen d.G_holo d.pos i).continuousOn)) ?_
  filter_upwards [d.ae_mem d.w₁] with x hx
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (d.ρ_bound x hx i) (norm_nonneg _)

theorem kernelProj_gammaFun (α : Fin R → testForms d.L) (β : d.H₂) {x : ComplexModel n}
    (hx : x ∈ d.L) :
    kernelProj d.G x (fun k => d.gammaFun α β k x) =
      kernelProj d.G x (fun k => tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ) x) := by
  have e : (fun k => d.gammaFun α β k x) = fun k => d.sTstar α k x +
      (d.expKerPair β x * (((generatorNormSq d.G x)⁻¹ : ℝ) : ℂ)) * conj (d.G k x) := by
    funext k; simp only [gammaFun, normalDir]; ring
  rw [e, kernelProj_add_conj d.G (d.pos x hx)]
  exact kernelProj_kernelProj d.G (d.pos x hx) _

/-- The `∂̄`-energy of the projection `P_S α`, the term removed in Step 3. -/
def Qfun (α : Fin R → testForms d.L) : ℝ :=
  ∑ i, ∫ x, (∑ p, ‖dbarForm (kernelProjForm d.G
    (fun k => (α k : Fin n → ComplexModel n → ℂ)) i) p x‖ ^ 2) * Real.exp (-d.w₃ x)

/-- **The rows of `β = π_W(α)` satisfy `T* βᵢ = γᵢ` weakly** (Step 3 of
`skoda:twisted-hormander`), in the form of TN's density statement. -/
theorem weak_tstar_rows (α : Fin R → testForms d.L) {β : d.H₂}
    (hβS : β ∈ kernelSubmodule d.G d.μ₂) (horth : d.aMap α - β ∈ d.Wᗮ) (i : Fin R)
    (g : ComplexModel n → ℂ) (hg : IsTestFunctionOn d.L g) :
    ∑ j, ∫ x in d.L, conj (dbarDir (coordVec j) g x) * d.rows β i j x *
        Real.exp (-(d.w₃ x - d.ψ₀ x)) =
      ∫ x in d.L, conj (g x) * d.gammaFun α β i x * Real.exp (-(d.w₃ x - 2 * d.ψ₀ x)) := by
  -- the decomposition `g eᵢ = hS + hQ`, `hS` kernel-valued and `hQ = Ḡ c`
  set s' : ComplexModel n → ℂ := fun y => (((generatorNormSq d.G y)⁻¹ : ℝ) : ℂ) with hs'
  have hs'smooth : ContDiffOn ℝ ∞ s' d.L :=
    contDiffOn_inv_generatorNormSq d.isOpen d.G_holo d.pos
  set cf : ComplexModel n → ℂ := fun y => (d.G i y * s' y) * g y with hcf
  have hcf_test : IsTestFunctionOn d.L cf := IsTestFunctionOn.mul_left d.isOpen
    ((contDiffOn_real_of_holo d.isOpen (d.G_holo i)).mul hs'smooth) hg
  set e : Fin R → ComplexModel n → ℂ := fun k y => if k = i then g y else 0 with he
  have he_test : ∀ k, IsTestFunctionOn d.L (e k) := fun k => by
    by_cases hk : k = i
    · simp only [he, hk, if_true]; exact hg
    · simp only [he, hk, if_false]; exact isTestFunctionOn_zero
  set hQ : Fin R → ComplexModel n → ℂ := fun k y => conj (d.G k y) * cf y with hhQ
  have hQ_test : ∀ k, IsTestFunctionOn d.L (hQ k) := fun k =>
    IsTestFunctionOn.mul_left d.isOpen (contDiffOn_conj_of_holo d.isOpen (d.G_holo k)) hcf_test
  set hS : Fin R → ComplexModel n → ℂ := fun k y => e k y - hQ k y with hhS
  have hS_test : ∀ k, IsTestFunctionOn d.L (hS k) := fun k =>
    IsTestFunctionOn.sub' (he_test k) (hQ_test k)
  have hSker : ∀ x ∈ d.L, ∑ k, d.G k x * hS k x = 0 := by
    intro x hx
    have hsum := sum_mul_normalDir d.G (d.pos x hx)
    have h1 : ∑ k, d.G k x * e k x = d.G i x * g x := by simp [he, mul_ite]
    have h2 : ∑ k, d.G k x * hQ k x = d.G i x * g x := by
      have : ∑ k, d.G k x * hQ k x = (∑ k, d.G k x * normalDir d.G k x) * (d.G i x * g x) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by simp only [hhQ, hcf, normalDir, hs']; ring
      rw [this, hsum, one_mul]
    simp only [hhS, mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
  -- integrability
  have hβr : ∀ k j, MemLp (d.rows β k j) 2 d.μ₂ := d.memLp_rows β
  have hdS : ∀ k j, MemLp (dbarDir (coordVec j) (hS k)) 2 d.μ₂ := fun k j =>
    memLp_test d.isOpen d.w₂_cont ((hS_test k).dbarDir _)
  have hdQ : ∀ k j, MemLp (dbarDir (coordVec j) (hQ k)) 2 d.μ₂ := fun k j =>
    memLp_test d.isOpen d.w₂_cont ((hQ_test k).dbarDir _)
  -- (1) the left side as a `μ₂`-integral
  have hL1 : ∀ j, ∫ x in d.L, conj (dbarDir (coordVec j) g x) * d.rows β i j x *
      Real.exp (-(d.w₃ x - d.ψ₀ x)) =
      ∫ x, conj (dbarDir (coordVec j) g x) * d.rows β i j x ∂d.μ₂ := by
    intro j
    rw [integral_weightedVolume d.isOpen d.w₂_cont]
    refine setIntegral_congr_fun d.isOpen.measurableSet fun x _ => ?_
    simp only [Complex.real_smul, w₂]
    ring
  -- (2) splitting `g eᵢ = hS + hQ`
  have hsplit : ∀ k j, ∫ x, conj (dbarDir (coordVec j) (e k) x) * d.rows β k j x ∂d.μ₂ =
      ∫ x, conj (dbarDir (coordVec j) (hS k) x) * d.rows β k j x ∂d.μ₂ +
        ∫ x, conj (dbarDir (coordVec j) (hQ k) x) * d.rows β k j x ∂d.μ₂ := by
    intro k j
    rw [← integral_add (integrable_conj_mul (hdS k j) (hβr k j))
      (integrable_conj_mul (hdQ k j) (hβr k j))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hek : e k = fun y => hS k y + hQ k y := by funext y; simp [hhS]
    have hdx : dbarDir (coordVec j) (e k) x =
        dbarDir (coordVec j) (hS k) x + dbarDir (coordVec j) (hQ k) x := by
      rw [hek, dbarDir_add ((isTestFunctionOn_contDiff_one (hS_test k)).differentiable
        one_ne_zero x) ((isTestFunctionOn_contDiff_one (hQ_test k)).differentiable
          one_ne_zero x)]
    simp only [hdx, map_add, add_mul]
  have hsum_e : ∀ j, ∑ k, ∫ x, conj (dbarDir (coordVec j) (e k) x) * d.rows β k j x ∂d.μ₂ =
      ∫ x, conj (dbarDir (coordVec j) g x) * d.rows β i j x ∂d.μ₂ := by
    intro j
    rw [Finset.sum_eq_single i]
    · simp only [he, if_true]
    · intro k _ hk
      simp only [he, hk, if_false, dbarDir_const, map_zero, zero_mul, integral_zero]
    · simp
  -- (3) the kernel part: `∂̄ hS ∈ W`
  set hvS : Fin R → testForms d.L := fun k => dbarTest (hS_test k) with hhvS
  have hW : d.aMap hvS ∈ d.W := by
    refine ⟨?_, fun k => formToL2_dbarTest_mem_closedForms d.isOpen d.w₂_smooth (hS_test k)⟩
    rw [SetLike.mem_coe, mem_kernelSubmodule_iff]
    have hae := ae_all_iff.mpr fun k => (memLp_formVec d.isOpen d.w₂_cont (hvS k).2).coeFn_toLp
    filter_upwards [hae, d.ae_mem d.w₂] with x hx hxL
    have hx' : ∀ k, (d.aMap hvS k : ComplexModel n → EuclideanSpace ℂ (Fin n)) x =
        formVec (hvS k : Fin n → ComplexModel n → ℂ) x := hx
    simp only [hx']
    refine PiLp.ext fun j => ?_
    have h0 := sum_mul_dbarDir_of_inKernel d.isOpen d.G_holo
      (fun k => isTestFunctionOn_contDiff_one (hS_test k)) hSker hxL (coordVec j)
    simpa [formVec, hhvS, dbarTest] using h0
  have h3a : ⟪d.aMap hvS, β⟫_ℂ =
      ∑ k, ∑ j, ∫ x, conj (dbarDir (coordVec j) (hS k) x) * d.rows β k j x ∂d.μ₂ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (d.aMap hvS).ofLp k = formToL2 d.isOpen d.w₂_cont (hvS k) from rfl, inner_formToL2]
    rfl
  have h3b : ⟪d.aMap hvS, β⟫_ℂ = ⟪d.aMap hvS, d.aMap α⟫_ℂ := by
    have h0 := Submodule.inner_right_of_mem_orthogonal hW horth
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0.symm
  have h3c : ⟪d.aMap hvS, d.aMap α⟫_ℂ =
      ∑ k, ∫ x, conj (hS k x) * tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ) x
        ∂d.μ₁ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (d.aMap hvS).ofLp k = formToL2 d.isOpen d.w₂_cont (hvS k) from rfl,
      show (d.aMap α).ofLp k = formToL2 d.isOpen d.w₂_cont (α k) from rfl]
    have h2 := (weakDbarEq_iff_inner d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn d.h12
      (memLp_test d.isOpen d.w₁_cont (hS_test k)) (hdS k)).mp (weakDbarEq_dbarTest (hS_test k))
      (α k)
    have h3 : ⟪formToL2 d.isOpen d.w₂_cont (hvS k), formToL2 d.isOpen d.w₂_cont (α k)⟫_ℂ =
        ⟪(memLp_test d.isOpen d.w₁_cont (hS_test k)).toLp (hS k),
          tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α k)⟫_ℂ := by
      rw [← inner_conj_symm, ← inner_conj_symm ((memLp_test d.isOpen d.w₁_cont
        (hS_test k)).toLp (hS k))]
      congr 1
      exact h2.symm
    rw [h3, inner_toLp_eq_integral]
    have hA : tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α k) =
        (memLp_tstarForm d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α k).2).toLp _ :=
      rfl
    rw [hA]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_tstarForm d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn
      (α k).2).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h3d : ∑ k, ∫ x, conj (hS k x) * tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ) x
      ∂d.μ₁ = ∫ x, ∑ k, conj (hS k x) * d.sTstar α k x ∂d.μ₁ := by
    rw [← integral_finsetSum _ fun k _ => integrable_conj_mul
      (memLp_test d.isOpen d.w₁_cont (hS_test k)) (d.memLp_tstar α k)]
    refine integral_congr_ae ?_
    filter_upwards [d.ae_mem d.w₁] with x hx
    exact (sum_conj_mul_kernelProj d.G x (hSker x hx) _).symm
  -- (4) the normal part
  have h4 : ∑ k, ∑ j, ∫ x, conj (dbarDir (coordVec j) (hQ k) x) * d.rows β k j x ∂d.μ₂ =
      ∫ x, conj (cf x) * d.expKerPair β x ∂d.μ₁ := by
    have hint : ∀ k j, Integrable
        (fun x => conj (dbarDir (coordVec j) (hQ k) x) * d.rows β k j x) d.μ₂ :=
      fun k j => integrable_conj_mul (hdQ k j) (hβr k j)
    rw [Finset.sum_congr rfl fun k _ => (integral_finsetSum _ fun j _ => hint k j).symm,
      ← integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j]
    have hpt : ∀ᵐ x ∂d.μ₂, ∑ k, ∑ j, conj (dbarDir (coordVec j) (hQ k) x) * d.rows β k j x =
        conj (cf x) * d.kerPair β x := by
      filter_upwards [d.rows_inKernel hβS, d.ae_mem d.w₂] with x hker hx
      have hcd : DifferentiableAt ℝ cf x :=
        (isTestFunctionOn_contDiff_one hcf_test).differentiable one_ne_zero x
      have hd : ∀ k j, dbarDir (coordVec j) (hQ k) x =
          conj (dDir (coordVec j) (d.G k) x) * cf x +
            conj (d.G k x) * dbarDir (coordVec j) cf x :=
        fun k j => dbarDir_conj_mul d.isOpen (d.G_holo k) hx hcd _
      simp only [hd, map_add, map_mul, Complex.conj_conj, add_mul, Finset.sum_add_distrib]
      have hz : ∑ k, ∑ j, d.G k x * conj (dbarDir (coordVec j) cf x) * d.rows β k j x = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [show ∑ k, d.G k x * conj (dbarDir (coordVec j) cf x) * d.rows β k j x =
          conj (dbarDir (coordVec j) cf x) * ∑ k, d.G k x * d.rows β k j x by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hker j, mul_zero]
      rw [hz, add_zero, kerPair, kernelPairing, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [integral_congr_ae hpt, integral_weightedVolume d.isOpen d.w₂_cont,
      integral_weightedVolume d.isOpen d.w₁_cont]
    refine setIntegral_congr_fun d.isOpen.measurableSet fun x _ => ?_
    have hexp : Real.exp (-d.w₂ x) = Real.exp (-d.w₁ x) * Real.exp (-d.ψ₀ x) := by
      rw [← Real.exp_add]; congr 1; simp only [w₂, w₁]; ring
    simp only [expKerPair, Complex.real_smul, hexp]
    push_cast
    ring
  -- (5) the right side
  have h5 : ∫ x in d.L, conj (g x) * d.gammaFun α β i x * Real.exp (-(d.w₃ x - 2 * d.ψ₀ x)) =
      ∫ x, ∑ k, conj (hS k x) * d.sTstar α k x ∂d.μ₁ +
        ∫ x, conj (cf x) * d.expKerPair β x ∂d.μ₁ := by
    have hi1 : Integrable (fun x => ∑ k, conj (hS k x) * d.sTstar α k x) d.μ₁ :=
      integrable_finsetSum _ fun k _ => integrable_conj_mul
        (memLp_test d.isOpen d.w₁_cont (hS_test k)) (d.memLp_sTstar α k)
    have hi2 : Integrable (fun x => conj (cf x) * d.expKerPair β x) d.μ₁ :=
      integrable_conj_mul (memLp_test d.isOpen d.w₁_cont hcf_test) (d.memLp_expKerPair β)
    rw [← integral_add hi1 hi2, integral_weightedVolume d.isOpen d.w₁_cont]
    refine setIntegral_congr_fun d.isOpen.measurableSet fun x hx => ?_
    have hT0 : ∑ k, d.G k x * d.sTstar α k x = 0 := sum_mul_kernelProj d.G (d.pos x hx) _
    have hA : ∑ k, conj (hS k x) * d.sTstar α k x =
        conj (g x) * d.sTstar α i x - conj (cf x) * ∑ k, d.G k x * d.sTstar α k x := by
      simp only [hhS, hhQ, map_sub, map_mul, Complex.conj_conj, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · simp [he, apply_ite conj]
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Complex.real_smul]
    rw [hA, hT0, mul_zero, sub_zero]
    simp only [gammaFun, normalDir, hcf, hs', map_mul, Complex.conj_ofReal, w₁]
    ring
  -- assembly
  calc ∑ j, ∫ x in d.L, conj (dbarDir (coordVec j) g x) * d.rows β i j x *
        Real.exp (-(d.w₃ x - d.ψ₀ x))
      = ∑ j, ∑ k, ∫ x, conj (dbarDir (coordVec j) (e k) x) * d.rows β k j x ∂d.μ₂ :=
        Finset.sum_congr rfl fun j _ => (hL1 j).trans (hsum_e j).symm
    _ = ∑ k, ∑ j, (∫ x, conj (dbarDir (coordVec j) (hS k) x) * d.rows β k j x ∂d.μ₂ +
          ∫ x, conj (dbarDir (coordVec j) (hQ k) x) * d.rows β k j x ∂d.μ₂) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hsplit k j
    _ = ⟪d.aMap hvS, β⟫_ℂ + ∫ x, conj (cf x) * d.expKerPair β x ∂d.μ₁ := by
        rw [h3a, ← h4]; simp only [Finset.sum_add_distrib]
    _ = _ := by rw [h3b, h3c, h3d, h5]

/-- The rows of an element of `Wcl` are weakly `∂̄`-closed, in the form of TN's density
statement. -/
theorem weak_closed_rows {β : d.H₂} (hβ : β ∈ d.Wcl) (i : Fin R) :
    ∀ h, IsTestFunctionOn d.L h → ∀ j k,
      ∫ x, (d.rows β i k x * dbarDir (coordVec j) h x - d.rows β i j x * dbarDir (coordVec k) h x) =
        - ∫ x, (0 : Fin n × Fin n → ComplexModel n → ℂ) (j, k) x * h x := by
  intro h hh j k
  have h0 := (mem_closedForms_iff d.isOpen d.w₂_smooth (β i)).mp (hβ i) h hh j k
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]
  exact h0

/-- The pointwise bound behind `∂̄ (P_S αₘ) → 0`: for a kernel-valued `β` and test forms `α'`,
`|∂̄(P_S α')ᵢ| ≤ C (∑ₖ |∂̄ α'ₖ| + ∑ₖ |α'ₖ - βₖ|)` on `L`. -/
theorem norm_dbarForm_kernelProjForm_le {α' : Fin R → Fin n → ComplexModel n → ℂ}
    (hα' : ∀ k, α' k ∈ testForms d.L) {β : d.H₂} {x : ComplexModel n} (hx : x ∈ d.L)
    (hker : ∀ j, ∑ k, d.G k x * d.rows β k j x = 0) (i : Fin R) (p : Fin n × Fin n) :
    ‖dbarForm (kernelProjForm d.G α' i) p x‖ ≤ (2 + |d.Cdρ| * |d.CG|) *
      (∑ k, ‖dbarForm (α' k) p x‖ + (∑ k, ‖α' k p.2 x - d.rows β k p.2 x‖ +
        ∑ k, ‖α' k p.1 x - d.rows β k p.1 x‖)) := by
  have hc1 : ∀ k j, ContDiff ℝ 1 (α' k j) := fun k j => isTestFunctionOn_contDiff_one (hα' k j)
  rw [dbarForm_kernelProjForm d.isOpen d.G_holo d.pos hc1 hx i p]
  have hcl : ∀ l, ∑ k, d.G k x * α' k l x = ∑ k, d.G k x * (α' k l x - d.rows β k l x) := by
    intro l
    simp only [mul_sub, Finset.sum_sub_distrib, hker l, sub_zero]
  have hbd : ∀ (l : Fin n) (v : ComplexModel n), ‖dbarDir v (normalDir d.G i) x‖ ≤ |d.Cdρ| →
      ‖dbarDir v (normalDir d.G i) x * ∑ k, d.G k x * α' k l x‖ ≤
        |d.Cdρ| * |d.CG| * ∑ k, ‖α' k l x - d.rows β k l x‖ := by
    intro l v hv
    rw [hcl l, norm_mul, mul_assoc]
    refine mul_le_mul hv ?_ (norm_nonneg _) (abs_nonneg _)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((d.G_bound x hx k).trans (le_abs_self _)) (norm_nonneg _)
  have h1 := hbd p.2 (coordVec p.1) ((d.dρ_bound x hx i p.1).trans (le_abs_self _))
  have h2 := hbd p.1 (coordVec p.2) ((d.dρ_bound x hx i p.2).trans (le_abs_self _))
  have h3 := norm_kernelProj_le d.G x (fun k => dbarForm (α' k) p x) i
  have hA0 : 0 ≤ ∑ k, ‖dbarForm (α' k) p x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : 0 ≤ ∑ k, ‖α' k p.2 x - d.rows β k p.2 x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC0 : 0 ≤ ∑ k, ‖α' k p.1 x - d.rows β k p.1 x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK0 : 0 ≤ |d.Cdρ| * |d.CG| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc ‖kernelProj d.G x (fun k => dbarForm (α' k) p x) i -
        (dbarDir (coordVec p.1) (normalDir d.G i) x * ∑ k, d.G k x * α' k p.2 x -
          dbarDir (coordVec p.2) (normalDir d.G i) x * ∑ k, d.G k x * α' k p.1 x)‖
      ≤ ‖kernelProj d.G x (fun k => dbarForm (α' k) p x) i‖ +
          (‖dbarDir (coordVec p.1) (normalDir d.G i) x * ∑ k, d.G k x * α' k p.2 x‖ +
            ‖dbarDir (coordVec p.2) (normalDir d.G i) x * ∑ k, d.G k x * α' k p.1 x‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ 2 * ∑ k, ‖dbarForm (α' k) p x‖ + (|d.Cdρ| * |d.CG| *
          ∑ k, ‖α' k p.2 x - d.rows β k p.2 x‖ +
            |d.Cdρ| * |d.CG| * ∑ k, ‖α' k p.1 x - d.rows β k p.1 x‖) := by gcongr
    _ ≤ _ := by nlinarith

/-- **Approximation** (Step 3 of `skoda:twisted-hormander`): for every test form `α` there are
test forms `αₘ` with `αₘ → π_W(α)` in `H₂`, `P_S T* αₘ → P_S T* α` in `H₁` and
`∂̄ (P_S αₘ) → 0`. -/
theorem exists_approx (α : Fin R → testForms d.L) :
    ∃ αs : ℕ → Fin R → testForms d.L,
      Tendsto (fun m => d.aMap (αs m)) atTop (𝓝 (d.W.starProjection (d.aMap α))) ∧
      Tendsto (fun m => d.AMap (αs m)) atTop (𝓝 (d.AMap α)) ∧
      Tendsto (fun m => d.Qfun (αs m)) atTop (𝓝 0) := by
  set β := d.W.starProjection (d.aMap α) with hβdef
  have hβW : β ∈ d.W := d.W.starProjection_apply_mem _
  have horth : d.aMap α - β ∈ d.Wᗮ := d.W.sub_starProjection_mem_orthogonal _
  have hβS : β ∈ kernelSubmodule d.G d.μ₂ := hβW.1
  have hβcl : β ∈ d.Wcl := hβW.2
  have hden := fun i => hormanderDensityStatement n d.L d.isOpen d.w₃ d.ψ₀ d.w₃_smooth
    d.ψ_smooth d.ψ_nonneg d.η d.η_test d.η_ev d.η_grad (d.rows β i) (d.gammaFun α β i) 0
    (fun j => d.memLp_rows β i j) (d.memLp_gammaFun α β i) (fun _ => MemLp.zero)
    (d.weak_tstar_rows α hβS horth i) (d.weak_closed_rows hβcl i)
  choose βs hβs c1 c2 c3 using hden
  set αs : ℕ → Fin R → testForms d.L := fun m i => ⟨βs i m, hβs i m⟩ with hαs
  refine ⟨αs, ?_, ?_, ?_⟩
  · -- `αₘ → β`
    have e : β = WithLp.toLp 2 (fun i => β i) := rfl
    rw [e]
    exact ((PiLp.continuous_toLp 2 _).tendsto _).comp
      (tendsto_pi_nhds.mpr fun i => tendsto_formToL2 d.isOpen d.w₂_cont (βs := fun m => αs m i)
        (c1 i))
  · -- `P_S T* αₘ → P_S T* α`
    refine ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.mpr fun i => ?_)
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m => d.memLp_sTstar (αs m) i) _
      (d.memLp_sTstar α i)).mpr ?_
    refine tendsto_eLpNorm_of_le_sum (C := 2)
      (f := fun m k x => tstarForm d.w₂ d.ψ₀ (βs k m) x - d.gammaFun α β k x)
      (fun m k => ((d.memLp_tstar (αs m) k).1).sub (d.memLp_gammaFun α β k).1)
      (fun m => ?_) (fun k => c2 k)
    filter_upwards [d.ae_mem d.w₁] with x hx
    have e1 : (d.sTstar (αs m) i - d.sTstar α i) x = kernelProj d.G x
        (fun k => tstarForm d.w₂ d.ψ₀ (βs k m) x - d.gammaFun α β k x) i := by
      rw [Pi.sub_apply, kernelProj_sub, d.kernelProj_gammaFun α β hx]
      rfl
    rw [e1]
    exact norm_kernelProj_le _ _ _ _
  · -- `∂̄ (P_S αₘ) → 0`
    have hac : d.μ₃ ≪ d.μ₂ := Measure.absolutelyContinuous_of_le d.μ₃_le_μ₂
    have hker₃ : ∀ᵐ x ∂d.μ₃, ∀ j, ∑ k, d.G k x * d.rows β k j x = 0 :=
      hac.ae_le (d.rows_inKernel hβS)
    have hi : ∀ i, Tendsto (fun m => ∫ x, (∑ p, ‖dbarForm (kernelProjForm d.G
        (fun k => βs k m) i) p x‖ ^ 2) * Real.exp (-d.w₃ x)) atTop (𝓝 0) := by
      intro i
      have hmem : ∀ m, kernelProjForm d.G (fun k => βs k m) i ∈ testForms d.L := fun m =>
        kernelProjForm_mem d.isOpen d.G_holo d.pos (fun k => (αs m k).2) i
      refine tendsto_dbarEnergy d.isOpen d.w₃_cont (βs := fun m => ⟨_, hmem m⟩) fun p => ?_
      simp only [Pi.zero_apply, sub_zero]
      refine tendsto_eLpNorm_of_le_sum (C := 2 + |d.Cdρ| * |d.CG|)
        (f := fun m => Sum.elim (fun k x => dbarForm (βs k m) p x)
          (Sum.elim (fun k x => βs k m p.2 x - d.rows β k p.2 x)
            (fun k x => βs k m p.1 x - d.rows β k p.1 x)))
        (fun m q => ?_) (fun m => ?_) (fun q => ?_)
      · rcases q with k | k | k
        · exact (continuous_dbarForm (αs m k).2 p).aestronglyMeasurable
        · exact ((hβs k m p.2).1.continuous.aestronglyMeasurable).sub
            ((d.memLp_rows β k p.2).1.mono_ac hac)
        · exact ((hβs k m p.1).1.continuous.aestronglyMeasurable).sub
            ((d.memLp_rows β k p.1).1.mono_ac hac)
      · filter_upwards [d.ae_mem d.w₃, hker₃] with x hx hkx
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        exact d.norm_dbarForm_kernelProjForm_le (fun k => (αs m k).2) hx hkx i p
      · rcases q with k | k | k
        · simpa only [Sum.elim_inl, Pi.zero_apply, sub_zero] using c3 k p
        · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (c1 k p.2)
            (fun _ => zero_le) fun m => eLpNorm_mono_measure _ d.μ₃_le_μ₂
        · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (c1 k p.1)
            (fun _ => zero_le) fun m => eLpNorm_mono_measure _ d.μ₃_le_μ₂
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin R)) fun i _ => hi i
    rw [Finset.sum_const_zero] at h
    exact h

end KernelL2Data

end SGPT.Okounkov.TranscendentalSkoda
