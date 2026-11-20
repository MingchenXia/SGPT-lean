import SGPT.Foundations.Analysis.Pending.PolydiskMobiusSemiconcave
import SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity

/-!
# Jacobians of the polydisk automorphisms and the second differences of a density

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`,
Step 2, the estimate on the data, transposed from the ball to the unit polydisk
`P = {z : ∀ i, |zᵢ| < 1}` (route: `claude-ma-dir2.tex`). The automorphisms are TN's
coordinatewise Möbius maps `T_{a,h} = M_{-(a+h)} ∘ M_a` (`polydiskAut`, `T_{a,h}(a) = a + h`,
`T_{a,0} = id`). A biholomorphism multiplies the Monge–Ampère density by the squared modulus of
its complex Jacobian determinant, so for a density `Fⁿ` the transported density is
`((F ∘ T_{a,h}) · |J_{a,h}|^{2/n})ⁿ` (`polydiskDensity`).

* `mobDeriv`, `hasDerivAt_discMobius`: `M_c'(w) = (1 - |c|²)/(1 - c̄ w)²`.
* `jacobianMatrix_polydiskAut`: the complex Jacobian matrix of `T_{a,h}` is diagonal, with the
  derivatives of the coordinate Möbius maps on the diagonal.
* `exists_polydiskDensity_secondDifference` (FPT Step 2, first claimed inequality): for `F` of
  class `C²` and `ρ < 1` there is `M` with
  `½ ((F ∘ T_{a,h})|J_{a,h}|^{2/n} + (F ∘ T_{a,-h})|J_{a,-h}|^{2/n}) ≥ F - M |h|²` on `P`,
  for all `a, a ± h` with coordinates of modulus `≤ ρ`.

As in TN's `exists_secondDifference_bound`, everything factors through the two-variable Möbius
shift `S(c, w)` (`polydiskShift`): `T_{a,h} = S(a + h, ·) ∘ S(-a, ·)`, and the transported density
is `Γ(a + h, S(-a, z)) · |J_{S(-a,·)}(z)|^{2/n}` with the fixed function
`Γ(c, w) = F(S(c, w)) |J_{S(c, ·)}(w)|^{2/n}`, which is `C²` near the compact parameter box.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity

variable {n : ℕ}

/-! ### The derivative of a disc Möbius map -/

/-- The derivative `(1 - |c|²)/(1 - c̄ w)²` of the disc Möbius map `M_c(w) = (w - c)/(1 - c̄ w)`. -/
def mobDeriv (c w : ℂ) : ℂ := (1 - conj c * c) / (1 - conj c * w) ^ 2

theorem discMobius_eq (c : ℂ) : discMobius c = fun w => (w - c) / (1 - conj c * w) := rfl

theorem hasDerivAt_discMobius {c w : ℂ} (h : 1 - conj c * w ≠ 0) :
    HasDerivAt (discMobius c) (mobDeriv c w) w := by
  have h1 : HasDerivAt (fun w : ℂ => w - c) 1 w := (hasDerivAt_id w).sub_const c
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj c * w) (-(conj c * 1)) w :=
    ((hasDerivAt_id w).const_mul (conj c)).const_sub 1
  have h3 := h1.div h2 h
  have hval : mobDeriv c w =
      (1 * (1 - conj c * w) - (w - c) * -(conj c * 1)) / (1 - conj c * w) ^ 2 := by
    rw [mobDeriv]
    congr 1
    ring
  rw [discMobius_eq, hval]
  exact h3

/-- `M_{-a} ∘ M_a = id` at the level of derivatives. -/
theorem mobDeriv_neg_discMobius_mul {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    mobDeriv (-a) (discMobius a z) * mobDeriv a z = 1 := by
  have hd : 1 - conj a * z ≠ 0 := discMobius_denom_ne_zero ha hz
  have hs : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    intro h0
    have h1 : (Complex.normSq a : ℂ) = 1 := by linear_combination -h0
    have h2 : Complex.normSq a = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg a]
  simp only [mobDeriv, discMobius, map_neg]
  have hd' : 1 - -conj a * ((z - a) / (1 - conj a * z)) = (1 - conj a * a) / (1 - conj a * z) := by
    field_simp
    ring
  rw [hd']
  field_simp

theorem mobDeriv_ne_zero {c w : ℂ} (hc : ‖c‖ < 1) (h : 1 - conj c * w ≠ 0) : mobDeriv c w ≠ 0 := by
  have hs : (1 : ℂ) - conj c * c ≠ 0 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    intro h0
    have h1 : (Complex.normSq c : ℂ) = 1 := by linear_combination -h0
    have h2 : Complex.normSq c = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg c]
  exact div_ne_zero hs (pow_ne_zero 2 h)

/-! ### The Jacobian of `T_{a,h}` -/

/-- The derivative of the `i`-th coordinate map `w ↦ M_{-(aᵢ+hᵢ)}(M_{aᵢ}(w))` of `T_{a,h}` at `zᵢ`. -/
def autDeriv (a h z : ComplexModel n) (i : Fin n) : ℂ :=
  mobDeriv (-(a i + h i)) (discMobius (a i) (z i)) * mobDeriv (a i) (z i)

section Jacobian

variable {a h z : ComplexModel n}

theorem hasDerivAt_autCoord (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) (i : Fin n) :
    HasDerivAt (fun w => discMobius (-(a i + h i)) (discMobius (a i) w)) (autDeriv a h z i)
      (z i) := by
  have h1 : 1 - conj (a i) * z i ≠ 0 := discMobius_denom_ne_zero (ha i) (hz i)
  have h2 : 1 - conj (-(a i + h i)) * discMobius (a i) (z i) ≠ 0 :=
    discMobius_denom_ne_zero (by rw [norm_neg]; exact hah i) (norm_discMobius_le_one (ha i) (hz i))
  exact (hasDerivAt_discMobius h2).comp (z i) (hasDerivAt_discMobius h1)

theorem differentiableAt_polydiskAut (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) : DifferentiableAt ℂ (polydiskAut a h) z := by
  have hpi : DifferentiableAt ℂ (fun y : ComplexModel n => fun i =>
      discMobius (-(a i + h i)) (discMobius (a i) (y i))) z := by
    refine differentiableAt_pi.mpr fun i => ?_
    have hcoord : DifferentiableAt ℂ (fun y : ComplexModel n => y i) z :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt
    exact (hasDerivAt_autCoord ha hah hz i).differentiableAt.comp z hcoord
  exact (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiableAt.comp z hpi

/-- **The complex Jacobian matrix of `T_{a,h}` is diagonal.** -/
theorem jacobianMatrix_polydiskAut (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) :
    jacobianMatrix (polydiskAut a h) z = Matrix.diagonal (autDeriv a h z) := by
  have hT := differentiableAt_polydiskAut ha hah hz
  ext k j
  simp only [jacobianMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  rw [hT.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars']
  have hk : (fderiv ℂ (polydiskAut a h) z (coordinateVector j)) k =
      fderiv ℂ (fun y => polydiskAut a h y k) z (coordinateVector j) := by
    rw [RegularLocusDense.fderiv_coordinate_eq hT k]
    rfl
  rw [hk]
  have hcoord : HasFDerivAt (fun y : ComplexModel n => y k)
      (EuclideanSpace.proj (𝕜 := ℂ) k) z := (EuclideanSpace.proj (𝕜 := ℂ) k).hasFDerivAt
  have hcomp := (hasDerivAt_autCoord ha hah hz k).hasFDerivAt.comp z hcoord
  have hfun : (fun y => polydiskAut a h y k) =
      (fun w => discMobius (-(a k + h k)) (discMobius (a k) w)) ∘ fun y : ComplexModel n => y k := by
    funext y
    rw [polydiskAut_apply]
    rfl
  rw [hfun, hcomp.fderiv]
  by_cases hkj : k = j
  · subst hkj; simp [coordinateVector]
  · simp [coordinateVector, hkj]

theorem det_jacobianMatrix_polydiskAut (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) :
    (jacobianMatrix (polydiskAut a h) z).det = ∏ i, autDeriv a h z i := by
  rw [jacobianMatrix_polydiskAut ha hah hz, Matrix.det_diagonal]

end Jacobian

/-! ### The factorization through the Möbius shift -/

/-- `|J_{S(c,·)}(w)|²`, the squared modulus of the complex Jacobian of `S(c, ·)` at `w`. -/
def shiftJac (p : ComplexModel n × ComplexModel n) : ℝ :=
  ∏ i, Complex.normSq (mobDeriv (-(p.1 i)) (p.2 i))

/-- The open set of parameters on which the shift and its Jacobian are smooth and nonvanishing. -/
def shiftDomain (n : ℕ) : Set (ComplexModel n × ComplexModel n) :=
  {p | p ∈ mobiusDomain n ∧ ∀ i, ‖p.1 i‖ < 1}

theorem isOpen_shiftDomain : IsOpen (shiftDomain n) := by
  have h1 : ∀ i : Fin n, Continuous fun p : ComplexModel n × ComplexModel n => ‖p.1 i‖ :=
    fun i => continuous_norm.comp (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous).comp continuous_fst)
  have : shiftDomain n = mobiusDomain n ∩
      ⋂ i : Fin n, {p : ComplexModel n × ComplexModel n | ‖p.1 i‖ < 1} := by
    ext p; simp [shiftDomain]
  rw [this]
  exact isOpen_mobiusDomain.inter (isOpen_iInter_of_finite fun i => isOpen_lt (h1 i) continuous_const)

theorem paramBox_subset_shiftDomain {ρ : ℝ} (hρ : ρ < 1) : paramBox n ρ ⊆ shiftDomain n :=
  fun _ hp => ⟨paramBox_subset_mobiusDomain hρ hp, fun i => lt_of_le_of_lt (hp.1 i) hρ⟩

theorem shiftJac_pos {p : ComplexModel n × ComplexModel n} (hp : p ∈ shiftDomain n) :
    0 < shiftJac p := by
  refine Finset.prod_pos fun i _ => Complex.normSq_pos.mpr ?_
  exact mobDeriv_ne_zero (by rw [norm_neg]; exact hp.2 i) (hp.1 i)

theorem contDiffOn_mobDeriv_shift (i : Fin n) :
    ContDiffOn ℝ 2 (fun p : ComplexModel n × ComplexModel n => mobDeriv (-(p.1 i)) (p.2 i))
      (mobiusDomain n) := by
  have hproj1 : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n => p.1 i :=
    (((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).comp
      (ContinuousLinearMap.fst ℝ (ComplexModel n) (ComplexModel n))).contDiff
  have hproj2 : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n => p.2 i :=
    (((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).comp
      (ContinuousLinearMap.snd ℝ (ComplexModel n) (ComplexModel n))).contDiff
  have hconj : ContDiff ℝ 2 fun z : ℂ => conj z := Complex.conjCLE.toContinuousLinearMap.contDiff
  have hnum : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n =>
      (1 : ℂ) - conj (-(p.1 i)) * -(p.1 i) :=
    contDiff_const.sub ((hconj.comp hproj1.neg).mul hproj1.neg)
  have hden : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n =>
      ((1 : ℂ) - conj (-(p.1 i)) * p.2 i) ^ 2 :=
    (contDiff_const.sub ((hconj.comp hproj1.neg).mul hproj2)).pow 2
  have hden0 : ∀ p ∈ mobiusDomain n, ((1 : ℂ) - conj (-(p.1 i)) * p.2 i) ^ 2 ≠ 0 :=
    fun p hp => pow_ne_zero 2 (hp i)
  have hinv : ContDiffOn ℝ 2 (fun p : ComplexModel n × ComplexModel n =>
      (((1 : ℂ) - conj (-(p.1 i)) * p.2 i) ^ 2)⁻¹) (mobiusDomain n) := by
    simpa only [Pi.inv_def] using hden.contDiffOn.inv hden0
  have hmul := hnum.contDiffOn.mul hinv
  simpa only [mobDeriv, div_eq_mul_inv] using hmul

theorem contDiffOn_shiftJac : ContDiffOn ℝ 2 (shiftJac (n := n)) (mobiusDomain n) := by
  have : (shiftJac (n := n)) = fun p => ∏ i, ‖mobDeriv (-(p.1 i)) (p.2 i)‖ ^ 2 := by
    funext p
    simp only [shiftJac, Complex.normSq_eq_norm_sq]
  rw [this]
  exact contDiffOn_prod fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn (contDiffOn_mobDeriv_shift i)

/-- The function `Γ(c, w) = F(S(c, w)) |J_{S(c,·)}(w)|^{2/n}`. -/
def shiftDensity (F : ComplexModel n → ℝ) (p : ComplexModel n × ComplexModel n) : ℝ :=
  F (polydiskShift p) * shiftJac p ^ ((n : ℝ)⁻¹)

theorem contDiffOn_shiftDensity {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiffOn ℝ 2 (shiftDensity F) (shiftDomain n) := by
  have h1 : ContDiffOn ℝ 2 (fun p => F (polydiskShift p)) (shiftDomain n) :=
    (hF.comp_contDiffOn contDiffOn_polydiskShift).mono fun p hp => hp.1
  have h2 : ContDiffOn ℝ 2 (fun p => shiftJac p ^ ((n : ℝ)⁻¹)) (shiftDomain n) :=
    (contDiffOn_shiftJac.mono fun p hp => hp.1).rpow_const_of_ne fun p hp => (shiftJac_pos hp).ne'
  exact h1.mul h2

/-- The transported density `(F ∘ T_{a,h}) · |det J_{a,h}|^{2/n}`. -/
def polydiskDensity (F : ComplexModel n → ℝ) (a h z : ComplexModel n) : ℝ :=
  F (polydiskAut a h z) * Complex.normSq (∏ i, autDeriv a h z i) ^ ((n : ℝ)⁻¹)

theorem normSq_prod_autDeriv (a h z : ComplexModel n) :
    Complex.normSq (∏ i, autDeriv a h z i) =
      shiftJac (a + h, polydiskShift (-a, z)) * shiftJac (-a, z) := by
  simp only [shiftJac, autDeriv, map_prod, Complex.normSq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [polydiskShift_neg_left]
  simp

theorem polydiskDensity_eq (F : ComplexModel n → ℝ) (a h z : ComplexModel n) :
    polydiskDensity F a h z =
      shiftDensity F (a + h, polydiskShift (-a, z)) * shiftJac (-a, z) ^ ((n : ℝ)⁻¹) := by
  have h0 : 0 ≤ shiftJac (a + h, polydiskShift (-a, z)) :=
    Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _
  have h1 : 0 ≤ shiftJac (-a, z) := Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _
  rw [polydiskDensity, normSq_prod_autDeriv, Real.mul_rpow h0 h1, shiftDensity,
    polydiskAut_eq_polydiskShift]
  ring

theorem shiftJac_mul_eq_one {a z : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) :
    shiftJac (a, polydiskShift (-a, z)) * shiftJac (-a, z) = 1 := by
  simp only [shiftJac, ← Finset.prod_mul_distrib, ← Complex.normSq_mul]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [polydiskShift_neg_left]
  have h := mobDeriv_neg_discMobius_mul (ha i) (hz i)
  simp only [PiLp.neg_apply, neg_neg] at *
  rw [h, map_one]

/-- At `h = 0` the transported density is `F` itself. -/
theorem shiftDensity_mul_eq {F : ComplexModel n → ℝ} {a z : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n) :
    shiftDensity F (a, polydiskShift (-a, z)) * shiftJac (-a, z) ^ ((n : ℝ)⁻¹) = F z := by
  have h0 : 0 ≤ shiftJac (a, polydiskShift (-a, z)) :=
    Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _
  have h1 : 0 ≤ shiftJac (-a, z) := Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _
  rw [shiftDensity, mul_assoc, ← Real.mul_rpow h0 h1, shiftJac_mul_eq_one ha hz, Real.one_rpow,
    mul_one, polydiskShift_polydiskShift_neg ha hz]

/-- **The data half of the second-difference estimate** (FPT
`thm:continuous-density-ball-dirichlet`, Step 2, first inequality, on the polydisk): the
transported densities have second differences bounded below, uniformly on the parameter box. -/
theorem exists_polydiskDensity_secondDifference {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    {ρ : ℝ} (hρ : ρ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a h : ComplexModel n, (∀ i, ‖a i‖ ≤ ρ) → (∀ i, ‖a i + h i‖ ≤ ρ) →
      (∀ i, ‖a i - h i‖ ≤ ρ) → ∀ z ∈ closedUnitPolydisk n,
        F z - M * ‖h‖ ^ 2 ≤ (polydiskDensity F a h z + polydiskDensity F a (-h) z) / 2 := by
  classical
  set Γ : ComplexModel n × ComplexModel n → ℝ := fun p => -shiftDensity F p with hΓ
  have hU : IsOpen (shiftDomain n) := isOpen_shiftDomain
  have hΓC : ContDiffOn ℝ 2 Γ (shiftDomain n) := (contDiffOn_shiftDensity hF).neg
  obtain ⟨M₀, hM₀0, hMbound⟩ := exists_bound_fderiv_fderiv_of_isCompact hU hΓC
    (isCompact_paramBox (n := n) ρ) (paramBox_subset_shiftDomain hρ)
  -- a bound for the inner Jacobian factor
  have hJc : ContinuousOn (fun p : ComplexModel n × ComplexModel n => shiftJac p ^ ((n : ℝ)⁻¹))
      (paramBox n ρ) :=
    ((contDiffOn_shiftJac.continuousOn.mono (fun p hp => paramBox_subset_mobiusDomain hρ hp)).rpow_const
      fun _ _ => Or.inr (by positivity))
  obtain ⟨B, hB⟩ := (isCompact_paramBox (n := n) ρ).exists_bound_of_continuousOn hJc
  refine ⟨2 * M₀ * max B 0, by positivity, ?_⟩
  intro a h ha hah hah' z hz
  have haP : ∀ i, ‖a i‖ < 1 := fun i => lt_of_le_of_lt (ha i) hρ
  set w : ComplexModel n := polydiskShift (-a, z) with hwdef
  have hw : ∀ i, ‖w i‖ ≤ 1 := polydiskShift_neg_mem_closedUnitPolydisk haP hz
  have hx : ((a, w) : ComplexModel n × ComplexModel n) ∈ paramBox n ρ := ⟨ha, hw⟩
  have hadd : ((a, w) + (h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n) = (a + h, w) := by
    simp
  have hsub : ((a, w) - (h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n) = (a - h, w) := by
    simp
  have hxp : ((a, w) + (h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n) ∈ paramBox n ρ := by
    rw [hadd]
    exact ⟨fun i => by rw [complexModel_add_apply]; exact hah i, hw⟩
  have hxm : ((a, w) - (h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n) ∈ paramBox n ρ := by
    rw [hsub]
    exact ⟨fun i => by rw [complexModel_sub_apply]; exact hah' i, hw⟩
  have hbound := secondDifference_le_of_norm_fderiv_fderiv_le_on hU hΓC (convex_paramBox ρ)
    (paramBox_subset_shiftDomain hρ) hMbound hx hxp hxm
  have hnorm : ‖((h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n)‖ = ‖h‖ := by
    rw [Prod.norm_def]
    simp
  rw [hadd, hsub, hnorm] at hbound
  simp only [hΓ] at hbound
  -- the inner factor
  set J₀ : ℝ := shiftJac (-a, z) ^ ((n : ℝ)⁻¹) with hJ₀
  have hJ₀0 : 0 ≤ J₀ := by
    have : 0 ≤ shiftJac (-a, z) := Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _
    positivity
  have hmem : ((-a, z) : ComplexModel n × ComplexModel n) ∈ paramBox n ρ :=
    ⟨fun i => by simpa using ha i, hz⟩
  have hJ₀B : J₀ ≤ max B 0 := by
    have := hB _ hmem
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have e₁ : polydiskDensity F a h z = shiftDensity F (a + h, w) * J₀ := polydiskDensity_eq F a h z
  have e₂ : polydiskDensity F a (-h) z = shiftDensity F (a - h, w) * J₀ := by
    rw [polydiskDensity_eq, ← sub_eq_add_neg]
  have e₃ : shiftDensity F (a, w) * J₀ = F z := shiftDensity_mul_eq haP hz
  rw [e₁, e₂, ← e₃]
  have hkey : (shiftDensity F (a, w) - M₀ * ‖h‖ ^ 2) * J₀ ≤
      ((shiftDensity F (a + h, w) + shiftDensity F (a - h, w)) / 2) * J₀ :=
    mul_le_mul_of_nonneg_right (by linarith) hJ₀0
  have hM : M₀ * ‖h‖ ^ 2 * J₀ ≤ M₀ * ‖h‖ ^ 2 * max B 0 :=
    mul_le_mul_of_nonneg_left hJ₀B (by positivity)
  have hM' : 0 ≤ M₀ * ‖h‖ ^ 2 * max B 0 := by positivity
  calc shiftDensity F (a, w) * J₀ - 2 * M₀ * max B 0 * ‖h‖ ^ 2
      ≤ (shiftDensity F (a, w) - M₀ * ‖h‖ ^ 2) * J₀ := by nlinarith
    _ ≤ ((shiftDensity F (a + h, w) + shiftDensity F (a - h, w)) / 2) * J₀ := hkey
    _ = (shiftDensity F (a + h, w) * J₀ + shiftDensity F (a - h, w) * J₀) / 2 := by ring

end SGPT.Envelopes.MADirichlet
