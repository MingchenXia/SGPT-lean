import SGPT.NPP.DN5Smoothing
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Smooth unitary frames of the Kähler metric; the smoothing with a fixed kernel

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1: "in unitary coordinates of `T_x X`
the kernel has total mass one").  FPT integrates over `T_x X` in unitary coordinates; to compare
the smoothing at nearby centres (lane DN6, generator) the unitary frame must depend smoothly on
the centre.  Pointwise frames exist (`SGPT.Analysis.KahlerNormal.exists_normalizing_linear`);
here a smooth one is produced near every chart point:

* `exists_smooth_implicit` — the implicit function theorem with a solution smooth on a whole
  neighbourhood (inverse function theorem for `(x, y) ↦ (x, f(x, y))`).
* `hermOp α` — the Hermitian operator of a real `(1,1)`-form, `⟪w, hermOp α v⟫ = π H_α(v, w)`;
  a complex-linear `P` normalizes `α` (`α(P u, P v) = flatForm(u, v)`) iff `P† (hermOp α) P = 1`.
* `exists_smooth_normalizingFrame` — near every chart point there is a smooth family `P z` of
  frames normalizing the Kähler form: solve `(1 + X)† M(z) (1 + X) - 1 + (X - X†) = 0`,
  `M(z) = P₀† (hermOp ω_z) P₀`, by the implicit function theorem (the derivative in `X` at `0` is
  `2·id`; a solution has a self-adjoint first part and an anti-self-adjoint second part, so both
  vanish).
* `chartSmoothing_eq_smoothFrame` — hence, near every chart point,
  `Ψ_g(e⁻¹ z, t) = ∫ g(F(e⁻¹ z, t P(z) s)) χ(‖s‖²) ds` with the fixed kernel `χ(‖s‖²)` and a frame
  `P(z)` smooth in `z`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Analysis.KahlerNormal

/-! ### The implicit function theorem, smooth on a neighbourhood -/

section Implicit

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]

/-- A block-triangular operator with invertible diagonal block is invertible. -/
theorem isInvertible_fst_prod (D : E₁ × E₂ →L[ℝ] E₂)
    (hD : (D.comp (ContinuousLinearMap.inr ℝ E₁ E₂)).IsInvertible) :
    ((ContinuousLinearMap.fst ℝ E₁ E₂).prod D).IsInvertible := by
  obtain ⟨T, hT⟩ := hD
  have hTy : ∀ y, T y = D (0, y) := fun y => by
    rw [show (T : E₂ → E₂) y = (T : E₂ →L[ℝ] E₂) y from rfl, hT]
    rfl
  have hsplit : ∀ a y, D (a, y) = D (a, 0) + T y := by
    intro a y
    rw [hTy, ← map_add]
    simp
  let inv : E₁ × E₂ →L[ℝ] E₁ × E₂ := (ContinuousLinearMap.fst ℝ E₁ E₂).prod
    ((T.symm : E₂ →L[ℝ] E₂).comp (ContinuousLinearMap.snd ℝ E₁ E₂ -
      D.comp ((ContinuousLinearMap.inl ℝ E₁ E₂).comp (ContinuousLinearMap.fst ℝ E₁ E₂))))
  refine ⟨ContinuousLinearEquiv.equivOfInverse ((ContinuousLinearMap.fst ℝ E₁ E₂).prod D) inv
    ?_ ?_, rfl⟩
  · rintro ⟨a, y⟩
    simp only [inv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply]
    rw [hsplit a y, add_sub_cancel_left]
    simp
  · rintro ⟨a, w⟩
    simp only [inv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply]
    rw [hsplit, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      add_sub_cancel]

/-- **The implicit function theorem, with a solution smooth on a neighbourhood.** -/
theorem exists_smooth_implicit {f : E₁ × E₂ → E₂} {S : Set (E₁ × E₂)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {u : E₁ × E₂} (hu : u ∈ S)
    (hinv : ((fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ E₁ E₂)).IsInvertible) :
    ∃ U : Set E₁, IsOpen U ∧ u.1 ∈ U ∧ ∃ ψ : E₁ → E₂, ContDiffOn ℝ ∞ ψ U ∧ ψ u.1 = u.2 ∧
      ∀ x ∈ U, (x, ψ x) ∈ S ∧ f (x, ψ x) = f u := by
  let Θ : E₁ × E₂ → E₁ × E₂ := fun p => (p.1, f p)
  have hΘ : ContDiffOn ℝ ∞ Θ S := contDiffOn_fst.prodMk hf
  have hΘ0 : ContDiffAt ℝ ∞ Θ u := hΘ.contDiffAt (hS.mem_nhds hu)
  have hfd : DifferentiableAt ℝ f u := (hf.contDiffAt (hS.mem_nhds hu)).differentiableAt (by simp)
  obtain ⟨Λ, hΛ⟩ := isInvertible_fst_prod (fderiv ℝ f u) hinv
  have hd0 : HasFDerivAt Θ (Λ : E₁ × E₂ →L[ℝ] E₁ × E₂) u := by
    rw [hΛ]
    exact (hasFDerivAt_fst).prodMk hfd.hasFDerivAt
  let Ψ₀ := hΘ0.toOpenPartialHomeomorph Θ hd0 (by simp)
  have hDcont : ContinuousAt (fderiv ℝ Θ) u :=
    (hΘ0.fderiv_right (m := ∞) (by simp)).continuousAt
  let Inv : Set ((E₁ × E₂) →L[ℝ] (E₁ × E₂)) :=
    range ((↑) : ((E₁ × E₂) ≃L[ℝ] (E₁ × E₂)) → _)
  have hInv : Inv ∈ 𝓝 (fderiv ℝ Θ u) :=
    ContinuousLinearEquiv.isOpen.mem_nhds ⟨Λ, hd0.fderiv.symm⟩
  have hgood : S ∩ (fderiv ℝ Θ) ⁻¹' Inv ∈ 𝓝 u :=
    inter_mem (hS.mem_nhds hu) (hDcont.preimage_mem_nhds hInv)
  obtain ⟨O, hOsub, hO, huO⟩ := _root_.mem_nhds_iff.mp hgood
  let Ψ := Ψ₀.restrOpen O hO
  have hcoe : ⇑Ψ = Θ := by
    rw [OpenPartialHomeomorph.coe_restrOpen]
    exact ContDiffAt.toOpenPartialHomeomorph_coe hΘ0 hd0 (by simp)
  have hsrc : Ψ.source ⊆ O := by
    intro q hq
    rw [OpenPartialHomeomorph.restrOpen_source] at hq
    exact hq.2
  have husrc : u ∈ Ψ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source hΘ0 hd0 (by simp), huO⟩
  have hsymm : ∀ q ∈ Ψ.target, ContDiffAt ℝ ∞ Ψ.symm q := by
    intro q hqt
    have hqs := Ψ.map_target hqt
    have hqgood := hOsub (hsrc hqs)
    obtain ⟨L, hL⟩ := hqgood.2
    have hFat : ContDiffAt ℝ ∞ Θ (Ψ.symm q) := hΘ.contDiffAt (hS.mem_nhds hqgood.1)
    have hd : HasFDerivAt Ψ (L : E₁ × E₂ →L[ℝ] E₁ × E₂) (Ψ.symm q) := by
      rw [hcoe, hL]
      exact (hFat.differentiableAt (by simp)).hasFDerivAt
    apply Ψ.contDiffAt_symm hqt hd
    rw [hcoe]
    exact hFat
  have hident : ∀ q ∈ Ψ.target, (Ψ.symm q).1 = q.1 ∧ f (Ψ.symm q) = q.2 := by
    intro q hqt
    have H := Ψ.right_inv hqt
    rw [hcoe] at H
    have h1 : (Θ (Ψ.symm q)).1 = q.1 := congrArg Prod.fst H
    have h2 : (Θ (Ψ.symm q)).2 = q.2 := congrArg Prod.snd H
    exact ⟨h1, h2⟩
  have huT : (u.1, f u) ∈ Ψ.target := by
    have H := Ψ.map_source husrc
    rw [hcoe] at H
    exact H
  have hc : Continuous fun x : E₁ => (x, f u) := continuous_id.prodMk continuous_const
  refine ⟨{x | (x, f u) ∈ Ψ.target}, Ψ.open_target.preimage hc, huT,
    fun x => (Ψ.symm (x, f u)).2, ?_, ?_, ?_⟩
  · intro x hx
    exact ((contDiffAt_snd.comp _ (hsymm _ hx)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · have H := Ψ.left_inv husrc
    rw [hcoe] at H
    change (Ψ.symm (Θ u)).2 = u.2
    rw [H]
  · intro x hx
    have hx' : (x, f u) ∈ Ψ.target := hx
    have hp : Ψ.symm (x, f u) = (x, (Ψ.symm (x, f u)).2) :=
      Prod.ext (hident _ hx').1 rfl
    refine ⟨?_, ?_⟩
    · have := (hOsub (hsrc (Ψ.map_target hx'))).1
      rwa [hp] at this
    · have := (hident _ hx').2
      rwa [hp] at this

end Implicit

/-! ### Operators on `ℂⁿ` -/

section Operators

variable {N : ℕ}

/-- The adjoint is a bounded real-linear map. -/
theorem isBoundedLinearMap_star :
    IsBoundedLinearMap ℝ (fun X : ComplexModel N →L[ℂ] ComplexModel N => star X) where
  map_add x y := star_add x y
  map_smul r x := by
    have h1 : (r • x : ComplexModel N →L[ℂ] ComplexModel N) = ((r : ℂ) • x) :=
      (Complex.coe_smul r x).symm
    have h2 : (r • star x : ComplexModel N →L[ℂ] ComplexModel N) = ((r : ℂ) • star x) :=
      (Complex.coe_smul r (star x)).symm
    have h3 : star ((r : ℂ) • x) = star (r : ℂ) • star x := star_smul (r : ℂ) x
    have h4 : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    change star (r • x) = r • star x
    rw [h1, h2, h3, h4]
  bound := ⟨1, one_pos, fun x => by
    have := norm_star x
    rw [this, one_mul]⟩

section Generic

variable {R : Type*} [Ring R] [StarRing R]

theorem star_sub_star_self (X : R) : star (X - star X) = -(X - star X) := by
  rw [star_sub, star_star]; abel

theorem star_conj_mul (a b h : R) :
    star (a * b) * h * (a * b) = star b * (star a * h * a) * b := by
  rw [star_mul]; simp only [mul_assoc]

theorem star_conj_sub_one {M : R} (hM : star M = M) (Y : R) :
    star (star Y * M * Y - 1) = star Y * M * Y - 1 := by
  rw [star_sub, star_one, star_mul, star_mul, star_star, hM, mul_assoc]

theorem self_add_self_of_sa_eq_neg_skew {S K : R} (hS : star S = S) (hK : star K = -K)
    (hSK : S = -K) : S + S = 0 := by
  have h1 : star S = K := by rw [hSK, star_neg, hK, neg_neg]
  have h2 : S = K := hS.symm.trans h1
  rw [h2] at hSK
  rw [h2]
  nth_rewrite 1 [hSK]
  abel

end Generic

theorem contDiff_star_op :
    ContDiff ℝ ∞ (fun X : ComplexModel N →L[ℂ] ComplexModel N => star X) :=
  isBoundedLinearMap_star.contDiff

end Operators

/-! ### The Hermitian operator of a `(1,1)`-form -/

section HermOp

variable {N : ℕ}

/-- Hermitian symmetry of the Hermitian entry of a `(1,1)`-form. -/
theorem hermitianEntry_swap {α : CoordinateRealTwoForm N} (hα : IsOneOne α)
    (v w : ComplexModel N) :
    hermitianEntry α w v = (starRingEnd ℂ) (hermitianEntry α v w) := by
  have h1 : α ![w, Complex.I • v] = α ![v, Complex.I • w] := by
    rw [twoForm_swap (α := α), twoForm_I_left (α := α) hα v w, neg_neg]
  have h2 : α ![w, v] = -α ![v, w] := twoForm_swap (α := α) v w
  simp only [hermitianEntry, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, h1, h2]
  push_cast
  ring

/-- The Hermitian operator of a real two-form: `⟪w, hermOp α v⟫ = π H_α(v, w)`. -/
def hermOp (α : CoordinateRealTwoForm N) : ComplexModel N →L[ℂ] ComplexModel N :=
  ∑ j : Fin N, ∑ k : Fin N,
    ((Real.pi : ℂ) * hermitianEntry α (coordinateVector k) (coordinateVector j)) •
      ((EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).smulRight (coordinateVector j))

theorem hermOp_apply {α : CoordinateRealTwoForm N} (hα : IsOneOne α) (v : ComplexModel N) :
    hermOp α v = ∑ j : Fin N, ((Real.pi : ℂ) * hermitianEntry α v (coordinateVector j)) •
      coordinateVector j := by
  classical
  have hproj : ∀ k : Fin N, (EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ) v = v k :=
    fun k => rfl
  simp only [hermOp, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply, hproj]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [eq_sum_coordinateVector v, hermitianEntry_sum_left hα]
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  ring

theorem inner_hermOp {α : CoordinateRealTwoForm N} (hα : IsOneOne α) (v w : ComplexModel N) :
    inner ℂ w (hermOp α v) = (Real.pi : ℂ) * hermitianEntry α v w := by
  classical
  rw [hermOp_apply hα, inner_sum]
  conv_rhs => rw [eq_sum_coordinateVector w, hermitianEntry_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, inner_coordinateVector_right]
  ring

theorem star_hermOp {α : CoordinateRealTwoForm N} (hα : IsOneOne α) :
    star (hermOp α) = hermOp α := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm, inner_hermOp hα, inner_hermOp hα, map_mul, Complex.conj_ofReal,
    ← hermitianEntry_swap hα]

/-- `π H_α(P u, P v) = ⟪v, P† (hermOp α) P u⟫`. -/
theorem hermitianEntry_comp {α : CoordinateRealTwoForm N} (hα : IsOneOne α)
    (P : ComplexModel N →L[ℂ] ComplexModel N) (u v : ComplexModel N) :
    (Real.pi : ℂ) * hermitianEntry α (P u) (P v) = inner ℂ v ((star P * hermOp α * P) u) := by
  rw [← inner_hermOp hα, ContinuousLinearMap.star_eq_adjoint]
  change _ = inner ℂ v (ContinuousLinearMap.adjoint P (hermOp α (P u)))
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- **Normalization from the operator identity** `P† (hermOp α) P = 1`. -/
theorem normalizing_of_star_mul {α : CoordinateRealTwoForm N} (hα : IsOneOne α)
    {P : ComplexModel N →L[ℂ] ComplexModel N} (hP : star P * hermOp α * P = 1)
    (u v : ComplexModel N) : α ![P u, P v] = flatForm N ![u, v] := by
  have h := hermitianEntry_comp hα P u v
  rw [hP, ContinuousLinearMap.one_apply] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h' : hermitianEntry α (P u) (P v) = ((Real.pi⁻¹ : ℝ) : ℂ) * inner ℂ v u := by
    rw [← h, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
  have h3 : (inner ℂ u v).im = -(inner ℂ v u).im := by
    rw [← inner_conj_symm, Complex.conj_im]
  rw [twoForm_eq_neg_im_hermitianEntry, flatForm_apply, h', Complex.im_ofReal_mul, h3]
  ring

/-- **The operator identity from normalization.** -/
theorem star_mul_eq_one_of_normalizing {α : CoordinateRealTwoForm N} (hα : IsOneOne α)
    {P : ComplexModel N →L[ℂ] ComplexModel N} (hP : ∀ u v, α ![P u, P v] = flatForm N ![u, v]) :
    star P * hermOp α * P = 1 := by
  set T := star P * hermOp α * P
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him : ∀ u v, (inner ℂ v (T u)).im = (inner ℂ v u).im := by
    intro u v
    have h := hermitianEntry_comp hα P u v
    have h2 := hP u v
    have h' : hermitianEntry α (P u) (P v) = ((Real.pi⁻¹ : ℝ) : ℂ) * inner ℂ v (T u) := by
      rw [← h, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    have e1 : (hermitianEntry α (P u) (P v)).im = Real.pi⁻¹ * (inner ℂ v (T u)).im := by
      rw [h', Complex.im_ofReal_mul]
    have h3 : (inner ℂ u v).im = -(inner ℂ v u).im := by
      rw [← inner_conj_symm, Complex.conj_im]
    rw [twoForm_eq_neg_im_hermitianEntry, flatForm_apply, e1, h3] at h2
    have h4 : Real.pi⁻¹ * (inner ℂ v (T u)).im = Real.pi⁻¹ * (inner ℂ v u).im := by linarith
    exact mul_left_cancel₀ (inv_ne_zero Real.pi_ne_zero) h4
  refine ContinuousLinearMap.ext fun u => ?_
  refine ext_inner_left ℂ fun v => ?_
  apply Complex.ext
  · have h := him u (Complex.I • v)
    rw [inner_smul_left, inner_smul_left, Complex.conj_I] at h
    simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add] at h
    rw [ContinuousLinearMap.one_apply]
    linarith
  · rw [ContinuousLinearMap.one_apply]
    exact him u v

/-- Smoothness of `α ↦ hermOp α`. -/
theorem contDiff_hermOp : ContDiff ℝ ∞ (hermOp : CoordinateRealTwoForm N → _) := by
  unfold hermOp
  refine ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_
  have hc : ContDiff ℝ ∞ (fun α : CoordinateRealTwoForm N =>
      (Real.pi : ℂ) * hermitianEntry α (coordinateVector k) (coordinateVector j)) := by
    refine contDiff_const.mul ?_
    unfold hermitianEntry
    have h1 : ContDiff ℝ ∞ (fun α : CoordinateRealTwoForm N =>
        α ![coordinateVector k, Complex.I • coordinateVector j]) :=
      (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ
        ![coordinateVector k, Complex.I • coordinateVector j]).contDiff
    have h2 : ContDiff ℝ ∞ (fun α : CoordinateRealTwoForm N =>
        α ![coordinateVector k, coordinateVector j]) :=
      (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ
        ![coordinateVector k, coordinateVector j]).contDiff
    exact (Complex.ofRealCLM.contDiff.comp h1).sub
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h2))
  exact hc.smul contDiff_const

end HermOp

/-! ### Smooth normalizing frames -/

section Frame

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **A smooth family of frames normalizing the Kähler form** near every chart point. -/
theorem exists_smooth_normalizingFrame (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {z₀ : ComplexModel N} (hz₀ : z₀ ∈ e.val.target) :
    ∃ U : Set (ComplexModel N), IsOpen U ∧ z₀ ∈ U ∧ U ⊆ e.val.target ∧
      ∃ P : ComplexModel N → (ComplexModel N →L[ℂ] ComplexModel N), ContDiffOn ℝ ∞ P U ∧
        ∀ z ∈ U, ∀ u v, wY.form.val.coeff e z ![P z u, P z v] = flatForm N ![u, v] := by
  set α := wY.form.val.coeff e
  have h11 : ∀ z ∈ e.val.target, IsOneOne (α z) := fun z hz => (wY.isKahler.1 e z hz).1
  obtain ⟨L₀, hL₀⟩ := exists_normalizingFrame wY hz₀
  set P₀ : ComplexModel N →L[ℂ] ComplexModel N := (L₀ : ComplexModel N →L[ℂ] ComplexModel N)
  have hP₀ : star P₀ * hermOp (α z₀) * P₀ = 1 :=
    star_mul_eq_one_of_normalizing (h11 z₀ hz₀) (fun u v => hL₀ u v)
  set M : ComplexModel N → (ComplexModel N →L[ℂ] ComplexModel N) :=
    fun z => star P₀ * hermOp (α z) * P₀
  have hM : ContDiffOn ℝ ∞ M e.val.target :=
    (contDiffOn_const.mul (contDiff_hermOp.comp_contDiffOn (wY.form.val.smooth e))).mul
      contDiffOn_const
  have hMsa : ∀ z ∈ e.val.target, IsSelfAdjoint (M z) := by
    intro z hz
    have hH : IsSelfAdjoint (hermOp (α z)) := star_hermOp (h11 z hz)
    exact hH.conjugate' P₀
  set f : ComplexModel N × (ComplexModel N →L[ℂ] ComplexModel N) →
      (ComplexModel N →L[ℂ] ComplexModel N) :=
    fun p => star (1 + p.2) * M p.1 * (1 + p.2) - 1 + (p.2 - star p.2)
  set S : Set (ComplexModel N × (ComplexModel N →L[ℂ] ComplexModel N)) :=
    e.val.target ×ˢ univ
  have hS : IsOpen S := e.val.open_target.prod isOpen_univ
  have hstar : ContDiff ℝ ∞ (fun X : ComplexModel N →L[ℂ] ComplexModel N => star X) :=
    contDiff_star_op
  have hf : ContDiffOn ℝ ∞ f S := by
    have h1 : ContDiffOn ℝ ∞ (fun p : ComplexModel N × (ComplexModel N →L[ℂ] ComplexModel N) =>
        (1 : ComplexModel N →L[ℂ] ComplexModel N) + p.2) S := contDiffOn_const.add contDiffOn_snd
    have hMp : ContDiffOn ℝ ∞ (fun p : ComplexModel N × (ComplexModel N →L[ℂ] ComplexModel N) =>
        M p.1) S := hM.comp contDiffOn_fst (fun p hp => hp.1)
    exact ((((hstar.comp_contDiffOn h1).mul hMp).mul h1).sub contDiffOn_const).add
      (contDiffOn_snd.sub (hstar.comp_contDiffOn contDiffOn_snd))
  have hu : ((z₀, 0) : ComplexModel N × (ComplexModel N →L[ℂ] ComplexModel N)) ∈ S :=
    ⟨hz₀, mem_univ _⟩
  have hMz₀ : M z₀ = 1 := hP₀
  have hs1 : star (1 + 0 : ComplexModel N →L[ℂ] ComplexModel N) = 1 := by
    rw [add_zero]; exact star_one _
  have hs0 : star (0 : ComplexModel N →L[ℂ] ComplexModel N) = 0 :=
    star_zero (ComplexModel N →L[ℂ] ComplexModel N)
  -- the derivative in `X` at `0` is `2 • id`
  have hslice : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => f (z₀, X))
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (ComplexModel N →L[ℂ] ComplexModel N)) 0 := by
    have hfun : (fun X : ComplexModel N →L[ℂ] ComplexModel N => f (z₀, X)) =
        fun X => star (1 + X) * (1 + X) - 1 + (X - star X) := by
      funext X
      change star (1 + X) * M z₀ * (1 + X) - 1 + (X - star X) = _
      rw [hMz₀, mul_one]
    rw [hfun]
    have hb : IsBoundedBilinearMap ℝ (fun p : (ComplexModel N →L[ℂ] ComplexModel N) ×
        (ComplexModel N →L[ℂ] ComplexModel N) => p.1 * p.2) := isBoundedBilinearMap_mul
    set Ls := isBoundedLinearMap_star (N := N) |>.toContinuousLinearMap
    have hs : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => star X) Ls 0 :=
      isBoundedLinearMap_star.hasFDerivAt
    have h1 : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => 1 + X)
        (ContinuousLinearMap.id ℝ _) 0 := (hasFDerivAt_id _).const_add _
    have h2 : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => star (1 + X)) Ls 0 := by
      have h := (isBoundedLinearMap_star (N := N)).hasFDerivAt (x := 1 + 0)
      have h' := h.comp (0 : ComplexModel N →L[ℂ] ComplexModel N) h1
      rw [ContinuousLinearMap.comp_id] at h'
      exact h'
    have hpair := h2.prodMk h1
    have hq := (hb.hasFDerivAt (star (1 + 0), 1 + 0)).comp
      (0 : ComplexModel N →L[ℂ] ComplexModel N) hpair
    have hlin : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => X - star X)
        (ContinuousLinearMap.id ℝ _ - Ls) 0 := (hasFDerivAt_id _).sub hs
    have htot := (hq.sub_const 1).add hlin
    refine htot.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
    change star (1 + 0) * Y + star Y * (1 + 0) + (Y - star Y) = (2 : ℝ) • Y
    rw [hs1, add_zero, one_mul, mul_one]
    have h2Y : (2 : ℝ) • Y = Y + Y := two_smul ℝ Y
    rw [h2Y]
    abel
  have hinv : ((fderiv ℝ f (z₀, 0)).comp
      (ContinuousLinearMap.inr ℝ (ComplexModel N) (ComplexModel N →L[ℂ] ComplexModel N))).IsInvertible := by
    have hfd : DifferentiableAt ℝ f (z₀, 0) :=
      (hf.contDiffAt (hS.mem_nhds hu)).differentiableAt (by simp)
    have hcomp : HasFDerivAt (fun X : ComplexModel N →L[ℂ] ComplexModel N => f (z₀, X))
        ((fderiv ℝ f (z₀, 0)).comp (ContinuousLinearMap.inr ℝ _ _)) 0 :=
      hfd.hasFDerivAt.comp 0 ((hasFDerivAt_const z₀ 0).prodMk (hasFDerivAt_id 0))
    rw [hcomp.unique hslice]
    refine ⟨ContinuousLinearEquiv.equivOfInverse
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (ComplexModel N →L[ℂ] ComplexModel N))
      ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ (ComplexModel N →L[ℂ] ComplexModel N)) ?_ ?_, rfl⟩
    · intro X; simp [smul_smul]
    · intro X; simp [smul_smul]
  obtain ⟨U, hU, hz₀U, ψ, hψ, hψ0, hψf⟩ := exists_smooth_implicit hS hf hu hinv
  have hf0 : f (z₀, 0) = 0 := by
    change star (1 + 0) * M z₀ * (1 + 0) - 1 + (0 - star 0) = 0
    rw [hs1, hs0, hMz₀]
    simp
  refine ⟨U ∩ e.val.target, hU.inter e.val.open_target, ⟨hz₀U, hz₀⟩, inter_subset_right,
    fun z => P₀ * (1 + ψ z), (contDiffOn_const.mul (contDiffOn_const.add hψ)).mono
      inter_subset_left, ?_⟩
  intro z hz u v
  have hfz := (hψf z hz.1).2
  rw [hf0] at hfz
  set X := ψ z
  set R := star (1 + X) * M z * (1 + X) - 1
  have hMz : star (M z) = M z := hMsa z hz.2
  have hRsa : star R = R := star_conj_sub_one hMz (1 + X)
  have hR : R = -(X - star X) := eq_neg_of_add_eq_zero_left hfz
  have hRR : R + R = 0 := self_add_self_of_sa_eq_neg_skew hRsa (star_sub_star_self X) hR
  have hR0 : R = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h := congrArg (fun T : ComplexModel N →L[ℂ] ComplexModel N => T w) hRR
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply] at h
    have h2 : (2 : ℂ) • R w = 0 := by rw [two_smul]; exact h
    rw [ContinuousLinearMap.zero_apply]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hone : star (1 + X) * M z * (1 + X) = 1 := sub_eq_zero.mp hR0
  have hnorm : star (P₀ * (1 + X)) * hermOp (α z) * (P₀ * (1 + X)) = 1 := by
    rw [star_conj_mul]
    exact hone
  exact normalizing_of_star_mul (h11 z hz.2) hnorm u v

end Frame

end SGPT.NPP.DN5
