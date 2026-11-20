import SGPT.Foundations.Analysis.Pending.CalabiFlatIdentity
import SGPT.Foundations.Analysis.Pending.ThirdOrderTraceIdentity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Laplacian of Calabi's quantity at a point with `H = 1`

For a smooth real `u` on `ℂⁿ` with complex Hessian `H = (u_{jk̄})`, `P = H⁻¹` and `X_m = ∂_m H`
(`dH`), Calabi's quantity is `S = Σ_{m,t} P_{tm} tr(P X_m P X_t*)` (`calabiS`;
`pss07-multiplier-krf:page-0008`, (2.39)–(2.40), flat reference metric). This file computes, at a point
`x` with `H(x) = 1`, the Laplacian `Σ_p ∂_p∂̄_p S(x)` of the metric `H` by the Leibniz rule
(`sum_wirt_wirt_calabiS`): it is the 25-term sum `CalabiFlatIdentity.calabiFlatSum` of the derivatives
`X_m = ∂_m H`, `V_{pm} = ∂_p∂_m H` (`dV`), `Z_{mq} = ∂̄_q∂_m H` (`dZ`) and `Σ_p ∂_p∂̄_p∂_m H` (`dW`)
at `x`, to which Calabi's identity `CalabiFlatIdentity.calabiFlatSum_eq` applies.

* A matrix-valued Wirtinger calculus (`wirtM_mul`, `wirtM_inv`, `wirtM_I_conjTranspose`, ...) and the
  Leibniz rule for the five-slot form (`wirt_calabiForm`).
* The symmetries of the derivatives of `H` that the identity needs (`dH_symm`, `dV_symm`, `dV_symm'`,
  `dZ_symm`, `dZ_symm'`, `dZ_conjTranspose`, `wirtM_I_dV`), from the commutation of Wirtinger derivatives
  of the smooth function `u`.
* The two Leibniz stages: `∂̄_p S` near `x` (`wirt_calabiS`, using `∂̄_p P = -P X_p* P`) and its `∂_p` at
  `x` (`wirt_stageOne`, using `P(x) = 1`, `∂_p P(x) = -X_p`, `∂_p∂̄_p P(x) = X_p X_p* - Z_{pp} + X_p* X_p`).

TN.4 B5, nonlinear track N4 (b), blueprint `bou:yau-c3-estimate`
.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CalabiFlatLaplacian

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity

noncomputable section

/-! ### Matrix-valued Wirtinger calculus -/

section MatrixCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {c : ℂ} {v : E} {x : E}

/-- All entries of a matrix-valued function are differentiable at `x`. -/
def MDiffAt (M : E → Matrix ι ι ℂ) (x : E) : Prop := ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x

theorem MDiffAt.mul {M N : E → Matrix ι ι ℂ} (hM : MDiffAt M x) (hN : MDiffAt N x) :
    MDiffAt (fun y => M y * N y) x := fun i j => by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (hM i k).mul (hN k j)

theorem MDiffAt.neg {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) : MDiffAt (fun y => -M y) x :=
  fun i j => by simpa using (hM i j).neg

theorem MDiffAt.add {M N : E → Matrix ι ι ℂ} (hM : MDiffAt M x) (hN : MDiffAt N x) :
    MDiffAt (fun y => M y + N y) x := fun i j => by
  simp only [Matrix.add_apply]
  exact (hM i j).add (hN i j)

theorem MDiffAt.conjTranspose {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    MDiffAt (fun y => (M y)ᴴ) x := fun i j => by
  simp only [conjTranspose_apply, RCLike.star_def]
  exact (Complex.conjCLE.differentiable.differentiableAt).comp x (hM j i)

theorem MDiffAt.inv {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) (hx : (M x).det ≠ 0) :
    MDiffAt (fun y => (M y)⁻¹) x := fun i j => differentiableAt_inv_apply hM hx i j

theorem wirtM_congr {M N : E → Matrix ι ι ℂ} (h : M =ᶠ[𝓝 x] N) :
    wirtM c v M x = wirtM c v N x := by
  ext i j
  simp only [wirtM_apply]
  exact wirt_congr (h.mono fun y hy => by simp only [hy])

theorem wirtM_mul {M N : E → Matrix ι ι ℂ} (hM : MDiffAt M x) (hN : MDiffAt N x) :
    wirtM c v (fun y => M y * N y) x = wirtM c v M x * N x + M x * wirtM c v N x := by
  ext i j
  simp only [wirtM_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [wirt_sum Finset.univ (f := fun k y => M y i k * N y k j)
    fun k _ => (hM i k).mul (hN k j), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => wirt_mul (hM i k) (hN k j)

theorem wirtM_neg {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    wirtM c v (fun y => -M y) x = -wirtM c v M x := by
  ext i j
  simp only [wirtM_apply, Matrix.neg_apply]
  have h := wirt_const_mul (c := c) (v := v) (-1) (hM i j)
  simp only [neg_one_mul] at h
  exact h

theorem wirt_trace {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    wirt c v (fun y => (M y).trace) x = (wirtM c v M x).trace := by
  simp only [Matrix.trace, Matrix.diag, wirtM_apply]
  exact wirt_sum Finset.univ fun i _ => hM i i

theorem wirtM_inv {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) (hx : (M x).det ≠ 0) :
    wirtM c v (fun y => (M y)⁻¹) x = -((M x)⁻¹ * wirtM c v M x * (M x)⁻¹) := by
  ext i j
  rw [wirtM_apply, wirt_inv_apply hM hx i j, Matrix.neg_apply]

theorem wirt_negI_conj {f : E → ℂ} (hf : DifferentiableAt ℝ f x) :
    wirt (-I) v (fun y => conj (f y)) x = conj (wirt I v f x) := by
  have hg : DifferentiableAt ℝ (fun y => conj (f y)) x :=
    (Complex.conjCLE.differentiable.differentiableAt).comp x hf
  have h := wirt_I_conj (v := v) hg
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at h
  rw [h, Complex.conj_conj]

theorem wirtM_I_conjTranspose {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    wirtM I v (fun y => (M y)ᴴ) x = (wirtM (-I) v M x)ᴴ := by
  ext i j
  simp only [wirtM_apply, conjTranspose_apply, RCLike.star_def]
  exact wirt_I_conj (hM j i)

theorem wirtM_negI_conjTranspose {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    wirtM (-I) v (fun y => (M y)ᴴ) x = (wirtM I v M x)ᴴ := by
  ext i j
  simp only [wirtM_apply, conjTranspose_apply, RCLike.star_def]
  exact wirt_negI_conj (hM j i)

theorem MDiffAt.differentiableAt_trace {M : E → Matrix ι ι ℂ} (hM : MDiffAt M x) :
    DifferentiableAt ℝ (fun y => (M y).trace) x := by
  simp only [Matrix.trace, Matrix.diag]
  exact DifferentiableAt.fun_sum fun i _ => hM i i

end MatrixCalculus

/-! ### The Leibniz rule for the five-slot form -/

section Leibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {c : ℂ} {v : E} {x : E}

/-- **Leibniz rule** for `calabiForm`: a first-order operator `wirt c v` hits one slot at a time. -/
theorem wirt_calabiForm {A B D : E → Mat n} {C Y : E → Fin n → Mat n} (hA : MDiffAt A x)
    (hB : MDiffAt B x) (hC : ∀ m, MDiffAt (fun y => C y m) x) (hD : MDiffAt D x)
    (hY : ∀ t, MDiffAt (fun y => Y y t) x) :
    wirt c v (fun y => calabiForm (A y) (B y) (C y) (D y) (Y y)) x =
      calabiForm (wirtM c v A x) (B x) (C x) (D x) (Y x) +
        calabiForm (A x) (wirtM c v B x) (C x) (D x) (Y x) +
        calabiForm (A x) (B x) (fun m => wirtM c v (fun y => C y m) x) (D x) (Y x) +
        calabiForm (A x) (B x) (C x) (wirtM c v D x) (Y x) +
        calabiForm (A x) (B x) (C x) (D x) (fun t => wirtM c v (fun y => Y y t) x) := by
  have hP : ∀ m t, MDiffAt (fun y => B y * C y m * D y * Y y t) x := fun m t =>
    ((hB.mul (hC m)).mul hD).mul (hY t)
  unfold calabiForm
  rw [wirt_sum Finset.univ (f := fun m y => ∑ t, A y t m * (B y * C y m * D y * Y y t).trace)
    fun m _ => DifferentiableAt.fun_sum fun t _ => (hA t m).mul (hP m t).differentiableAt_trace]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [wirt_sum Finset.univ (f := fun t y => A y t m * (B y * C y m * D y * Y y t).trace)
    fun t _ => (hA t m).mul (hP m t).differentiableAt_trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [wirt_mul (f := fun y => A y t m) (g := fun y => (B y * C y m * D y * Y y t).trace)
    (hA t m) (hP m t).differentiableAt_trace, wirt_trace (hP m t),
    wirtM_mul ((hB.mul (hC m)).mul hD) (hY t), wirtM_mul (hB.mul (hC m)) hD,
    wirtM_mul hB (hC m)]
  simp only [wirtM_apply, Matrix.add_mul, trace_add, mul_add]
  ring

theorem differentiableAt_calabiForm {A B D : E → Mat n} {C Y : E → Fin n → Mat n}
    (hA : MDiffAt A x) (hB : MDiffAt B x) (hC : ∀ m, MDiffAt (fun y => C y m) x)
    (hD : MDiffAt D x) (hY : ∀ t, MDiffAt (fun y => Y y t) x) :
    DifferentiableAt ℝ (fun y => calabiForm (A y) (B y) (C y) (D y) (Y y)) x := by
  unfold calabiForm
  exact DifferentiableAt.fun_sum fun m _ => DifferentiableAt.fun_sum fun t _ =>
    (hA t m).mul (((hB.mul (hC m)).mul hD).mul (hY t)).differentiableAt_trace

theorem wirt_add5 {f₁ f₂ f₃ f₄ f₅ : E → ℂ} (h₁ : DifferentiableAt ℝ f₁ x)
    (h₂ : DifferentiableAt ℝ f₂ x) (h₃ : DifferentiableAt ℝ f₃ x) (h₄ : DifferentiableAt ℝ f₄ x)
    (h₅ : DifferentiableAt ℝ f₅ x) :
    wirt c v (fun y => f₁ y + f₂ y + f₃ y + f₄ y + f₅ y) x =
      wirt c v f₁ x + wirt c v f₂ x + wirt c v f₃ x + wirt c v f₄ x + wirt c v f₅ x := by
  rw [wirt_add (f := fun y => f₁ y + f₂ y + f₃ y + f₄ y) (g := f₅)
      (((h₁.fun_add h₂).fun_add h₃).fun_add h₄) h₅,
    wirt_add (f := fun y => f₁ y + f₂ y + f₃ y) (g := f₄) ((h₁.fun_add h₂).fun_add h₃) h₄,
    wirt_add (f := fun y => f₁ y + f₂ y) (g := f₃) (h₁.fun_add h₂) h₃, wirt_add h₁ h₂]

end Leibniz

/-! ### The derivatives of the complex Hessian of a smooth function -/

section Data

variable {n : ℕ} (u : ComplexModel n → ℝ)

/-- `X_m = ∂_m H`, `H = (u_{jk̄})`. -/
def dH (m : Fin n) : ComplexModel n → Mat n :=
  wirtM (-I) (coordinateVector m) (complexHessian u)

/-- Calabi's quantity `S = Σ_{m,t} P_{tm} tr(P X_m P X_t*)`, `P = H⁻¹` (complex-valued; it is real). -/
def calabiS (y : ComplexModel n) : ℂ :=
  calabiForm (complexHessian u y)⁻¹ (complexHessian u y)⁻¹ (fun m => dH u m y)
    (complexHessian u y)⁻¹ (fun m => (dH u m y)ᴴ)

/-- `∂_p X_m`. -/
def dV (p m : Fin n) : ComplexModel n → Mat n := wirtM (-I) (coordinateVector p) (dH u m)

/-- `∂̄_q X_m`. -/
def dZ (m q : Fin n) : ComplexModel n → Mat n := wirtM I (coordinateVector q) (dH u m)

/-- `∂_p ∂̄_q X_m`. -/
def dW (p q m : Fin n) : ComplexModel n → Mat n := wirtM (-I) (coordinateVector p) (dZ u m q)

variable {u}

/-- All entries smooth. -/
def MSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : E → Mat n) : Prop :=
  ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)

theorem MSmooth.wirtM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M : E → Mat n}
    (hM : MSmooth M) (c : ℂ) (v : E) : MSmooth (WirtingerLogDet.wirtM c v M) := fun i j => by
  simp only [wirtM_apply]
  exact contDiff_wirt (hM i j)

theorem MSmooth.mdiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M : E → Mat n}
    (hM : MSmooth M) (x : E) : MDiffAt M x := fun i j =>
  (hM i j).differentiable (by simp) x

theorem MSmooth.conjTranspose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : E → Mat n} (hM : MSmooth M) : MSmooth (fun y => (M y)ᴴ) := fun i j => by
  simp only [conjTranspose_apply, RCLike.star_def]
  exact Complex.conjCLE.contDiff.comp (hM j i)

theorem mSmooth_complexHessian (hu : ContDiff ℝ ∞ u) : MSmooth (complexHessian u) :=
  fun i j => contDiff_complexHessian_apply hu i j

theorem mSmooth_dH (hu : ContDiff ℝ ∞ u) (m : Fin n) : MSmooth (dH u m) :=
  (mSmooth_complexHessian hu).wirtM _ _

theorem mSmooth_dV (hu : ContDiff ℝ ∞ u) (p m : Fin n) : MSmooth (dV u p m) :=
  (mSmooth_dH hu m).wirtM _ _

theorem mSmooth_dZ (hu : ContDiff ℝ ∞ u) (m q : Fin n) : MSmooth (dZ u m q) :=
  (mSmooth_dH hu m).wirtM _ _

/-- The entries of `H` as iterated Wirtinger derivatives of `u`. -/
theorem complexHessian_entry (hu : ContDiff ℝ ∞ u) (a b : Fin n) :
    (fun y => complexHessian u y a b) =
      wirt (-I) (coordinateVector a) (wirt I (coordinateVector b) (fun z => (u z : ℂ))) :=
  BlockiLocalEstimate.complexHessian_apply_eq_wirt hu a b

theorem contDiff_wirt_I_ofReal (hu : ContDiff ℝ ∞ u) (b : Fin n) :
    ContDiff ℝ ∞ (wirt I (coordinateVector b) (fun z => (u z : ℂ))) :=
  contDiff_wirt (BlockiLocalEstimate.contDiff_ofReal_comp hu)

theorem dH_entry (hu : ContDiff ℝ ∞ u) (m a b : Fin n) :
    (fun y => dH u m y a b) = wirt (-I) (coordinateVector m) (wirt (-I) (coordinateVector a)
      (wirt I (coordinateVector b) (fun z => (u z : ℂ)))) := by
  funext y
  simp only [dH, wirtM_apply, complexHessian_entry hu a b]

/-- `X_m[a,b] = X_a[m,b]` (as functions). -/
theorem dH_symm (hu : ContDiff ℝ ∞ u) (m a b : Fin n) :
    (fun y => dH u m y a b) = fun y => dH u a y m b := by
  rw [dH_entry hu, dH_entry hu, BlockiLocalEstimate.wirt_comm_fun (contDiff_wirt_I_ofReal hu b)]

theorem dV_symm (hu : ContDiff ℝ ∞ u) (p m : Fin n) (y : ComplexModel n) :
    dV u p m y = dV u m p y := by
  ext a b
  simp only [dV, wirtM_apply]
  rw [dH_entry hu, dH_entry hu, BlockiLocalEstimate.wirt_comm_fun
    (contDiff_wirt (contDiff_wirt_I_ofReal hu b))]

theorem dV_symm' (hu : ContDiff ℝ ∞ u) (p m a b : Fin n) (y : ComplexModel n) :
    dV u p m y a b = dV u p a y m b := by
  simp only [dV, wirtM_apply]
  rw [dH_symm hu m a b]

theorem dZ_symm (hu : ContDiff ℝ ∞ u) (m q a b : Fin n) (y : ComplexModel n) :
    dZ u m q y a b = dZ u a q y m b := by
  simp only [dZ, wirtM_apply]
  rw [dH_symm hu m a b]

theorem dZ_entry (hu : ContDiff ℝ ∞ u) (m q a b : Fin n) :
    (fun y => dZ u m q y a b) = wirt (-I) (coordinateVector m) (wirt (-I) (coordinateVector a)
      (wirt I (coordinateVector q) (wirt I (coordinateVector b) (fun z => (u z : ℂ))))) := by
  have hb := contDiff_wirt_I_ofReal hu b
  funext y
  simp only [dZ, wirtM_apply]
  rw [dH_entry hu, BlockiLocalEstimate.wirt_comm_fun (contDiff_wirt hb),
    BlockiLocalEstimate.wirt_comm_fun hb]

theorem dZ_symm' (hu : ContDiff ℝ ∞ u) (m q a b : Fin n) (y : ComplexModel n) :
    dZ u m q y a b = dZ u m b y a q := by
  have h := congrFun (dZ_entry hu m q a b) y
  have h' := congrFun (dZ_entry hu m b a q) y
  rw [h, h', BlockiLocalEstimate.wirt_comm_fun (c := I) (d := I)
    (BlockiLocalEstimate.contDiff_ofReal_comp hu)]

theorem dZ_conjTranspose (hu : ContDiff ℝ ∞ u) (m q : Fin n) (y : ComplexModel n) :
    (dZ u m q y)ᴴ = dZ u q m y := by
  ext a b
  have hab := contDiff_complexHessian_apply hu a b
  have hHerm : (fun z => complexHessian u z b a) = fun z => conj (complexHessian u z a b) :=
    funext fun z => by
      have := congrFun (congrFun (isHermitian_complexHessian hu z) a) b
      rw [conjTranspose_apply] at this
      rw [← this, RCLike.star_def, Complex.conj_conj]
  rw [conjTranspose_apply, RCLike.star_def]
  simp only [dZ, dH, wirtM_apply]
  rw [hHerm]
  have h1 : wirt (-I) (coordinateVector m) (fun z => conj (complexHessian u z a b)) =
      fun z => conj (wirt I (coordinateVector m) (fun z => complexHessian u z a b) z) :=
    funext fun z => wirt_negI_conj (hab.differentiable (by simp) z)
  rw [h1, wirt_I_conj ((contDiff_wirt hab).differentiable (by simp) y), Complex.conj_conj,
    BlockiLocalEstimate.wirt_comm_fun hab]

theorem wirtM_I_dV (hu : ContDiff ℝ ∞ u) (p t : Fin n) (y : ComplexModel n) :
    wirtM I (coordinateVector p) (dV u p t) y = dW u p p t y := by
  ext a b
  simp only [dW, dZ, dV, wirtM_apply]
  exact congrFun (BlockiLocalEstimate.wirt_comm_fun ((mSmooth_dH hu t) a b)) y

/-! ### The two Leibniz stages -/

/-- `P = H⁻¹`. -/
def invH (u : ComplexModel n → ℝ) (y : ComplexModel n) : Mat n := (complexHessian u y)⁻¹

/-- `∂̄_p P = -P X_p* P`. -/
def aOne (u : ComplexModel n → ℝ) (p : Fin n) (y : ComplexModel n) : Mat n :=
  -(invH u y * (dH u p y)ᴴ * invH u y)

/-- `∂̄_p S`, by the Leibniz rule. -/
def stageOne (u : ComplexModel n → ℝ) (p : Fin n) (y : ComplexModel n) : ℂ :=
  calabiForm (aOne u p y) (invH u y) (fun m => dH u m y) (invH u y) (fun m => (dH u m y)ᴴ) +
    calabiForm (invH u y) (aOne u p y) (fun m => dH u m y) (invH u y) (fun m => (dH u m y)ᴴ) +
    calabiForm (invH u y) (invH u y) (fun m => dZ u m p y) (invH u y) (fun m => (dH u m y)ᴴ) +
    calabiForm (invH u y) (invH u y) (fun m => dH u m y) (aOne u p y) (fun m => (dH u m y)ᴴ) +
    calabiForm (invH u y) (invH u y) (fun m => dH u m y) (invH u y) (fun m => (dV u p m y)ᴴ)

theorem mdiffAt_invH (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : (complexHessian u y).det ≠ 0) : MDiffAt (invH u) y :=
  ((mSmooth_complexHessian hu).mdiffAt y).inv hy

theorem wirtM_invH (hu : ContDiff ℝ ∞ u) {y : ComplexModel n} (hy : (complexHessian u y).det ≠ 0)
    (c : ℂ) (p : Fin n) :
    wirtM c (coordinateVector p) (invH u) y =
      -(invH u y * wirtM c (coordinateVector p) (complexHessian u) y * invH u y) :=
  wirtM_inv ((mSmooth_complexHessian hu).mdiffAt y) hy

theorem wirtM_I_invH (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : (complexHessian u y).det ≠ 0) (p : Fin n) :
    wirtM I (coordinateVector p) (invH u) y = aOne u p y := by
  rw [wirtM_invH hu hy, wirtM_I_complexHessian hu]
  rfl

theorem wirt_calabiS (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : (complexHessian u y).det ≠ 0) (p : Fin n) :
    wirt I (coordinateVector p) (calabiS u) y = stageOne u p y := by
  have hP := mdiffAt_invH hu hy
  have hX : ∀ m, MDiffAt (fun z => dH u m z) y := fun m => (mSmooth_dH hu m).mdiffAt y
  have hXh : ∀ m, MDiffAt (fun z => (dH u m z)ᴴ) y := fun m =>
    ((mSmooth_dH hu m).conjTranspose).mdiffAt y
  have h := wirt_calabiForm (c := I) (v := coordinateVector p) (A := invH u) (B := invH u)
    (D := invH u) (C := fun z m => dH u m z) (Y := fun z m => (dH u m z)ᴴ) hP hP hX hP hXh
  unfold calabiS
  change wirt I (coordinateVector p) (fun z => calabiForm (invH u z) (invH u z)
    (fun m => dH u m z) (invH u z) (fun m => (dH u m z)ᴴ)) y = _
  rw [h, wirtM_I_invH hu hy]
  have hY : (fun t => wirtM I (coordinateVector p) (fun z => (dH u t z)ᴴ) y) =
      fun t => (dV u p t y)ᴴ := funext fun t => wirtM_I_conjTranspose ((mSmooth_dH hu t).mdiffAt y)
  rw [hY]
  rfl

/-- The summand of `calabiFlatSum` at `p`. -/
def flatSummand (X : Fin n → Mat n) (V Z : Fin n → Fin n → Mat n) (p : Fin n) : ℂ :=
  calabiForm (mDiag X Z p) 1 X 1 (fun t => (X t)ᴴ) +
    calabiForm 1 (mDiag X Z p) X 1 (fun t => (X t)ᴴ) +
    calabiForm 1 1 X (mDiag X Z p) (fun t => (X t)ᴴ) +
    calabiForm (-X p) (-(X p)ᴴ) X 1 (fun t => (X t)ᴴ) +
    calabiForm (-(X p)ᴴ) (-X p) X 1 (fun t => (X t)ᴴ) +
    calabiForm (-X p) 1 (fun m => Z m p) 1 (fun t => (X t)ᴴ) +
    calabiForm (-(X p)ᴴ) 1 (V p) 1 (fun t => (X t)ᴴ) +
    calabiForm (-X p) 1 X (-(X p)ᴴ) (fun t => (X t)ᴴ) +
    calabiForm (-(X p)ᴴ) 1 X (-X p) (fun t => (X t)ᴴ) +
    calabiForm (-X p) 1 X 1 (fun t => (V p t)ᴴ) +
    calabiForm (-(X p)ᴴ) 1 X 1 (Z p) +
    calabiForm 1 (-X p) (fun m => Z m p) 1 (fun t => (X t)ᴴ) +
    calabiForm 1 (-(X p)ᴴ) (V p) 1 (fun t => (X t)ᴴ) +
    calabiForm 1 (-X p) X (-(X p)ᴴ) (fun t => (X t)ᴴ) +
    calabiForm 1 (-(X p)ᴴ) X (-X p) (fun t => (X t)ᴴ) +
    calabiForm 1 (-X p) X 1 (fun t => (V p t)ᴴ) +
    calabiForm 1 (-(X p)ᴴ) X 1 (Z p) +
    calabiForm 1 1 (V p) (-(X p)ᴴ) (fun t => (X t)ᴴ) +
    calabiForm 1 1 (fun m => Z m p) (-X p) (fun t => (X t)ᴴ) +
    calabiForm 1 1 (V p) 1 (fun t => (V p t)ᴴ) +
    calabiForm 1 1 (fun m => Z m p) 1 (Z p) +
    calabiForm 1 1 X (-X p) (fun t => (V p t)ᴴ) +
    calabiForm 1 1 X (-(X p)ᴴ) (Z p)

theorem calabiFlatSum_eq_sum (X : Fin n → Mat n) (V Z : Fin n → Fin n → Mat n)
    (SW : Fin n → Mat n) :
    calabiFlatSum X V Z SW = calabiForm 1 1 SW 1 (fun t => (X t)ᴴ) +
      calabiForm 1 1 X 1 (fun t => (SW t)ᴴ) + ∑ p, flatSummand X V Z p := rfl

theorem mdiffAt_aOne (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : (complexHessian u y).det ≠ 0) (p : Fin n) : MDiffAt (aOne u p) y :=
  (((mdiffAt_invH hu hy).mul ((mSmooth_dH hu p).conjTranspose.mdiffAt y)).mul
    (mdiffAt_invH hu hy)).neg

theorem sum_calabiForm_C {ι : Type*} [Fintype ι] (A B : Mat n) (f : ι → Fin n → Mat n) (D : Mat n)
    (Y : Fin n → Mat n) :
    ∑ p, calabiForm A B (f p) D Y = calabiForm A B (fun m => ∑ p, f p m) D Y := by
  unfold calabiForm
  simp only [Matrix.sum_mul, trace_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_calabiForm_Y {ι : Type*} [Fintype ι] (A B : Mat n) (C : Fin n → Mat n) (D : Mat n)
    (f : ι → Fin n → Mat n) :
    ∑ p, calabiForm A B C D (f p) = calabiForm A B C D (fun t => ∑ p, f p t) := by
  unfold calabiForm
  simp only [trace_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

section AtOne

variable {x : ComplexModel n} (hu : ContDiff ℝ ∞ u) (hx : complexHessian u x = 1)
include hu hx

theorem det_ne_zero_of_eq_one : (complexHessian u x).det ≠ 0 := by
  rw [hx, det_one]; exact one_ne_zero

theorem invH_eq_one : invH u x = 1 := by
  rw [invH, hx, inv_one]

theorem aOne_eq (p : Fin n) : aOne u p x = -(dH u p x)ᴴ := by
  rw [aOne, invH_eq_one hu hx, Matrix.one_mul, Matrix.mul_one]

theorem wirtM_negI_invH (p : Fin n) :
    wirtM (-I) (coordinateVector p) (invH u) x = -dH u p x := by
  rw [wirtM_invH hu (det_ne_zero_of_eq_one hu hx), invH_eq_one hu hx, Matrix.one_mul,
    Matrix.mul_one]
  rfl

theorem wirtM_negI_dH_conjTranspose (p t : Fin n) :
    wirtM (-I) (coordinateVector p) (fun y => (dH u t y)ᴴ) x = dZ u p t x := by
  rw [wirtM_negI_conjTranspose ((mSmooth_dH hu t).mdiffAt x)]
  exact dZ_conjTranspose hu t p x

theorem wirtM_negI_aOne (p : Fin n) :
    wirtM (-I) (coordinateVector p) (aOne u p) x =
      mDiag (fun m => dH u m x) (fun m q => dZ u m q x) p := by
  have hd := det_ne_zero_of_eq_one hu hx
  have hP := mdiffAt_invH hu hd
  have hXh := (mSmooth_dH hu p).conjTranspose.mdiffAt x
  change wirtM (-I) (coordinateVector p) (fun y => -(invH u y * (dH u p y)ᴴ * invH u y)) x = _
  rw [wirtM_neg ((hP.mul hXh).mul hP), wirtM_mul (hP.mul hXh) hP, wirtM_mul hP hXh,
    wirtM_negI_invH hu hx, wirtM_negI_dH_conjTranspose hu hx, invH_eq_one hu hx]
  simp only [mDiag, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  abel

/-- **The second Leibniz stage** at a point with `H = 1`. -/
theorem wirt_stageOne (p : Fin n) :
    wirt (-I) (coordinateVector p) (stageOne u p) x =
      calabiForm 1 1 (fun m => dW u p p m x) 1 (fun t => (dH u t x)ᴴ) +
        calabiForm 1 1 (fun m => dH u m x) 1 (fun t => (dW u p p t x)ᴴ) +
        flatSummand (fun m => dH u m x) (fun p m => dV u p m x) (fun m q => dZ u m q x) p := by
  have hd := det_ne_zero_of_eq_one hu hx
  have hP := mdiffAt_invH hu hd
  have hA := mdiffAt_aOne hu hd p
  have hX : ∀ m, MDiffAt (fun z => dH u m z) x := fun m => (mSmooth_dH hu m).mdiffAt x
  have hXh : ∀ m, MDiffAt (fun z => (dH u m z)ᴴ) x := fun m =>
    ((mSmooth_dH hu m).conjTranspose).mdiffAt x
  have hZ : ∀ m, MDiffAt (fun z => dZ u m p z) x := fun m => (mSmooth_dZ hu m p).mdiffAt x
  have hVh : ∀ m, MDiffAt (fun z => (dV u p m z)ᴴ) x := fun m =>
    ((mSmooth_dV hu p m).conjTranspose).mdiffAt x
  unfold stageOne
  rw [wirt_add5 (differentiableAt_calabiForm hA hP hX hP hXh)
    (differentiableAt_calabiForm hP hA hX hP hXh) (differentiableAt_calabiForm hP hP hZ hP hXh)
    (differentiableAt_calabiForm hP hP hX hA hXh) (differentiableAt_calabiForm hP hP hX hP hVh)]
  rw [wirt_calabiForm (C := fun z m => dH u m z) (Y := fun z m => (dH u m z)ᴴ) hA hP hX hP hXh,
    wirt_calabiForm (C := fun z m => dH u m z) (Y := fun z m => (dH u m z)ᴴ) hP hA hX hP hXh,
    wirt_calabiForm (C := fun z m => dZ u m p z) (Y := fun z m => (dH u m z)ᴴ) hP hP hZ hP hXh,
    wirt_calabiForm (C := fun z m => dH u m z) (Y := fun z m => (dH u m z)ᴴ) hP hP hX hA hXh,
    wirt_calabiForm (C := fun z m => dH u m z) (Y := fun z m => (dV u p m z)ᴴ) hP hP hX hP hVh]
  have e1 : (fun t => wirtM (-I) (coordinateVector p) (fun z => (dH u t z)ᴴ) x) =
      fun t => dZ u p t x := funext fun t => wirtM_negI_dH_conjTranspose hu hx p t
  have e2 : (fun t => wirtM (-I) (coordinateVector p) (fun z => (dV u p t z)ᴴ) x) =
      fun t => (dW u p p t x)ᴴ := funext fun t => by
    rw [wirtM_negI_conjTranspose ((mSmooth_dV hu p t).mdiffAt x), wirtM_I_dV hu]
  have e3 : (fun m => wirtM (-I) (coordinateVector p) (fun y => dH u m y) x) =
      fun m => dV u p m x := rfl
  have e4 : (fun m => wirtM (-I) (coordinateVector p) (fun y => dZ u m p y) x) =
      fun m => dW u p p m x := rfl
  rw [e1, e2, e3, e4, wirtM_negI_aOne hu hx, wirtM_negI_invH hu hx, aOne_eq hu hx,
    invH_eq_one hu hx]
  unfold flatSummand
  beta_reduce
  ring

/-- **`Σ_p ∂_p∂̄_p S` at a point with `H = 1`** is the 25-term Leibniz sum `calabiFlatSum` of the
derivatives `X = ∂H`, `V = ∂∂H`, `Z = ∂̄∂H`, `SW = Σ_p ∂_p∂̄_p∂H`. -/
theorem sum_wirt_wirt_calabiS :
    ∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p) (calabiS u)) x =
      calabiFlatSum (fun m => dH u m x) (fun p m => dV u p m x) (fun m q => dZ u m q x)
        (fun m => ∑ p, dW u p p m x) := by
  have hev : ∀ᶠ y in 𝓝 x, (complexHessian u y).det ≠ 0 :=
    (contDiff_det_complexHessian hu).continuous.continuousAt.eventually_ne
      (det_ne_zero_of_eq_one hu hx)
  have h1 : ∀ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p) (calabiS u)) x =
      wirt (-I) (coordinateVector p) (stageOne u p) x := fun p =>
    wirt_congr (hev.mono fun y hy => wirt_calabiS hu hy p)
  simp only [h1, wirt_stageOne hu hx, Finset.sum_add_distrib]
  rw [calabiFlatSum_eq_sum, sum_calabiForm_C, sum_calabiForm_Y]
  simp only [conjTranspose_sum]

end AtOne

end Data

end

end SGPT.Foundations.Analysis.Pending.CalabiFlatLaplacian
