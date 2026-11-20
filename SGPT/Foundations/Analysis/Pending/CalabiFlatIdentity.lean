import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
-- the expansion macro `calabi_expand` uses one fixed simp set for all reindexing lemmas
set_option linter.unusedSimpArgs false

/-!
# Calabi's identity for the third derivatives, flat coordinates, at a point where `H = 1`

Let `u` be a smooth real function on `ℂⁿ` with complex Hessian `H = (u_{jk̄})`, `P = H⁻¹`, and the
Christoffel matrices `Γ_m = ∂_m H · P` of the Kähler metric `H`. Calabi's quantity is
`S = Σ_{m,t} P_{tm} tr(P X_m P X_t*)`, `X_m = ∂_m H` (`= |Γ|²` in the metric `H`; `pss07-multiplier-krf:page-0008`,
(2.39)–(2.40)). At a point where `H = 1` the Laplacian `Δ'S = Σ_p ∂_p∂̄_p S` of the metric `H` is, by the
Leibniz rule, a sum of 25 terms `calabiFlatSum X V Z SW` in the data

* `X m = ∂_m H` (third derivatives), `V p m = ∂_p∂_m H`, `Z m q = ∂̄_q∂_m H` (fourth derivatives),
* `SW m = Σ_p ∂_p∂̄_p∂_m H` (fifth derivatives),

each a value of the five-slot form `calabiForm A B C D Y = Σ_{m,t} A_{tm} tr(B C_m D Y_t)` (the factors
`P, P, X, P, X*` of `S`, differentiated). This file proves the **flat Bochner–Kodaira identity**
(`calabiFlatSum_eq`): if the data have the symmetries of derivatives and satisfy the twice and thrice
differentiated equation `log det H = F` at the point (`F2 = (F_{ab̄})`, `F3 m = (F_{ab̄m})`),

  `Δ'S = |∇Γ|² + |∇̄Γ|² + 2 Re Σ_m tr(F3_m X_m*) - Ric(F2)`,

where `∇_pΓ_m = V_{pm} - X_p X_m - Σ_l (X_p)_{ml} X_l` (`calA`), `∇̄_qΓ_m = Z_{mq} - X_m X_q*` (`calB`) and
`Ric(F2)` (`ricTerm`) is linear in `F2` and quadratic in `X`. This is PSS (2.43)/(2.44) with flat
reference metric (`R̂ = 0`), written with ordinary derivatives at a point with `H = 1`
(`pss07-multiplier-krf:page-0009`); the reference-curvature terms are absent and the Ricci terms are
those of `Ric(H) = -∂∂̄F`.

The proof is pure algebra: every term is reduced, by reindexing finite sums with the symmetries of the
derivatives, to a few atoms (`kappa4`, the cross terms of the squares); the five quartic terms are all
equal to `kappa4`.

TN.4 B5, nonlinear track N4 (b), blueprint `bou:yau-c3-estimate`
.
-/

open Matrix

namespace SGPT.Foundations.Analysis.Pending.CalabiFlatIdentity

variable {n : ℕ}

/-- Square complex matrices of size `n`. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-! ### Reordering nested finite sums -/

section Swap

variable {α β : Type*} [Fintype α] [AddCommMonoid β]

theorem sw2_0 (f : α → α → β) :
    ∑ a, ∑ b, f a b =
      ∑ b, ∑ a, f a b :=
  Finset.sum_comm
theorem sw3_0 (f : α → α → α → β) :
    ∑ a, ∑ b, ∑ c, f a b c =
      ∑ b, ∑ a, ∑ c, f a b c :=
  Finset.sum_comm
theorem sw3_1 (f : α → α → α → β) :
    ∑ a, ∑ b, ∑ c, f a b c =
      ∑ a, ∑ c, ∑ b, f a b c :=
  Finset.sum_congr rfl fun _ _ => sw2_0 _
theorem sw4_0 (f : α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d =
      ∑ b, ∑ a, ∑ c, ∑ d, f a b c d :=
  Finset.sum_comm
theorem sw4_1 (f : α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d =
      ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
  Finset.sum_congr rfl fun _ _ => sw3_0 _
theorem sw4_2 (f : α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d =
      ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
  Finset.sum_congr rfl fun _ _ => sw3_1 _
theorem sw5_0 (f : α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e =
      ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e :=
  Finset.sum_comm
theorem sw5_1 (f : α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e =
      ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e :=
  Finset.sum_congr rfl fun _ _ => sw4_0 _
theorem sw5_2 (f : α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e =
      ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, f a b c d e :=
  Finset.sum_congr rfl fun _ _ => sw4_1 _
theorem sw5_3 (f : α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, f a b c d e :=
  Finset.sum_congr rfl fun _ _ => sw4_2 _
theorem sw6_0 (f : α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g :=
  Finset.sum_comm
theorem sw6_1 (f : α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ g, f a b c d e g :=
  Finset.sum_congr rfl fun _ _ => sw5_0 _
theorem sw6_2 (f : α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, ∑ g, f a b c d e g :=
  Finset.sum_congr rfl fun _ _ => sw5_1 _
theorem sw6_3 (f : α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, ∑ g, f a b c d e g :=
  Finset.sum_congr rfl fun _ _ => sw5_2 _
theorem sw6_4 (f : α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, ∑ e, f a b c d e g :=
  Finset.sum_congr rfl fun _ _ => sw5_3 _
theorem sw7_0 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h :=
  Finset.sum_comm
theorem sw7_1 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h :=
  Finset.sum_congr rfl fun _ _ => sw6_0 _
theorem sw7_2 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, ∑ g, ∑ h, f a b c d e g h :=
  Finset.sum_congr rfl fun _ _ => sw6_1 _
theorem sw7_3 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, ∑ g, ∑ h, f a b c d e g h :=
  Finset.sum_congr rfl fun _ _ => sw6_2 _
theorem sw7_4 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, ∑ e, ∑ h, f a b c d e g h :=
  Finset.sum_congr rfl fun _ _ => sw6_3 _
theorem sw7_5 (f : α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, f a b c d e g h =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ h, ∑ g, f a b c d e g h :=
  Finset.sum_congr rfl fun _ _ => sw6_4 _
theorem sw8_0 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i :=
  Finset.sum_comm
theorem sw8_1 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_0 _
theorem sw8_2 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_1 _
theorem sw8_3 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, ∑ g, ∑ h, ∑ i, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_2 _
theorem sw8_4 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ g, ∑ e, ∑ h, ∑ i, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_3 _
theorem sw8_5 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ h, ∑ g, ∑ i, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_4 _
theorem sw8_6 (f : α → α → α → α → α → α → α → α → β) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ h, ∑ i, f a b c d e g h i =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∑ i, ∑ h, f a b c d e g h i :=
  Finset.sum_congr rfl fun _ _ => sw7_5 _


end Swap

/-- Expands traces, products, adjoints and scalar multiples into nested index sums. -/
macro "calabi_expand" : tactic => `(tactic| simp only [Matrix.mul_one, Matrix.one_mul,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply, trace_neg, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, conjTranspose_sum, conjTranspose_smul, conjTranspose_mul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    trace_sum, trace_smul, smul_eq_mul, Matrix.sum_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul])

/-! ### The five-slot form -/

/-- `calabiForm A B C D Y = Σ_{m,t} A_{tm} tr(B C_m D Y_t)`: Calabi's quantity
`S = Σ_{m,t} P_{tm} tr(P X_m P X_t*)` is `calabiForm P P X P X*`. -/
def calabiForm (A B : Mat n) (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) : ℂ :=
  ∑ m, ∑ t, A t m * (B * C m * D * Y t).trace

theorem star_calabiForm (A B : Mat n) (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    star (calabiForm A B C D Y) =
      calabiForm Aᴴ Bᴴ (fun m => (Y m)ᴴ) Dᴴ (fun m => (C m)ᴴ) := by
  unfold calabiForm
  rw [Finset.sum_comm]
  simp only [star_sum, star_mul', ← trace_conjTranspose, conjTranspose_mul, conjTranspose_apply,
    Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem calabiForm_one (B : Mat n) (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    calabiForm 1 B C D Y = ∑ m, (B * C m * D * Y m).trace := by
  unfold calabiForm
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Matrix.one_apply]

theorem sum_calabiForm_left {ι : Type*} [Fintype ι] (f : ι → Mat n) (B : Mat n)
    (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    ∑ p, calabiForm (f p) B C D Y = calabiForm (∑ p, f p) B C D Y := by
  unfold calabiForm
  simp only [Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_calabiForm_mid {ι : Type*} [Fintype ι] (A : Mat n) (f : ι → Mat n)
    (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    ∑ p, calabiForm A (f p) C D Y = calabiForm A (∑ p, f p) C D Y := by
  unfold calabiForm
  simp only [Matrix.sum_mul, trace_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_calabiForm_right {ι : Type*} [Fintype ι] (A B : Mat n) (C : Fin n → Mat n)
    (f : ι → Mat n) (Y : Fin n → Mat n) :
    ∑ p, calabiForm A B C (f p) Y = calabiForm A B C (∑ p, f p) Y := by
  unfold calabiForm
  simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem calabiForm_sub_left (A A' B : Mat n) (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    calabiForm (A - A') B C D Y = calabiForm A B C D Y - calabiForm A' B C D Y := by
  simp only [calabiForm, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem calabiForm_sub_mid (A B B' : Mat n) (C : Fin n → Mat n) (D : Mat n) (Y : Fin n → Mat n) :
    calabiForm A (B - B') C D Y = calabiForm A B C D Y - calabiForm A B' C D Y := by
  simp only [calabiForm, Matrix.sub_mul, trace_sub, mul_sub, Finset.sum_sub_distrib]

theorem calabiForm_sub_right (A B : Mat n) (C : Fin n → Mat n) (D D' : Mat n)
    (Y : Fin n → Mat n) :
    calabiForm A B C (D - D') Y = calabiForm A B C D Y - calabiForm A B C D' Y := by
  simp only [calabiForm, Matrix.mul_sub, Matrix.sub_mul, trace_sub, mul_sub, Finset.sum_sub_distrib]

/-! ### The data and the two sides of the identity -/

/-- The second connection term of `∇_pΓ_m`: `Σ_l (X_p)_{ml} X_l`. -/
def lterm (X : Fin n → Mat n) (p m : Fin n) : Mat n := ∑ l, X p m l • X l

/-- `∇_pΓ_m = V_{pm} - X_p X_m - Σ_l (X_p)_{ml} X_l` at a point with `H = 1`. -/
def calA (X : Fin n → Mat n) (V : Fin n → Fin n → Mat n) (p m : Fin n) : Mat n :=
  V p m - X p * X m - lterm X p m

/-- `∇̄_qΓ_m = Z_{mq} - X_m X_q*` at a point with `H = 1`. -/
def calB (X : Fin n → Mat n) (Z : Fin n → Fin n → Mat n) (m q : Fin n) : Mat n :=
  Z m q - X m * (X q)ᴴ

/-- `∂_p∂̄_p P = X_p X_p* - Z_{pp} + X_p* X_p` at a point with `H = 1`. -/
def mDiag (X : Fin n → Mat n) (Z : Fin n → Fin n → Mat n) (p : Fin n) : Mat n :=
  X p * (X p)ᴴ - Z p p + (X p)ᴴ * X p

/-- The Ricci terms `Σ_{m,t} F_{tm̄} tr(X_m X_t*) + Σ_m tr(F X_m X_m*) + Σ_m tr(X_m F X_m*)`. -/
def ricTerm (X : Fin n → Mat n) (F2 : Mat n) : ℂ :=
  calabiForm F2 1 X 1 (fun t => (X t)ᴴ) + calabiForm 1 F2 X 1 (fun t => (X t)ᴴ) +
    calabiForm 1 1 X F2 (fun t => (X t)ᴴ)

/-- The quartic atom `κ₄ = Σ_{p,m,l} conj((X_p)_{ml}) tr(X_p X_m X_l*)`. -/
def kappa4 (X : Fin n → Mat n) : ℂ :=
  ∑ p, ∑ m, ∑ l, star (X p m l) * (X p * X m * (X l)ᴴ).trace

/-- `Δ'S` at a point with `H = 1`, by the Leibniz rule: the terms `T(i,j)` (`∂_p` on factor `j`,
`∂̄_p` on factor `i` of `S = Σ P_{tm} tr(P X_m P X_t*)`), summed over `p`. -/
def calabiFlatSum (X : Fin n → Mat n) (V Z : Fin n → Fin n → Mat n) (SW : Fin n → Mat n) : ℂ :=
  calabiForm 1 1 SW 1 (fun t => (X t)ᴴ) + calabiForm 1 1 X 1 (fun t => (SW t)ᴴ) +
  ∑ p, (calabiForm (mDiag X Z p) 1 X 1 (fun t => (X t)ᴴ) +
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
    calabiForm 1 1 X (-(X p)ᴴ) (Z p))

/-! ### Reindexing lemmas -/

section Reindex

variable (X : Fin n → Mat n) (V Z : Fin n → Fin n → Mat n)

theorem sum_T12 (hX : ∀ m a b, X m a b = X a m b) :
    ∑ p, calabiForm (-X p) (-(X p)ᴴ) X 1 (fun t => (X t)ᴴ) = kappa4 X := by
  unfold calabiForm kappa4
  calabi_expand
  conv_lhs => rw [sw6_4]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_4]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hX m i b, hX t a b]
  ring

theorem sum_T14 (hX : ∀ m a b, X m a b = X a m b) :
    ∑ p, calabiForm (-X p) 1 X (-(X p)ᴴ) (fun t => (X t)ᴴ) = kappa4 X := by
  unfold calabiForm kappa4
  calabi_expand
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_0]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_4]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun x_4 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hX x_3 x i]
  conv_lhs => rw [hX i x_1 x_4]
  conv_lhs => rw [hX x_3 x_2 x_4]
  all_goals ring

theorem sum_T24 (hX : ∀ m a b, X m a b = X a m b) :
    ∑ p, calabiForm 1 (-X p) X (-(X p)ᴴ) (fun t => (X t)ᴴ) = kappa4 X := by
  simp only [calabiForm_one]
  unfold kappa4
  calabi_expand
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_0]
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_2]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun x_4 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hX x_3 x i]
  conv_lhs => rw [hX x_3 x_2 x_4]
  conv_lhs => rw [hX x_1 x x_2]
  all_goals ring

theorem sum_A4 :
    ∑ m, ∑ a, ∑ b, (X m * X a * (X b)ᴴ).trace * star (X m a b) = kappa4 X := by
  unfold kappa4
  calabi_expand
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun x_4 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  all_goals ring

theorem sum_A5 (hX : ∀ m a b, X m a b = X a m b) :
    ∑ m, ∑ a, ∑ b, (X a * X m * (X b)ᴴ).trace * star (X m a b) = kappa4 X := by
  unfold kappa4
  calabi_expand
  conv_lhs => rw [sw6_0]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun x_4 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hX x_1 x x_2]
  all_goals ring

theorem sum_R1 (hX : ∀ m a b, X m a b = X a m b) (hV' : ∀ p m a b, V p m a b = V p a m b) :
    ∑ m, ∑ a, ∑ b, (V m a * (X b)ᴴ).trace * star (X m a b) =
      -∑ p, calabiForm 1 (-(X p)ᴴ) (V p) 1 (fun t => (X t)ᴴ) := by
  simp only [calabiForm_one]
  calabi_expand
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_1]
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_3]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hV' x i x_1 x_3]
  conv_lhs => rw [hX x_2 x_1 x_3]
  all_goals ring

theorem sum_R2 (hX : ∀ m a b, X m a b = X a m b) (hZq : ∀ m q a b, Z m q a b = Z m b a q) :
    ∑ m, ∑ a, ∑ b, (X a * Z m b).trace * star (X m a b) =
      -∑ p, calabiForm 1 (-X p) (fun m => Z m p) 1 (fun t => (X t)ᴴ) := by
  simp only [calabiForm_one]
  calabi_expand
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_1]
  conv_lhs => rw [sw5_0]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hX x_2 x i]
  conv_lhs => rw [hZq x_1 x_3 i x]

theorem sum_R3 (hX : ∀ m a b, X m a b = X a m b) (hZ : ∀ m q a b, Z m q a b = Z a q m b)
    (hZq : ∀ m q a b, Z m q a b = Z m b a q) :
    ∑ m, ∑ a, ∑ b, (X m * Z a b).trace * star (X m a b) =
      -∑ p, calabiForm (-X p) 1 (fun m => Z m p) 1 (fun t => (X t)ᴴ) := by
  unfold calabiForm
  calabi_expand
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_1]
  conv_lhs => rw [sw5_0]
  conv_lhs => rw [sw5_3]
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_1]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun x_3 _ => ?_
  refine Finset.sum_congr rfl fun x_4 _ => ?_
  conv_lhs => rw [hX x_2 x x_1]
  conv_lhs => rw [hZ x_3 x_4 x_1 x]
  conv_lhs => rw [hZq x_1 x_4 x_3 x]
  all_goals ring

theorem calabiForm_K_left :
    calabiForm (∑ p, (X p)ᴴ * X p) 1 X 1 (fun t => (X t)ᴴ) =
      ∑ p, ∑ m, (lterm X p m * (lterm X p m)ᴴ).trace := by
  unfold calabiForm lterm
  calabi_expand
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_0]
  conv_lhs => rw [sw6_4]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_1]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_2]
  conv_lhs => rw [sw6_4]
  conv_lhs => rw [sw6_3]
  conv_lhs => rw [sw6_4]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun x_2 _ => ?_
  refine Finset.sum_congr rfl fun i_1 _ => ?_
  all_goals ring

theorem sum_T31 :
    ∑ p, calabiForm (-(X p)ᴴ) 1 (V p) 1 (fun t => (X t)ᴴ) =
      -∑ p, ∑ m, (V p m * (lterm X p m)ᴴ).trace := by
  unfold calabiForm lterm
  calabi_expand
  rw [neg_inj]
  conv_lhs => rw [sw5_2]
  conv_lhs => rw [sw5_3]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  refine Finset.sum_congr rfl fun i_1 _ => ?_
  all_goals ring

theorem sum_T34 (hV : ∀ p m, V p m = V m p) :
    ∑ p, calabiForm 1 1 (V p) (-(X p)ᴴ) (fun t => (X t)ᴴ) =
      -∑ p, ∑ m, (V p m * (X p * X m)ᴴ).trace := by
  simp only [calabiForm_one]
  calabi_expand
  rw [neg_inj]
  conv_lhs => rw [sw5_0]
  conv_lhs => rw [sw5_3]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i_1 _ => ?_
  conv_lhs => rw [hV m x]
  all_goals ring


end Reindex

/-! ### Matrix identities from the symmetries and the equation -/

section Identity

variable (X : Fin n → Mat n) (V Z : Fin n → Fin n → Mat n) (SW : Fin n → Mat n) (F2 : Mat n)
  (F3 : Fin n → Mat n)

theorem trace_mul_conjTranspose (M N : Mat n) :
    (M * Nᴴ).trace = ∑ a, ∑ b, M a b * star (N a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem sum_mul_conjTranspose_self (hX : ∀ m a b, X m a b = X a m b) :
    ∑ p, X p * (X p)ᴴ = Matrix.of fun t m => (X t * (X m)ᴴ).trace := by
  ext t m
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hX a t b, hX a m b]

theorem sum_diag_eq_trace (hZ : ∀ m q a b, Z m q a b = Z a q m b)
    (hZq : ∀ m q a b, Z m q a b = Z m b a q) :
    ∑ p, Z p p = Matrix.of fun a b => (Z a b).trace := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.of_apply, Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hZ p p a b, hZq a p p b]

theorem sum_mDiag (hX : ∀ m a b, X m a b = X a m b) (hZ : ∀ m q a b, Z m q a b = Z a q m b)
    (hZq : ∀ m q a b, Z m q a b = Z m b a q)
    (hF2 : ∀ a b, (Z a b).trace = F2 a b + (X a * (X b)ᴴ).trace) :
    ∑ p, mDiag X Z p = ∑ p, (X p)ᴴ * X p - F2 := by
  unfold mDiag
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_mul_conjTranspose_self X hX, sum_diag_eq_trace Z hZ hZq]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, hF2]
  ring

theorem calabiForm_K_mid :
    calabiForm 1 (∑ p, (X p)ᴴ * X p) X 1 (fun t => (X t)ᴴ) =
      ∑ p, ∑ m, (X p * X m * (X p * X m)ᴴ).trace := by
  rw [calabiForm_one]
  simp only [Matrix.mul_one, Matrix.sum_mul, trace_sum, conjTranspose_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem calabiForm_K_right :
    calabiForm 1 1 X (∑ p, (X p)ᴴ * X p) (fun t => (X t)ᴴ) =
      ∑ m, ∑ q, (X m * (X q)ᴴ * (X m * (X q)ᴴ)ᴴ).trace := by
  rw [calabiForm_one]
  simp only [Matrix.one_mul, Matrix.mul_sum, Matrix.sum_mul, trace_sum, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem sum_T35 :
    ∑ p, calabiForm 1 1 (V p) 1 (fun t => (V p t)ᴴ) = ∑ p, ∑ m, (V p m * (V p m)ᴴ).trace := by
  simp only [calabiForm_one, Matrix.one_mul, Matrix.mul_one]

theorem sum_T43 :
    ∑ p, calabiForm 1 1 (fun m => Z m p) (-X p) (fun t => (X t)ᴴ) =
      -∑ m, ∑ q, (Z m q * (X m * (X q)ᴴ)ᴴ).trace := by
  simp only [calabiForm_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, trace_neg,
    Finset.sum_neg_distrib, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Finset.sum_comm]

theorem sum_T53 (hZ' : ∀ m q, (Z m q)ᴴ = Z q m) :
    ∑ p, calabiForm 1 1 (fun m => Z m p) 1 (Z p) = ∑ m, ∑ q, (Z m q * (Z m q)ᴴ).trace := by
  simp only [calabiForm_one, Matrix.one_mul, Matrix.mul_one, hZ']
  rw [Finset.sum_comm]

theorem kappa4_eq_cross :
    ∑ p, ∑ m, (X p * X m * (lterm X p m)ᴴ).trace = kappa4 X := by
  unfold lterm kappa4
  simp only [conjTranspose_sum, conjTranspose_smul, Matrix.mul_sum, Matrix.mul_smul, trace_sum,
    trace_smul, smul_eq_mul]

/-- The fifth-derivative term, through the thrice differentiated equation. -/
theorem calabiForm_SW
    (hSW : ∀ m a b, SW m a b = F3 m a b + (X m * Z a b).trace - (X m * X a * (X b)ᴴ).trace -
      (X a * X m * (X b)ᴴ).trace + (V m a * (X b)ᴴ).trace + (X a * Z m b).trace) :
    calabiForm 1 1 SW 1 (fun t => (X t)ᴴ) =
      ∑ m, (F3 m * (X m)ᴴ).trace +
        ∑ m, ∑ a, ∑ b, (X m * Z a b).trace * star (X m a b) -
        ∑ m, ∑ a, ∑ b, (X m * X a * (X b)ᴴ).trace * star (X m a b) -
        ∑ m, ∑ a, ∑ b, (X a * X m * (X b)ᴴ).trace * star (X m a b) +
        ∑ m, ∑ a, ∑ b, (V m a * (X b)ᴴ).trace * star (X m a b) +
        ∑ m, ∑ a, ∑ b, (X a * Z m b).trace * star (X m a b) := by
  rw [calabiForm_one]
  simp only [Matrix.one_mul, Matrix.mul_one]
  have h1 : ∀ m, (SW m * (X m)ᴴ).trace = ∑ a, ∑ b, SW m a b * star (X m a b) := fun m =>
    trace_mul_conjTranspose _ _
  have h2 : ∀ m, (F3 m * (X m)ᴴ).trace = ∑ a, ∑ b, F3 m a b * star (X m a b) := fun m =>
    trace_mul_conjTranspose _ _
  simp only [h1, h2, hSW, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem trace_sq_sub_sub (A W L : Mat n) :
    ((A - W - L) * (A - W - L)ᴴ).trace =
      (A * Aᴴ).trace - (A * Wᴴ).trace - (A * Lᴴ).trace - star (A * Wᴴ).trace -
        star (A * Lᴴ).trace + (W * Wᴴ).trace + (W * Lᴴ).trace + star (W * Lᴴ).trace +
        (L * Lᴴ).trace := by
  simp only [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, trace_sub]
  ring

theorem trace_sq_sub (A W : Mat n) :
    ((A - W) * (A - W)ᴴ).trace =
      (A * Aᴴ).trace - (A * Wᴴ).trace - star (A * Wᴴ).trace + (W * Wᴴ).trace := by
  simp only [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, trace_sub]
  ring

/-- **Calabi's identity in flat coordinates at a point with `H = 1`** (PSS (2.43)/(2.44) with flat
reference metric, `pss07-multiplier-krf:page-0009`):
`Δ'S = |∇Γ|² + |∇̄Γ|² + 2 Re Σ_m tr(F3_m X_m*) - Ric(F2)`. -/
theorem calabiFlatSum_eq (hX : ∀ m a b, X m a b = X a m b) (hV : ∀ p m, V p m = V m p)
    (hV' : ∀ p m a b, V p m a b = V p a m b) (hZ : ∀ m q a b, Z m q a b = Z a q m b)
    (hZq : ∀ m q a b, Z m q a b = Z m b a q) (hZ' : ∀ m q, (Z m q)ᴴ = Z q m)
    (hF2 : ∀ a b, (Z a b).trace = F2 a b + (X a * (X b)ᴴ).trace)
    (hSW : ∀ m a b, SW m a b = F3 m a b + (X m * Z a b).trace - (X m * X a * (X b)ᴴ).trace -
      (X a * X m * (X b)ᴴ).trace + (V m a * (X b)ᴴ).trace + (X a * Z m b).trace) :
    calabiFlatSum X V Z SW =
      ∑ p, ∑ m, (calA X V p m * (calA X V p m)ᴴ).trace +
        ∑ m, ∑ q, (calB X Z m q * (calB X Z m q)ᴴ).trace +
        (∑ m, (F3 m * (X m)ᴴ).trace + star (∑ m, (F3 m * (X m)ᴴ).trace)) - ricTerm X F2 := by
  -- the conjugate pairs
  have s0 : calabiForm 1 1 X 1 (fun t => (SW t)ᴴ) =
      star (calabiForm 1 1 SW 1 (fun t => (X t)ᴴ)) := by
    rw [star_calabiForm]; simp
  have s1 : ∀ p, calabiForm (-(X p)ᴴ) (-X p) X 1 (fun t => (X t)ᴴ) =
      star (calabiForm (-X p) (-(X p)ᴴ) X 1 (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s2 : ∀ p, calabiForm (-(X p)ᴴ) 1 X 1 (Z p) =
      star (calabiForm (-X p) 1 (fun m => Z m p) 1 (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp [hZ']
  have s3 : ∀ p, calabiForm (-X p) 1 X 1 (fun t => (V p t)ᴴ) =
      star (calabiForm (-(X p)ᴴ) 1 (V p) 1 (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s4 : ∀ p, calabiForm (-(X p)ᴴ) 1 X (-X p) (fun t => (X t)ᴴ) =
      star (calabiForm (-X p) 1 X (-(X p)ᴴ) (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s5 : ∀ p, calabiForm 1 (-(X p)ᴴ) X 1 (Z p) =
      star (calabiForm 1 (-X p) (fun m => Z m p) 1 (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp [hZ']
  have s6 : ∀ p, calabiForm 1 (-X p) X 1 (fun t => (V p t)ᴴ) =
      star (calabiForm 1 (-(X p)ᴴ) (V p) 1 (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s7 : ∀ p, calabiForm 1 (-(X p)ᴴ) X (-X p) (fun t => (X t)ᴴ) =
      star (calabiForm 1 (-X p) X (-(X p)ᴴ) (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s8 : ∀ p, calabiForm 1 1 X (-X p) (fun t => (V p t)ᴴ) =
      star (calabiForm 1 1 (V p) (-(X p)ᴴ) (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp
  have s9 : ∀ p, calabiForm 1 1 X (-(X p)ᴴ) (Z p) =
      star (calabiForm 1 1 (fun m => Z m p) (-X p) (fun t => (X t)ᴴ)) := fun p => by
    rw [star_calabiForm]; simp [hZ']
  unfold calabiFlatSum
  simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, Finset.sum_add_distrib, ← star_sum]
  rw [sum_T12 X hX, sum_T14 X hX, sum_T24 X hX, sum_T31 X V, sum_T34 X V hV, sum_T35 V,
    sum_T43 X Z, sum_T53 Z hZ', sum_calabiForm_left, sum_calabiForm_mid, sum_calabiForm_right,
    sum_mDiag X Z F2 hX hZ hZq hF2, calabiForm_sub_left, calabiForm_sub_mid, calabiForm_sub_right,
    calabiForm_K_left, calabiForm_K_mid, calabiForm_K_right,
    calabiForm_SW X V Z SW F3 hSW, sum_A4, sum_A5 X hX, sum_R1 X V hX hV', sum_R2 X Z hX hZq,
    sum_R3 X Z hX hZ hZq]
  simp only [calA, trace_sq_sub_sub]
  simp only [calB, trace_sq_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← star_sum, kappa4_eq_cross, ricTerm, star_add, star_sub, star_neg]
  ring

end Identity

end SGPT.Foundations.Analysis.Pending.CalabiFlatIdentity
