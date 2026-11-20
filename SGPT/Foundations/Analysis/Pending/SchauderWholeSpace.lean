import SGPT.Foundations.Analysis.Pending.SchauderBlowup
import SGPT.Foundations.Analysis.Pending.HolderInterpolation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Schauder estimate on the whole space, `C⁰` form, with lower-order terms

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, and
`0 < α < 1`.  For coefficients `a : E → (E →L[ℝ] E)` in `IsEllipticCoeff a λ Λ α` (symmetric,
`λ`-elliptic, bounded by `Λ`, `(Λ, α)`-Hölder) and lower-order coefficients `β : E → E`,
`c : E → ℝ` in `IsLowerCoeff β c Λ α` (bounded by `Λ`, `(Λ, α)`-Hölder), let

`L u (x) = a(x) : D²u(x) + Du(x)(β x) + c(x) u(x)`   (`ellipticOp b a β c u x`).

**The Schauder estimate** (`exists_schauder_estimate`): there is `C = C(b, λ, Λ, α)` such that every
`C²` function `u` with bounded, `α`-Hölder second derivative satisfies

`[D²u]_α + |D²u|_0 + |Du|_0 ≤ C ([L u]_α + |u|_0)`

(each of the three terms separately, with the same `C`).  This is the whole-space (global) form of
estimate (2.3) of Székelyhidi, Theorem 2.8 (`szekelyhidi-extremal:page-0044`), for `k = 0`; there
the right-hand side carries the full norm `‖L u‖_{C^α} = |L u|_0 + [L u]_α` -- on the whole space
the Hölder seminorm suffices.

The proof combines Simon's estimate `SchauderBlowup.exists_holder_hessian_le`
(`[D²u]_α ≤ C₀ ([a : D²u]_α + |D²u|_0)`) with the interpolation inequalities of
`HolderInterpolation`: the lower-order terms are absorbed into `[a : D²u]_α` with
`[Du]_α ≤ 3 |D²u|_0 + 4 |u|_0`, `[u]_α ≤ |D²u|_0 + 4 |u|_0`, `|Du|_0 ≤ 2 |u|_0 + |D²u|_0`, and
`|D²u|_0 ≤ 32 |u|_0 / ρ² + 2 [D²u]_α ρ^α` is absorbed for a fixed small `ρ`.  (Székelyhidi passes
from the `C²` form to the `C⁰` form by a second blow-up, `page-0047`; on the whole space
interpolation suffices.)

Part L2.7 (`C⁰` form, lower-order terms) of the linear track for Yau's theorem
(the linear elliptic estimates; blueprint `bou:schauder-interior`).
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.SchauderWholeSpace

open EllipticMeanValue SchauderBlowup HolderInterpolation

/-! ### Hölder bounds from Lipschitz and sup bounds -/

section Generic

variable {X : Type*} [NormedAddCommGroup X] {Y : Type*} [NormedAddCommGroup Y]

/-- A bounded Lipschitz map is `α`-Hölder for every `α ∈ [0, 1]`:
`‖g x - g y‖ ≤ (L + 2K) ‖x - y‖^α` when `g` is `L`-Lipschitz and bounded by `K`. -/
theorem norm_sub_le_rpow_of_lipschitz_of_bound {g : X → Y} {L K α : ℝ} (hL0 : 0 ≤ L)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hK : ∀ x, ‖g x‖ ≤ K) (x y : X) : ‖g x - g y‖ ≤ (L + 2 * K) * ‖x - y‖ ^ α := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x)
  have hpow0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  rcases le_total ‖x - y‖ 1 with h1 | h1
  · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
      rcases (norm_nonneg (x - y)).eq_or_lt with h0 | h0
      · rw [← h0]; exact Real.rpow_nonneg le_rfl _
      · calc ‖x - y‖ = ‖x - y‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow_of_exponent_ge h0 h1 hα1
    calc ‖g x - g y‖ ≤ L * ‖x - y‖ := hL x y
      _ ≤ L * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hle hL0
      _ ≤ (L + 2 * K) * ‖x - y‖ ^ α := by nlinarith
  · have hge : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow h1 hα0
    calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * K := by linarith [hK x, hK y]
      _ ≤ 2 * K * ‖x - y‖ ^ α := le_mul_of_one_le_right (by positivity) hge
      _ ≤ (L + 2 * K) * ‖x - y‖ ^ α := by nlinarith

end Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### The operator -/

/-- Lower-order coefficients of an elliptic operator: a vector field `β` and a function `c`, both
bounded by `Λ` and `(Λ, α)`-Hölder. -/
structure IsLowerCoeff (β : E → E) (c : E → ℝ) (Λ α : ℝ) : Prop where
  bound_β : ∀ x, ‖β x‖ ≤ Λ
  holder_β : ∀ x y, ‖β x - β y‖ ≤ Λ * ‖x - y‖ ^ α
  bound_c : ∀ x, |c x| ≤ Λ
  holder_c : ∀ x y, |c x - c y| ≤ Λ * ‖x - y‖ ^ α

/-- The second-order operator `L u (x) = a(x) : D²u(x) + Du(x)(β x) + c(x) u(x)`, with
`a(x) : Q = hessTrace b (a x) Q = ∑ᵢ Q (bᵢ) (a(x) bᵢ)`. -/
def ellipticOp (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ) (u : E → ℝ) (x : E) : ℝ :=
  hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) + fderiv ℝ u x (β x) + c x * u x

theorem isLowerCoeff_zero {Λ α : ℝ} (hΛ : 0 ≤ Λ) :
    IsLowerCoeff (fun _ : E => (0 : E)) (fun _ => (0 : ℝ)) Λ α where
  bound_β _ := by simpa using hΛ
  holder_β _ _ := by simp only [sub_self, norm_zero]; positivity
  bound_c _ := by simpa using hΛ
  holder_c _ _ := by simp only [sub_self, abs_zero]; positivity

theorem ellipticOp_zero (a : E → E →L[ℝ] E) (u : E → ℝ) (x : E) :
    ellipticOp b a (fun _ => 0) (fun _ => 0) u x = hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) := by
  simp [ellipticOp]

theorem nonneg_of_isEllipticCoeff {a : E → E →L[ℝ] E} {lam Λ α : ℝ}
    (ha : IsEllipticCoeff a lam Λ α) : 0 ≤ Λ :=
  (norm_nonneg _).trans (ha.bound 0)

/-! ### First-order bounds from `|u|_0` and `|D²u|_0` -/

section FirstOrder

variable {u : E → ℝ}

/-- `Du` is `B`-Lipschitz when `|D²u|_0 ≤ B`. -/
theorem norm_fderiv_sub_le (hu : ContDiff ℝ 2 u) {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) (x y : E) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ B * ‖x - y‖ := by
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  have h := holderWith_one_fderiv_of_bound hu (M := B.toNNReal) fun y => by
    rw [Real.coe_toNNReal _ hB0]; exact hB y
  have := h.dist_le x y
  rwa [Real.coe_toNNReal _ hB0, NNReal.coe_one, Real.rpow_one, dist_eq_norm, dist_eq_norm] at this

/-- `|Du|_0 ≤ 2 |u|_0 + |D²u|_0`. -/
theorem norm_fderiv_le_two_mul_add (hu : ContDiff ℝ 2 u) {A B : ℝ} (hA : ∀ x, |u x| ≤ A)
    (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) (x : E) : ‖fderiv ℝ u x‖ ≤ 2 * A + B := by
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  have hlip : HolderWith B.toNNReal 1 (fderiv ℝ u) :=
    holderWith_one_fderiv_of_bound hu fun y => by rw [Real.coe_toNNReal _ hB0]; exact hB y
  have h := norm_fderiv_le_of_holderWith (hu.differentiable (by norm_num))
    (A := A) (fun y => by rw [Real.norm_eq_abs]; exact hA y) hlip one_pos x
  rwa [Real.coe_toNNReal _ hB0, NNReal.coe_one, Real.rpow_one, div_one, mul_one] at h

/-- `u` is `D`-Lipschitz when `|Du|_0 ≤ D`. -/
theorem abs_sub_le_of_fderiv (hu : ContDiff ℝ 2 u) {D : ℝ} (hD : ∀ x, ‖fderiv ℝ u x‖ ≤ D)
    (x y : E) : |u x - u y| ≤ D * ‖x - y‖ := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z _ => hD z) (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

/-- `[Du]_α ≤ 3 |D²u|_0 + 4 |u|_0`. -/
theorem norm_fderiv_sub_le_rpow (hu : ContDiff ℝ 2 u) {A B α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA : ∀ x, |u x| ≤ A) (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) (x y : E) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ (3 * B + 4 * A) * ‖x - y‖ ^ α := by
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  have h := norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] ℝ) hB0 hα0 hα1
    (norm_fderiv_sub_le hu hB) (norm_fderiv_le_two_mul_add hu hA hB) x y
  calc ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ (B + 2 * (2 * A + B)) * ‖x - y‖ ^ α := h
    _ = (3 * B + 4 * A) * ‖x - y‖ ^ α := by ring

/-- `[u]_α ≤ |D²u|_0 + 4 |u|_0`. -/
theorem abs_sub_le_rpow (hu : ContDiff ℝ 2 u) {A B α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA : ∀ x, |u x| ≤ A) (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) (x y : E) :
    |u x - u y| ≤ (B + 4 * A) * ‖x - y‖ ^ α := by
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have h := norm_sub_le_rpow_of_lipschitz_of_bound (g := u) (by positivity : 0 ≤ 2 * A + B)
    hα0 hα1 (fun x y => by
      rw [Real.norm_eq_abs]
      exact abs_sub_le_of_fderiv hu (norm_fderiv_le_two_mul_add hu hA hB) x y)
    (fun x => by rw [Real.norm_eq_abs]; exact hA x) x y
  rw [Real.norm_eq_abs] at h
  calc |u x - u y| ≤ (2 * A + B + 2 * A) * ‖x - y‖ ^ α := h
    _ = (B + 4 * A) * ‖x - y‖ ^ α := by ring

/-- **The lower-order terms are Hölder**: `[Du · β + c u]_α ≤ Λ (11 |u|_0 + 5 |D²u|_0)`. -/
theorem abs_lowerOrder_sub_le (hu : ContDiff ℝ 2 u) {β : E → E} {c : E → ℝ} {Λ α A B : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβc : IsLowerCoeff β c Λ α) (hA : ∀ x, |u x| ≤ A)
    (hB : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) (x y : E) :
    |(fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)| ≤
      Λ * (11 * A + 5 * B) * ‖x - y‖ ^ α := by
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hβc.bound_c 0)
  have hp0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  set p := ‖x - y‖ ^ α with hp
  -- first-order term
  have h1 : |fderiv ℝ u x (β x) - fderiv ℝ u y (β y)| ≤ Λ * (6 * A + 4 * B) * p := by
    have hsplit : fderiv ℝ u x (β x) - fderiv ℝ u y (β y) =
        fderiv ℝ u x (β x - β y) + (fderiv ℝ u x - fderiv ℝ u y) (β y) := by
      simp only [map_sub, sub_apply]; ring
    rw [hsplit, ← Real.norm_eq_abs]
    have hDx := norm_fderiv_le_two_mul_add hu hA hB x
    have hDxy := norm_fderiv_sub_le_rpow hu hα0 hα1 hA hB x y
    calc ‖fderiv ℝ u x (β x - β y) + (fderiv ℝ u x - fderiv ℝ u y) (β y)‖
        ≤ ‖fderiv ℝ u x‖ * ‖β x - β y‖ + ‖fderiv ℝ u x - fderiv ℝ u y‖ * ‖β y‖ :=
          (norm_add_le _ _).trans (add_le_add ((fderiv ℝ u x).le_opNorm _)
            ((fderiv ℝ u x - fderiv ℝ u y).le_opNorm _))
      _ ≤ (2 * A + B) * (Λ * p) + ((3 * B + 4 * A) * p) * Λ := by
          gcongr
          · exact hβc.holder_β x y
          · exact hβc.bound_β y
      _ = Λ * (6 * A + 4 * B) * p := by ring
  -- zeroth-order term
  have h2 : |c x * u x - c y * u y| ≤ Λ * (5 * A + B) * p := by
    have hsplit : c x * u x - c y * u y = c x * (u x - u y) + (c x - c y) * u y := by ring
    rw [hsplit]
    have hux := abs_sub_le_rpow hu hα0 hα1 hA hB x y
    calc |c x * (u x - u y) + (c x - c y) * u y| ≤ |c x| * |u x - u y| + |c x - c y| * |u y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Λ * ((B + 4 * A) * p) + (Λ * p) * A := by
          gcongr
          · exact hβc.bound_c x
          · exact hβc.holder_c x y
          · exact hA y
      _ = Λ * (5 * A + B) * p := by ring
  calc |(fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)|
      = |(fderiv ℝ u x (β x) - fderiv ℝ u y (β y)) + (c x * u x - c y * u y)| := by ring_nf
    _ ≤ |fderiv ℝ u x (β x) - fderiv ℝ u y (β y)| + |c x * u x - c y * u y| := abs_add_le _ _
    _ ≤ Λ * (6 * A + 4 * B) * p + Λ * (5 * A + B) * p := add_le_add h1 h2
    _ = Λ * (11 * A + 5 * B) * p := by ring

end FirstOrder

/-! ### The estimate -/

/-- **The Schauder estimate on the whole space, `C⁰` form** (Székelyhidi Thm 2.8, estimate (2.3)
for `k = 0`, global form; lower-order terms included): there is `C = C(b, λ, Λ, α) ≥ 0` such that
for all coefficients `a ∈ IsEllipticCoeff a λ Λ α`, `(β, c) ∈ IsLowerCoeff β c Λ α` and every `C²`
function `u` with bounded `α`-Hölder second derivative, `|u| ≤ A` and `[L u]_α ≤ M`:
`[D²u]_α ≤ C (M + A)`, `|D²u|_0 ≤ C (M + A)` and `|Du|_0 ≤ C (M + A)`. -/
theorem exists_schauder_estimate {lam Λ α : ℝ} (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E → E →L[ℝ] E) (β : E → E) (c : E → ℝ),
      IsEllipticCoeff a lam Λ α → IsLowerCoeff β c Λ α →
      ∀ u : E → ℝ, ContDiff ℝ 2 u →
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) →
      ∀ A M : ℝ, 0 ≤ M → (∀ x, |u x| ≤ A) →
      (∀ x y, |ellipticOp b a β c u x - ellipticOp b a β c u y| ≤ M * ‖x - y‖ ^ α) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (M + A) * ‖x - y‖ ^ α) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (M + A)) ∧
      (∀ x, ‖fderiv ℝ u x‖ ≤ C * (M + A)) := by
  obtain ⟨C₀, hC₀, hS⟩ := exists_holder_hessian_le (Λ := Λ) b hlam hα0 hα1
  set L : ℝ := |Λ| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  -- the absorption scale `ρ`, with `ρ^α = t`
  set t : ℝ := 1 / (4 * (C₀ + 1) * (5 * L + 1)) with ht
  have ht0 : 0 < t := by positivity
  set ρ : ℝ := t ^ (1 / α) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos ht0 _
  have hρα : ρ ^ α = t := by
    rw [hρ, ← Real.rpow_mul ht0.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  have hs1 : 2 * t * C₀ * (5 * L + 1) ≤ 1 / 2 := by
    rw [ht]
    field_simp
    nlinarith
  have hs2 : 2 * t * C₀ ≤ 1 := by
    have h5 : 1 ≤ 5 * L + 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht0.le) hC₀]
  set K₁ : ℝ := 2 + 64 / ρ ^ 2 + 22 * L with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨C₀ * (1 + 11 * L + (5 * L + 1) * K₁) + K₁ + 2, by positivity, ?_⟩
  intro a β c ha hβc u hu hH hBex A M hM hA hLu
  have hΛ : 0 ≤ Λ := nonneg_of_isEllipticCoeff ha
  have hLΛ : L = Λ := abs_of_nonneg hΛ
  rw [← hLΛ] at hβc
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  -- `B₀ = |D²u|_0`
  obtain ⟨B, hB⟩ := hBex
  have hbdd : BddAbove (range fun x => ‖fderiv ℝ (fderiv ℝ u) x‖) :=
    ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  set B₀ : ℝ := ⨆ x, ‖fderiv ℝ (fderiv ℝ u) x‖ with hB₀
  have hB₀x : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₀ := fun x => le_ciSup hbdd x
  have hB₀0 : 0 ≤ B₀ := (ContinuousLinearMap.opNorm_nonneg _).trans (hB₀x 0)
  -- the top-order part is Hölder
  set M' : ℝ := M + L * (11 * A + 5 * B₀) with hM'
  have htop : ∀ x y, |hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) -
      hessTrace b (a y) (fderiv ℝ (fderiv ℝ u) y)| ≤ M' * ‖x - y‖ ^ α := by
    intro x y
    have hlow := abs_lowerOrder_sub_le hu hα0.le hα1.le hβc hA hB₀x x y
    have hsplit : hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) -
        hessTrace b (a y) (fderiv ℝ (fderiv ℝ u) y) =
        (ellipticOp b a β c u x - ellipticOp b a β c u y) -
          ((fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)) := by
      simp only [ellipticOp]; ring
    rw [hsplit]
    calc _ ≤ |ellipticOp b a β c u x - ellipticOp b a β c u y| +
          |(fderiv ℝ u x (β x) + c x * u x) - (fderiv ℝ u y (β y) + c y * u y)| := abs_sub _ _
      _ ≤ M * ‖x - y‖ ^ α + L * (11 * A + 5 * B₀) * ‖x - y‖ ^ α := add_le_add (hLu x y) hlow
      _ = M' * ‖x - y‖ ^ α := by ring
  -- Simon's estimate
  set H₁ : ℝ := C₀ * (M' + B₀) with hH₁
  have hH₁0 : 0 ≤ H₁ := by positivity
  have hS' : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H₁ * ‖x - y‖ ^ α :=
    hS a ha u hu hH B₀ M' hB₀x htop
  -- interpolation: `B₀ ≤ 32 A / ρ² + 2 H₁ ρ^α`
  have hHol : HolderWith H₁.toNNReal ⟨α, hα0.le⟩ (fderiv ℝ (fderiv ℝ u)) :=
    HolderWith.of_dist_le fun x y => by
      rw [Real.coe_toNNReal _ hH₁0, dist_eq_norm, dist_eq_norm]
      exact hS' x y
  have hint : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ 32 * A / ρ ^ 2 + 2 * H₁ * t := by
    intro x
    have := norm_fderiv_fderiv_le_interpolation hu (A := A)
      (fun y => by rw [Real.norm_eq_abs]; exact hA y) ⟨B, hB⟩ hHol hρ0 x
    rw [Real.coe_toNNReal _ hH₁0] at this
    change _ ≤ _ + 2 * H₁ * ρ ^ α at this
    rwa [hρα] at this
  have hB₀le : B₀ ≤ 32 * A / ρ ^ 2 + 2 * H₁ * t := ciSup_le hint
  have hB₀K : B₀ ≤ K₁ * (M + A) := by
    have e1 : 2 * H₁ * t = (2 * t * C₀) * (M + 11 * L * A) + (2 * t * C₀ * (5 * L + 1)) * B₀ := by
      rw [hH₁, hM']; ring
    have h1 : (2 * t * C₀) * (M + 11 * L * A) ≤ M + 11 * L * A :=
      mul_le_of_le_one_left (by positivity) hs2
    have h2 : (2 * t * C₀ * (5 * L + 1)) * B₀ ≤ 1 / 2 * B₀ :=
      mul_le_mul_of_nonneg_right hs1 hB₀0
    have h3 : B₀ ≤ 64 * A / ρ ^ 2 + 2 * M + 22 * L * A := by
      have : 64 * A / ρ ^ 2 = 2 * (32 * A / ρ ^ 2) := by ring
      linarith
    have h4 : 64 * A / ρ ^ 2 ≤ 64 / ρ ^ 2 * (M + A) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]; nlinarith
    have h5 : 22 * L * A ≤ 22 * L * (M + A) := by nlinarith
    have h6 : 2 * M ≤ 2 * (M + A) := by linarith
    calc B₀ ≤ 64 * A / ρ ^ 2 + 2 * M + 22 * L * A := h3
      _ ≤ 64 / ρ ^ 2 * (M + A) + 2 * (M + A) + 22 * L * (M + A) := by linarith
      _ = K₁ * (M + A) := by rw [hK₁]; ring
  have hMA : 0 ≤ M + A := by linarith
  have hH₁le : H₁ ≤ C₀ * (1 + 11 * L + (5 * L + 1) * K₁) * (M + A) := by
    rw [hH₁, hM']
    have : M + L * (11 * A + 5 * B₀) + B₀ ≤ (1 + 11 * L + (5 * L + 1) * K₁) * (M + A) := by
      have e : M + L * (11 * A + 5 * B₀) + B₀ = M + 11 * L * A + (5 * L + 1) * B₀ := by ring
      rw [e]
      have : (5 * L + 1) * B₀ ≤ (5 * L + 1) * (K₁ * (M + A)) :=
        mul_le_mul_of_nonneg_left hB₀K (by positivity)
      nlinarith
    calc C₀ * (M + L * (11 * A + 5 * B₀) + B₀) ≤ C₀ * ((1 + 11 * L + (5 * L + 1) * K₁) * (M + A)) :=
          mul_le_mul_of_nonneg_left this hC₀
      _ = _ := by ring
  set C := C₀ * (1 + 11 * L + (5 * L + 1) * K₁) + K₁ + 2 with hC
  have hC1 : C₀ * (1 + 11 * L + (5 * L + 1) * K₁) * (M + A) ≤ C * (M + A) :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hMA
  have hC2 : K₁ * (M + A) ≤ C * (M + A) :=
    mul_le_mul_of_nonneg_right (by rw [hC]; nlinarith [mul_nonneg hC₀ (by positivity :
      (0:ℝ) ≤ 1 + 11 * L + (5 * L + 1) * K₁)]) hMA
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · calc _ ≤ H₁ * ‖x - y‖ ^ α := hS' x y
      _ ≤ C * (M + A) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (hH₁le.trans hC1) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact (hB₀x x).trans (hB₀K.trans hC2)
  · calc ‖fderiv ℝ u x‖ ≤ 2 * A + B₀ := norm_fderiv_le_two_mul_add hu hA hB₀x x
      _ ≤ 2 * (M + A) + K₁ * (M + A) := by linarith
      _ ≤ C * (M + A) := by
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (by rw [hC]; nlinarith [mul_nonneg hC₀ (by positivity :
            (0:ℝ) ≤ 1 + 11 * L + (5 * L + 1) * K₁)]) hMA

/-- **The pure second-order case**: `[D²u]_α ≤ C ([a : D²u]_α + |u|_0)`. -/
theorem exists_holder_hessian_le_of_sup {lam Λ α : ℝ} (hlam : 0 < lam) (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : E → E →L[ℝ] E, IsEllipticCoeff a lam Λ α →
      ∀ u : E → ℝ, ContDiff ℝ 2 u →
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) →
      ∀ A M : ℝ, 0 ≤ M → (∀ x, |u x| ≤ A) →
      (∀ x y, |hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) -
        hessTrace b (a y) (fderiv ℝ (fderiv ℝ u) y)| ≤ M * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (M + A) * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, h⟩ := exists_schauder_estimate (Λ := Λ) b hlam hα0 hα1
  refine ⟨C, hC, fun a ha u hu hH hB A M hM hA hLu => ?_⟩
  refine (h a _ _ ha (isLowerCoeff_zero (nonneg_of_isEllipticCoeff ha)) u hu hH hB A M hM hA ?_).1
  intro x y
  simpa only [ellipticOp_zero] using hLu x y

end SGPT.Foundations.Analysis.Pending.SchauderWholeSpace
