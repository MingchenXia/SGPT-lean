import SGPT.Foundations.Analysis.Pending.CalabiFlatInequality
import SGPT.Foundations.Analysis.Pending.HolomorphicHessianTwo
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Complex-linear changes of coordinates for Calabi's third-order estimate

Calabi's identity and inequality (`CalabiFlatEquation.calabi_identity`,
`CalabiFlatInequality.calabi_inequality_at_one`) are proved at a point where the complex Hessian
`H = (u_{jk̄})` is the identity. This file reduces an arbitrary point to that case by a complex-linear
change of coordinates `v = u ∘ L` (`L : ℂⁿ →L[ℂ] ℂⁿ` with matrix `lmat L`, `L e_j = Σ_a (lmat L)_{aj} e_a`):

* the chain rule for Wirtinger derivatives (`wirt_comp_clm`): `∂_w (f ∘ L) = (∂_{Lw} f) ∘ L`;
* `H(g ∘ L) = Lᵀ H(g)(L·) L̄` (`complexHessian_comp_clm`, from `HolomorphicHessianTwo`) and
  `∂_m H(g ∘ L) = Lᵀ (Σ_r L_{rm} ∂_r H(g)(L·)) L̄` (`dH_comp_clm`);
* Calabi's quantity is invariant: `S(u ∘ L) = S(u) ∘ L` (`calabiS_comp_clm`, from the algebraic
  `calabiForm_transform`);
* the determinant (`det_sandwich`, `log det H(u ∘ L) = log det H(u) ∘ L + log |det L|²`) and the trace
  (`trace_eq_trace_mul_sandwich`: `tr H(u)(L·) = tr(M · H(u ∘ L))`, `M = (Lᵀ L̄)⁻¹` constant);
* Frobenius bounds for the transformed derivatives (`frob_sandwich_le`, `sum_frob_transform_le`) and the
  inverse transformation (`transform_inv_transform`);
* the normalisation (`exists_normalizing`): for `H > 0` there is `R` with `Rᴴ H R = 1`,
  `frob R = tr H⁻¹` and `frob R⁻¹ = tr H`; with `L = toEuclideanCLM (R̄)` one has `lmat L = R̄`,
  hence `H(u ∘ L)(y) = 1` at `L y = x` (`lmat_toEuclideanCLM`, `toEuclideanCLM_apply_inv`).

TN.4 B5, nonlinear track N4 (plan C1–C8 of the third-order Monge–Ampère estimate,
run-0171 section), blueprint `bou:yau-c3-estimate`.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.CalabiLinearChange

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity
  CalabiFlatLaplacian CalabiFlatInequality

noncomputable section

variable {n : ℕ}

/-! ### Frobenius bounds -/

section Frobenius

theorem frob_transpose (A : Mat n) : frob Aᵀ = frob A := by
  unfold frob
  rw [Finset.sum_comm]
  simp only [transpose_apply]

theorem frob_map_conj (A : Mat n) : frob (A.map (starRingEnd ℂ)) = frob A := by
  unfold frob
  simp only [map_apply, Complex.norm_conj]

theorem frob_sandwich_le (L A : Mat n) :
    frob (Lᵀ * A * L.map (starRingEnd ℂ)) ≤ frob L ^ 2 * frob A := by
  calc frob (Lᵀ * A * L.map (starRingEnd ℂ))
      ≤ frob (Lᵀ * A) * frob (L.map (starRingEnd ℂ)) := frob_mul_le _ _
    _ ≤ frob Lᵀ * frob A * frob (L.map (starRingEnd ℂ)) :=
        mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _)
    _ = frob L ^ 2 * frob A := by rw [frob_transpose, frob_map_conj]; ring

theorem frob_sum_smul_le {ι : Type*} [Fintype ι] (a : ι → ℂ) (X : ι → Mat n) :
    frob (∑ r, a r • X r) ≤ (∑ r, ‖a r‖ ^ 2) * ∑ r, frob (X r) := by
  unfold frob
  calc ∑ i, ∑ j, ‖(∑ r, a r • X r) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (∑ r, ‖a r‖ ^ 2) * ∑ r, ‖X r i j‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        exact norm_sum_mul_sq_le' _ _
    _ = (∑ r, ‖a r‖ ^ 2) * ∑ r, ∑ i, ∑ j, ‖X r i j‖ ^ 2 := by
        simp only [← Finset.mul_sum]
        congr 1
        exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

/-- `X'_m = Lᵀ (Σ_r L_{rm} X_r) L̄`: the third derivatives after the change of coordinates. -/
def transform (L : Mat n) (X : Fin n → Mat n) (m : Fin n) : Mat n :=
  Lᵀ * (∑ r, L r m • X r) * L.map (starRingEnd ℂ)

theorem sum_frob_transform_le (L : Mat n) (X : Fin n → Mat n) :
    ∑ m, frob (transform L X m) ≤ frob L ^ 3 * ∑ r, frob (X r) := by
  have hX : 0 ≤ ∑ r, frob (X r) := Finset.sum_nonneg fun _ _ => frob_nonneg _
  calc ∑ m, frob (transform L X m)
      ≤ ∑ m, frob L ^ 2 * ((∑ r, ‖L r m‖ ^ 2) * ∑ r, frob (X r)) :=
        Finset.sum_le_sum fun m _ => (frob_sandwich_le L _).trans
          (mul_le_mul_of_nonneg_left (frob_sum_smul_le _ _) (by positivity))
    _ = frob L ^ 2 * (∑ m, ∑ r, ‖L r m‖ ^ 2) * ∑ r, frob (X r) := by
        have e : ∀ m, frob L ^ 2 * ((∑ r, ‖L r m‖ ^ 2) * ∑ r, frob (X r)) =
            (frob L ^ 2 * ∑ r, frob (X r)) * ∑ r, ‖L r m‖ ^ 2 := fun m => by ring
        rw [Finset.sum_congr rfl fun m _ => e m, ← Finset.mul_sum]
        ring
    _ = frob L ^ 3 * ∑ r, frob (X r) := by
        have h : (∑ m, ∑ r, ‖L r m‖ ^ 2) = frob L := by unfold frob; exact Finset.sum_comm
        rw [h]
        ring

/-- The transformation by `L⁻¹` undoes the transformation by `L`. -/
theorem transform_inv_transform {L : Mat n} (hL : L.det ≠ 0) (X : Fin n → Mat n) :
    transform L⁻¹ (transform L X) = X := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr hL
  have h1 : L⁻¹ᵀ * Lᵀ = 1 := by
    rw [← transpose_mul, mul_nonsing_inv L hu, transpose_one]
  have h2 : L.map (starRingEnd ℂ) * L⁻¹.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv L hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : ∀ m, L⁻¹ᵀ * (Lᵀ * (∑ q, L q m • X q) * L.map (starRingEnd ℂ)) *
      L⁻¹.map (starRingEnd ℂ) = ∑ q, L q m • X q := fun m => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  funext r
  unfold transform
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hq : ∀ q, ∑ m, (L⁻¹ m r * L q m) • X q = (if q = r then (1 : ℂ) else 0) • X q := by
    intro q
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun (mul_nonsing_inv L hu) q) r
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  simp only [hq, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Frobenius

/-! ### Calabi's quantity, the determinant and the trace under a change of coordinates -/

section Algebra

theorem sum4_swap {β : Type*} [AddCommMonoid β] (f : Fin n → Fin n → Fin n → Fin n → β) :
    ∑ m, ∑ t, ∑ r, ∑ s, f m t r s = ∑ r, ∑ s, ∑ m, ∑ t, f m t r s := by
  calc ∑ m, ∑ t, ∑ r, ∑ s, f m t r s = ∑ m, ∑ r, ∑ t, ∑ s, f m t r s :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ r, ∑ m, ∑ t, ∑ s, f m t r s := Finset.sum_comm
    _ = ∑ r, ∑ m, ∑ s, ∑ t, f m t r s :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ r, ∑ s, ∑ m, ∑ t, f m t r s := Finset.sum_congr rfl fun r _ => Finset.sum_comm

theorem conjTranspose_transpose_eq (L : Mat n) : (Lᵀ)ᴴ = L.map (starRingEnd ℂ) := by
  ext i j
  simp [conjTranspose_apply]

theorem det_map_conj (L : Mat n) : (L.map (starRingEnd ℂ)).det = starRingEnd ℂ L.det := by
  rw [RingHom.map_det]
  rfl

/-- **Invariance of Calabi's quantity** (algebra): for `det L ≠ 0`, `H' = Lᵀ H L̄` and
`X' = transform L X`, `Σ_{m,t} H'⁻¹_{tm} tr(H'⁻¹ X'_m H'⁻¹ X'_t*) = Σ_{m,t} H⁻¹_{tm} tr(H⁻¹ X_m H⁻¹ X_t*)`. -/
theorem calabiForm_transform {L : Mat n} (hL : L.det ≠ 0) (H : Mat n) (X : Fin n → Mat n) :
    calabiForm (Lᵀ * H * L.map (starRingEnd ℂ))⁻¹ (Lᵀ * H * L.map (starRingEnd ℂ))⁻¹
        (transform L X) (Lᵀ * H * L.map (starRingEnd ℂ))⁻¹ (fun m => (transform L X m)ᴴ) =
      calabiForm H⁻¹ H⁻¹ X H⁻¹ (fun m => (X m)ᴴ) := by
  set A : Mat n := Lᵀ with hA
  set B : Mat n := L.map (starRingEnd ℂ) with hB
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr hL
  have hAu : IsUnit A.det := by rw [hA, det_transpose]; exact hu
  have hAinv : ∀ Z : Mat n, A⁻¹ * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, nonsing_inv_mul A hAu, Matrix.one_mul]
  have hBu : IsUnit B.det := by rw [hB, det_map_conj]; exact hu.map _
  have hBinv : ∀ Z : Mat n, B * (B⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv B hBu, Matrix.one_mul]
  have hAh : Aᴴ = B := conjTranspose_transpose_eq L
  have hBh : Bᴴ = A := by rw [← hAh, conjTranspose_conjTranspose]
  set P : Mat n := H⁻¹ with hPdef
  have hP' : (A * H * B)⁻¹ = B⁻¹ * P * A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  set Y : Fin n → Mat n := fun m => ∑ r, L r m • X r with hYdef
  have hX' : ∀ m, transform L X m = A * Y m * B := fun m => rfl
  have hX'h : ∀ t, (transform L X t)ᴴ = A * (Y t)ᴴ * B := by
    intro t
    rw [hX', conjTranspose_mul, conjTranspose_mul, hAh, hBh, Matrix.mul_assoc]
  have hYh : ∀ t, (Y t)ᴴ = ∑ s, starRingEnd ℂ (L s t) • (X s)ᴴ := by
    intro t
    simp only [hYdef, conjTranspose_sum, conjTranspose_smul]
    rfl
  have key : ∀ m t, ((A * H * B)⁻¹ * transform L X m * (A * H * B)⁻¹ * (transform L X t)ᴴ).trace =
      ∑ r, ∑ s, L r m * starRingEnd ℂ (L s t) * (P * X r * P * (X s)ᴴ).trace := by
    intro m t
    rw [hP', hX', hX'h]
    have e : B⁻¹ * P * A⁻¹ * (A * Y m * B) * (B⁻¹ * P * A⁻¹) * (A * (Y t)ᴴ * B) =
        B⁻¹ * (P * Y m * P * (Y t)ᴴ * B) := by
      simp only [Matrix.mul_assoc, hAinv, hBinv]
    rw [e, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv B hBu, Matrix.mul_one, hYh t]
    simp only [hYdef, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      trace_sum, trace_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hPsr : ∀ s r, P s r = ∑ m, ∑ t, starRingEnd ℂ (L s t) * (B⁻¹ * P * A⁻¹) t m * L r m := by
    intro s r
    have hP : P = B * (B⁻¹ * P * A⁻¹) * A := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul A hAu,
        Matrix.mul_one, hBinv]
    conv_lhs => rw [hP]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
    simp [hA, hB]
  unfold calabiForm
  simp only [key]
  simp only [hP', Finset.mul_sum]
  conv_rhs => simp only [hPsr, Finset.sum_mul]
  refine (sum4_swap _).trans ?_
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `det(Lᵀ H L̄) = |det L|² det H`. -/
theorem det_sandwich (L H : Mat n) :
    (Lᵀ * H * L.map (starRingEnd ℂ)).det = (Complex.normSq L.det : ℂ) * H.det := by
  rw [det_mul, det_mul, det_transpose, det_map_conj, Complex.normSq_eq_conj_mul_self]
  ring

/-- `tr H = tr(M · Lᵀ H L̄)` with the constant `M = (Lᵀ L̄)⁻¹`. -/
theorem trace_eq_trace_mul_sandwich {L : Mat n} (hL : L.det ≠ 0) (H : Mat n) :
    H.trace = ((Lᵀ * L.map (starRingEnd ℂ))⁻¹ * (Lᵀ * H * L.map (starRingEnd ℂ))).trace := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.mpr hL
  have hA : Lᵀ⁻¹ * Lᵀ = 1 := nonsing_inv_mul _ (by rw [det_transpose]; exact hu)
  have hBu : IsUnit (L.map (starRingEnd ℂ)).det := by rw [det_map_conj]; exact hu.map _
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ⁻¹, ← Matrix.mul_assoc Lᵀ⁻¹,
    hA, Matrix.one_mul, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv _ hBu, Matrix.mul_one]

theorem frob_inv_map_conj (A : Mat n) : frob (A.map (starRingEnd ℂ))⁻¹ = frob A⁻¹ := by
  have h : A.map (starRingEnd ℂ) = Aᴴᵀ := by ext; simp
  rw [h, ← transpose_nonsing_inv, ← conjTranspose_nonsing_inv, frob_transpose,
    frob_conjTranspose]

/-- With `M = (Rᴴ R)⁻¹`: `frob Y ≤ frob R · Re tr(M Y Yᴴ)`. -/
theorem frob_le_mul_re_trace {R : Mat n} (hR : R.det ≠ 0) (Y : Mat n) :
    frob Y ≤ frob R * ((Rᴴ * R)⁻¹ * (Y * Yᴴ)).trace.re := by
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hu.star
  set W : Mat n := Rᴴ⁻¹ * Y with hW
  have htr : ((Rᴴ * R)⁻¹ * (Y * Yᴴ)).trace = (frob W : ℂ) := by
    rw [← trace_mul_conjTranspose_self, hW, conjTranspose_mul, conjTranspose_nonsing_inv,
      conjTranspose_conjTranspose, Matrix.mul_inv_rev, Matrix.mul_assoc, trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  have hY : Y = Rᴴ * W := by
    rw [hW, ← Matrix.mul_assoc, mul_nonsing_inv _ hRh, Matrix.one_mul]
  rw [htr, Complex.ofReal_re]
  calc frob Y = frob (Rᴴ * W) := by rw [← hY]
    _ ≤ frob Rᴴ * frob W := frob_mul_le _ _
    _ = frob R * frob W := by rw [frob_conjTranspose]

/-- With `M = (Rᴴ R)⁻¹`: `|tr(M F)| ≤ frob R⁻¹ · √(frob F)`. -/
theorem norm_trace_inv_mul_le (R F : Mat n) :
    ‖((Rᴴ * R)⁻¹ * F).trace‖ ≤ frob R⁻¹ * √(frob F) := by
  have hM : frob (Rᴴ * R)⁻¹ ≤ frob R⁻¹ ^ 2 := by
    rw [Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, sq]
    nth_rewrite 2 [← frob_conjTranspose R⁻¹]
    exact frob_mul_le _ _
  refine (norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  calc √(frob (Rᴴ * R)⁻¹) ≤ √(frob R⁻¹ ^ 2) := Real.sqrt_le_sqrt hM
    _ = frob R⁻¹ := Real.sqrt_sq (frob_nonneg _)

/-- **Normalisation** (C8): for `H > 0` there is `R` with `Rᴴ H R = 1`, `frob R = tr H⁻¹` and
`frob R⁻¹ = tr H`. -/
theorem exists_normalizing {H : Mat n} (hH : H.PosDef) :
    ∃ R : Mat n, R.det ≠ 0 ∧ Rᴴ * H * R = 1 ∧ frob R = (H⁻¹).trace.re ∧
      frob R⁻¹ = H.trace.re := by
  classical
  obtain ⟨R, hdet, hHR, -⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hH hH
  rw [star_eq_conjTranspose] at hHR
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hu.star
  have hH' : H = Rᴴ⁻¹ * R⁻¹ := by
    calc H = Rᴴ⁻¹ * (Rᴴ * H * R) * R⁻¹ := by
          simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hRh, Matrix.one_mul]
      _ = Rᴴ⁻¹ * R⁻¹ := by rw [hHR, Matrix.mul_one]
  refine ⟨R, hdet, hHR, ?_, ?_⟩
  · have : H⁻¹ = R * Rᴴ := by
      rw [hH', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu,
        Matrix.nonsing_inv_nonsing_inv _ hRh]
    rw [this, trace_mul_conjTranspose_self, Complex.ofReal_re]
  · rw [hH', trace_mul_comm, ← conjTranspose_nonsing_inv, trace_mul_conjTranspose_self,
      Complex.ofReal_re]

end Algebra

/-! ### The chain rule for a complex-linear map -/

section Chain

variable (L : ComplexModel n →L[ℂ] ComplexModel n)

/-- The matrix of `L` in the standard basis: `L e_j = Σ_a (lmat L)_{aj} e_a`. -/
def lmat : Mat n := Matrix.of fun a j => L (coordinateVector j) a

theorem fderiv_clm (y : ComplexModel n) : fderiv ℝ (fun z => L z) y = L.restrictScalars ℝ :=
  (L.restrictScalars ℝ).fderiv

theorem contDiff_comp_clm {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => g (L z)) :=
  hg.comp (L.restrictScalars ℝ).contDiff

/-- **Chain rule**: `∂_w (f ∘ L) = (∂_{Lw} f) ∘ L` (and the same for `∂̄`). -/
theorem wirt_comp_clm {c : ℂ} {v : ComplexModel n} {f : ComplexModel n → ℂ} {y : ComplexModel n}
    (hf : DifferentiableAt ℝ f (L y)) :
    wirt c v (fun z => f (L z)) y = wirt c (L v) f (L y) := by
  have h : fderiv ℝ (fun z => f (L z)) y = (fderiv ℝ f (L y)).comp (L.restrictScalars ℝ) := by
    have := fderiv_comp (𝕜 := ℝ) y hf (L.restrictScalars ℝ).differentiableAt
    have hL : fderiv ℝ (⇑L) y = L.restrictScalars ℝ := (L.restrictScalars ℝ).fderiv
    rw [hL] at this
    exact this
  simp only [wirt, h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem wirtM_comp_clm {c : ℂ} {v : ComplexModel n} {M : ComplexModel n → Mat n}
    {y : ComplexModel n} (hM : MDiffAt M (L y)) :
    wirtM c v (fun z => M (L z)) y = wirtM c (L v) M (L y) := by
  ext i j
  simp only [wirtM_apply]
  exact wirt_comp_clm L (hM i j)

theorem wirtM_negI_clm_apply {M : ComplexModel n → Mat n} (m : Fin n) (x : ComplexModel n) :
    wirtM (-I) (L (coordinateVector m)) M x =
      ∑ r, lmat L r m • wirtM (-I) (coordinateVector r) M x := by
  ext i j
  simp only [wirtM_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact AubinYauUniformConstants.wirt_negI_sum_dir _ _ _

theorem wirtM_const (c : ℂ) (v : ComplexModel n) (A : Mat n) (y : ComplexModel n) :
    wirtM c v (fun _ : ComplexModel n => A) y = 0 := by
  ext i j
  simp [wirtM_apply, wirt]

theorem wirtM_const_sandwich {c : ℂ} {v : ComplexModel n} {M : ComplexModel n → Mat n}
    {y : ComplexModel n} (A B : Mat n) (hM : MDiffAt M y) :
    wirtM c v (fun z => A * M z * B) y = A * wirtM c v M y * B := by
  have hA : MDiffAt (fun _ : ComplexModel n => A) y := fun i j => differentiableAt_const _
  have hB : MDiffAt (fun _ : ComplexModel n => B) y := fun i j => differentiableAt_const _
  rw [wirtM_mul (hA.mul hM) hB, wirtM_mul hA hM, wirtM_const, wirtM_const]
  simp

/-- **`H(g ∘ L) = Lᵀ H(g)(L·) L̄`** (C1). -/
theorem complexHessian_comp_clm {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g)
    (y : ComplexModel n) :
    complexHessian (fun z => g (L z)) y =
      (lmat L)ᵀ * complexHessian g (L y) * (lmat L).map (starRingEnd ℂ) := by
  have h := HolomorphicHessianTwo.complexHessian_comp_holomorphic_two (F := fun z => L z)
    (p := g) isOpen_univ isOpen_univ L.contDiff.contDiffOn
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn (mapsTo_univ _ _)
    (mem_univ y)
  rw [h]
  have hJ : HolomorphicMixedDensity.jacobianMatrix (fun z => L z) y = lmat L := by
    ext a j
    simp only [HolomorphicMixedDensity.jacobianMatrix, lmat, Matrix.of_apply, fderiv_clm,
      ContinuousLinearMap.coe_restrictScalars']
  rw [hJ]

theorem mdiffAt_comp_clm {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) (y : ComplexModel n) :
    MDiffAt (fun z => complexHessian g (L z)) y := fun i j =>
  (differentiable_complexHessian_apply hg i j (L y)).comp y
    (L.restrictScalars ℝ).differentiableAt

/-- **`∂_m H(g ∘ L) = Lᵀ (Σ_r L_{rm} ∂_r H(g)(L·)) L̄`** (C2). -/
theorem dH_comp_clm {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) (m : Fin n)
    (y : ComplexModel n) :
    dH (fun z => g (L z)) m y = transform (lmat L) (fun r => dH g r (L y)) m := by
  have hfun : complexHessian (fun z => g (L z)) =
      fun z => (lmat L)ᵀ * complexHessian g (L z) * (lmat L).map (starRingEnd ℂ) :=
    funext (complexHessian_comp_clm L hg)
  unfold dH transform
  rw [hfun, wirtM_const_sandwich _ _ (mdiffAt_comp_clm L hg y),
    wirtM_comp_clm L ((mSmooth_complexHessian hg).mdiffAt (L y)), wirtM_negI_clm_apply]

/-- **Invariance of Calabi's quantity** (C3): `S(u ∘ L) = S(u) ∘ L` for invertible `L`. -/
theorem calabiS_comp_clm {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u) (hL : (lmat L).det ≠ 0)
    (y : ComplexModel n) : calabiS (fun z => u (L z)) y = calabiS u (L y) := by
  unfold calabiS
  simp only [complexHessian_comp_clm L hu y, dH_comp_clm L hu]
  exact calabiForm_transform hL _ _

/-- The trace of `H(u)` at `L y` through the constant `M = (Lᵀ L̄)⁻¹`. -/
theorem trace_complexHessian_comp_clm {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hL : (lmat L).det ≠ 0) (y : ComplexModel n) :
    (complexHessian u (L y)).trace =
      (((lmat L)ᵀ * (lmat L).map (starRingEnd ℂ))⁻¹ * complexHessian (fun z => u (L z)) y).trace := by
  rw [complexHessian_comp_clm L hu y]
  exact trace_eq_trace_mul_sandwich hL _

/-- The determinant of `H(u ∘ L)`: `det H(u ∘ L) = |det L|² det H(u)(L·)`. -/
theorem det_complexHessian_comp_clm {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (y : ComplexModel n) :
    (complexHessian (fun z => u (L z)) y).det =
      (Complex.normSq (lmat L).det : ℂ) * (complexHessian u (L y)).det := by
  rw [complexHessian_comp_clm L hu y, det_sandwich]

/-! ### From a matrix to a map -/

theorem lmat_toEuclideanCLM (A : Mat n) : lmat (Matrix.toEuclideanCLM (𝕜 := ℂ) A) = A := by
  ext a j
  simp [lmat, coordinateVector]

theorem toEuclideanCLM_apply_inv {A : Mat n} (hA : A.det ≠ 0) (x : ComplexModel n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) A (Matrix.toEuclideanCLM (𝕜 := ℂ) A⁻¹ x) = x := by
  have h : Matrix.toEuclideanCLM (𝕜 := ℂ) A * Matrix.toEuclideanCLM (𝕜 := ℂ) A⁻¹ = 1 := by
    rw [← map_mul, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), map_one]
  exact congrArg (fun T : ComplexModel n →L[ℂ] ComplexModel n => T x) h

/-- **The normalising change of coordinates** at a point `x` with `H(u)(x) > 0`: a map `L` and a
point `y` with `L y = x`, `det L ≠ 0`, `H(u ∘ L)(y) = 1`, `frob L = tr H(u)(x)⁻¹`,
`frob L⁻¹ = tr H(u)(x)`, and the two bounds for `M = (Lᵀ L̄)⁻¹` used by the cutoff argument. -/
theorem exists_normalizing_clm {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : ComplexModel n} (hx : (complexHessian u x).PosDef) :
    ∃ (L : ComplexModel n →L[ℂ] ComplexModel n) (y : ComplexModel n), L y = x ∧
      (lmat L).det ≠ 0 ∧ complexHessian (fun z => u (L z)) y = 1 ∧
      frob (lmat L) = ((complexHessian u x)⁻¹).trace.re ∧
      frob (lmat L)⁻¹ = (complexHessian u x).trace.re ∧
      (∀ Y : Mat n, frob Y ≤ frob (lmat L) *
        (((lmat L)ᵀ * (lmat L).map (starRingEnd ℂ))⁻¹ * (Y * Yᴴ)).trace.re) ∧
      (∀ F : Mat n, ‖(((lmat L)ᵀ * (lmat L).map (starRingEnd ℂ))⁻¹ * F).trace‖ ≤
        frob (lmat L)⁻¹ * √(frob F)) := by
  obtain ⟨R, hdet, hHR, hfR, hfRi⟩ := exists_normalizing hx
  have hAt : (R.map (starRingEnd ℂ))ᵀ = Rᴴ := by ext; simp [conjTranspose_apply]
  have hAc : (R.map (starRingEnd ℂ)).map (starRingEnd ℂ) = R := by ext; simp
  have hAdet : (R.map (starRingEnd ℂ)).det ≠ 0 := by
    rw [det_map_conj]; exact (map_ne_zero _).mpr hdet
  have hl : lmat (Matrix.toEuclideanCLM (𝕜 := ℂ) (R.map (starRingEnd ℂ))) =
      R.map (starRingEnd ℂ) := lmat_toEuclideanCLM _
  refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (R.map (starRingEnd ℂ)),
    Matrix.toEuclideanCLM (𝕜 := ℂ) (R.map (starRingEnd ℂ))⁻¹ x,
    toEuclideanCLM_apply_inv hAdet x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact hAdet
  · rw [complexHessian_comp_clm _ hu, toEuclideanCLM_apply_inv hAdet x, hl, hAt, hAc, hHR]
  · rw [hl, frob_map_conj, hfR]
  · rw [hl, frob_inv_map_conj, hfRi]
  · intro Y
    rw [hl, hAt, hAc, frob_map_conj]
    exact frob_le_mul_re_trace hdet Y
  · intro F
    rw [hl, hAt, hAc, frob_inv_map_conj]
    exact norm_trace_inv_mul_le R F

end Chain

end

end SGPT.Foundations.Analysis.Pending.CalabiLinearChange
