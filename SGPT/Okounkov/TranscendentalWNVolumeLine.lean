import SGPT.Okounkov.TranscendentalWNVolumeStatement
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity

/-!
# The logarithmic Fubini--Study weights of `ℙ¹` (package WN-VF)

Blueprint `claude-tok-wn-vf` (node `tok-wn-vf:line-weights`), used in WN21 §4: in the affine
coordinate `τ = v₀ / v₁` of `ℙ¹`,

  `log N₀ = log (|τ|² / (1 + |τ|²))`,   `log N₁ = log (1 / (1 + |τ|²)) = -log (1 + |τ|²)`,

where `Nᵢ([v₀ : v₁]) = |vᵢ|² / (|v₀|² + |v₁|²)` (`projectiveWeight`).  They are the weights of the
Fubini--Study metric of `𝒪(1)` on the sections `v₀` and `v₁`, so `ω_FS + ddᶜ log Nᵢ` is the
current of integration on the zero of `vᵢ`:

* `thetaPlurisubharmonic_projectiveLogWeight`: `log Nᵢ ∈ PSH(ℙ¹, ω_FS)`;
* `projectiveLogWeight_le_zero`: `log Nᵢ ≤ 0`;
* `λ log N₀ + (b - λ) log N₁ = λ log |τ|² - b log (1 + |τ|²)` is the weight of WN21 §4.

Proof: in either affine chart, with coordinate `w`, `log Nᵢ + log (1 + |w|²)` is `log |w|²` or
`0`, i.e. `log |ℓ(w)|²` for the affine function `ℓ = vᵢ` of the homogeneous lift `(w, 1)` or
`(1, w)`, which is plurisubharmonic; and `log (1 + |w|²)` is the chart potential of `ω_FS`
(`SGPT.Toric.projectiveNativeFSForm`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Toric

/-- `log Nᵢ` as an extended real (`-∞` at the zero of `vᵢ`). -/
def projectiveLogWeight (i : Fin 2) (p : ProjectiveLine) : EReal :=
  ENNReal.log (ENNReal.ofReal (projectiveWeight i p))

theorem projectiveLogWeight_le_zero (i : Fin 2) (p : ProjectiveLine) :
    projectiveLogWeight i p ≤ 0 := by
  unfold projectiveLogWeight
  rw [ENNReal.log_le_zero_iff]
  exact ENNReal.ofReal_le_one.mpr (projectiveWeight_le_one i p)

theorem projectiveLogWeight_eq_coe {i : Fin 2} {p : ProjectiveLine}
    (h : 0 < projectiveWeight i p) :
    projectiveLogWeight i p = ((Real.log (projectiveWeight i p) : ℝ) : EReal) :=
  ENNReal.log_ofReal_of_pos h

theorem projectiveAffineLift_normSq_add (b : Bool) (z : ComplexModel 1) :
    ‖projectiveAffineLift b z 0‖ ^ 2 + ‖projectiveAffineLift b z 1‖ ^ 2 =
      1 + Complex.normSq (projectiveModelEquiv.symm z) := by
  cases b <;> simp [projectiveAffineLift, ← Complex.sq_norm, add_comm]

/-- `log (A / D) + log D = log A` in `EReal`, for `A ≥ 0`, `D > 0`. -/
theorem log_ofReal_div_add_log {A D : ℝ} (hA : 0 ≤ A) (hD : 0 < D) :
    ENNReal.log (ENNReal.ofReal (A / D)) + ((Real.log D : ℝ) : EReal) =
      ENNReal.log (ENNReal.ofReal A) := by
  rw [← ENNReal.log_ofReal_of_pos hD, ← ENNReal.log_mul_add,
    ← ENNReal.ofReal_mul (div_nonneg hA hD.le), div_mul_cancel₀ A hD.ne']

/-- In the affine chart `b`, `log Nᵢ + log (1 + |w|²) = log |vᵢ(lift w)|²`. -/
theorem projectiveLogWeight_chart_add (i : Fin 2) (b : Bool) (z : ComplexModel 1) :
    projectiveLogWeight i ((projectiveModelChart b).symm z) +
        ((projectiveFSPotential z : ℝ) : EReal) =
      generatorLog (fun _ : Fin 1 => fun y : ComplexModel 1 => projectiveAffineLift b y i) z := by
  rw [generatorLog_eq_log_sum, projectiveLogWeight, projectiveWeight_chart_symm,
    projectiveAffineLift_normSq_add, projectiveFSPotential]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  exact log_ofReal_div_add_log (sq_nonneg _)
    (by have := Complex.normSq_nonneg (projectiveModelEquiv.symm z); linarith)

theorem differentiable_projectiveAffineLift (b : Bool) (i : Fin 2) :
    Differentiable ℂ (fun y : ComplexModel 1 => projectiveAffineLift b y i) := by
  cases b <;> fin_cases i <;> simp [projectiveAffineLift] <;>
    first
    | exact differentiable_const _
    | exact projectiveModelEquiv.symm.differentiable

/-- **`log Nᵢ ∈ PSH(ℙ¹, ω_FS)`**: `ω_FS + ddᶜ log Nᵢ` is the current of integration on
`{vᵢ = 0}`. -/
theorem thetaPlurisubharmonic_projectiveLogWeight (i : Fin 2) :
    ThetaPlurisubharmonic projectiveNativeFSClosedForm.val (projectiveLogWeight i) := by
  intro e z hz
  obtain ⟨b, hb⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  refine ⟨e.val.target, projectiveFSPotential, hz,
    ⟨e.val.open_target, subset_rfl, contDiff_projectiveFSPotential.contDiffOn, fun y _ => rfl⟩,
    ?_⟩
  have hfun : (fun y => chartFunction (projectiveLogWeight i) e y +
      ((projectiveFSPotential y : ℝ) : EReal)) = fun y =>
      (((1 : ℚ) : ℝ) : EReal) *
        generatorLog (fun _ : Fin 1 => fun y : ComplexModel 1 => projectiveAffineLift b y i) y := by
    funext y
    rw [Rat.cast_one, EReal.coe_one, one_mul, ← projectiveLogWeight_chart_add]
    simp only [chartFunction, hb]
  rw [hfun]
  exact (MeteredDivisorPositivity.plurisubharmonicOn_qsmul_generatorLog isOpen_univ
    (by norm_num) (differentiable_projectiveAffineLift b i).differentiableOn).mono
    (subset_univ _)

/-! ### Values -/

theorem projectiveWeight_zero_pos {p : ProjectiveLine} (hp : p ≠ projectiveZero) :
    0 < projectiveWeight 0 p := by
  refine div_pos ?_ (normSq_add_pos _ p.rep_nonzero)
  have h0 : p.rep 0 ≠ 0 := fun h => hp (eq_projectiveZero_of_rep_zero h)
  positivity

/-- `log N₀(τ)` is finite for `τ ≠ 0`. -/
theorem projectiveLogWeight_zero_eq_coe {p : ProjectiveLine} (hp : p ≠ projectiveZero) :
    projectiveLogWeight 0 p = ((Real.log (projectiveWeight 0 p) : ℝ) : EReal) :=
  projectiveLogWeight_eq_coe (projectiveWeight_zero_pos hp)

/-- `N₁(0) = 1`. -/
theorem projectiveWeight_one_projectiveZero : projectiveWeight 1 projectiveZero = 1 := by
  linarith [projectiveWeight_add projectiveZero, projectiveWeight_zero_projectiveZero]

/-- `log N₁(0) = 0`. -/
theorem projectiveLogWeight_one_projectiveZero : projectiveLogWeight 1 projectiveZero = 0 := by
  rw [projectiveLogWeight, projectiveWeight_one_projectiveZero, ENNReal.ofReal_one,
    ENNReal.log_one]

end SGPT.Okounkov.TranscendentalWN
