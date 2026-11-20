import SGPT.GAGA.SerreHomogeneous
import SGPT.Projective.Basic

/-!
# Holomorphic sections of `𝒪(m)` on `ℙᴺ` are homogeneous polynomials

On `ℙᴺ` with homogeneous coordinates `Z₀, …, Z_N`, a holomorphic section `s` of `𝒪(m)` is
given in the affine chart `U_i = {Z_i ≠ 0}` by its coefficient `g_i` in the frame `Z_i^m`:
`g_i : ℂᴺ → ℂ` holomorphic (`ℂᴺ` the chart target, `SGPT.Projective.affineChart`). The
coefficients satisfy the transition law `v_i^m g_i(v/v_i) = v_j^m g_j(v/v_j)` for every
homogeneous vector `v` with `v_i, v_j ≠ 0`, where `v/v_i = affineRatio i v`.

`exists_isHomogeneous_of_chartSections` proves: there is a homogeneous polynomial `P` of degree
`m` with `g_i(z) = P(insertNth i 1 z)` for all `i, z`, i.e. `s = P`. This is
`H⁰(ℙᴺ, 𝒪(m)) = ℂ[Z₀, …, Z_N]_m` (GAGA for global sections on `ℙᴺ`). The proof assembles the
homogeneous function `F(v) = v_i^m g_i(v/v_i)` on `ℂ^{N+1} ∖ 0` and applies
`exists_isHomogeneous_eq_of_homogeneous`.

Blueprint: `claude-serre-gaga.tex`, node `claude-serre-gaga:projective-sections`.
-/

set_option autoImplicit false

open Filter Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

namespace SGPT.GAGA

noncomputable section

variable {N : ℕ}

/-- The affine coordinates `y ↦ (y_{i.succAbove k}/y_i)_k` are holomorphic where `y_i ≠ 0`. -/
theorem differentiableAt_affineRatio (i : Fin (N + 1)) {x : ComplexModel (N + 1)}
    (hx : x i ≠ 0) :
    DifferentiableAt ℂ (fun y : ComplexModel (N + 1) => affineRatio i (WithLp.ofLp y)) x := by
  have h1 : DifferentiableAt ℂ
      (fun y : ComplexModel (N + 1) => fun k : Fin N => y (i.succAbove k) / y i) x := by
    rw [differentiableAt_pi]
    intro k
    have hp1 : DifferentiableAt ℂ (fun y : ComplexModel (N + 1) => y (i.succAbove k)) x :=
      (EuclideanSpace.proj (𝕜 := ℂ) (i.succAbove k)).differentiableAt
    have hp2 : DifferentiableAt ℂ (fun y : ComplexModel (N + 1) => y i) x :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt
    have := hp1.mul (hp2.inv hx)
    convert this using 1 <;> rfl
  exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiableAt.comp x h1

/-- The affine coordinates are invariant under scaling. -/
theorem affineRatio_smul (i : Fin (N + 1)) {c : ℂ} (hc : c ≠ 0) (v : Fin (N + 1) → ℂ) :
    affineRatio i (c • v) = affineRatio i v := by
  ext k
  simp only [affineRatio_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc]

/-- **`H⁰(ℙᴺ, 𝒪(m))` consists of the homogeneous polynomials of degree `m`.** Let
`g_i : ℂᴺ → ℂ` (`i = 0, …, N`) be holomorphic, the coefficients of a section of `𝒪(m)` in the
frames `Z_i^m` of the affine charts, so that `v_i^m g_i(v/v_i) = v_j^m g_j(v/v_j)` whenever
`v_i, v_j ≠ 0`. Then there is a homogeneous polynomial `P` of degree `m` with
`g_i(z) = P(insertNth i 1 z)` for all `i` and `z`. -/
theorem exists_isHomogeneous_of_chartSections {m : ℕ} (g : Fin (N + 1) → ComplexModel N → ℂ)
    (hg : ∀ i, Differentiable ℂ (g i))
    (htrans : ∀ (i j : Fin (N + 1)) (v : Fin (N + 1) → ℂ), v i ≠ 0 → v j ≠ 0 →
      v i ^ m * g i (affineRatio i v) = v j ^ m * g j (affineRatio j v)) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, P.IsHomogeneous m ∧
      ∀ (i : Fin (N + 1)) (z : ComplexModel N), g i z = MvPolynomial.eval (affineLift i z) P := by
  classical
  -- the homogeneous function `F(v) = v_i^m g_i(v/v_i)` on `ℂ^{N+1} ∖ 0`
  let F : ComplexModel (N + 1) → ℂ := fun x =>
    if h : ∃ i, x i ≠ 0 then x h.choose ^ m * g h.choose (affineRatio h.choose (WithLp.ofLp x))
    else 0
  have hF : ∀ (x : ComplexModel (N + 1)) (i : Fin (N + 1)), x i ≠ 0 →
      F x = x i ^ m * g i (affineRatio i (WithLp.ofLp x)) := by
    intro x i hi
    have h : ∃ i, x i ≠ 0 := ⟨i, hi⟩
    simp only [F, dif_pos h]
    exact htrans _ _ (WithLp.ofLp x) h.choose_spec hi
  have hne : ∀ x : ComplexModel (N + 1), x ≠ 0 → ∃ i, x i ≠ 0 := by
    intro x hx
    by_contra h
    push Not at h
    exact hx (by ext i; simpa using h i)
  have hFd : DifferentiableOn ℂ F {x | x ≠ 0} := by
    intro x hx
    obtain ⟨i, hi⟩ := hne x hx
    have hcont : ContinuousAt (fun y : ComplexModel (N + 1) => y i) x :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt
    have hev : (fun y : ComplexModel (N + 1) => y i ^ m * g i (affineRatio i (WithLp.ofLp y)))
        =ᶠ[𝓝 x] F := by
      filter_upwards [hcont.eventually_ne hi] with y hy
      exact (hF y i hy).symm
    have hd : DifferentiableAt ℂ
        (fun y : ComplexModel (N + 1) => y i ^ m * g i (affineRatio i (WithLp.ofLp y))) x :=
      (((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt).pow m).mul
        ((hg i).differentiableAt.comp x (differentiableAt_affineRatio i hi))
    exact (hd.congr_of_eventuallyEq hev.symm).differentiableWithinAt
  have hhom : ∀ (c : ℂ) (x : ComplexModel (N + 1)), c ≠ 0 → x ≠ 0 →
      F (c • x) = c ^ m * F x := by
    intro c x hc hx
    obtain ⟨i, hi⟩ := hne x hx
    have hci : (c • x) i ≠ 0 := by simpa using mul_ne_zero hc hi
    rw [hF _ i hci, hF x i hi]
    have hsm : WithLp.ofLp (c • x) = c • WithLp.ofLp x := rfl
    rw [hsm, affineRatio_smul i hc, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  obtain ⟨P, hPh, hPF⟩ := exists_isHomogeneous_eq_of_homogeneous hFd hhom
  refine ⟨P, hPh, fun i z => ?_⟩
  let x : ComplexModel (N + 1) := WithLp.toLp 2 (affineLift i z)
  have hxi : x i = 1 := by simp [x]
  have hx0 : x ≠ 0 := by
    intro h
    have := congrArg (fun y : ComplexModel (N + 1) => y i) h
    simp [hxi] at this
  have h1 := hPF x hx0
  rw [hF x i (by rw [hxi]; exact one_ne_zero), hxi, one_pow, one_mul] at h1
  have h2 : affineRatio i (WithLp.ofLp x) = z := affineRatio_affineLift i z
  rw [h2] at h1
  exact h1

end

end SGPT.GAGA
