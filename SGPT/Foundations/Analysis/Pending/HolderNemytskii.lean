import SGPT.Foundations.Analysis.Pending.ManifoldParametrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Nemytskii operators on Hölder spaces: the remainder of the linearisation

Let `Γ : X → ℝ` be differentiable with derivative `g = DΓ`, and `g` differentiable with bounded
(`B₂`) and Lipschitz (`B₃`) derivative.  For maps `P₀, P₁, P₂ : E → X` (in the application
`P_j(z) = (z, D²w_j(z))`) the **remainder of the linearisation at `P₀`**

`R(z) = Γ(P₁ z) - Γ(P₂ z) - g(P₀ z)(P₁ z - P₂ z)`

is quadratically small in Hölder norm: if `P_j - P₀` (`j = 1, 2`) are `δ`-small in `C^{0,r}`,
`P₁ - P₂` is `d`-small in `C^{0,r}` and `P₀` is `(M₀, r)`-Hölder at scales `≤ 1`, then
`|R| ≤ B₂ δ d` (`abs_remainder_le`) and `|R z - R z'| ≤ (2 B₂ + B₃ (M₀ + δ)) δ d ‖z - z'‖^r`
(`abs_remainder_sub_le`).  Two mean-value arguments: along `s ↦ P₂ + s (P₁ - P₂)`, and for the
mixed second difference of `g` (`norm_mixed_sub_le`).

This is the analytic core of the strict differentiability of the complex Monge–Ampère operator
`φ ↦ log det(H + complexHessian φ)` on `C^{2,r}(M)` (TN.4 B5, nonlinear track N1, openness of the
continuity path; blueprint `bou:yau-openness`).

Also: `abs_comp_sub_le` (a Lipschitz `Γ` of a Hölder map is Hölder) and `abs_mul_sub_le` (product
with a bounded Lipschitz cut-off).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal

namespace SGPT.Foundations.Analysis.Pending.HolderNemytskii

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A map with derivative bounded by `B` is `B`-Lipschitz. -/
theorem norm_sub_le_of_hasFDerivAt {g : X → Y} {g' : X → X →L[ℝ] Y} {B : ℝ}
    (hg : ∀ p, HasFDerivAt g (g' p) p) (hb : ∀ p, ‖g' p‖ ≤ B) (p q : X) :
    ‖g p - g q‖ ≤ B * ‖p - q‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (f' := g') (fun x _ => (hg x).hasFDerivWithinAt) (fun x _ => hb x) (mem_univ q)
    (mem_univ p)
  exact h

/-- **The mixed second difference**: for `g` with `B₂`-bounded, `B₃`-Lipschitz derivative,
`‖g(q₁ + u₁) - g q₁ - (g(q₂ + u₂) - g q₂)‖ ≤ B₂ ‖u₁ - u₂‖ + B₃ (‖q₁ - q₂‖ + ‖u₁ - u₂‖) ‖u₂‖`. -/
theorem norm_mixed_sub_le {g : X → Y} {g' : X → X →L[ℝ] Y} {B₂ B₃ : ℝ}
    (hg : ∀ p, HasFDerivAt g (g' p) p) (hb : ∀ p, ‖g' p‖ ≤ B₂)
    (hl : ∀ p q, ‖g' p - g' q‖ ≤ B₃ * ‖p - q‖) (hB₃ : 0 ≤ B₃) (q₁ q₂ u₁ u₂ : X) :
    ‖g (q₁ + u₁) - g q₁ - (g (q₂ + u₂) - g q₂)‖ ≤
      B₂ * ‖u₁ - u₂‖ + B₃ * (‖q₁ - q₂‖ + ‖u₁ - u₂‖) * ‖u₂‖ := by
  set ψ : ℝ → Y := fun τ => g (q₁ + τ • u₁) - g (q₂ + τ • u₂) with hψ
  have hderiv : ∀ τ : ℝ, HasDerivAt ψ (g' (q₁ + τ • u₁) u₁ - g' (q₂ + τ • u₂) u₂) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => q₁ + τ • u₁) u₁ τ := by
      simpa using ((hasDerivAt_id τ).smul_const u₁).const_add q₁
    have h2 : HasDerivAt (fun τ : ℝ => q₂ + τ • u₂) u₂ τ := by
      simpa using ((hasDerivAt_id τ).smul_const u₂).const_add q₂
    exact ((hg _).comp_hasDerivAt τ h1).sub ((hg _).comp_hasDerivAt τ h2)
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1, ‖g' (q₁ + τ • u₁) u₁ - g' (q₂ + τ • u₂) u₂‖ ≤
      B₂ * ‖u₁ - u₂‖ + B₃ * (‖q₁ - q₂‖ + ‖u₁ - u₂‖) * ‖u₂‖ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2.le
    have hsplit : g' (q₁ + τ • u₁) u₁ - g' (q₂ + τ • u₂) u₂ =
        g' (q₁ + τ • u₁) (u₁ - u₂) + (g' (q₁ + τ • u₁) - g' (q₂ + τ • u₂)) u₂ := by
      simp [map_sub]
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((g' _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
    · refine ((g' _ - g' _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (hl _ _).trans (mul_le_mul_of_nonneg_left ?_ hB₃)
      have : q₁ + τ • u₁ - (q₂ + τ • u₂) = (q₁ - q₂) + τ • (u₁ - u₂) := by
        simp only [smul_sub]; abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
      exact mul_le_of_le_one_left (norm_nonneg _) hτ1
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ)
    (fun τ _ => (hderiv τ).hasDerivWithinAt) hbound
  simp only [hψ, one_smul, zero_smul, add_zero] at h
  have heq : g (q₁ + u₁) - g q₁ - (g (q₂ + u₂) - g q₂) =
      g (q₁ + u₁) - g (q₂ + u₂) - (g q₁ - g q₂) := by abel
  rw [heq]
  exact h

variable {Γ : X → ℝ} {g : X → X →L[ℝ] ℝ} {g' : X → X →L[ℝ] X →L[ℝ] ℝ} {B₂ B₃ : ℝ}

/-- The interpolating maps `Q_s = P₂ + s (P₁ - P₂)` stay `δ`-close to `P₀`. -/
theorem norm_interp_sub_le {P₀ P₁ P₂ : E → X} {δ : ℝ}
    (h1 : ∀ z, ‖P₁ z - P₀ z‖ ≤ δ) (h2 : ∀ z, ‖P₂ z - P₀ z‖ ≤ δ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (z : E) : ‖P₂ z + s • (P₁ z - P₂ z) - P₀ z‖ ≤ δ := by
  have : P₂ z + s • (P₁ z - P₂ z) - P₀ z = (1 - s) • (P₂ z - P₀ z) + s • (P₁ z - P₀ z) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg hs0]
  nlinarith [h1 z, h2 z]

theorem norm_interp_sub_sub_le {P₀ P₁ P₂ : E → X} {δ ρ : ℝ} {z z' : E}
    (h1 : ‖P₁ z - P₀ z - (P₁ z' - P₀ z')‖ ≤ δ * ρ) (h2 : ‖P₂ z - P₀ z - (P₂ z' - P₀ z')‖ ≤ δ * ρ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖P₂ z + s • (P₁ z - P₂ z) - P₀ z - (P₂ z' + s • (P₁ z' - P₂ z') - P₀ z')‖ ≤ δ * ρ := by
  have : P₂ z + s • (P₁ z - P₂ z) - P₀ z - (P₂ z' + s • (P₁ z' - P₂ z') - P₀ z') =
      (1 - s) • (P₂ z - P₀ z - (P₂ z' - P₀ z')) + s • (P₁ z - P₀ z - (P₁ z' - P₀ z')) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg hs0]
  nlinarith

/-- **Sup bound of the remainder**: `|R z| ≤ B₂ δ ‖P₁ z - P₂ z‖`. -/
theorem abs_remainder_le (hΓ : ∀ p, HasFDerivAt Γ (g p) p) (hg : ∀ p, HasFDerivAt g (g' p) p)
    (hb : ∀ p, ‖g' p‖ ≤ B₂) {P₀ P₁ P₂ : E → X} {δ : ℝ} (h1 : ∀ z, ‖P₁ z - P₀ z‖ ≤ δ)
    (h2 : ∀ z, ‖P₂ z - P₀ z‖ ≤ δ) (z : E) :
    |Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) (P₁ z - P₂ z)| ≤ B₂ * δ * ‖P₁ z - P₂ z‖ := by
  set D := P₁ z - P₂ z with hD
  set k : ℝ → ℝ := fun s => Γ (P₂ z + s • D) - s * g (P₀ z) D with hk
  have hderiv : ∀ s : ℝ, HasDerivAt k (g (P₂ z + s • D) D - g (P₀ z) D) s := by
    intro s
    have h1' : HasDerivAt (fun s : ℝ => P₂ z + s • D) D s := by
      simpa using ((hasDerivAt_id s).smul_const D).const_add (P₂ z)
    have := ((hΓ (P₂ z + s • D)).comp_hasDerivAt s h1').sub
      ((hasDerivAt_id s).mul_const (g (P₀ z) D))
    exact this.congr_deriv (by rw [one_mul])
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖g (P₂ z + s • D) D - g (P₀ z) D‖ ≤ B₂ * δ * ‖D‖ := by
    intro s hs
    rw [← sub_apply]
    refine ((g _ - g _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_sub_le_of_hasFDerivAt hg hb _ _).trans ?_
    have hB₂ : 0 ≤ B₂ := (norm_nonneg (g' 0)).trans (hb 0)
    exact mul_le_mul_of_nonneg_left (norm_interp_sub_le h1 h2 hs.1 hs.2.le z) hB₂
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := k)
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound
  simp only [hk, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero,
    Real.norm_eq_abs] at h
  have heq : P₂ z + D = P₁ z := by rw [hD]; abel
  rw [heq] at h
  have e : Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) D = Γ (P₁ z) - g (P₀ z) D - Γ (P₂ z) := by ring
  rw [e]
  exact h

/-- **Hölder bound of the remainder** at scales `‖z - z'‖ ≤ 1`. -/
theorem abs_remainder_sub_le_of_le_one (hΓ : ∀ p, HasFDerivAt Γ (g p) p)
    (hg : ∀ p, HasFDerivAt g (g' p) p) (hb : ∀ p, ‖g' p‖ ≤ B₂)
    (hl : ∀ p q, ‖g' p - g' q‖ ≤ B₃ * ‖p - q‖) (hB₃ : 0 ≤ B₃) {P₀ P₁ P₂ : E → X}
    {δ d M₀ ρ : ℝ} {z z' : E}
    (h1 : ∀ z, ‖P₁ z - P₀ z‖ ≤ δ) (h2 : ∀ z, ‖P₂ z - P₀ z‖ ≤ δ)
    (h1' : ‖P₁ z - P₀ z - (P₁ z' - P₀ z')‖ ≤ δ * ρ)
    (h2' : ‖P₂ z - P₀ z - (P₂ z' - P₀ z')‖ ≤ δ * ρ)
    (h0 : ‖P₀ z - P₀ z'‖ ≤ M₀ * ρ) (hd : ‖P₁ z - P₂ z‖ ≤ d)
    (hd' : ‖P₁ z - P₂ z - (P₁ z' - P₂ z')‖ ≤ d * ρ) (hρ : 0 ≤ ρ) (hM₀ : 0 ≤ M₀) :
    |(Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) (P₁ z - P₂ z)) -
        (Γ (P₁ z') - Γ (P₂ z') - g (P₀ z') (P₁ z' - P₂ z'))| ≤
      (2 * B₂ + B₃ * (M₀ + δ)) * δ * d * ρ := by
  have hB₂ : 0 ≤ B₂ := (norm_nonneg (g' 0)).trans (hb 0)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (h1 z)
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  set D := P₁ z - P₂ z with hD
  set D' := P₁ z' - P₂ z' with hD'
  set m : ℝ → ℝ := fun s => (Γ (P₂ z + s • D) - s * g (P₀ z) D) -
    (Γ (P₂ z' + s • D') - s * g (P₀ z') D') with hm
  have hderiv : ∀ s : ℝ, HasDerivAt m ((g (P₂ z + s • D) D - g (P₀ z) D) -
      (g (P₂ z' + s • D') D' - g (P₀ z') D')) s := by
    intro s
    have hA : ∀ (Pz : X) (DD : X) (c : X →L[ℝ] ℝ), HasDerivAt
        (fun s : ℝ => Γ (Pz + s • DD) - s * c DD) (g (Pz + s • DD) DD - c DD) s := by
      intro Pz DD c
      have h1' : HasDerivAt (fun s : ℝ => Pz + s • DD) DD s := by
        simpa using ((hasDerivAt_id s).smul_const DD).const_add Pz
      have := ((hΓ (Pz + s • DD)).comp_hasDerivAt s h1').sub
        ((hasDerivAt_id s).mul_const (c DD))
      exact this.congr_deriv (by rw [one_mul])
    exact (hA (P₂ z) D (g (P₀ z))).sub (hA (P₂ z') D' (g (P₀ z')))
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖(g (P₂ z + s • D) D - g (P₀ z) D) -
      (g (P₂ z' + s • D') D' - g (P₀ z') D')‖ ≤ (2 * B₂ + B₃ * (M₀ + δ)) * δ * d * ρ := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.le
    set u₁ := P₂ z + s • D - P₀ z with hu₁
    set u₂ := P₂ z' + s • D' - P₀ z' with hu₂
    have hu₁₂ : ‖u₁ - u₂‖ ≤ δ * ρ := norm_interp_sub_sub_le h1' h2' hs0 hs1
    have hu₂b : ‖u₂‖ ≤ δ := norm_interp_sub_le h1 h2 hs0 hs1 z'
    have hmix := norm_mixed_sub_le hg hb hl hB₃ (P₀ z) (P₀ z') u₁ u₂
    have e1 : P₀ z + u₁ = P₂ z + s • D := by rw [hu₁]; abel
    have e2 : P₀ z' + u₂ = P₂ z' + s • D' := by rw [hu₂]; abel
    rw [e1, e2] at hmix
    have hsplit : (g (P₂ z + s • D) D - g (P₀ z) D) - (g (P₂ z' + s • D') D' - g (P₀ z') D') =
        ((g (P₂ z + s • D) - g (P₀ z)) - (g (P₂ z' + s • D') - g (P₀ z'))) D +
          (g (P₂ z' + s • D') - g (P₀ z')) (D - D') := by
      simp only [sub_apply, map_sub]; abel
    rw [hsplit]
    have hT1 : ‖((g (P₂ z + s • D) - g (P₀ z)) - (g (P₂ z' + s • D') - g (P₀ z'))) D‖ ≤
        (B₂ * (δ * ρ) + B₃ * (M₀ * ρ + δ * ρ) * δ) * d := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul ?_ hd (norm_nonneg _) ?_)
      · refine hmix.trans (add_le_add (mul_le_mul_of_nonneg_left hu₁₂ hB₂) ?_)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add h0 hu₁₂) hB₃) hu₂b
          (norm_nonneg _) (by positivity)
      · positivity
    have hT2 : ‖(g (P₂ z' + s • D') - g (P₀ z')) (D - D')‖ ≤ (B₂ * δ) * (d * ρ) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul ?_ hd' (norm_nonneg _)
        (by positivity))
      exact (norm_sub_le_of_hasFDerivAt hg hb _ _).trans (mul_le_mul_of_nonneg_left hu₂b hB₂)
    refine (norm_add_le _ _).trans ((add_le_add hT1 hT2).trans (le_of_eq ?_))
    ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := m)
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound
  simp only [hm, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero,
    Real.norm_eq_abs] at h
  have e1 : P₂ z + D = P₁ z := by rw [hD]; abel
  have e2 : P₂ z' + D' = P₁ z' := by rw [hD']; abel
  rw [e1, e2] at h
  have heq : (Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) (P₁ z - P₂ z)) -
      (Γ (P₁ z') - Γ (P₂ z') - g (P₀ z') (P₁ z' - P₂ z')) =
      Γ (P₁ z) - g (P₀ z) D - (Γ (P₁ z') - g (P₀ z') D') - (Γ (P₂ z) - Γ (P₂ z')) := by
    rw [hD, hD']; ring
  rw [heq]
  exact h

/-- **Hölder bound of the remainder** at all scales (`r ≥ 0`). -/
theorem abs_remainder_sub_le (hΓ : ∀ p, HasFDerivAt Γ (g p) p)
    (hg : ∀ p, HasFDerivAt g (g' p) p) (hb : ∀ p, ‖g' p‖ ≤ B₂)
    (hl : ∀ p q, ‖g' p - g' q‖ ≤ B₃ * ‖p - q‖) (hB₃ : 0 ≤ B₃) {P₀ P₁ P₂ : E → X}
    {δ d M₀ r : ℝ} (hr : 0 ≤ r) (hM₀ : 0 ≤ M₀)
    (h1 : ∀ z, ‖P₁ z - P₀ z‖ ≤ δ) (h2 : ∀ z, ‖P₂ z - P₀ z‖ ≤ δ)
    (h1' : ∀ z z', ‖P₁ z - P₀ z - (P₁ z' - P₀ z')‖ ≤ δ * ‖z - z'‖ ^ r)
    (h2' : ∀ z z', ‖P₂ z - P₀ z - (P₂ z' - P₀ z')‖ ≤ δ * ‖z - z'‖ ^ r)
    (h0 : ∀ z z', ‖z - z'‖ ≤ 1 → ‖P₀ z - P₀ z'‖ ≤ M₀ * ‖z - z'‖ ^ r)
    (hd : ∀ z, ‖P₁ z - P₂ z‖ ≤ d)
    (hd' : ∀ z z', ‖P₁ z - P₂ z - (P₁ z' - P₂ z')‖ ≤ d * ‖z - z'‖ ^ r) (z z' : E) :
    |(Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) (P₁ z - P₂ z)) -
        (Γ (P₁ z') - Γ (P₂ z') - g (P₀ z') (P₁ z' - P₂ z'))| ≤
      (2 * B₂ + B₃ * (M₀ + δ)) * δ * d * ‖z - z'‖ ^ r := by
  rcases le_or_gt ‖z - z'‖ 1 with hzz | hzz
  · exact abs_remainder_sub_le_of_le_one hΓ hg hb hl hB₃ h1 h2 (h1' z z') (h2' z z')
      (h0 z z' hzz) (hd z) (hd' z z') (Real.rpow_nonneg (norm_nonneg _) _) hM₀
  · have hB₂ : 0 ≤ B₂ := (norm_nonneg (g' 0)).trans (hb 0)
    have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (h1 z)
    have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd z)
    have hρ1 : 1 ≤ ‖z - z'‖ ^ r := Real.one_le_rpow hzz.le hr
    have ha := (abs_remainder_le hΓ hg hb h1 h2 z).trans
      (mul_le_mul_of_nonneg_left (hd z) (by positivity))
    have hb' := (abs_remainder_le hΓ hg hb h1 h2 z').trans
      (mul_le_mul_of_nonneg_left (hd z') (by positivity))
    calc _ ≤ |Γ (P₁ z) - Γ (P₂ z) - g (P₀ z) (P₁ z - P₂ z)| +
          |Γ (P₁ z') - Γ (P₂ z') - g (P₀ z') (P₁ z' - P₂ z')| := abs_sub _ _
      _ ≤ 2 * B₂ * δ * d := by linarith
      _ ≤ 2 * B₂ * δ * d * ‖z - z'‖ ^ r :=
          le_mul_of_one_le_right (by positivity) hρ1
      _ ≤ (2 * B₂ + B₃ * (M₀ + δ)) * δ * d * ‖z - z'‖ ^ r := by
          gcongr
          nlinarith [mul_nonneg hB₃ (add_nonneg hM₀ hδ0)]

/-- **Product with a cut-off**: for `|χ| ≤ K₀`, `χ` `K₁`-Lipschitz, `|f| ≤ F` and `f` `(H, r)`-Hölder,
`χ f` is `(K₀ H + (K₁ + 2 K₀) F, r)`-Hölder. -/
theorem abs_mul_sub_le {χ f : E → ℝ} {K₀ K₁ F H r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hK₁ : 0 ≤ K₁) (hχ0 : ∀ z, |χ z| ≤ K₀) (hχ1 : ∀ z z', |χ z - χ z'| ≤ K₁ * ‖z - z'‖)
    (hf0 : ∀ z, |f z| ≤ F) (hf1 : ∀ z z', |f z - f z'| ≤ H * ‖z - z'‖ ^ r) (z z' : E) :
    |χ z * f z - χ z' * f z'| ≤ (K₀ * H + (K₁ + 2 * K₀) * F) * ‖z - z'‖ ^ r := by
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (hχ0 z)
  have hF : 0 ≤ F := (abs_nonneg _).trans (hf0 z)
  have hχr : |χ z - χ z'| ≤ (K₁ + 2 * K₀) * ‖z - z'‖ ^ r := by
    have := SchauderWholeSpace.norm_sub_le_rpow_of_lipschitz_of_bound (g := χ) hK₁ hr0 hr1
      (fun x y => by rw [Real.norm_eq_abs]; exact hχ1 x y)
      (fun x => by rw [Real.norm_eq_abs]; exact hχ0 x) z z'
    rwa [Real.norm_eq_abs] at this
  have e : χ z * f z - χ z' * f z' = χ z * (f z - f z') + (χ z - χ z') * f z' := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hρ : 0 ≤ ‖z - z'‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
  calc |χ z| * |f z - f z'| + |χ z - χ z'| * |f z'|
      ≤ K₀ * (H * ‖z - z'‖ ^ r) + (K₁ + 2 * K₀) * ‖z - z'‖ ^ r * F :=
        add_le_add (mul_le_mul (hχ0 z) (hf1 z z') (abs_nonneg _) hK₀)
          (mul_le_mul hχr (hf0 z') (abs_nonneg _) (by positivity))
    _ = (K₀ * H + (K₁ + 2 * K₀) * F) * ‖z - z'‖ ^ r := by ring

end SGPT.Foundations.Analysis.Pending.HolderNemytskii
