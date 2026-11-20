import SGPT.Convex.ClosedStripExtension
import SGPT.Convex.TimeConjugateBounds

/-! Genuine forward dual bounds for the literal closed-strip extension. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter Topology
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
theorem closedStripExtension_left (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x))) (x : E) :
    closedStripExtension g f₀ hf₀ hg (x, 0) = (f₀ x : EReal) := by
  unfold closedStripExtension
  rw [if_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
    closedConvexStripProfile_left g f₀ hf₀ hg h₀]

omit [FiniteDimensional ℝ E] in
theorem closedStripExtension_right (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) (x : E) :
    closedStripExtension g f₀ hf₀ hg (x, 1) = (f₁ x : EReal) := by
  unfold closedStripExtension
  rw [if_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
    closedConvexStripProfile_right g f₀ f₁ hf₀ hf₁ hg h₁]

omit [FiniteDimensional ℝ E] in
/-- Endpoint hyperplanes of the actual extension supply both true conjugate
lower bounds, including every +∞ value of the spatial conjugates. -/
theorem closedStripConjugate_lower_bounds (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x)))
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x)))
    (m : F) (s : ℝ) :
    max (conjugate B (fun x => (f₀ x : EReal)) m)
      (conjugate B (fun x => (f₁ x : EReal)) m + (s : EReal)) ≤
      conjugate (timeProductPairing B) (closedStripExtension g f₀ hf₀ hg) (m, s) := by
  apply max_le
  · apply iSup_le
    intro x
    have hh := le_iSup (fun p : E × ℝ => (timeProductPairing B p (m, s) : EReal) -
      closedStripExtension g f₀ hf₀ hg p) (x, 0)
    simpa only [conjugate, timeProductPairing_apply, zero_mul, add_zero,
      closedStripExtension_left g f₀ hf₀ hg h₀] using hh
  · have hex := iSup_add_iSup (fun x : E => (B x m : EReal) - (f₁ x : EReal))
      (fun _ : Unit => (s : EReal))
    simp only [iSup_const] at hex
    change (⨆ x : E, (B x m : EReal) - (f₁ x : EReal)) + (s : EReal) ≤ _
    rw [hex]
    apply iSup_le
    intro x
    have hh := le_iSup (fun p : E × ℝ => (timeProductPairing B p (m, s) : EReal) -
      closedStripExtension g f₀ hf₀ hg p) (x, 1)
    simp only [timeProductPairing_apply, one_mul,
      closedStripExtension_right g f₀ f₁ hf₀ hf₁ hg h₁] at hh
    change (B x m : EReal) - (f₁ x : EReal) + (s : EReal) ≤ _
    have heq : B x m - f₁ x + s = B x m + s - f₁ x := by ring
    rw [← EReal.coe_sub, ← EReal.coe_add, heq]
    exact hh

omit [FiniteDimensional ℝ E] in
/-- An actual finite common lower profile gives the original dual upper
bound G(m)+max(s,0), for the literal manufactured closed-strip function. -/
theorem closedStripConjugate_upper_bound (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (g : E × ℝ → ℝ) (f₀ η : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (hlower : ∀ (x : E) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      η x ≤ closedConvexStripProfile g f₀ hf₀ hg (x, t))
    (m : F) (s : ℝ) :
    conjugate (timeProductPairing B) (closedStripExtension g f₀ hf₀ hg) (m, s) ≤
      conjugate B (fun x => (η x : EReal)) m + ((max s 0 : ℝ) : EReal) := by
  apply iSup_le
  intro p
  by_cases hp : p.2 ∈ Icc (0 : ℝ) 1
  · have htime : p.2 * s ≤ max s 0 := by
      by_cases hs : 0 ≤ s
      · rw [max_eq_left hs]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hp.2 hs
      · rw [max_eq_right (le_of_not_ge hs)]
        exact mul_nonpos_of_nonneg_of_nonpos hp.1 (le_of_not_ge hs)
    have hcost : B p.1 m + p.2 * s - closedConvexStripProfile g f₀ hf₀ hg p ≤
        B p.1 m - η p.1 + max s 0 := by
      have hh := hlower p.1 p.2 hp
      linarith
    have hfenchel : ((B p.1 m - η p.1 : ℝ) : EReal) ≤
        conjugate B (fun x => (η x : EReal)) m := by
      simpa only [conjugate, ← EReal.coe_sub] using
        (le_iSup (fun x : E => (B x m : EReal) - (η x : EReal)) p.1)
    change (timeProductPairing B p (m, s) : EReal) -
      closedStripExtension g f₀ hf₀ hg p ≤ _
    rw [timeProductPairing_apply, closedStripExtension, if_pos hp, ← EReal.coe_sub]
    exact (EReal.coe_le_coe_iff.mpr hcost).trans (by
      rw [EReal.coe_add]
      exact add_le_add hfenchel le_rfl)
  · simp only [closedStripExtension, if_neg hp, EReal.sub_top, bot_le]

end SGPT.Convex
