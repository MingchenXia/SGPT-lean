import SGPT.Unibranch.E2Nov16FNOkaWeil

/-! Actual holomorphic hull maximum, from manufactured Oka--Weil approximation.
Blueprint: e2-nov16-fn-holomorphic-hull-maximum.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.E2Nov16FNHolomorphicHullMaximum
open E2Nov16FNPolynomialPolyhedron E2Nov16FNOkaWeil

theorem subset_polyHull {n : ℕ} (K : Set (ComplexModel n)) : K ⊆ polyHull K := by
  intro x hx p C hC
  exact hC x hx

theorem norm_le_on_polyHull {n : ℕ} {K U : Set (ComplexModel n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : polyHull K ⊆ U)
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U)
    (C : ℝ) (hC : ∀ z∈K, ‖f z‖≤C) :
    ∀ x∈polyHull K, ‖f x‖≤C := by
  intro x hx
  by_contra h
  have hgap : 0 < (‖f x‖-C)/3 := by linarith [lt_of_not_ge h]
  obtain ⟨Q,hQ⟩ := exists_polynomial_approx_on_hull hK hU hKU f hf hgap
  have hBound : ∀ z∈K, ‖polyEval Q z‖≤C+(‖f x‖-C)/3 := by
    intro z hz
    have hApprox := hQ z (subset_polyHull K hz)
    have htri : ‖polyEval Q z‖≤‖f z-polyEval Q z‖+‖f z‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_sub_add (polyEval Q z) (f z)
    linarith [hC z hz]
  have hp := hx Q (C+(‖f x‖-C)/3) hBound
  have htri := norm_le_norm_sub_add (f x) (polyEval Q x)
  have hApprox := hQ x hx
  linarith
end SGPT.Unibranch.E2Nov16FNHolomorphicHullMaximum
