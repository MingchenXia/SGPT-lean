import SGPT.Convex.DerivativeConvergence
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.CorrectedSecant
open Set Filter
open scoped Topology

/-- Exact concave one-sided secant route: only all-t lower limits,
convergence at zero and differentiability at zero are needed. This uses
the accepted genuine original one-sided convex secant theorem by negation;
it does not assume all-t convergence of the concave sequence. -/
theorem tendsto_deriv_of_concave_liminf_ge
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ k, ConcaveOn ℝ univ (f k))
    (hfd : ∀ k, DifferentiableAt ℝ (f k) 0) (hgd : DifferentiableAt ℝ g 0)
    (hlim : ∀ t, (g t : EReal) ≤ liminf (fun k => (f k t : EReal)) atTop)
    (hvalue : Tendsto (fun k => f k 0) atTop (𝓝 (g 0))) :
    Tendsto (fun k => deriv (f k) 0) atTop (𝓝 (deriv g 0)) := by
  have hupper (t : ℝ) (_ht : t ∈ (univ : Set ℝ)) :
      limsup (fun k => (-f k t : EReal)) atTop ≤ (-g t : EReal) := by
    change limsup (-(fun k => (f k t : EReal))) atTop ≤ -(g t : EReal)
    rw [EReal.limsup_neg]
    exact EReal.negOrderIso.monotone (hlim t)
  have h := SGPT.Convex.tendsto_deriv_of_convex_limsup_le isOpen_univ (mem_univ 0)
    (f := fun k t => -f k t) (g := fun t => -g t)
    (fun k => (hf k).neg) (fun k => (hfd k).neg) hgd.neg hupper hvalue.neg
  have hd (F : ℝ → ℝ) : deriv (fun t => -F t) 0 = -deriv F 0 := deriv.neg
  simp only [hd] at h
  simpa only [neg_neg] using h.neg

/-- A genuinely convergent lower approximant gives the needed complete
extended-real lower limit; no boundedness or desired limit certificate
for the upper sequence is assumed. -/
theorem le_liminf_of_lower_approx
    {a f : ℕ → ℝ} {b : ℝ} (hcompare : ∀ k, a k ≤ f k)
    (ha : Tendsto a atTop (𝓝 b)) :
    (b : EReal) ≤ liminf (fun k => (f k : EReal)) atTop := by
  have he : Tendsto (fun k => (a k : EReal)) atTop (𝓝 (b : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp ha
  have hm : liminf (fun k => (a k : EReal)) atTop ≤
      liminf (fun k => (f k : EReal)) atTop :=
    liminf_le_liminf (Filter.Eventually.of_forall
      (fun k => EReal.coe_le_coe_iff.mpr (hcompare k)))
  rwa [he.liminf_eq] at hm

/-- The corrected source-proof scalar consumer: actual lower approximant
limits at all t and convergence of f ONLY at zero suffice. For the book,
the lower approximants are the actual sup-norm Donaldson functionals;
their asymptotic limits remain separate genuine producers. -/
theorem tendsto_deriv_of_concave_lower_approx
    {a f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ k, ConcaveOn ℝ univ (f k))
    (hfd : ∀ k, DifferentiableAt ℝ (f k) 0) (hgd : DifferentiableAt ℝ g 0)
    (hcompare : ∀ k t, a k t ≤ f k t)
    (ha : ∀ t, Tendsto (fun k => a k t) atTop (𝓝 (g t)))
    (hvalue : Tendsto (fun k => f k 0) atTop (𝓝 (g 0))) :
    Tendsto (fun k => deriv (f k) 0) atTop (𝓝 (deriv g 0)) :=
  tendsto_deriv_of_concave_liminf_ge hf hfd hgd
    (fun t => le_liminf_of_lower_approx (fun k => hcompare k t) (ha t)) hvalue

/-- The precise corrected source-data pattern: all-t SUP lower
approximant convergence and only the actual base BM difference at zero.
No convergence of f away from zero, or extra all-t BM property, is used. -/
theorem tendsto_deriv_of_concave_lower_approx_zero_difference
    {a f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ k, ConcaveOn ℝ univ (f k))
    (hfd : ∀ k, DifferentiableAt ℝ (f k) 0) (hgd : DifferentiableAt ℝ g 0)
    (hcompare : ∀ k t, a k t ≤ f k t)
    (ha : ∀ t, Tendsto (fun k => a k t) atTop (𝓝 (g t)))
    (hzero : Tendsto (fun k => a k 0 - f k 0) atTop (𝓝 0)) :
    Tendsto (fun k => deriv (f k) 0) atTop (𝓝 (deriv g 0)) := by
  have hvalue : Tendsto (fun k => f k 0) atTop (𝓝 (g 0)) := by
    simpa only [sub_sub_cancel, sub_zero] using (ha 0).sub hzero
  exact tendsto_deriv_of_concave_lower_approx hf hfd hgd hcompare ha hvalue

end SGPT.Bergman.CorrectedSecant
