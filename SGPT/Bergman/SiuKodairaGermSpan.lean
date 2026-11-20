import SGPT.PSH.BookMultiplierSections
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Evaluation and first derivatives of actual germ generation relations

These scalar identities differentiate the finite holomorphic germ span
itself. They do not posit any jet-surjectivity or separating-section output.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:separation`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Evaluate the actual finite germ relation; a nonzero value detects one
actual nonzero generator. -/
theorem exists_generator_ne_zero_of_isInSpanAt
    {S : (X → ℂ) → Prop} {x : X} {g : X → ℂ}
    (hg : IsInSpanAt (n := n) S x g) (hg0 : g x ≠ 0) :
    ∃ s : X → ℂ, S s ∧ s x ≠ 0 := by
  classical
  obtain ⟨-, N, s, a, hs, -, heq⟩ := hg
  have heq0 : g x = ∑ i, a i x * s i x := heq.self_of_nhds
  have hsum : ∑ i, a i x * s i x ≠ 0 := fun hz => hg0 (heq0.trans hz)
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨s i, hs i, fun hz => hi (by rw [hz, mul_zero])⟩

/-- The coefficient of a native holomorphic germ in an actual source chart
is genuinely complex differentiable at the original point. -/
theorem differentiableAt_chart_of_holomorphicAt (c : ComplexChart n X)
    {x : X} (hx : x ∈ c.val.source) {g : X → ℂ} (hg : HolomorphicAt n g x) :
    DifferentiableAt ℂ (fun z => g (c.val.symm z)) (c.val x) := by
  apply SGPT.PSH.differentiableAt_comp_chart_symm c (c.val.map_source hx)
  simpa only [c.val.left_inv hx] using hg.self_of_nhds

/-- A nonzero first derivative of a generated germ must occur in one of the
actual generators when all their values vanish. -/
theorem exists_generator_derivative_ne_zero_of_isInSpanAt
    {S : (X → ℂ) → Prop} {x : X} {g : X → ℂ}
    (hg : IsInSpanAt (n := n) S x g)
    (hhol : ∀ s : X → ℂ, S s → HolomorphicAt n s x)
    (hzero : ∀ s : X → ℂ, S s → s x = 0)
    (c : ComplexChart n X) (hx : x ∈ c.val.source) (v : ComplexModel n)
    (hder : fderiv ℂ (fun z => g (c.val.symm z)) (c.val x) v ≠ 0) :
    ∃ s : X → ℂ, S s ∧
      fderiv ℂ (fun z => s (c.val.symm z)) (c.val x) v ≠ 0 := by
  classical
  obtain ⟨-, N, s, a, hs, ha, heq⟩ := hg
  by_contra hbad
  have hsz : ∀ i, fderiv ℂ (fun z => s i (c.val.symm z)) (c.val x) v = 0 := by
    intro i
    by_contra hi
    exact hbad ⟨s i, hs i, hi⟩
  have hsd := fun i => differentiableAt_chart_of_holomorphicAt c hx (hhol (s i) (hs i))
  have had := fun i => differentiableAt_chart_of_holomorphicAt c hx (ha i)
  have hprod : ∀ i, fderiv ℂ (fun z => a i (c.val.symm z) * s i (c.val.symm z))
      (c.val x) v = 0 := by
    intro i
    rw [fderiv_fun_mul (had i) (hsd i)]
    simp only [add_apply, smul_apply, smul_eq_mul,
      c.val.left_inv hx, hzero (s i) (hs i), hsz i, mul_zero, zero_mul, add_zero]
  have hsum : fderiv ℂ (fun z => ∑ i, a i (c.val.symm z) * s i (c.val.symm z))
      (c.val x) v = 0 := by
    rw [fderiv_fun_sum (fun i _ => (had i).fun_mul (hsd i))]
    simp only [sum_apply]
    exact Finset.sum_eq_zero fun i _ => hprod i
  have heq' : (fun z => g (c.val.symm z)) =ᶠ[𝓝 (c.val x)]
      fun z => ∑ i, a i (c.val.symm z) * s i (c.val.symm z) := by
    have heq0 : g =ᶠ[𝓝 (c.val.symm (c.val x))] fun y => ∑ i, a i y * s i y := by
      simpa only [c.val.left_inv hx] using heq
    exact (c.val.continuousAt_symm (c.val.map_source hx)).eventually heq0
  exact hder (by rw [heq'.fderiv_eq]; exact hsum)

end SGPT.Bergman.SiuKodaira
