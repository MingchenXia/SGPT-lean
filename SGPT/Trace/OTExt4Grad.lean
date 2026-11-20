import SGPT.Trace.TwistedL2SingularCutoff
import SGPT.Trace.TwistedL2YDensity
import SGPT.Trace.OTExt2LocalCalc
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

/-!
# Cut-offs on a compact Kähler manifold: gradient bounds and partitions of unity

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:cutoffs`.  Inputs of the gluing in FPT
`lem:critical-gain-initial-gluing` ("the bounds on the cutoffs and their derivatives"):

* `exists_holDerivSq_le_kahlerQuad`: for a smooth function `η` on a compact Kähler manifold
  there is `M` with `|∂η(v)|² ≤ M ω(v, iv)` in **every** holomorphic chart.  Proof: by
  `ddᶜ(η²) = 2η ddᶜη + 2 i∂η ∧ ∂̄η/π` it suffices to bound `ddᶜ(η²)` above and `ddᶜη` above and
  below by multiples of `ω`, which holds near every point in every chart
  (`exists_nhds_smoothDDC_domination`); finitely many such neighbourhoods cover `X`.
* `norm_dbarPairing_ofReal_sq`: `|⟨∂̄η, v⟩|² = |∂η(v)|²` for real `η`.
* `exists_chartSmooth_partition`: a smooth partition of unity subordinate to a finite open
  cover of a compact complex manifold, with chart-smooth members.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Trace.TwistedL2

variable {n : ℕ}

/-- `|⟨∂̄g, v⟩|² = |∂g(v)|²` for a real function `g`. -/
theorem norm_dbarPairing_ofReal_sq {g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hg : DifferentiableAt ℝ g z) (v : ComplexModel n) :
    ‖dbarPairing (fun y => (g y : ℂ)) z v‖ ^ 2 = holDerivSq g z v := by
  rw [dbarPairing_eq_dbarDir, SGPT.Trace.OTExt2.norm_dbarDir_ofReal_sq hg]

/-- `L(g²) = 2 g L(g) + 4 |∂g|²`, in the normalization of `leviForm` and `holDerivSq`. -/
theorem leviForm_mul_self {g : ComplexModel n → ℝ} {z : ComplexModel n} (hg : ContDiffAt ℝ 2 g z)
    (v : ComplexModel n) :
    leviForm (fun y => g y * g y) z v = 2 * g z * leviForm g z v + 2 * holDerivSq g z v := by
  rw [Pending.ConcentrationPotentialLevi.leviForm_mul hg hg, holDerivSq]
  ring

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Gradient bound of a smooth function in every chart.**  On a compact Kähler manifold, for a
chart-smooth `η` there is `M ≥ 0` with `|∂(η ∘ c⁻¹)(v)|² ≤ M ω_c(v, iv)` for every chart `c`. -/
theorem exists_holDerivSq_le_kahlerQuad [CompactSpace X] (ωb : KahlerBackground n X) {η : X → ℝ}
    (hη : ChartSmooth (n := n) η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      holDerivSq (fun y => η (c.val.symm y)) z v ≤ M * kahlerQuad ωb c z v := by
  have hsq : ChartSmooth (n := n) (fun x => -(η x * η x)) := fun c => ((hη c).mul (hη c)).neg
  have hneg : ChartSmooth (n := n) (fun x => -η x) := fun c => (hη c).neg
  choose B₁ hB₁ V₁ hV₁o hxV₁ hd₁ using fun x => exists_nhds_smoothDDC_domination ωb hsq x
  choose B₂ hB₂ V₂ hV₂o hxV₂ hd₂ using fun x => exists_nhds_smoothDDC_domination ωb hη x
  choose B₃ hB₃ V₃ hV₃o hxV₃ hd₃ using fun x => exists_nhds_smoothDDC_domination ωb hneg x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => V₁ x ∩ V₂ x ∩ V₃ x)
    (fun x => ((hV₁o x).inter (hV₂o x)).inter (hV₃o x))
    (fun y _ => mem_iUnion.mpr ⟨y, ⟨hxV₁ y, hxV₂ y⟩, hxV₃ y⟩)
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_chartSmooth hη).continuousOn
  set S : ℝ := ∑ x ∈ t, (B₁ x + B₂ x + B₃ x) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => by linarith [hB₁ x, hB₂ x, hB₃ x]
  set A' : ℝ := max A 0
  refine ⟨Real.pi * (S + 2 * A' * S), by positivity, fun c z hz v => ?_⟩
  obtain ⟨x, hxt, hzx⟩ : ∃ x ∈ t, c.val.symm z ∈ V₁ x ∩ V₂ x ∩ V₃ x := by
    have := ht (mem_univ (c.val.symm z))
    simp only [mem_iUnion] at this
    obtain ⟨x, hxt, h⟩ := this
    exact ⟨x, hxt, h⟩
  set g : ComplexModel n → ℝ := fun y => η (c.val.symm y) with hg
  have hg2 : ContDiffAt ℝ 2 g z :=
    ((hη c z hz).contDiffAt (c.val.open_target.mem_nhds hz)).of_le (by norm_cast)
  have hgg2 : ContDiffAt ℝ 2 (fun y => -(g y * g y)) z := (hg2.mul hg2).neg
  have hn1 : leviForm (fun y => -(g y * g y)) z v = -leviForm (fun y => g y * g y) z v :=
    leviForm_neg (fun y => g y * g y) z v
  have hn3 : leviForm (fun y => -g y) z v = -leviForm g z v := leviForm_neg g z v
  have e₁ : 0 ≤ -(2 * g z * leviForm g z v + 2 * holDerivSq g z v) / Real.pi +
      B₁ x * kahlerQuad ωb c z v := by
    have h := hd₁ x c z hz hzx.1.1 v
    have h' : smoothDDC (fun y => -(g y * g y)) z ![v, Complex.I • v] =
        leviForm (fun y => -(g y * g y)) z v / Real.pi := smoothDDC_complexDiagonal_eq_leviForm hgg2 v
    rw [hn1, leviForm_mul_self hg2 v] at h'
    exact h' ▸ h
  have e₂ : 0 ≤ leviForm g z v / Real.pi + B₂ x * kahlerQuad ωb c z v := by
    have h := hd₂ x c z hz hzx.1.2 v
    have h' : smoothDDC g z ![v, Complex.I • v] = leviForm g z v / Real.pi :=
      smoothDDC_complexDiagonal_eq_leviForm hg2 v
    exact h' ▸ h
  have e₃ : 0 ≤ -leviForm g z v / Real.pi + B₃ x * kahlerQuad ωb c z v := by
    have h := hd₃ x c z hz hzx.2 v
    have h' : smoothDDC (fun y => -g y) z ![v, Complex.I • v] = leviForm (fun y => -g y) z v / Real.pi :=
      smoothDDC_complexDiagonal_eq_leviForm hg2.neg v
    rw [hn3] at h'
    exact h' ▸ h
  have hkq : 0 ≤ kahlerQuad ωb c z v := kahlerQuad_nonneg ωb c hz v
  have hpi := Real.pi_pos
  have hsx := Finset.single_le_sum (f := fun y => B₁ y + B₂ y + B₃ y)
    (fun y _ => by linarith [hB₁ y, hB₂ y, hB₃ y]) hxt
  have h1 : B₁ x ≤ S := by linarith [hB₂ x, hB₃ x]
  have h2 : B₂ x ≤ S := by linarith [hB₁ x, hB₃ x]
  have h3 : B₃ x ≤ S := by linarith [hB₁ x, hB₂ x]
  have hgz : |g z| ≤ A' := by
    have h := hA (c.val.symm z) (mem_univ _)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  -- `L(g) ≤ π B₃ ω` and `-L(g) ≤ π B₂ ω`
  have hL1 : leviForm g z v ≤ Real.pi * (S * kahlerQuad ωb c z v) := by
    have : leviForm g z v / Real.pi ≤ B₃ x * kahlerQuad ωb c z v := by
      rw [neg_div] at e₃; linarith
    rw [div_le_iff₀ hpi] at this
    nlinarith [mul_le_mul_of_nonneg_right h3 hkq]
  have hL2 : -leviForm g z v ≤ Real.pi * (S * kahlerQuad ωb c z v) := by
    have : -(leviForm g z v / Real.pi) ≤ B₂ x * kahlerQuad ωb c z v := by linarith
    rw [← neg_div, div_le_iff₀ hpi] at this
    nlinarith [mul_le_mul_of_nonneg_right h2 hkq]
  have hLabs : |leviForm g z v| ≤ Real.pi * (S * kahlerQuad ωb c z v) := abs_le.mpr ⟨by linarith, hL1⟩
  have hgL : -(2 * g z * leviForm g z v) ≤ 2 * A' * (Real.pi * (S * kahlerQuad ωb c z v)) := by
    have h := abs_mul (g z) (leviForm g z v)
    have h' : |g z| * |leviForm g z v| ≤ A' * (Real.pi * (S * kahlerQuad ωb c z v)) :=
      mul_le_mul hgz hLabs (abs_nonneg _) ((le_max_right _ _))
    nlinarith [neg_abs_le (g z * leviForm g z v)]
  have hsq' : (2 * g z * leviForm g z v + 2 * holDerivSq g z v) / Real.pi ≤
      B₁ x * kahlerQuad ωb c z v := by rw [neg_div] at e₁; linarith
  rw [div_le_iff₀ hpi] at hsq'
  have hB1S : B₁ x * kahlerQuad ωb c z v * Real.pi ≤ S * kahlerQuad ωb c z v * Real.pi :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hkq) hpi.le
  have hH : 2 * holDerivSq g z v ≤
      Real.pi * (S * kahlerQuad ωb c z v) + 2 * A' * (Real.pi * (S * kahlerQuad ωb c z v)) := by
    have e : S * kahlerQuad ωb c z v * Real.pi = Real.pi * (S * kahlerQuad ωb c z v) := by ring
    linarith
  have hX : 0 ≤ Real.pi * (S * kahlerQuad ωb c z v) := by positivity
  have hA0 : 0 ≤ A' := le_max_right _ _
  have e2 : Real.pi * (S + 2 * A' * S) * kahlerQuad ωb c z v =
      Real.pi * (S * kahlerQuad ωb c z v) + 2 * A' * (Real.pi * (S * kahlerQuad ωb c z v)) := by ring
  rw [e2]
  nlinarith [mul_nonneg hA0 hX]

/-- **A chart-smooth partition of unity** subordinate to a finite open cover of a compact complex
manifold. -/
theorem exists_chartSmooth_partition [CompactSpace X] {ι : Type} [Fintype ι] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i) :
    ∃ η : ι → X → ℝ, (∀ i, ChartSmooth (n := n) (η i)) ∧ (∀ i x, 0 ≤ η i x) ∧
      (∀ x, ∑ i, η i x = 1) ∧ ∀ i, tsupport (η i) ⊆ U i := by
  have : IsManifold 𝓘(ℝ, ComplexModel n) ∞ X := isManifold_realX
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ComplexModel n)
    isClosed_univ U hU (fun x _ => mem_iUnion.mpr (hcov x))
  refine ⟨fun i x => θ i x, fun i c => chartSmooth_of_contMDiff (θ i).contMDiff c,
    fun i x => θ.nonneg i x, fun x => ?_, hθ⟩
  rw [← finsum_eq_sum_of_fintype]
  exact θ.sum_eq_one (mem_univ x)

end SGPT.Trace.OTExt4
