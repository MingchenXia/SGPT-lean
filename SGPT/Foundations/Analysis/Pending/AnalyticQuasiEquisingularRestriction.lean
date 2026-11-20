import SGPT.Foundations.Analysis.Pending.CompactAnalyticPoleLelongGap
import SGPT.Foundations.Analysis.Pending.KahlerCurrentMax

set_option autoImplicit false

/-! # Actual quasi-equisingular terms have genuine ordinary restrictions -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction

open FirstPass FirstPass.NonKahlerLocus FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual decreasing convergence produces the Lelong comparison and zero
generic infimum for each term, without analytic type of the limit. -/
theorem term_generic_lelong_inf_eq_zero
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {V : Type*} (ι : V → M)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) (j : ℕ) :
    (⨅ y : V, lelongNumber (n := n) (uSeq j) (ι y)) = 0 := by
  have hpoint : ∀ x : M, u x ≤ uSeq j x := fun x =>
    (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  have hle : (⨅ y : V, lelongNumber (n := n) (uSeq j) (ι y)) ≤
      ⨅ y : V, lelongNumber (n := n) u (ι y) :=
    iInf_mono fun _ => KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (Eventually.of_forall hpoint)
  exact le_antisymm (by simpa only [hgeneric] using hle) zero_le

/-- The genuine approximation itself supplies every analytic term and its
background; zero generic infimum internally supplies the finite point. -/
theorem isThetaPshPotential_ordinaryRestriction_term
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [CompactSpace V] [ConnectedSpace V] {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) (j : ℕ) :
    IsThetaPshPotential
      (FirstPass.ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val
      (fun y => uSeq j (ι y)) := by
  apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
    hι (happ.term j).1
  · intro x _
    exact happ.term_hasAnalyticSingularityType j (complexChartAt (n := n) x)
      ((complexChartAt (n := n) x).val x)
      ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))
  · exact term_generic_lelong_inf_eq_zero happ ι hgeneric j

end

end SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
