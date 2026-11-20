import SGPT.Foundations.Analysis.Pending.IntrinsicJacobianCoefficient


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.UniformLocalCanonicalNecessity

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder IntrinsicJacobianCoefficient

universe u

private theorem exists_finite_order_of_factor_sum (r : ℕ∞) (a A : ℕ)
    (h : (a : ℕ∞) + 1 = r + (A : ℕ∞)) :
    ∃ b : ℕ, r = (b : ℕ∞) ∧ a + 1 = b + A := by
  have hr : r ≠ ⊤ := by
    intro hh
    simp [hh] at h
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hr
  refine ⟨b, hb.symm, ?_⟩
  apply ENat.natCast_inj.mp
  simpa only [ENat.natCast_add, ENat.natCast_one, hb] using h

/-- One original strict margin is read by actual local normal orders and the exact produced discrepancy. -/
theorem exists_uniform_canonical_local_bound
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {x : X} {c : ℝ} {F : X → ℂ}
    (hint : (multiplierIdeal (n := m + 1) c u).mem x F)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X)
      (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (E : Set Y) (hE : FirstPass.BlowupSequences.IsClosedConnectedSubmanifold (m + 1) E m)
      (y : Y) (hy : π y = x) (Φ : DivisorFlattening (m := m) E y),
      ∃ b : ℕ,
        pullbackNormalOrder hπ Φ F (by rw [hy]; exact hint.1) = (b : ℕ∞) ∧
        ENNReal.ofReal ((1 + δ) * c) *
          (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) <
            ENNReal.ofReal (2 * ((b + representedLogDiscrepancy hπ hE : ℕ) : ℝ)) := by
  obtain ⟨δ, hδ, hmodels⟩ :=
    RawQuasiPshModificationUniformNecessity.exists_uniform_strict_modification_bound hu hint hFnon
  refine ⟨δ, hδ, ?_⟩
  intro Y _ _ _ π hπ E hE y hy Φ
  obtain ⟨a, H, hH, _hHnon, hfactor, hnot, hbound⟩ := hmodels Y π hπ y hy E Φ
  have hF : HolomorphicAt (m + 1) F (π y) := by rw [hy]; exact hint.1
  have horder := weightedTest_order_add_one_eq_localOrder_add_logDiscrepancy
    hπ hE Φ F hF a H hH (by simpa only [hy] using hfactor) (hnot (Fin.last m))
  obtain ⟨b, hb, hnum⟩ := exists_finite_order_of_factor_sum
    (pullbackNormalOrder hπ Φ F hF) (a (Fin.last m)) (representedLogDiscrepancy hπ hE) horder
  refine ⟨b, hb, ?_⟩
  have hreal : 2 * ((a (Fin.last m) : ℝ) + 1) =
      2 * ((b + representedLogDiscrepancy hπ hE : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => 2 * (k : ℝ)) hnum
  rwa [hreal] at hbound

end SGPT.Foundations.Analysis.Pending.UniformLocalCanonicalNecessity
