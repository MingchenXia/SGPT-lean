import SGPT.Okounkov.EffectiveDivisorOrder
import SGPT.Okounkov.FlattenedDivisorMetric
import SGPT.Foundations.Analysis.Pending.ActualInvertibleIdealDifference

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open DivisorExponent IdealWeightPowers GermIdealTotalTransform

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem mem_vanishingIdeal_power_off_closed {W : Set M} (hW : IsClosed W)
    {x : M} (hx : x ∉ W) {g : M → ℂ} (hg : HolomorphicAt n g x) (r : ℕ) :
    (idealPow (vanishingIdeal (n := n) W) r).mem x g := by
  have h1 : (vanishingIdeal (n := n) W).mem x (fun _ : M => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1, ?_⟩
    filter_upwards [hW.isOpen_compl.mem_nhds hx] with y hy hyW
    exact absurd hyW hy
  induction r with
  | zero => exact hg
  | succ r ih =>
    have hmul := mem_mul_of_mem_mem ih h1 (hg.mul (holomorphicAt_const 1))
    simpa only [idealPow_succ, Pi.mul_apply, mul_one] using hmul

/-- Actual maximal local divisibility produces GLOBAL inclusion in the
same smooth-component ideal power, including original off-component stalks. -/
theorem effectiveDivisor_ideal_le_component_power {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (D : EffectiveDivisor n M) {a : ℕ}
    (ha : ∀ x ∈ W, IsDivNear n D.ideal W a x) :
    D.ideal.Le (idealPow (vanishingIdeal (n := n) W) a) := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  intro x g hg
  by_cases hx : x ∈ W
  · exact (isDivNear_iff hcoh (hW.2.2 x hx)).mp (ha x hx) g hg
  · exact mem_vanishingIdeal_power_off_closed hW.1 hx
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) a

/-- The original Cartier divisor and genuine smooth connected divisor
internally produce their effective residual: one actual integer power
is removed, and its actual residual support does not contain the component. -/
theorem exists_effectiveDivisor_residual_smooth_component {m : ℕ}
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) :
    ∃ (a : ℕ) (R : EffectiveDivisor (m + 1) M),
      (∀ x ∈ W, ∀ r : ℕ, IsDivNear (m + 1) D.ideal W r x ↔ r ≤ a) ∧
      D.ideal = (idealPow (vanishingIdeal (n := m + 1) W) a).mul R.ideal ∧
      ¬ W ⊆ R.support := by
  obtain ⟨a, ha⟩ := exists_effectiveDivisor_order_on_connected_component hW D
  have hIW : (vanishingIdeal (n := m + 1) W).IsInvertible :=
    BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne hW.1
      (smooth_divisor_interior_eq_empty hW) (fun x hx => ⟨m, hW.2.2 x hx, rfl⟩)
  let L : EffectiveDivisor (m + 1) M :=
    ⟨idealPow (vanishingIdeal (n := m + 1) W) a,
      BlowupExceptionalDivisor.isInvertible_idealPow hIW a⟩
  have hle : D.ideal.Le L.ideal :=
    effectiveDivisor_ideal_le_component_power hW D
      (fun x hx => (ha x hx a).mpr le_rfl)
  obtain ⟨R, hDR⟩ := ActualInvertibleIdealDifference.exists_effectiveDivisor_difference D L hle
  refine ⟨a, R, ha, hDR, ?_⟩
  intro hcontains
  have hRcoh := DivisorMetric.isCoherent_of_isInvertible R.isInvertible
  have hRle : R.ideal.Le (vanishingIdeal (n := m + 1) W) := by
    intro x g hg
    refine ⟨RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hRcoh hg, ?_⟩
    filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hRcoh hg] with y hy hyW
    exact hcontains hyW g hy
  have hsucc : D.ideal.Le (idealPow (vanishingIdeal (n := m + 1) W) (a + 1)) := by
    rw [hDR]
    intro x g hg
    rw [idealPow_succ]
    change ((idealPow (vanishingIdeal (n := m + 1) W) a).mul R.ideal).mem x g at hg
    exact InvertibleIdealQuotient.mem_mul_iff.mpr ((InvertibleIdealQuotient.mem_mul_iff.mp hg).mono
      (fun t ⟨p, q, hp, hq, heq⟩ => ⟨p, q, hp, hRle x q hq, heq⟩))
  obtain ⟨p, hp⟩ := hW.2.1.nonempty
  have hnear : IsDivNear (m + 1) D.ideal W (a + 1) p :=
    (isDivNear_iff (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
      (hW.2.2 p hp)).mpr (hsucc p)
  have := (ha p hp (a + 1)).mp hnear
  omega

end SGPT.Okounkov
