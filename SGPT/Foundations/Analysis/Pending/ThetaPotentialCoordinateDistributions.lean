import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.XiaoPoissonChartCompatibility
import SGPT.Foundations.Analysis.GermPshLeviPositivity

set_option autoImplicit false

/-! # Actual compatible locally theta-PSH distributions from genuine potentials -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.ThetaPotentialCoordinateDistributions

open FirstPass GlobalCurrentPotentials ThetaPshChartLimitGluing

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual regular coordinate distributions, with integrability produced from the genuine potential. -/
def potentialCoordinateDistribution
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) :
    ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ) :=
  fun e => regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal)
    (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e)

/-- The actual potential distributions satisfy the genuine Jacobian-weighted overlap identity. -/
theorem isCoordinateCompatible_potentialCoordinateDistribution
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) :
    XiaoPoissonChartCompatibility.IsCoordinateCompatible
      (potentialCoordinateDistribution b θ u hu) := by
  let v : ℕ → M → ℝ := fun _ x => (u x).toReal
  have hT (e : ComplexChart (m + 1) M) :
      IsChartLimit b.addHaar atTop v e (potentialCoordinateDistribution b θ u hu e) := by
    intro φ
    simp only [potentialCoordinateDistribution, regularDistribution_apply, chartFunction, v]
    exact tendsto_const_nhds
  intro e f ψ hψ
  exact (hT e).apply_pullTest (hT f) ψ hψ

/-- Genuine theta-PSH potentials produce actual locally theta-PSH regular distributions. -/
theorem isLocallyThetaPshDistribution_potentialCoordinateDistribution
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1)))
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M) :
    IsLocallyThetaPshDistribution b.addHaar θ e
      (potentialCoordinateDistribution b θ u hu e) := by
  intro z hz
  obtain ⟨W, ρ, hzW, hpot, hpsh⟩ := hu.1 e z hz
  let Ω : Opens (ComplexModel (m + 1)) := ⟨W, hpot.1⟩
  have hW : Ω ≤ chartTarget e := hpot.2.1
  have hρ : LocallyIntegrableOn ρ Ω b.addHaar :=
    hpot.2.2.1.continuousOn.locallyIntegrableOn hpot.1.measurableSet
  have hUL : LocallyIntegrableOn (fun y => (chartFunction u e y).toReal) Ω b.addHaar :=
    (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e).mono_set hW
  have hfin : ∀ᵐ y ∂b.addHaar.restrict Ω,
      chartFunction u e y ≠ ⊤ ∧ chartFunction u e y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hW
      (quasiPsh_chart_ae_finite b (Nat.succ_pos m) u hu.quasiPshPotential e)
  have hreal : (fun y => (chartFunction u e y).toReal + ρ y) =ᵐ[b.addHaar.restrict Ω]
      (fun y => (chartFunction u e y + (ρ y : EReal)).toReal) :=
    hfin.mono fun _ hy => (ereal_toReal_add_coe hy _).symm
  have hgL : LocallyIntegrableOn
      (fun y => (chartFunction u e y + (ρ y : EReal)).toReal) Ω b.addHaar :=
    (hUL.add hρ).congr hreal
  have hgf : ∀ᵐ y ∂b.addHaar.restrict Ω,
      chartFunction u e y + (ρ y : EReal) ≠ ⊤ ∧
      chartFunction u e y + (ρ y : EReal) ≠ ⊥ :=
    hfin.mono fun _ hy => ereal_add_coe_finite hy _
  have heq : regularDistribution b.addHaar
      (fun y => (chartFunction u e y + (ρ y : EReal)).toReal) hgL =
      restrictDistribution (potentialCoordinateDistribution b θ u hu e) hW +
        regularDistribution b.addHaar ρ hρ := by
    rw [potentialCoordinateDistribution, restrictDistribution_regularDistribution]
    exact (regularDistribution_congr_ae_on (hUL.add hρ) hgL hreal).symm.trans
      (regularDistribution_add hUL hρ)
  refine ⟨Ω, hW, ρ, hρ, hzW, hpot, ?_⟩
  rw [← heq]
  exact hpsh.hasNonnegativeDistributionalLevi_of_locallyIntegrable hgL hgf

end

end SGPT.Foundations.Analysis.Pending.ThetaPotentialCoordinateDistributions
