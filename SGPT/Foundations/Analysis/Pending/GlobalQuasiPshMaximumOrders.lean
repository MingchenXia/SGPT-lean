import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
import SGPT.Foundations.Analysis.Pending.IEquivalentMax

set_option autoImplicit false

/-! # Actual one-way multiplier maximum and full quasi-PSH P/I characterizations -/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope IEquivalentMax
  GlobalQuasiPshPositivePDomain SingularGlobalPOrder SingularGlobalPMaximum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual asymmetric chart-max producer consumes only one-way
multiplier inclusion and produces the maximum's full multiplier type. -/
theorem iOrderOnManifold_iff_iEquivalent_max
    {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v) :
    IOrderOnManifold (n := n) u v ↔
      IEquivalentOnManifold (n := n) (fun x => max (u x) (v x)) v := by
  have hw := IsThetaPshPotential.max hu hv
  constructor
  · intro huv
    refine ⟨?_, iOrderOnManifold_of_le hw.1.quasiPlurisubharmonic
      (fun x => le_max_right _ _)⟩
    intro c hc e z hz f hf hmem
    let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    obtain ⟨W, ρ, hzW, hρ⟩ := hv.1.hasSmoothLocalPotentials e z hz
    have hpsh : ∀ {q : M → EReal}, IsThetaPshPotential θ q →
        PlurisubharmonicOn (fun y => chartFunction q e y + (ρ y : EReal)) W :=
      fun {q} hq => chartCorrectedFamily_plurisubharmonicOn (F := {q})
        (fun _ h => by rw [mem_singleton_iff.mp h]; exact hq)
        e hρ _ ⟨q, mem_singleton _, rfl⟩
    have hmaxvu := IsThetaPshPotential.max hv hu
    have hchartmax : chartFunction (fun x => max (u x) (v x)) e =
        (fun y => max (chartFunction v e y) (chartFunction u e y)) := by
      funext y
      exact max_comm _ _
    have hmemvu : MultiplierIntegrableAt
        (fun y => max (chartFunction v e y) (chartFunction u e y)) c f z volume := by
      rw [hchartmax] at hmem
      exact hmem
    exact multiplierIntegrableAt_of_max_chart (increasingStrongOpenness_ofRegularRoute n)
      W ρ (chartFunction v e) (chartFunction u e)
      hρ.1 hρ.2.2.1.continuousOn (hpsh hv) (hpsh hu)
      (fun y hy => hv.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy => hu.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy => hmaxvu.1.quasiPlurisubharmonic e y (hρ.2.1 hy))
      (fun y hy a ha g hg hgu => huv a ha e y (hρ.2.1 hy) g hg hgu)
      z hzW c hc f hf hmemvu
  · intro h
    exact (iOrderOnManifold_of_le hw.1.quasiPlurisubharmonic
      (fun x => le_max_left _ _)).trans h.1

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- All genuine local quasi-PSH inputs internally acquire the common
background needed by the actual one-way multiplier maximum theorem. -/
theorem iOrderOnManifold_iff_iEquivalent_max_globalQuasiPsh
    (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    IOrderOnManifold (n := n) u v ↔
      IEquivalentOnManifold (n := n) (fun x => max (u x) (v x)) v := by
  obtain ⟨_, _, huC, hvC, _, _⟩ := exists_pos_common_kahler_background omega hu hv
  exact iOrderOnManifold_iff_iEquivalent_max huC hvC

/-- The source P-maximum characterization holds on the full genuine
quasi-PSH domain without a prescribed smooth background. -/
theorem sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    SourcePOrder (n := n) u v ↔
      SourcePEquivalent (n := n) (fun x => max (u x) (v x)) v := by
  obtain ⟨_, _, huC, hvC, _, _⟩ := exists_pos_common_kahler_background omega hu hv
  exact sourcePOrder_iff_sourcePEquivalent_max omega huC hvC

end

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
