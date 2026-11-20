import SGPT.Foundations.Analysis.Pending.SNCGlobalPrimeComponents
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison
import SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

set_option autoImplicit false

/-! # Whole point-centered prime readers preserve the literal original germ -/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PointCenteredPrimeGermReaders

open FirstPass FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves NormalCrossings

noncomputable section

/-- Continuity and actual point-centered geometry preserve the whole reader of an original germ. -/
theorem iInf_lelong_comp_eq_of_germ_eq {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : Y → X} (hπ : Continuous π) {x : X} {E : Set Y}
    (hcenter : ∀ y ∈ E, π y = x) {u v : X → EReal} (heq : u =ᶠ[𝓝 x] v) :
    (⨅ y ∈ E, lelongNumber (n := n) (fun z => u (π z)) y) =
      ⨅ y ∈ E, lelongNumber (n := n) (fun z => v (π z)) y := by
  apply iInf_congr
  intro y
  apply iInf_congr
  intro hy
  apply LelongNumberComparison.lelongNumber_congr
  have hmap : Tendsto π (𝓝 y) (𝓝 x) := by
    simpa only [hcenter y hy] using hπ.tendsto y
  exact hmap.eventually heq

/-- Literal point-supported SNC data internally supply whole primes and their original germ readers. -/
theorem exists_global_prime_germ_reader {m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X} (hπ : Continuous π) {x : X}
    (D : EffectiveDivisor (m + 1) Y) {E : List (Set Y)} (hE : IsSNCDivisor (m + 1) E)
    (hsupport : D.support = ⋃ H ∈ E, H) (hpoint : D.support ⊆ π ⁻¹' {x})
    (i : Fin E.length) {y : Y} (hy : y ∈ E.get i) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m ∧ V.carrier = connectedComponentIn (E.get i) y ∧ y ∈ V.carrier ∧
      V.carrier ⊆ E.get i ∧ IsConnected V.carrier ∧
      (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
      (∀ z ∈ V.carrier, ∃ W : Set Y, IsOpen W ∧ z ∈ W ∧
        E.get i ∩ W = V.carrier ∩ W) ∧
      (∀ z ∈ V.carrier, π z = x) ∧
      ∀ F G : X → ℂ, F =ᶠ[𝓝 x] G →
        (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
          (fun w => ENNReal.log (ENNReal.ofReal ‖F (π w)‖)) z) =
        ⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
          (fun w => ENNReal.log (ENNReal.ofReal ‖G (π w)‖)) z := by
  obtain ⟨V, hdim, hcomp, hyV, hVH, hconn, hreg, hlocal⟩ :=
    SNCGlobalPrimeComponents.exists_global_prime_component (m := m) (Y := Y) hE i hy
  have hcenter : ∀ z ∈ V.carrier, π z = x := by
    intro z hz
    have hzD : z ∈ D.support := by
      rw [hsupport]
      exact mem_iUnion.2 ⟨E.get i, mem_iUnion.2 ⟨List.get_mem _ _, hVH hz⟩⟩
    exact Set.mem_singleton_iff.mp (hpoint hzD)
  refine ⟨V, hdim, hcomp, hyV, hVH, hconn, hreg, hlocal, hcenter, ?_⟩
  intro F G hFG
  have hlog : (fun t => ENNReal.log (ENNReal.ofReal ‖F t‖)) =ᶠ[𝓝 x]
      (fun t => ENNReal.log (ENNReal.ofReal ‖G t‖)) :=
    hFG.mono fun _ hz => congrArg (fun t : ℂ => ENNReal.log (ENNReal.ofReal ‖t‖)) hz
  exact iInf_lelong_comp_eq_of_germ_eq (n := m + 1) (X := X) (Y := Y)
    (x := x) (E := V.carrier)
    (u := fun t => ENNReal.log (ENNReal.ofReal ‖F t‖))
    (v := fun t => ENNReal.log (ENNReal.ofReal ‖G t‖)) hπ hcenter hlog

end
end SGPT.Foundations.Analysis.Pending.PointCenteredPrimeGermReaders
