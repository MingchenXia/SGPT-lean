import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original theta-PSH potential produces a genuine local PSH reader.
Its native point reader is literally the original ambient reader at every
point of the actual local domain; no reader covariance is supplied as input. -/
theorem exists_psh_local_theta_reader {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (e : ComplexChart n M) (x : M)
    (hx : x ∈ e.val.source) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
      e.val x ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) W ∧
      ∀ y ∈ W, lelongNumber (n := n)
        (fun z => chartFunction u e z + (ρ z : EReal)) y =
          lelongNumber (n := n) u (e.val.symm y) := by
  obtain ⟨W, ρ, hxW, hρ, hp⟩ := hu.1 e (e.val x) (e.val.map_source hx)
  refine ⟨W, ρ, hxW, hρ, hp, ?_⟩
  intro y hy
  have hyT : y ∈ e.val.target := hρ.2.1 hy
  calc
    _ = lelongNumber (n := n) (chartFunction u e) y :=
      LelongChartReaderInvariance.lelongNumber_add_continuous_eq
        ((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).continuousAt
    _ = _ := by
      simpa only [e.val.right_inv hyT] using
        LelongChartReaderInvariance.lelongNumber_chartFunction_eq e (e.val.map_target hyT)

/-- An actual local holomorphic flattening transports the produced original
PSH reader and its literal native Lelong values to the original flattened
domain.  Neither a local PSH nor a covariance certificate is assumed. -/
theorem exists_flattened_theta_psh_reader {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (e : ComplexChart n M) (x : M)
    (hx : x ∈ e.val.source)
    (Φ : LocalHolomorphicEquivAt (n := n) (e.val x)) :
    ∃ (D : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
      IsOpen D ∧ Φ.toFun (e.val x) ∈ D ∧ D ⊆ Φ.target ∧
      (∀ z ∈ D, ContDiffAt ℝ ∞ ρ (Φ.invFun z)) ∧
      PlurisubharmonicOn
        (fun z => chartFunction u e (Φ.invFun z) + (ρ (Φ.invFun z) : EReal)) D ∧
      ∀ z ∈ D, lelongNumber (n := n)
        (fun y => chartFunction u e (Φ.invFun y) + (ρ (Φ.invFun y) : EReal)) z =
          lelongNumber (n := n) u (e.val.symm (Φ.invFun z)) := by
  obtain ⟨W, ρ, hxW, hρ, hp, hν⟩ := exists_psh_local_theta_reader hu e x hx
  let D : Set (ComplexModel n) := Φ.target ∩ Φ.invFun ⁻¹' W
  have hD : IsOpen D := Φ.toOpenPartialHomeomorph.symm.isOpen_inter_preimage hρ.1
  have hxD : Φ.toFun (e.val x) ∈ D := by
    refine ⟨Φ.mapsTo_toFun Φ.center_mem_source, ?_⟩
    change Φ.invFun (Φ.toFun (e.val x)) ∈ W
    rwa [Φ.left_inv _ Φ.center_mem_source]
  have hDT : D ⊆ Φ.target := inter_subset_left
  have hpD : PlurisubharmonicOn
      (fun z => chartFunction u e (Φ.invFun z) + (ρ (Φ.invFun z) : EReal)) D :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD
      (Φ.invFun_holomorphic.mono hDT) (fun _ hz => hz.2) hp
  refine ⟨D, ρ, hD, hxD, hDT, ?_, hpD, ?_⟩
  · intro z hz
    exact (hρ.2.2.1 _ hz.2).contDiffAt (hρ.1.mem_nhds hz.2)
  intro z hz
  calc
    _ = lelongNumber (n := n)
        (fun y => chartFunction u e y + (ρ y : EReal)) (Φ.invFun z) := by
      simpa only [Φ.right_inv z hz.1] using
        LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ
          (Φ.mapsTo_invFun hz.1)
          (u := fun y => chartFunction u e y + (ρ y : EReal))
    _ = _ := hν _ hz.2

end SGPT.Okounkov
