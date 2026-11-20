import SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit

set_option autoImplicit false

/-!
# An actual finite base partition with two simultaneous local potentials

Independent simultaneous local-potential adaptation supporting Xia SGPT
PDF0171. The existing extra-form slot-chart cover is reused, including
dimension zero. Compactness then produces a genuine finite subordinate
smooth partition. Each selected theta chart uses its actual common theta
potential in every slot, and retains the separate background potential
on the identical coordinate domain. Neither local potentials nor a
partition are new inputs, and the extra background need not be positive.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergySimultaneousPartition

open FirstPass GlobalSlotStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine simultaneous local potentials and the actual compact smooth partition theorem produce a finite base family carrying theta and an independent closed background on exactly the same domains. -/
theorem exists_finite_energy_chart_partition_with_background
    (θ β : ClosedRealOneOneForm n M) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ)
      (J : Fin m → SlotChart (fun _ : Fin n => θ) θ)
      (r : Fin m → ComplexModel n → ℝ),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
      (∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) ∧
      (∀ a, HasCompactSupport (χ a)) ∧ (∀ x, ∑ a, χ a x = 1) ∧
      (∀ a, IsSmoothLocalPotential β.val (J a).chart (J a).domain (r a)) ∧
      ∀ a i z, (J a).potential i z = (J a).kahler z := by
  classical
  let ι := {d : SlotChart (fun _ : Fin n => θ) θ × (ComplexModel n → ℝ) //
    IsSmoothLocalPotential β.val d.1.chart d.1.domain d.2}
  have hcover (x : M) : ∃ d : ι, x ∈ d.val.1.source := by
    obtain ⟨J, r, hx, hr⟩ :=
      GlobalWeightedDecreasingLimit.exists_mem_source_potential (fun _ : Fin n => θ) θ β x
    exact ⟨⟨(J, r), hr⟩, hx⟩
  obtain ⟨m, χ, idx, hsm, h0, hsupp, hc, h1⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity
      (n := n) (fun d : ι => d.val.1.source) hcover
  let J : Fin m → SlotChart (fun _ : Fin n => θ) θ := fun a => {
    chart := (idx a).val.1.chart
    domain := (idx a).val.1.domain
    domain_le_target := (idx a).val.1.domain_le_target
    potential := fun _ => (idx a).val.1.kahler
    localPotential := fun _ => (idx a).val.1.kahlerLocal
    kahler := (idx a).val.1.kahler
    kahlerLocal := (idx a).val.1.kahlerLocal }
  exact ⟨m, χ, J, fun a => (idx a).val.2, hsm, h0, hsupp, hc, h1,
    fun a => (idx a).property, fun _ _ _ => rfl⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergySimultaneousPartition
