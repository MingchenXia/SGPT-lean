import SGPT.PSH.HermitianExtremalGlobalPoleUnion
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.Pending.GlobalPotentials

/-!
# Genuine quasi-PSH gluing over connected components

The functions, their local nondegeneracy, and their poles are retained through
open-submanifold restriction. This is the elementary component assembly used
after proving the connected compact nonclosed-background theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComponents

open Set Filter TopologicalSpace
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass OpensRestriction OpensRestrictionMeasure

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Raw local quasi-PSH regularity on an open submanifold gives the same
actual germ in every ambient chart over that open set. -/
theorem quasiPlurisubharmonicAt_of_restrict (U : Opens M) {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) (fun y : U => u y))
    (e : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ e.val.target) (hzU : e.val.symm z ∈ U) :
    QuasiPlurisubharmonicAt (chartFunction u e) z := by
  let y : U := ⟨e.val.symm z, hzU⟩
  let d := complexChartAt (n := n) y
  let a := complexChartAt (n := n) (y : M)
  have hdy : d.val y ∈ d.val.target := d.val.map_source (mem_complexChartAt_source y)
  have hbase : QuasiPlurisubharmonicAt (chartFunction u a) (a.val (y : M)) := by
    have h := hu d (d.val y) hdy
    rw [complexChartAt_opens_apply] at h
    apply h.congr
    filter_upwards [d.val.open_target.mem_nhds hdy] with w hw
    exact congrArg u (val_complexChartAt_opens_symm y hw)
  have he := (quasiPlurisubharmonicAt_chart_iff u a e (y : M)
    (mem_complexChartAt_source (y : M)) (e.val.map_target hz)).mp hbase
  simpa only [y, e.val.right_inv hz] using he

/-- A chosen representative of a connected component. -/
def representative (c : ConnectedComponents M) : M :=
  Quotient.out (s := connectedComponentSetoid M) c

theorem coe_representative (c : ConnectedComponents M) :
    ((representative c : M) : ConnectedComponents M) = c :=
  Quotient.out_eq (s := connectedComponentSetoid M) c

theorem mem_component_iff (c : ConnectedComponents M) (x : M) :
    x ∈ connectedComponent (representative c) ↔ (x : ConnectedComponents M) = c := by
  rw [← ConnectedComponents.coe_eq_coe', coe_representative]

variable [LocallyConnectedSpace M]

/-- Actual componentwise nonpositive quasi-PSH pole potentials glue to one
nonpositive potential, including on a disconnected or empty manifold. -/
theorem glue_component_quasiPsh_poles (A : Set M)
    (hA : ∀ c : ConnectedComponents M,
      ∃ u : componentOpens (representative c) → EReal,
        IsGlobalQuasiPshPotential (n := n) u ∧ (∀ x, u x ≤ 0) ∧
          ∀ x : componentOpens (representative c), (x : M) ∈ A → u x = ⊥) :
    ∃ q : M → EReal, IsGlobalQuasiPshPotential (n := n) q ∧
      (∀ x, q x ≤ 0) ∧ ∀ x ∈ A, q x = ⊥ := by
  classical
  choose u hu hu0 hpole using hA
  have hx (x : M) : x ∈ componentOpens (representative (x : ConnectedComponents M)) :=
    (mem_component_iff _ x).mpr rfl
  let q : M → EReal := fun x => u (x : ConnectedComponents M) ⟨x, hx x⟩
  have heq (c : ConnectedComponents M) (x : componentOpens (representative c)) :
      q x = u c x := by
    rcases x with ⟨x, hxc⟩
    have hc := (mem_component_iff c x).mp hxc
    subst c
    rfl
  have hq : ManifoldQuasiPlurisubharmonic (n := n) q := by
    intro e z hz
    have hlocal : ManifoldQuasiPlurisubharmonic (n := n)
        (fun x : componentOpens (representative ((e.val.symm z : M) : ConnectedComponents M)) => q x) := by
      simpa only [heq] using (hu ((e.val.symm z : M) : ConnectedComponents M)).1
    exact quasiPlurisubharmonicAt_of_restrict _ hlocal e z hz (hx (e.val.symm z))
  refine ⟨q, ⟨hq, ?_⟩, fun x => hu0 _ _, fun x hxA => hpole _ ⟨x, hx x⟩ hxA⟩
  intro x V hV hxV
  obtain ⟨y, hyV, hy⟩ := (hu (x : ConnectedComponents M)).2 ⟨x, hx x⟩
    (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) hxV
  exact ⟨y, hyV, by rw [heq]; exact hy⟩

end SGPT.PSH.HermitianComponents
