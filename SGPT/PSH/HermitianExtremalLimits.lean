import SGPT.PSH.HermitianExtremalL1Bound
import SGPT.PSH.QuasiPSHIdentity
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

/-!
# Decreasing limits with common smooth local corrections

The same smooth chart correction works before and after a decreasing limit.
The raw quasi-PSH limit may be identically negative infinity. On a connected
manifold, one actual nonpole rules out that collapse and supplies genuine
local nondegeneracy by the chartwise identity principle.

No exact or closed global background is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalLimits

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open HermitianExtremalL1Bound
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Family : (M → EReal) → Prop}

/-- Common smooth corrections make a pointwise decreasing infimum raw
quasi-plurisubharmonic. The identically bottom case is retained. -/
theorem manifoldQuasiPlurisubharmonic_iInf
    (hFamily : HasCommonLocalCorrections (n := n) Family)
    {w : ℕ → M → EReal} (hw : ∀ j, Family (w j))
    (hanti : ∀ x, Antitone fun j => w j x) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun x => ⨅ j, w j x) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hW, hWe, hρ, hcorr⟩ := hFamily e z hz
  have hpsh : PlurisubharmonicOn
      (fun y => ⨅ j, chartFunction (w j) e y + (ρ y : EReal)) W :=
    DiscPshOn.plurisubharmonicOn_iInf_of_antitone hW
      (fun j => (hcorr (w j) (hw j)).discPshOn)
      (fun y _ i j hij => add_le_add (hanti (e.val.symm y) hij) le_rfl)
  refine ⟨_, fun y => -ρ y, hpsh z hzW, ?_, ?_⟩
  · filter_upwards [hW.mem_nhds hzW] with y hy
    exact ((hρ.neg) y hy).contDiffAt (hW.mem_nhds hy)
  · apply Eventually.of_forall
    intro y
    change (⨅ j, w j (e.val.symm y)) =
      (⨅ j, w j (e.val.symm y) + (ρ y : EReal)) + ((-ρ y : ℝ) : EReal)
    rw [Pending.ThetaPshDecreasingLimit.iInf_add_coe,
      add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- On a connected manifold a genuine nonpole of the raw decreasing limit
propagates to nonpoles in every open neighborhood. -/
theorem isGlobalQuasiPshPotential_iInf_of_exists_ne_bot [ConnectedSpace M]
    (hFamily : HasCommonLocalCorrections (n := n) Family)
    {w : ℕ → M → EReal} (hw : ∀ j, Family (w j))
    (hanti : ∀ x, Antitone fun j => w j x)
    (hne : ∃ y, (⨅ j, w j y) ≠ ⊥) :
    IsGlobalQuasiPshPotential (n := n) (fun x => ⨅ j, w j x) := by
  have hraw := manifoldQuasiPlurisubharmonic_iInf hFamily hw hanti
  refine ⟨hraw, ?_⟩
  apply locallyNondegenerate_of_component_nonbot_of_local_coordinate_quasiPSH
  · intro x
    let e := complexChartAt (n := n) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    exact ⟨n, e.val, hx, hraw e _ (e.val.map_source hx)⟩
  · intro x
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, by rw [PreconnectedSpace.connectedComponent_eq_univ]; exact mem_univ y, hy⟩

end SGPT.PSH.HermitianExtremalLimits
