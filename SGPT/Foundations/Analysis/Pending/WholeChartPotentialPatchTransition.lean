import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic

set_option autoImplicit false

/-!
# Genuine transitions between every original chart and a potential patch

The two opens and maps are built from the actual chart and patch source.
No whole-chart local potential, transition certificate or current is supplied.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.WholeChartPotentialPatchTransition

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.HolomorphicMaps BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- The portion of the whole chart target lying over the actual patch source. -/
def chartOverlapDomain (e : ComplexChart n M) (P : Patch θ u) :
    Opens (ComplexModel n) :=
  ⟨e.val.target ∩ e.val.symm ⁻¹' P.source,
    e.val.symm.isOpen_inter_preimage P.source.isOpen⟩

/-- The portion of the actual patch domain lying over the original chart source. -/
def patchOverlapDomain (e : ComplexChart n M) (P : Patch θ u) :
    Opens (ComplexModel n) :=
  ⟨(P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' e.val.source,
    (P.chart.val.continuousOn_symm.mono P.domain_le_target).isOpen_inter_preimage
      P.domain.isOpen e.val.open_source⟩

/-- The genuine transition from original chart coordinates to patch coordinates. -/
def chartToPatch (e : ComplexChart n M) (P : Patch θ u) :
    ComplexModel n → ComplexModel n := fun z ↦ P.chart.val (e.val.symm z)

/-- The reverse transition, used only on its actual overlap domain. -/
def patchToChart (e : ComplexChart n M) (P : Patch θ u) :
    ComplexModel n → ComplexModel n := fun w ↦ e.val (P.chart.val.symm w)

/-- All domain, mapping, holomorphicity and inverse assertions are produced. -/
theorem isBiholomorphicPair (e : ComplexChart n M) (P : Patch θ u) :
    (chartOverlapDomain e P : Set (ComplexModel n)) ⊆ e.val.target ∧
    patchOverlapDomain e P ≤ P.domain ∧
    IsBiholomorphicPair (chartOverlapDomain e P) (patchOverlapDomain e P)
      (chartToPatch e P) (patchToChart e P) := by
  refine ⟨fun _ hz ↦ hz.1, fun _ hw ↦ hw.1, ?_⟩
  refine {
    holo := fun z hz ↦ (chartTransition_contDiffAt e P.chart
      ⟨hz.1, P.source_subset hz.2⟩).contDiffWithinAt
    holo_inv := fun w hw ↦ (chartTransition_contDiffAt P.chart e
      ⟨P.domain_le_target hw.1, hw.2⟩).contDiffWithinAt
    mapsTo := ?_
    mapsTo_inv := ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro z hz
    refine ⟨P.map_source hz.2, ?_⟩
    change P.chart.val.symm (P.chart.val (e.val.symm z)) ∈ e.val.source
    rw [P.chart.val.left_inv (P.source_subset hz.2)]
    exact e.val.map_target hz.1
  · intro w hw
    refine ⟨e.val.map_source hw.2, ?_⟩
    change e.val.symm (e.val (P.chart.val.symm w)) ∈ P.source
    rw [e.val.left_inv hw.2]
    exact P.map_target hw.1
  · intro z hz
    change e.val (P.chart.val.symm (P.chart.val (e.val.symm z))) = z
    rw [P.chart.val.left_inv (P.source_subset hz.2), e.val.right_inv hz.1]
  · intro w hw
    change P.chart.val (e.val.symm (e.val (P.chart.val.symm w))) = w
    rw [e.val.left_inv hw.2, P.chart.val.right_inv (P.domain_le_target hw.1)]

end SGPT.Foundations.Analysis.Pending.WholeChartPotentialPatchTransition
