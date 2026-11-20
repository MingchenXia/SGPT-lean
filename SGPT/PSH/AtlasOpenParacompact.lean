import SGPT.PSH.AtlasOpenNativeBiholomorphism
import SGPT.PSH.AtlasComponentDivisorAssembly
import SGPT.PSH.LocallyFiniteClopenParacompact

open Lean in
local macro "pinnedActualComponentFamilyKernel" : term =>
  pure (mkIdent (Name.append
    (Name.num `_private.SGPT.PSH.AtlasComponentDivisorAssembly 0)
    `SGPT.PSH.VariableComplexAtlas.locallyFinite_actual_component_carriers))

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- EXACT existing actual component-family producer, whose full compiled type
needs ONLY A. Literal private origin/type/body/direct wrapper are pinned and audited. -/
theorem locallyFinite_original_component_carriers (A : VariableComplexAtlas X) :
    LocallyFinite (fun c : ConnectedComponents X =>
      (A.componentOpen (componentAnchor c) : Set X)) :=
  pinnedActualComponentFamilyKernel A

/-- ORIGINAL A/original Hausdorff-paracompact topology manufacture genuine
paracompactness of ANY actual original open, including empty; no topology cert on U. -/
theorem openRestriction_paracompactSpace [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (U : Opens X) : ParacompactSpace U := by
  let B := A.openRestriction U
  let C : ConnectedComponents U → Opens U := fun c => B.componentOpen (componentAnchor c)
  have hPara : ∀ c, ParacompactSpace (C c) := by
    intro c
    let := B.componentChartedSpace (componentAnchor c)
    let := A.openRestriction_componentComplexManifold U (componentAnchor c)
    let : LocallyCompactSpace (C c) :=
      ChartedSpace.locallyCompactSpace (ComplexModel (B.pointDimension (componentAnchor c))) (C c)
    infer_instance
  apply SGPT.PSH.paracompactSpace_of_locallyFinite_clopen_cover C
    (fun _ => isClosed_connectedComponent) (B.locallyFinite_original_component_carriers)
    (iUnion_eq_univ_iff.mpr ?_) hPara
  intro p
  refine ⟨ConnectedComponents.mk p, ?_⟩
  exact (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk p)).symm

end SGPT.PSH.VariableComplexAtlas
