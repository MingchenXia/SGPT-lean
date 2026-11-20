import SGPT.PSH.AtlasModificationComponentDimension
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- ORIGINAL proper modification geometry gives a genuinely proper map of
SAME original components, via closed-source restriction and injective
codomain inclusion. No compactness or component properness premise is used. -/
theorem IsAtlasAnalyticModification.componentMap_isProperMap
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) (x : X) :
    IsProperMap (hf.1.componentMap x) := by
  have hproper : IsProperMap (fun p : A.componentOpen x => f p) :=
    hf.2.1.restrict isClosed_connectedComponent
  exact isProperMap_of_comp_of_inj
    ((hf.1.1.comp continuous_subtype_val).subtype_mk _)
    continuous_subtype_val hproper Subtype.val_injective

end SGPT.PSH.VariableComplexAtlas
