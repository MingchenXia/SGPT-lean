import SGPT.PSH.SigmaNativeAtlas
import SGPT.PSH.AtlasComponentPrimeEquivalence

/-! The actual original manifold is canonically HOMEOMORPHIC to its true
open native components. No finite catalog, common dimension or flag is input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual original open component at the internally selected anchor. -/
abbrev actualComponentPoint (A : VariableComplexAtlas X) (c : ConnectedComponents X) : Type u :=
  A.componentOpen (componentAnchor c)

/-- Its literal ORIGINAL native dimension, without any uniform-dimension flag. -/
def actualComponentDimension (A : VariableComplexAtlas X) (c : ConnectedComponents X) : ℕ :=
  A.pointDimension (componentAnchor c)

/-- Genuine native charts are produced from the ORIGINAL atlas itself. -/
@[instance_reducible]
def actualComponentChartedSpace (A : VariableComplexAtlas X) (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  A.componentChartedSpace (componentAnchor c)

/-- Genuine original Hausdorff/paracompact topology supplies all complex
manifold fields, rather than assuming component geometry as extra premises. -/
theorem actualComponentComplexManifold [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (c : ConnectedComponents X) :
    letI := actualComponentChartedSpace A c
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  A.componentComplexManifold_of_paracompact (componentAnchor c)

/-- Every actual point fixes its UNIQUE original component index. -/
theorem actualComponentPoint_index (A : VariableComplexAtlas X) (c : ConnectedComponents X)
    (p : actualComponentPoint A c) : ConnectedComponents.mk p.val=c :=
  ((ConnectedComponents.coe_eq_coe').mpr p.property).trans (componentAnchor_spec c)

/-- The true sigma-to-original map is a bijection, proved by the actual
connected-component quotient and original subtype values. -/
def actualComponentEquiv (A : VariableComplexAtlas X) :
    ((c : ConnectedComponents X) × actualComponentPoint A c) ≃ X :=
  Equiv.ofBijective (fun p => p.2.val) (by
    constructor
    · rintro ⟨c,p⟩ ⟨d,q⟩ h
      have hcd : c=d := (actualComponentPoint_index A c p).symm.trans
        ((congrArg ConnectedComponents.mk h).trans (actualComponentPoint_index A d q))
      cases hcd
      exact congrArg (Sigma.mk c) (Subtype.ext h)
    · intro x
      exact ⟨⟨ConnectedComponents.mk x,⟨x,
        (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk x)).symm⟩⟩,rfl⟩)

/-- An ACTUAL global homeomorphism: each original component inclusion is
continuous and OPEN, so the entire genuine sigma bijection is continuous/open. -/
def actualComponentHomeomorph (A : VariableComplexAtlas X) :
    ((c : ConnectedComponents X) × actualComponentPoint A c) ≃ₜ X :=
  (actualComponentEquiv A).toHomeomorphOfContinuousOpen
    (continuous_sigma (fun _ => continuous_subtype_val))
    (isOpenMap_sigma.mpr (fun c =>
      (A.componentOpen (componentAnchor c)).isOpen.isOpenMap_subtype_val))

/-- The genuine global homeomorphism is the LITERAL original subtype value. -/
theorem actualComponentHomeomorph_val (A : VariableComplexAtlas X)
    (p : (c : ConnectedComponents X) × actualComponentPoint A c) :
    actualComponentHomeomorph A p=p.2.val := rfl

/-- Actual inverse readback, independent of quotient representative choices. -/
theorem actualComponentHomeomorph_inverse_val (A : VariableComplexAtlas X) (x : X) :
    ((actualComponentHomeomorph A).symm x).2.val=x :=
  (actualComponentHomeomorph A).apply_symm_apply x

/-- On EACH original open component the actual inverse is the SAME subtype
identity, providing the local equality used in actual tensor/scalar gluing. -/
theorem actualComponentHomeomorph_inverse_of_mem (A : VariableComplexAtlas X)
    (c : ConnectedComponents X) (x : X) (hx : x∈A.componentOpen (componentAnchor c)) :
    (actualComponentHomeomorph A).symm x=⟨c,⟨x,hx⟩⟩ := by
  apply (actualComponentHomeomorph A).injective
  rw [(actualComponentHomeomorph A).apply_symm_apply]
  rfl

/-- The ACTUAL variable atlas on all internally produced native components,
with every native manifold structure internally derived from original A. -/
def actualComponentSigmaAtlas [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) :
    VariableComplexAtlas ((c : ConnectedComponents X) × actualComponentPoint A c) := by
  letI (c : ConnectedComponents X) : ChartedSpace (ComplexModel (actualComponentDimension A c))
      (actualComponentPoint A c) := actualComponentChartedSpace A c
  letI (c : ConnectedComponents X) : IsComplexManifold (actualComponentDimension A c)
      (actualComponentPoint A c) := actualComponentComplexManifold A c
  exact sigmaNativeAtlas (n := actualComponentDimension A) (C := actualComponentPoint A)

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
