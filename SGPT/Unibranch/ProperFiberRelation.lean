import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.Complex

/-! Genuine properness and closure lifting for the LITERAL matching-pair
subspace. Blueprint: proper-fiber-relation.tex. -/
set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open scoped Topology
namespace SGPT.Unibranch.ProperFiberRelation
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The LITERAL matching pairs and their actual subspace topology. -/
def relation (p : Y → X) (f : Z → X) : Set (Z × Y) := {q | f q.1 = p q.2}

/-- Properness of the actual first projection is produced from actual
properness and a closed diagonal; no base-change certificate is an input. -/
theorem isProperMap_projection [T2Space X] {p : Y → X} (hp : IsProperMap p)
    {f : Z → X} (hf : Continuous f) :
    IsProperMap (fun q : relation p f => q.val.1) := by
  have hrel : IsClosed (relation p f) := isClosed_eq (hf.comp continuous_fst)
    (hp.continuous.comp continuous_snd)
  have hi := hrel.isClosedEmbedding_subtypeVal.isProperMap
  have hprod := (isProperMap_id (X := Z)).prodMap hp
  have hcomp : IsProperMap ((fun z : Z => (z,f z)) ∘ (fun q : relation p f => q.val.1)) := by
    have hproper := hprod.comp hi
    have heq : (Prod.map (id : Z → Z) p ∘ (Subtype.val : relation p f → Z × Y)) =
        (fun z : Z => (z,f z)) ∘ (fun q : relation p f => q.val.1) := by
      funext q
      exact Prod.ext rfl q.property.symm
    rwa [heq] at hproper
  exact isProperMap_of_comp_of_inj (continuous_fst.comp continuous_subtype_val)
    (continuous_id.prodMk hf) hcomp (fun _ _ h => congrArg Prod.fst h)

omit [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] in
/-- Actual surjectivity of the SAME first projection. -/
theorem projection_surjective {p : Y → X} (hp : Surjective p) (f : Z → X) :
    Surjective (fun q : relation p f => q.val.1) := by
  intro z
  obtain ⟨y,hy⟩ := hp (f z)
  exact ⟨⟨(z,y),hy.symm⟩,rfl⟩

/-- Proper closed-image geometry produces an ACTUAL closure lift in the
literal matching-pair subspace; no analytic curve/lift certificate occurs. -/
theorem exists_closure_lift [T2Space X] {p : Y → X} (hp : IsProperMap p)
    (hps : Surjective p) {f : Z → X} (hf : Continuous f)
    {S : Set Z} {z : Z} (hz : z ∈ closure S) :
    ∃ q : relation p f,q.val.1 = z ∧ q ∈ closure {q : relation p f | q.val.1 ∈ S} := by
  let a : relation p f → Z := fun q => q.val.1
  have ha := isProperMap_projection hp hf
  have has : Surjective a := projection_surjective hps f
  have hzI : z ∈ closure (a '' (a ⁻¹' S)) := by
    rw [has.image_preimage]
    exact hz
  obtain ⟨q,hq,hqz⟩ := ha.isClosedMap.closure_image_subset (a ⁻¹' S) hzI
  exact ⟨q,hqz,hq⟩

end SGPT.Unibranch.ProperFiberRelation
