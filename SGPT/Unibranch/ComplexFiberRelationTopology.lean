import SGPT.Unibranch.ComplexLocalFiberRelation

/-! Genuine topology of the actual local holomorphic relation carrier.
Blueprint: complex-fiber-relation-topology.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.LocalFiberRelation

/-- The actual coordinate join is continuous complex linear. -/
def joinMap (m : ℕ) : (ComplexModel 1 × ComplexModel m) →L[ℂ] ComplexModel (m+1) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => join p.1 p.2
    map_add' := by
      intro x y
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    map_smul' := by
      intro a x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl }

/-- SAME original vector reconstructed, including the zero-dimensional tail. -/
theorem join_head_tail {m : ℕ} (z : ComplexModel (m+1)) : join (head m z) (tail m z) = z := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [join,head,SourceReducedComplexSpace.discCoordinate]
  · rfl

variable {m n : ℕ} (U : Opens (ComplexModel 1)) (V : Opens (ComplexModel m))
    (D : Set V) (F : ComplexModel 1 → ComplexModel n) (G : ComplexModel m → ComplexModel n)

/-- The literal matching-pair subspace of the SAME original carrier. -/
def pairCarrier : Set (U × D) := {p | G p.2.val.val = F p.1.val}

/-- Literal original head/tail coordinates in the matching-pair subspace. -/
def pairCoordinates (c : carrier U V D F G) : pairCarrier U V D F G :=
  ⟨(⟨head m c.val.val,c.val.property.1⟩,
    ⟨⟨tail m c.val.val,c.val.property.2⟩,c.property.1⟩),c.property.2⟩

/-- Every actual matching pair gives its explicit point of the SAME carrier. -/
def pairInverse (p : pairCarrier U V D F G) : carrier U V D F G := by
  have hA : join p.val.1.val p.val.2.val.val ∈ ambient U V := by
    constructor
    · change head m (join p.val.1.val p.val.2.val.val) ∈ U
      rw [head_join]
      exact p.val.1.property
    · change tail m (join p.val.1.val p.val.2.val.val) ∈ V
      rw [tail_join]
      exact p.val.2.val.property
  refine ⟨⟨join p.val.1.val p.val.2.val.val,hA⟩,?_,?_⟩
  · have heq : (⟨tail m (join p.val.1.val p.val.2.val.val),hA.2⟩ : V) = p.val.2.val :=
      Subtype.ext (tail_join _ _)
    rw [heq]
    exact p.val.2.property
  · simpa only [tail_join,head_join,pairCarrier,mem_ofPred_eq] using p.property

/-- Genuine homeomorphism, not a supplied local product-topology certificate. -/
def carrierHomeomorph : carrier U V D F G ≃ₜ pairCarrier U V D F G where
  toFun := pairCoordinates U V D F G
  invFun := pairInverse U V D F G
  left_inv := by
    intro c
    apply Subtype.ext
    apply Subtype.ext
    exact join_head_tail c.val.val
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact head_join _ _
    · apply Subtype.ext
      apply Subtype.ext
      exact tail_join _ _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (head m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (tail m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun p : pairCarrier U V D F G => join p.val.1.val p.val.2.val.val)
    exact (joinMap m).continuous.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_subtype_val.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))))

end SGPT.Unibranch.LocalFiberRelation
