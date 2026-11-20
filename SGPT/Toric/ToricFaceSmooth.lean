import SGPT.Toric.ToricFaceEdgeEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine integral coordinates of the actual annihilator, indexed by its
actual finite rank for the ordinary source toric model. -/
def toricFaceCharacterCoordinates (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) ≃ₗ[ℤ]
      (Fin (toricFaceDimension J) → ℤ) :=
  (toricStratumCharacterCoordinates v J).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : {j : Fin n // j ∉ J} => ℤ)
      (Fintype.equivFin {j : Fin n // j ∉ J}))

/-- The selected original ALL-edge basis, in the ACTUAL annihilator module. -/
def toricFaceAllEdgeBasis
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices γ)
    (hw : integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (w.val + b E) ∈ E.val) :
    Module.Basis {j : Fin n // (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆
      toricNativeVertexFace (hs := hs) v J} ℤ
      (toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :=
  (Pi.basisFun ℤ _).map (toricFaceAllEdgeCharacterCoordinates v J w hw b hmem).symm

/-- Each actual restricted basis vector is the SAME original primitive edge
vector, with its genuine annihilator membership. -/
theorem toricFaceAllEdgeBasis_apply
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices γ)
    (hw : integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (w.val + b E) ∈ E.val)
    (j : {j : Fin n // (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆
      toricNativeVertexFace (hs := hs) v J}) :
    toricFaceAllEdgeBasis v J w hw b hmem j =
      ⟨latticeEdgeCoordinateBasis γ w.val b j.val,
        toricNativeFace_edgeBasis_mem_annihilator v J w hw b hmem j.val j.property⟩ := by
  apply (toricFaceAllEdgeCharacterCoordinates v J w hw b hmem).injective
  change (toricFaceAllEdgeCharacterCoordinates v J w hw b hmem)
      ((toricFaceAllEdgeCharacterCoordinates v J w hw b hmem).symm (Pi.basisFun ℤ _ j)) = _
  rw [LinearEquiv.apply_symm_apply]
  funext i
  change (Pi.basisFun ℤ _) j i =
    (latticeEdgeCoordinateBasis γ w.val b).repr (latticeEdgeCoordinateBasis γ w.val b j.val) i.val
  simp only [Pi.basisFun_apply, Pi.single_apply, Module.Basis.repr_self_apply]
  by_cases hij : j = i
  · subst i
    simp
  · have hval : j.val ≠ i.val := fun heq => hij (Subtype.ext heq)
    simp only [if_neg (Ne.symm hij), if_neg hval]

/-- The genuine original selected edge index enumerates ALL actual target
edges under the actual affine face map. -/
def toricFaceAllEdgeIndexEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val.val) ℤ (Fin n → ℤ)) :
    {j : Fin n // (latticeEdgeBasisIndexEquiv γ w.val.val b j).val ⊆
      toricNativeVertexFace (hs := hs) v J} ≃
      latticePolytopeEdgesAt (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w).val :=
  ((latticeEdgeBasisIndexEquiv γ w.val.val b).subtypeEquiv (fun _ => Iff.rfl)).trans
    (toricFaceProjectedEdgeEquiv (hs := hs) v J w)

/-- Source integral projection of every actual face neighbor is the actual
target vertex plus the same character vector. -/
theorem toricFaceIntegralProjection_add_character
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (w : Fin n → ℤ)
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    toricFaceIntegralProjection (hs := hs) v J (w + m.val) =
      toricFaceIntegralProjection (hs := hs) v J w + toricFaceCharacterCoordinates v J m := by
  funext j
  change (originalPolytopeNativeBasis γ hs v).repr (w + m.val - v.val) _ =
    (originalPolytopeNativeBasis γ hs v).repr (w - v.val) _ +
      (originalPolytopeNativeBasis γ hs v).repr m.val _
  rw [show w + m.val - v.val = (w - v.val) + m.val by abel, map_add, Finsupp.add_apply]

/-- The constructed original integer face family satisfies the book's
ORIGINAL ALL-edge smoothness predicate. Every target vertex and EVERY target
edge is accounted for by the proved actual vertex/edge dictionaries; the
primitive integral neighbors come from the original ALL-edge smoothness.
No target smoothness, lattice rank, face model, or edge basis is assumed. -/
theorem latticePolytopeEdgeSmooth_toricFaceProjectedFamily
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    latticePolytopeEdgeSmooth (toricFaceProjectedFamily (hs := hs) v J) := by
  intro q
  let w := (toricFaceVertexEquiv (hs := hs) v J).symm q
  obtain ⟨b, hmem⟩ := hs w.val
  let C := toricFaceCharacterCoordinates (hs := hs) v J
  let B := toricFaceAllEdgeBasis v J w.val w.property b hmem
  let e := toricFaceAllEdgeIndexEquiv v J w b
  have hsource : latticePolytopeEdgeSmoothAt (toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w).val := by
    refine ⟨(B.map C).reindex e, ?_⟩
    intro E
    obtain ⟨j, rfl⟩ := e.surjective E
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
    change integerCast ((toricFaceVertexEquiv (hs := hs) v J w).val +
      C (toricFaceAllEdgeBasis v J w.val w.property b hmem j)) ∈ (e j).val
    rw [toricFaceAllEdgeBasis_apply]
    let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
      ⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
        toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hmem j.val j.property⟩
    have hpoint : toricFaceProjection (hs := hs) v J
        (integerCast (w.val.val + m.val)) ∈ (e j).val := by
      change toricFaceProjection (hs := hs) v J (integerCast (w.val.val + m.val)) ∈
        toricFaceProjection (hs := hs) v J '' (latticeEdgeBasisIndexEquiv γ w.val.val b j.val).val
      refine ⟨integerCast (w.val.val + m.val), ?_, rfl⟩
      change integerCast (w.val.val + latticeEdgeCoordinateBasis γ w.val.val b j.val) ∈ _
      rw [latticeEdgeCoordinateBasis_apply]
      exact hmem _
    rw [toricFaceProjection_integerCast, toricFaceIntegralProjection_add_character] at hpoint
    exact hpoint
  have hwq : (toricFaceVertexEquiv (hs := hs) v J w).val = q.val :=
    congrArg Subtype.val ((toricFaceVertexEquiv (hs := hs) v J).apply_symm_apply q)
  rwa [hwq] at hsource

end SGPT.Toric
