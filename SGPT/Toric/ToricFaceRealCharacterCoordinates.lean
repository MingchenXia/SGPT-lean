import SGPT.Toric.ToricFacePrimeDivisors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine continuous coordinates of the LITERAL real annihilator in the
SAME finite basis used by the actual quotient toric model. -/
def toricFaceRealCharacterCoordinates (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricStratumRealSpace (polytopeToricRay γ hs v '' J) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (toricFaceDimension J)) :=
  (toricStratumRealCoordinates (hs := hs) v J).trans
    (((LinearEquiv.piCongrLeft' ℝ (fun _ : {j : Fin n // j ∉ J} => ℝ)
      (Fintype.equivFin {j : Fin n // j ∉ J})).toContinuousLinearEquiv).trans
        (EuclideanSpace.equiv (Fin (toricFaceDimension J)) ℝ).symm)

/-- This actual real coordinate map preserves EVERY original lattice
character, with the literal integral coordinates Cσ. -/
theorem toricFaceRealCharacterCoordinates_latticeVector
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    toricFaceRealCharacterCoordinates (hs := hs) v J
      ⟨latticeVector m.val, latticeVector_mem_toricStratumRealSpace m.property⟩ =
      latticeVector (toricFaceCharacterCoordinates (hs := hs) v J m) := by
  ext j
  exact toricStratumRealCoordinates_latticeVector v J m
    ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j)

/-- The ACTUAL real inverse preserves every original target integral
character, with the SAME actual inverse integral coordinate map. -/
theorem toricFaceRealCharacterCoordinates_inverse_latticeVector
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ) :
    (toricFaceRealCharacterCoordinates (hs := hs) v J).symm (latticeVector q) =
      ⟨latticeVector ((toricFaceCharacterCoordinates (hs := hs) v J).symm q).val,
        latticeVector_mem_toricStratumRealSpace
          ((toricFaceCharacterCoordinates (hs := hs) v J).symm q).property⟩ := by
  apply (toricFaceRealCharacterCoordinates (hs := hs) v J).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, toricFaceRealCharacterCoordinates_latticeVector,
    LinearEquiv.apply_symm_apply]

/-- Literal dual pairing for EVERY real point of Mσ_R and EVERY genuine
quotient ray. Equality on a real basis whose inverse vectors are genuine
integral annihilator characters proves the result; no pairing/span certificate
or desired body equality is an assumption. -/
theorem toricFaceRealCharacterCoordinates_ray_pairing
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (x : toricStratumRealSpace (polytopeToricRay γ hs v '' J)) :
    latticeFunctional ρ.val (toricFaceRealCharacterCoordinates (hs := hs) v J x) =
      latticeFunctional (toricFaceRayLift (hs := hs) v J ρ).val x.val := by
  let C := toricFaceRealCharacterCoordinates (hs := hs) v J
  let CZ := toricFaceCharacterCoordinates (hs := hs) v J
  let B := (Pi.basisFun ℝ (Fin (toricFaceDimension J))).map
    (EuclideanSpace.equiv (Fin (toricFaceDimension J)) ℝ).symm.toLinearEquiv
  let L : EuclideanSpace ℝ (Fin (toricFaceDimension J)) →ₗ[ℝ] ℝ :=
    (latticeFunctional (toricFaceRayLift (hs := hs) v J ρ).val).comp
      ((toricStratumRealSpace (polytopeToricRay γ hs v '' J)).subtype.comp C.symm.toLinearMap)
  have hL : L = latticeFunctional ρ.val := by
    apply B.ext
    intro j
    have hB : B j = latticeVector (Pi.single j (1 : ℤ)) := by
      ext k
      simp [B, Module.Basis.map_apply, Pi.basisFun_apply, latticeVector, integerCast, Pi.single_apply]
    change latticeFunctional (toricFaceRayLift (hs := hs) v J ρ).val (C.symm (B j)).val =
      latticeFunctional ρ.val (B j)
    rw [hB, toricFaceRealCharacterCoordinates_inverse_latticeVector]
    rw [latticeFunctional_latticeVector, latticeFunctional_latticeVector]
    let m := CZ.symm (Pi.single j (1 : ℤ))
    have h := toricFaceRayLift_pairing v J ρ m
    change intPairing (CZ (CZ.symm (Pi.single j 1))) ρ.val =
      intPairing m.val (toricFaceRayLift v J ρ).val at h
    rw [LinearEquiv.apply_symm_apply] at h
    rw [intPairing_comm, intPairing_comm ρ.val]
    exact congrArg (fun z : ℤ => (z : ℝ)) h.symm
  have h := LinearMap.congr_fun hL (C x)
  change latticeFunctional (toricFaceRayLift v J ρ).val (C.symm (C x)).val = _ at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

end SGPT.Toric
