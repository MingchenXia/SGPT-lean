import SGPT.Toric.ToricStratumLattice
import SGPT.Toric.ToricFlagVolume
import SGPT.Toric.Toric4Delzant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal real source character space M(σ)_R inside M_R. -/
def toricStratumRealSpace (R : Set (PolytopeToricRays γ hs)) : Submodule ℝ E where
  carrier := {x | ∀ ρ ∈ R, latticeFunctional ρ.val x = 0}
  zero_mem' := by intro ρ _; simp
  add_mem' := by intro x y hx hy ρ hρ; rw [map_add, hx ρ hρ, hy ρ hρ, zero_add]
  smul_mem' := by intro c x hx ρ hρ; rw [map_smul, hx ρ hρ, smul_zero]

/-- The same original integral inclusion lands in the actual real
annihilator, without assuming a realification certificate. -/
theorem latticeVector_mem_toricStratumRealSpace {R : Set (PolytopeToricRays γ hs)}
    {m : Fin n → ℤ} (hm : m ∈ toricStratumCharacterLattice R) :
    latticeVector m ∈ toricStratumRealSpace R := by
  intro ρ hρ
  rw [latticeFunctional_latticeVector, intPairing_comm, hm ρ hρ, Int.cast_zero]

/-- Genuine continuous real coordinates on the actual annihilator space,
constructed from the original inverse edge-basis transpose and its inverse. -/
def toricStratumRealCoordinates (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricStratumRealSpace (polytopeToricRay γ hs v '' J) ≃L[ℝ]
      ({j : Fin n // j ∉ J} → ℝ) := by
  classical
  let A := latticeBasisLogInverseTransposeEquiv (originalPolytopeNativeBasis γ hs v)
  let extend : ({j : Fin n // j ∉ J} → ℝ) → E := fun f =>
    (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => if hj : j ∈ J then 0 else f ⟨j, hj⟩)
  have hmem (f : {j : Fin n // j ∉ J} → ℝ) :
      A.symm (extend f) ∈ toricStratumRealSpace (polytopeToricRay γ hs v '' J) := by
    rintro ρ ⟨j, hj, rfl⟩
    change latticeFunctional (polytopeToricRayGenerator γ hs v j) (A.symm (extend f)) = 0
    rw [← latticeBasisLogInverseTranspose_vertex]
    change A (A.symm (extend f)) j = 0
    rw [A.apply_symm_apply]
    exact dif_pos hj
  let L : toricStratumRealSpace (polytopeToricRay γ hs v '' J) ≃ₗ[ℝ]
      ({j : Fin n // j ∉ J} → ℝ) := {
    toFun := fun x j => A x.val j.val
    invFun := fun f => ⟨A.symm (extend f), hmem f⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply A.injective
      ext j
      rw [A.apply_symm_apply]
      change (if _hj : j ∈ J then (0 : ℝ) else A x.val j) = A x.val j
      by_cases hj : j ∈ J
      · rw [dif_pos hj]
        symm
        exact (latticeBasisLogInverseTranspose_vertex v x.val j).trans
          (x.property (polytopeToricRay γ hs v j) ⟨j, hj, rfl⟩)
      · rw [dif_neg hj]
    right_inv := by
      intro f
      funext j
      change A (A.symm (extend f)) j.val = f j
      rw [A.apply_symm_apply]
      exact dif_neg j.property
    map_add' := by
      intro x y
      funext j
      exact congrArg (fun z : E => z j.val) (map_add A x.val y.val)
    map_smul' := by
      intro c x
      funext j
      exact congrArg (fun z : E => z j.val) (map_smul A c x.val) }
  exact L.toContinuousLinearEquiv

/-- Real and integral source coordinates agree on every actual integral
character of the stratum. This fixes the genuine normalized lattice. -/
theorem toricStratumRealCoordinates_latticeVector
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (j : {j : Fin n // j ∉ J}) :
    toricStratumRealCoordinates v J ⟨latticeVector m.val,
      latticeVector_mem_toricStratumRealSpace m.property⟩ j =
      ((toricStratumCharacterCoordinates v J m j : ℤ) : ℝ) := by
  change latticeBasisLogInverseTranspose (originalPolytopeNativeBasis γ hs v)
    (latticeVector m.val) j.val = ((originalPolytopeNativeBasis γ hs v).equivFun m.val j.val : ℝ)
  rw [latticeBasisLogInverseTranspose_vertex, latticeFunctional_latticeVector,
    intPairing_comm]
  simp only [Module.Basis.equivFun_apply, basis_repr_eq_intPairing]

/-- The original source Cartier datum along σ, with literal original
integral pairings and arbitrary representative. -/
def IsToricCartierDatumAlong (D : ToricDivisor γ hs)
    (R : Set (PolytopeToricRays γ hs)) (mσ : Fin n → ℤ) : Prop :=
  ∀ ρ ∈ R, intPairing mσ ρ.val = -D ρ

/-- The actual vertex datum satisfies the original cone equations. -/
theorem isToricCartierDatumAlong_vertex (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) (toricCartierDatum D v) := by
  rintro ρ ⟨j, _hj, rfl⟩
  exact toricCartierDatum_pairing D v j

/-- Arbitrary original representatives differ by a literal integral
character of the actual stratum, rather than a supplied identification. -/
theorem sub_mem_toricStratumCharacterLattice_of_Cartier_data
    {D : ToricDivisor γ hs} {R : Set (PolytopeToricRays γ hs)} {mσ mτ : Fin n → ℤ}
    (hσ : IsToricCartierDatumAlong D R mσ) (hτ : IsToricCartierDatumAlong D R mτ) :
    mσ - mτ ∈ toricStratumCharacterLattice R := by
  intro ρ hρ
  rw [intPairing_sub, hσ ρ hρ, hτ ρ hρ, sub_self]

/-- The literal original translated face really lies in M(σ)_R, including
empty faces and point strata. No face/body equality is an input. -/
theorem sub_Cartier_mem_toricStratumRealSpace_of_mem_face
    {D : ToricDivisor γ hs} {R : Set (PolytopeToricRays γ hs)} {mσ : Fin n → ℤ}
    (hσ : IsToricCartierDatumAlong D R mσ) {p : E}
    (hp : p ∈ toricDivisorFace D R) :
    p - latticeVector mσ ∈ toricStratumRealSpace R := by
  intro ρ hρ
  rw [map_sub, latticeFunctional_latticeVector, intPairing_comm, hσ ρ hρ, hp.2 ρ hρ]
  push_cast
  ring

end SGPT.Toric
