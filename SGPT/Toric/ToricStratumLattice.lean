import SGPT.Toric.Toric3Flag

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal original character lattice M(σ)=σ-perp∩M, with its original
integral inclusion. No desired quotient coordinates occur in the definition. -/
def toricStratumCharacterLattice (R : Set (PolytopeToricRays γ hs)) :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {m | ∀ ρ ∈ R, intPairing m ρ.val = 0}
  zero_mem' := by intro ρ _; simp [intPairing]
  add_mem' := by intro a b ha hb ρ hρ; rw [intPairing_add, ha ρ hρ, hb ρ hρ, zero_add]
  smul_mem' := by intro c a ha ρ hρ; rw [intPairing_smul, ha ρ hρ, mul_zero]

/-- Saturation is a consequence of the literal integral pairing equations,
including the empty cone and the point stratum. -/
theorem toricStratumCharacterLattice_saturated (R : Set (PolytopeToricRays γ hs))
    {c : ℤ} (hc : c ≠ 0) {m : Fin n → ℤ}
    (hm : c • m ∈ toricStratumCharacterLattice R) :
    m ∈ toricStratumCharacterLattice R := by
  intro ρ hρ
  have hh := hm ρ hρ
  rw [intPairing_smul] at hh
  exact (mul_eq_zero.mp hh).resolve_left hc

/-- A genuine original containing vertex cone identifies the ACTUAL
annihilator lattice with the complementary integral coordinate tuples.
Both inverse maps are constructed from the original integral edge basis. -/
def toricStratumCharacterCoordinates (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) ≃ₗ[ℤ]
      ({j : Fin n // j ∉ J} → ℤ) := by
  classical
  let b := originalPolytopeNativeBasis γ hs v
  let extend : ({j : Fin n // j ∉ J} → ℤ) → Fin n → ℤ :=
    fun f j => if hj : j ∈ J then 0 else f ⟨j, hj⟩
  have hmem (f : {j : Fin n // j ∉ J} → ℤ) :
      b.equivFun.symm (extend f) ∈
        toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
    rintro ρ ⟨j, hj, rfl⟩
    change intPairing (b.equivFun.symm (extend f)) (polytopeToricRayGenerator γ hs v j) = 0
    rw [← basis_repr_eq_intPairing hs v]
    change (b.equivFun (b.equivFun.symm (extend f))) j = 0
    rw [b.equivFun.apply_symm_apply]
    exact dif_pos hj
  exact {
    toFun := fun m j => b.equivFun m.val j.val
    invFun := fun f => ⟨b.equivFun.symm (extend f), hmem f⟩
    left_inv := by
      intro m
      apply Subtype.ext
      apply b.equivFun.injective
      funext j
      rw [b.equivFun.apply_symm_apply]
      change extend (fun i : {j : Fin n // j ∉ J} => b.equivFun m.val i.val) j = b.equivFun m.val j
      by_cases hj : j ∈ J
      · dsimp only [extend]
        rw [dif_pos hj]
        have hh := m.property (polytopeToricRay γ hs v j) ⟨j, hj, rfl⟩
        symm
        change (b.repr m.val) j = 0
        rw [basis_repr_eq_intPairing]
        exact hh
      · dsimp only [extend]
        rw [dif_neg hj]
    right_inv := by
      intro f
      funext j
      change (b.equivFun (b.equivFun.symm (extend f))) j.val = f j
      rw [b.equivFun.apply_symm_apply]
      exact dif_neg j.property
    map_add' := by
      intro a b
      funext j
      exact congrFun (map_add (originalPolytopeNativeBasis γ hs v).equivFun a.val b.val) j.val
    map_smul' := by
      intro c m
      funext j
      exact congrFun (map_smul (originalPolytopeNativeBasis γ hs v).equivFun c m.val) j.val }

/-- The complementary ORIGINAL edge vectors form an actual Z-basis of
M(σ), manufactured from the proved coordinate equivalence. -/
def toricStratumCharacterBasis (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Module.Basis {j : Fin n // j ∉ J} ℤ
      (toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) := by
  classical
  exact (Pi.basisFun ℤ {j : Fin n // j ∉ J}).map
    (toricStratumCharacterCoordinates v J).symm

/-- Every original source fan cone supplies its actual saturated character
lattice coordinates and basis; there is no incoming rank/basis certificate. -/
theorem exists_toricStratumCharacterCoordinates {R : Set (PolytopeToricRays γ hs)}
    (hR : IsToricFanCone R) :
    ∃ (v : latticePolytopeVertices γ) (J : Set (Fin n)),
      R = polytopeToricRay γ hs v '' J ∧
      Nonempty (toricStratumCharacterLattice R ≃ₗ[ℤ] ({j : Fin n // j ∉ J} → ℤ)) := by
  obtain ⟨v, J, rfl⟩ := hR
  exact ⟨v, J, rfl, ⟨toricStratumCharacterCoordinates v J⟩⟩

end SGPT.Toric
