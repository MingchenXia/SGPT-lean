import SGPT.Toric.ToricStratumLattice
import SGPT.Toric.LatticeCharacterCoordinates
import SGPT.Toric.GeodesicAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual source quotient torus map is evaluation at the original
complementary edge characters of M(σ), rather than an assigned action. -/
def toricStratumTorusQuotient (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (Fin n → ℂˣ) →* ({j : Fin n // j ∉ J} → ℂˣ) where
  toFun a j := latticeCharacter (originalPolytopeNativeBasis γ hs v j.val) a
  map_one' := funext fun j => map_one (latticeCharacter (originalPolytopeNativeBasis γ hs v j.val))
  map_mul' a b := funext fun j => map_mul (latticeCharacter (originalPolytopeNativeBasis γ hs v j.val)) a b

/-- Genuine Laurent products give continuity of the actual quotient. -/
theorem continuous_toricStratumTorusQuotient (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricStratumTorusQuotient (hs := hs) v J) := by
  apply continuous_pi
  intro j
  exact continuous_latticeCharacter _

/-- Compact original elements descend to actual compact quotient elements. -/
theorem norm_toricStratumTorusQuotient_of_compact (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (j : {j : Fin n // j ∉ J}) :
    ‖(toricStratumTorusQuotient (hs := hs) v J a j : ℂ)‖ = 1 :=
  norm_latticeCharacter_of_compact _ ha

/-- An actual lift extends quotient coordinates by1 on the selected rays,
then changes back through the genuine original integral edge basis. -/
def toricStratumTorusSection (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : {j : Fin n // j ∉ J} → ℂˣ) : Fin n → ℂˣ := by
  classical
  exact latticeBasisChangeEquiv (originalPolytopeNativeBasis γ hs v)
    (Pi.basisFun ℤ (Fin n)) (fun j => if hj : j ∈ J then 1 else a ⟨j, hj⟩)

/-- The constructed actual lift is continuous. -/
theorem continuous_toricStratumTorusSection (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricStratumTorusSection (hs := hs) v J) := by
  classical
  apply (continuous_latticeBasisChangeEquiv _ _).comp
  apply continuous_pi
  intro j
  by_cases hj : j ∈ J
  · simpa only [dif_pos hj] using (continuous_const : Continuous (fun _ :
      ({j : Fin n // j ∉ J} → ℂˣ) => (1 : ℂˣ)))
  · simpa only [dif_neg hj] using (continuous_apply (⟨j, hj⟩ : {j : Fin n // j ∉ J}))

/-- Readback of the actual lift on every original edge character. -/
theorem toricStratumTorusSection_character (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : {j : Fin n // j ∉ J} → ℂˣ) (j : Fin n) :
    latticeCharacter (originalPolytopeNativeBasis γ hs v j)
      (toricStratumTorusSection (hs := hs) v J a) =
      if hj : j ∈ J then 1 else a ⟨j, hj⟩ := by
  classical
  let b := originalPolytopeNativeBasis γ hs v
  let t : Fin n → ℂˣ := fun j => if hj : j ∈ J then 1 else a ⟨j, hj⟩
  have heq := congrArg (fun χ => χ (b j))
    (latticeBasisCharacterEquiv_basisChange b (Pi.basisFun ℤ (Fin n)) t)
  have hb : latticeBasisCharacterEquiv b t (b j) = t j :=
    congrFun ((latticeBasisCharacterEquiv b).symm_apply_apply t) j
  rw [hb] at heq
  change latticeCharacter (b j) (latticeBasisChangeEquiv b (Pi.basisFun ℤ (Fin n)) t) = t j
  simpa only [latticeBasisCharacterEquiv_apply, Pi.basisFun_repr] using heq

/-- The actual source quotient is surjective by the displayed genuine lift. -/
theorem toricStratumTorusQuotient_section (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : {j : Fin n // j ∉ J} → ℂˣ) :
    toricStratumTorusQuotient (hs := hs) v J
      (toricStratumTorusSection (hs := hs) v J a) = a := by
  classical
  funext j
  exact (toricStratumTorusSection_character (hs := hs) v J a j.val).trans (dif_neg j.property)

/-- Surjectivity retains the literal source torus and its integral quotient. -/
theorem toricStratumTorusQuotient_surjective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Surjective (toricStratumTorusQuotient (hs := hs) v J) :=
  fun a => ⟨toricStratumTorusSection (hs := hs) v J a, toricStratumTorusQuotient_section v J a⟩

/-- Every original character of the ACTUAL annihilator lattice factors
through the actual quotient with its literal integral coordinates. This is
the source M(σ) dictionary, not merely surjectivity of a coordinate map. -/
theorem latticeCharacter_toricStratum_factorization
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (a : Fin n → ℂˣ) :
    latticeCharacter m.val a =
      ∏ j : {j : Fin n // j ∉ J},
        toricStratumTorusQuotient (hs := hs) v J a j ^ toricStratumCharacterCoordinates v J m j := by
  classical
  let f : Fin n → ℂˣ := fun j =>
    latticeCharacter (originalPolytopeNativeBasis γ hs v j) a ^
      intPairing m.val (polytopeToricRayGenerator γ hs v j)
  have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun j : Fin n => j ∈ J) f
  have hselected : (∏ j : {j : Fin n // j ∈ J}, f j.val) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hm := m.property (polytopeToricRay γ hs v j.val) ⟨j.val, j.property, rfl⟩
    change intPairing m.val (polytopeToricRayGenerator γ hs v j.val) = 0 at hm
    change latticeCharacter _ a ^ intPairing m.val (polytopeToricRayGenerator γ hs v j.val) = 1
    rw [hm, zpow_zero]
  rw [hselected, one_mul] at hsplit
  calc
    latticeCharacter m.val a = ∏ j, f j := latticeCharacter_eq_prod_basis hs v m.val a
    _ = ∏ j : {j : Fin n // j ∉ J}, f j.val := hsplit.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      change latticeCharacter _ a ^ intPairing m.val (polytopeToricRayGenerator γ hs v j.val) =
        latticeCharacter _ a ^ ((originalPolytopeNativeBasis γ hs v).equivFun m.val j.val)
      simp only [Module.Basis.equivFun_apply, basis_repr_eq_intPairing]

/-- Every actual compact quotient element has an actual compact original
lift. This derives compact torus surjectivity, including rank zero, instead
of using a group-action presentation certificate. -/
theorem toricStratumTorusSection_compact (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : {j : Fin n // j ∉ J} → ℂˣ) (ha : ∀ j, ‖(a j : ℂ)‖ = 1) :
    IsCompactTorusElement (toricStratumTorusSection (hs := hs) v J a) := by
  classical
  have ht : IsCompactTorusElement (fun j => if hj : j ∈ J then 1 else a ⟨j, hj⟩) := by
    intro j
    dsimp only
    split_ifs with hj
    · simp
    · exact ha ⟨j, hj⟩
  intro j
  change ‖(latticeBasisCharacterEquiv (originalPolytopeNativeBasis γ hs v)
    (fun j => if hj : j ∈ J then 1 else a ⟨j, hj⟩) ((Pi.basisFun ℤ (Fin n)) j) : ℂ)‖ = 1
  rw [latticeBasisCharacterEquiv_apply]
  exact norm_latticeCharacter_of_compact _ ht

end SGPT.Toric
