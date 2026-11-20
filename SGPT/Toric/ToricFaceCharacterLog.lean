import SGPT.Toric.ToricFaceNormalDegeneration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- In the ACTUAL finite quotient basis, every original Mσ character has
exactly the target character, evaluated at the explicit original lift. -/
theorem latticeCharacter_toricFaceTorusSection
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    latticeCharacter m.val (toricFaceTorusSection (hs := hs) v J a) =
      latticeCharacter (toricFaceCharacterCoordinates (hs := hs) v J m) a := by
  rw [latticeCharacter_toricStratum_factorization]
  change (∏ j : {j : Fin n // j ∉ J},
    toricStratumTorusQuotient v J (toricStratumTorusSection v J
      (fun j => a ((Fintype.equivFin {j : Fin n // j ∉ J}) j))) j ^
      toricStratumCharacterCoordinates v J m j) = _
  rw [toricStratumTorusQuotient_section]
  change (∏ j : {j : Fin n // j ∉ J}, a ((Fintype.equivFin {j : Fin n // j ∉ J}) j) ^
      toricStratumCharacterCoordinates v J m j) =
    ∏ j, a j ^ toricFaceCharacterCoordinates v J m j
  apply Fintype.prod_equiv (Fintype.equivFin {j : Fin n // j ∉ J})
  intro j
  congr 1
  change toricStratumCharacterCoordinates v J m j =
    toricStratumCharacterCoordinates v J m
      ((Fintype.equivFin {j : Fin n // j ∉ J}).symm
        ((Fintype.equivFin {j : Fin n // j ∉ J}) j))
  rw [Equiv.symm_apply_apply]

/-- The literal squared-logarithm convention is the actual original
integral character logarithm, including every negative character exponent. -/
theorem latticeFunctional_unitTorusLog_eq_log_character (m : Fin n → ℤ) (a : Fin n → ℂˣ) :
    latticeFunctional m (unitTorusLog a) = Real.log (‖(latticeCharacter m a : ℂ)‖ ^ 2) :=
  (latticeCharacter_log_norm_sq m a).symm

/-- Actual quotient and source lattice logarithmic pairings agree under
the genuine original lift; no target tropical-coordinate certificate is used. -/
theorem latticeFunctional_toricFaceTorusSection
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    latticeFunctional m.val (unitTorusLog (toricFaceTorusSection (hs := hs) v J a)) =
      latticeFunctional (toricFaceCharacterCoordinates (hs := hs) v J m) (unitTorusLog a) := by
  rw [latticeFunctional_unitTorusLog_eq_log_character,
    latticeFunctional_unitTorusLog_eq_log_character, latticeCharacter_toricFaceTorusSection]

/-- The original transition character logarithm stays EXACTLY constant
on every actual ambient torus point of the genuine normal degeneration. -/
theorem latticeFunctional_toricFaceNormalCurve
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (a : Fin (toricFaceDimension J) → ℂˣ) (N : ℕ) :
    latticeFunctional m.val (unitTorusLog (toricFaceNormalCurve (hs := hs) v J a N)) =
      latticeFunctional (toricFaceCharacterCoordinates (hs := hs) v J m) (unitTorusLog a) := by
  rw [latticeFunctional_unitTorusLog_eq_log_character, latticeCharacter_toricFaceNormalCurve,
    ← latticeFunctional_unitTorusLog_eq_log_character, latticeFunctional_toricFaceTorusSection]

/-- Index-linearity of the literal integral pairing, used to retain the
original Cartier transition characters rather than separate divergent terms. -/
theorem latticeFunctional_sub_index (m m' : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional (m - m') x = latticeFunctional m x - latticeFunctional m' x := by
  simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

end SGPT.Toric
