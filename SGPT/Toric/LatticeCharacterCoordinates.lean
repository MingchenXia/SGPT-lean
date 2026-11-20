import SGPT.Toric.MonomialProjectiveOrbit
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open scoped BigOperators

variable {n : ℕ} {M : Type*} [AddCommGroup M]

/-- The ORIGINAL lattice character torus, in an actual lattice basis. This
composes existing basis and character equivalences rather than assuming extension. -/
def latticeBasisCharacterEquiv (b : Module.Basis (Fin n) ℤ M) :
    (Fin n → ℂˣ) ≃ AddChar M ℂˣ :=
  (Equiv.piCongrRight (fun _ : Fin n => (Additive.ofMul : ℂˣ ≃ Additive ℂˣ))).trans
    ((b.constr (M' := Additive ℂˣ) ℤ).toEquiv.trans
      ((addMonoidHomLequivInt (A := M) (B := Additive ℂˣ) ℤ).toEquiv.symm.trans AddChar.toAddMonoidHomEquiv.symm))

/-- Every original character is read back at the actual basis vectors. -/
theorem latticeBasisCharacterEquiv_symm_apply (b : Module.Basis (Fin n) ℤ M)
    (χ : AddChar M ℂˣ) (j : Fin n) :
    (latticeBasisCharacterEquiv b).symm χ j = χ (b j) := rfl

/-- The genuine universal character is the SAME existing Laurent product,
including all negative integer exponents and the empty rank-zero product. -/
theorem latticeBasisCharacterEquiv_apply (b : Module.Basis (Fin n) ℤ M)
    (a : Fin n → ℂˣ) (m : M) :
    latticeBasisCharacterEquiv b a m = latticeCharacter (fun j => b.repr m j) a := by
  change Additive.toMul ((b.constr ℤ (fun j => Additive.ofMul (a j))) m) = _
  rw [Module.Basis.constr_apply_fintype]
  simp [latticeCharacter, Module.Basis.equivFun_apply]

/-- Coordinate change is manufactured by the SAME original character, in two
actual integer bases. No toric chart or geometry certificate is supplied. -/
def latticeBasisChangeEquiv (b c : Module.Basis (Fin n) ℤ M) :
    (Fin n → ℂˣ) ≃ (Fin n → ℂˣ) :=
  (latticeBasisCharacterEquiv b).trans (latticeBasisCharacterEquiv c).symm

/-- Literal character evaluation gives every actual changed coordinate. -/
theorem latticeBasisChangeEquiv_apply (b c : Module.Basis (Fin n) ℤ M)
    (a : Fin n → ℂˣ) (j : Fin n) :
    latticeBasisChangeEquiv b c a j = latticeBasisCharacterEquiv b a (c j) := rfl

/-- Basis change preserves the actual original lattice character, before any
coordinate or real readback. -/
theorem latticeBasisCharacterEquiv_basisChange (b c : Module.Basis (Fin n) ℤ M)
    (a : Fin n → ℂˣ) :
    latticeBasisCharacterEquiv c (latticeBasisChangeEquiv b c a) =
      latticeBasisCharacterEquiv b a := by
  change (latticeBasisCharacterEquiv c)
    ((latticeBasisCharacterEquiv c).symm ((latticeBasisCharacterEquiv b) a)) = _
  exact (latticeBasisCharacterEquiv c).apply_symm_apply ((latticeBasisCharacterEquiv b) a)

/-- Actual Laurent character continuity gives original torus coordinate continuity. -/
theorem continuous_latticeBasisChangeEquiv (b c : Module.Basis (Fin n) ℤ M) :
    Continuous (latticeBasisChangeEquiv b c) := by
  apply continuous_pi
  intro j
  simpa only [latticeBasisChangeEquiv_apply, latticeBasisCharacterEquiv_apply] using
    continuous_latticeCharacter (fun k => b.repr (c j) k)

/-- An actual integer-basis change is a genuine homeomorphism of the original
complex unit torus, with the reverse basis change as its literal inverse. -/
def latticeBasisChangeHomeomorph (b c : Module.Basis (Fin n) ℤ M) :
    (Fin n → ℂˣ) ≃ₜ (Fin n → ℂˣ) where
  toEquiv := latticeBasisChangeEquiv b c
  continuous_toFun := continuous_latticeBasisChangeEquiv b c
  continuous_invFun := continuous_latticeBasisChangeEquiv c b

/-- The actual changed coordinates obey the original torus multiplication law. -/
theorem latticeBasisChangeEquiv_mul (b c : Module.Basis (Fin n) ℤ M)
    (a a' : Fin n → ℂˣ) :
    latticeBasisChangeEquiv b c (a * a') =
      latticeBasisChangeEquiv b c a * latticeBasisChangeEquiv b c a' := by
  ext j
  simp only [latticeBasisChangeEquiv_apply, latticeBasisCharacterEquiv_apply,
    map_mul, Pi.mul_apply]

/-- The squared-logarithm convention is the literal integral basis pairing. -/
theorem latticeBasisChangeEquiv_log_norm_sq (b c : Module.Basis (Fin n) ℤ M)
    (a : Fin n → ℂˣ) (j : Fin n) :
    Real.log (‖(latticeBasisChangeEquiv b c a j : ℂ)‖ ^ 2) =
      ∑ k, (b.repr (c j) k : ℝ) *
        SGPT.Convex.torusLogCoordinates (latticeTorusPoint a) k := by
  rw [latticeBasisChangeEquiv_apply, latticeBasisCharacterEquiv_apply]
  exact latticeCharacter_log_norm_sq _ _

/-- The changed torus identity is the original identity in every lattice basis. -/
theorem latticeBasisChangeEquiv_one (b c : Module.Basis (Fin n) ℤ M) :
    latticeBasisChangeEquiv b c 1 = 1 := by
  ext j
  simp only [latticeBasisChangeEquiv_apply, latticeBasisCharacterEquiv_apply,
    map_one, Pi.one_apply]

variable {I : Type*}

/-- Actual original homogeneous monomial vectors agree after the genuine lattice
basis change. Equality is proved through the SAME original character. -/
theorem monomialOrbitVector_latticeBasisChange (b c : Module.Basis (Fin n) ℤ M)
    (β : I → M) (a : Fin n → ℂˣ) :
    monomialOrbitVector (fun i j => c.repr (β i) j) (latticeBasisChangeEquiv b c a) =
      monomialOrbitVector (fun i j => b.repr (β i) j) a := by
  funext i
  change (latticeCharacter (fun j => c.repr (β i) j) _ : ℂ) =
    (latticeCharacter (fun j => b.repr (β i) j) _ : ℂ)
  rw [← latticeBasisCharacterEquiv_apply c, ← latticeBasisCharacterEquiv_apply b]
  exact congrArg (fun χ : AddChar M ℂˣ => (χ (β i) : ℂ))
    (latticeBasisCharacterEquiv_basisChange b c a)

/-- Projectivization retains literal equality of original orbit representatives. -/
theorem monomialProjectiveOrbit_latticeBasisChange [Nonempty I]
    (b c : Module.Basis (Fin n) ℤ M) (β : I → M) (a : Fin n → ℂˣ) :
    monomialProjectiveOrbit (fun i j => c.repr (β i) j) (latticeBasisChangeEquiv b c a) =
      monomialProjectiveOrbit (fun i j => b.repr (β i) j) a := by
  unfold monomialProjectiveOrbit
  congr 1
  exact monomialOrbitVector_latticeBasisChange b c β a

/-- Surjectivity of actual basis change gives equality of the SAME original orbit ranges. -/
theorem monomialProjectiveOrbit_range_latticeBasisChange [Nonempty I]
    (b c : Module.Basis (Fin n) ℤ M) (β : I → M) :
    Set.range (monomialProjectiveOrbit (fun i j => c.repr (β i) j)) =
      Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) := by
  apply Set.Subset.antisymm
  · rintro p ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := (latticeBasisChangeEquiv b c).surjective a
    exact ⟨a', (monomialProjectiveOrbit_latticeBasisChange b c β a').symm⟩
  · rintro p ⟨a, rfl⟩
    exact ⟨latticeBasisChangeEquiv b c a,
      monomialProjectiveOrbit_latticeBasisChange b c β a⟩

/-- The literal projective monomial orbit closure is independent of the chosen
integer lattice basis. No normal-fan realization is inferred from this identity. -/
theorem monomialProjectiveOrbitClosure_latticeBasisChange [Nonempty I]
    (b c : Module.Basis (Fin n) ℤ M) (β : I → M) :
    monomialProjectiveOrbitClosure (fun i j => c.repr (β i) j) =
      monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) := by
  unfold monomialProjectiveOrbitClosure
  rw [monomialProjectiveOrbit_range_latticeBasisChange b c β]

end SGPT.Toric
