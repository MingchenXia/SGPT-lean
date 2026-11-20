import SGPT.AlmostSemigroup.Conductor
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open SGPT.AlmostSemigroup.Counting
open scoped BigOperators

private instance standardLattice_discrete (n : ℕ) : DiscreteTopology (standardLattice n) := by
  unfold standardLattice
  infer_instance

private instance standardLattice_isZLattice (n : ℕ) : IsZLattice ℝ (standardLattice n) := by
  unfold standardLattice
  infer_instance

/-- The EXISTING actual integer-cast additive map, restricted to the EXISTING
standard lattice and bundled using its genuinely proved bijectivity. -/
def integerLatticeLinearEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] standardLattice n :=
  LinearEquiv.ofBijective
    (((SGPT.AlmostSemigroup.Conductor.integerCastHom n).toIntLinearMap).codRestrict
      (standardLattice n) integerCast_mem_standardLattice)
    (integerLatticeEquiv n).bijective

/-- The original literal integer vector is preserved, before any basis readback. -/
theorem integerLatticeLinearEquiv_apply {n : ℕ} (m : Fin n → ℤ) :
    ((integerLatticeLinearEquiv n m : standardLattice n) : Fin n → ℝ) = integerCast m := rfl

/-- Genuine existing Z-lattice basis extension, rather than supplied real linear
independence or a parallel scalar-extension proof. -/
def integralRealBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (b.map (integerLatticeLinearEquiv n)).ofZLatticeBasis ℝ (standardLattice n)

/-- The manufactured real basis consists of the SAME original integer vectors. -/
theorem integralRealBasis_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (j : Fin n) : integralRealBasis b j = integerCast (b j) := by
  rw [integralRealBasis, Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
  rfl

/-- Existing actual Z-lattice coordinate readback is exactly the original
integer basis coefficient, including rank zero. -/
theorem integralRealBasis_repr_integerCast {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (m : Fin n → ℤ) (j : Fin n) :
    (integralRealBasis b).repr (integerCast m) j = (b.repr m j : ℝ) := by
  have h := Module.Basis.ofZLatticeBasis_repr_apply ℝ (standardLattice n)
    (b.map (integerLatticeLinearEquiv n)) (integerLatticeLinearEquiv n m) j
  simpa only [integralRealBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, integerLatticeLinearEquiv_apply] using h

/-- Real coordinates are manufactured from an actual original integral
coordinate equivalence and the genuine lattice-basis mother. -/
def integralRealCoordinates {n : ℕ} (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (integralRealBasis ((Pi.basisFun ℤ (Fin n)).map c.symm)).equivFun

/-- Every actual original integer coordinate is preserved by real extension. -/
theorem integralRealCoordinates_integerCast {n : ℕ}
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (m : Fin n → ℤ) :
    integralRealCoordinates c (integerCast m) = integerCast (c m) := by
  ext j
  change (integralRealBasis ((Pi.basisFun ℤ (Fin n)).map c.symm)).repr
    (integerCast m) j = (c m j : ℝ)
  rw [integralRealBasis_repr_integerCast]
  simp

/-- The actual inverse preserves original lattice vectors as well. -/
theorem integralRealCoordinates_symm_integerCast {n : ℕ}
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (m : Fin n → ℤ) :
    (integralRealCoordinates c).symm (integerCast m) = integerCast (c.symm m) := by
  apply (integralRealCoordinates c).injective
  rw [LinearEquiv.apply_symm_apply, integralRealCoordinates_integerCast,
    LinearEquiv.apply_symm_apply]

/-- Original primal basis vectors are the SAME inverse real-coordinate vectors. -/
theorem integralRealCoordinates_symm_basis {n : ℕ}
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (j : Fin n) :
    (integralRealCoordinates c).symm (Pi.basisFun ℝ (Fin n) j) =
      integerCast (c.symm (Pi.basisFun ℤ (Fin n) j)) := by
  have hcast : Pi.basisFun ℝ (Fin n) j = integerCast (Pi.basisFun ℤ (Fin n) j) := by
    ext k
    simp [Pi.basisFun_apply, integerCast, Pi.single_apply]
  rw [hcast, integralRealCoordinates_symm_integerCast]

/-- The original integer functional is extended by the EXISTING genuine basis
construction, with coefficients equal to its original standard-basis values. -/
def integralRealFunctional {n : ℕ} (u : (Fin n → ℤ) →ₗ[ℤ] ℤ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Pi.basisFun ℝ (Fin n)).constr ℝ
    (fun i => (u (Pi.basisFun ℤ (Fin n) i) : ℝ)))

/-- The literal coefficient-sum expression of the original facet normal. -/
theorem integralRealFunctional_apply {n : ℕ} (u : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (x : Fin n → ℝ) : integralRealFunctional u x =
      ∑ i, x i * (u (Pi.basisFun ℤ (Fin n) i) : ℝ) := by
  simp [integralRealFunctional, Module.Basis.constr_apply_fintype]

/-- Genuine original integral evaluation is preserved before real facet readback. -/
theorem integralRealFunctional_integerCast {n : ℕ} (u : (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (m : Fin n → ℤ) : integralRealFunctional u (integerCast m) = (u m : ℝ) := by
  rw [integralRealFunctional_apply]
  have h := congrArg u ((Pi.basisFun ℤ (Fin n)).sum_repr m)
  simp only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul] at h
  change (∑ i, (m i : ℝ) * (u (Pi.basisFun ℤ (Fin n) i) : ℝ)) = (u m : ℝ)
  exact_mod_cast h

/-- Selected original facet normals become EXACTLY the manufactured real
coordinate functionals; equality precedes any coordinate inequalities. -/
theorem integralRealCoordinates_coord {n : ℕ}
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (j : Fin n) (x : Fin n → ℝ) :
    integralRealCoordinates c x j =
      integralRealFunctional ((LinearMap.proj j).comp c.toLinearMap) x := by
  have heq : (LinearMap.proj j).comp (integralRealCoordinates c).toLinearMap =
      (integralRealFunctional ((LinearMap.proj j).comp c.toLinearMap)).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro i
    have hcast : Pi.basisFun ℝ (Fin n) i = integerCast (Pi.basisFun ℤ (Fin n) i) := by
      ext k
      simp [Pi.basisFun_apply, integerCast, Pi.single_apply]
    change integralRealCoordinates c (Pi.basisFun ℝ (Fin n) i) j =
      integralRealFunctional ((LinearMap.proj j).comp c.toLinearMap) (Pi.basisFun ℝ (Fin n) i)
    rw [hcast, integralRealCoordinates_integerCast, integralRealFunctional_integerCast]
    rfl
  exact congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ => f x) heq

end SGPT.Toric
