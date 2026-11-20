import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateAction
import SGPT.Foundations.Schemes.NonnegativeDirectSumGrading
import SGPT.Foundations.Schemes.PolynomialCoordinateLocalization

/-! # The genuine integral polynomial grading of actual twisted global sections

The pieces are the actual homogeneous singleton summands of Γ_*M.  Their
native internal decomposition and the graded polynomial action are derived
from the literal direct sum and true coordinate-section action.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual structural base-field action on each genuine global twist. -/
instance polynomialProjTwistedGlobalSectionsBaseModule
    (M : (polynomialProj K n).Modules) (d : ℕ) :
    Module K (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :=
  schemeGlobalSectionModule (polynomialProjStructureMap K n)
    (bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d) M)

/-- The native componentwise field action on the literal direct sum Γ_*M. -/
instance polynomialProjTwistedSectionModuleBaseModule
    (M : (polynomialProj K n).Modules) :
    Module K (polynomialProjTwistedSectionModule K n M) :=
  inferInstanceAs (Module K
    (⨁ d : ℕ, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d))

/-- The actual polynomial constants agree with the native degreewise structural field action. -/
instance polynomialProjTwistedSectionModuleScalarTower
    (M : (polynomialProj K n).Modules) :
    IsScalarTower K (MvPolynomial (Fin (n + 1)) K)
      (polynomialProjTwistedSectionModule K n M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d t =>
      change (MvPolynomial.C c : MvPolynomial (Fin (n + 1)) K) •
        (polynomialProjTwistingLine K n).ofTwistedSection M d t =
        c • (polynomialProjTwistingLine K n).ofTwistedSection M d t
      rw [polynomialProjTwistedSectionModule_C_smul]
      exact DirectSum.of_smul K
        (M := bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) d c t
  | add x y hx hy =>
      simp only [smul_add]
      exact congrArg₂ (· + ·) hx hy

/-- Actual homogeneous integral pieces; negative degrees contain only the actual zero section. -/
def polynomialProjTwistedSectionPiece (M : (polynomialProj K n).Modules) (k : ℤ) :
    Submodule K (polynomialProjTwistedSectionModule K n M) :=
  nonnegativeDirectSumPiece K
    (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) k

/-- The native integral decomposition is the actual singleton decomposition of Γ_*M. -/
instance polynomialProjTwistedSectionDecomposition (M : (polynomialProj K n).Modules) :
    DirectSum.Decomposition (polynomialProjTwistedSectionPiece K n M) :=
  nonnegativeDirectSumDecomposition K
    (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M)

/-- A genuine homogeneous global twisted section belongs to its literal integral degree. -/
theorem polynomialProjTwistedSectionPiece_ofTwistedSection
    (M : (polynomialProj K n).Modules) (d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
    (polynomialProjTwistingLine K n).ofTwistedSection M d t ∈
      polynomialProjTwistedSectionPiece K n M (d : ℤ) :=
  (nonnegativeDirectSumPieceInclusion K
    (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) d t).property

/-- Negative integral pieces of the genuine nonnegative Γ_*M are literally zero. -/
theorem polynomialProjTwistedSectionPiece_negative (M : (polynomialProj K n).Modules)
    (k : ℤ) (hk : k < 0) : polynomialProjTwistedSectionPiece K n M k = ⊥ :=
  nonnegativeDirectSumPiece_eq_bot K
    (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) k hk

/-- Every actual coordinate power raises the genuine integral section degree by its real exponent. -/
theorem polynomialProjTwistedSectionPiece_X_pow_smul
    (M : (polynomialProj K n).Modules) (i : Fin (n + 1)) (N : ℕ) (k : ℤ)
    (x : polynomialProjTwistedSectionModule K n M)
    (hx : x ∈ polynomialProjTwistedSectionPiece K n M k) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N • x ∈
      polynomialProjTwistedSectionPiece K n M ((N : ℤ) + k) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    let y : ⨁ e : ℕ, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M e := x
    have he : x = (polynomialProjTwistingLine K n).ofTwistedSection M d (y d) :=
      nonnegativeDirectSumPiece_eq_single K
        (bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M) d ⟨y, hx⟩
    rw [he, polynomialProjTwistedSectionModule_X_pow_smul]
    simpa only [Nat.cast_add] using polynomialProjTwistedSectionPiece_ofTwistedSection K n M
      (N + d) (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M N d
        (polynomialProjTwistedGlobalCoordinatePower K n i N) (y d))
  · have he : x = 0 := by
      have hp := polynomialProjTwistedSectionPiece_negative K n M k (by omega)
      have hz : x ∈ (⊥ : Submodule K (polynomialProjTwistedSectionModule K n M)) := hp ▸ hx
      exact hz
    rw [he, smul_zero]
    exact Submodule.zero_mem _

/-- A literal finite coordinate monomial shifts the actual integral degree by its actual exponent sum. -/
theorem polynomialProjTwistedSectionPiece_variableProduct_smul
    (M : (polynomialProj K n).Modules) (s : Finset (Fin (n + 1)))
    (e : Fin (n + 1) → ℕ) (k : ℤ) (x : polynomialProjTwistedSectionModule K n M)
    (hx : x ∈ polynomialProjTwistedSectionPiece K n M k) :
    (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ e i) • x ∈
      polynomialProjTwistedSectionPiece K n M ((∑ i ∈ s, (e i : ℤ)) + k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hx
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_smul, add_assoc]
      exact polynomialProjTwistedSectionPiece_X_pow_smul K n M i (e i)
        ((∑ j ∈ s, (e j : ℤ)) + k) _ ih

/-- Every literal polynomial monomial has its genuine weighted homogeneous action. -/
theorem polynomialProjTwistedSectionPiece_monomial_smul
    (M : (polynomialProj K n).Modules) (e : Fin (n + 1) →₀ ℕ) (c : K) (k : ℤ)
    (x : polynomialProjTwistedSectionModule K n M)
    (hx : x ∈ polynomialProjTwistedSectionPiece K n M k) :
    (MvPolynomial.monomial e c) • x ∈
      polynomialProjTwistedSectionPiece K n M
        (Finsupp.weight (fun _ : Fin (n + 1) => (1 : ℤ)) e + k) := by
  rw [MvPolynomial.monomial_eq, mul_smul]
  have hp := polynomialProjTwistedSectionPiece_variableProduct_smul K n M e.support e k x hx
  have hw : Finsupp.weight (fun _ : Fin (n + 1) => (1 : ℤ)) e =
      ∑ i ∈ e.support, (e i : ℤ) := by
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hw]
  have hc := (polynomialProjTwistedSectionPiece K n M
    ((∑ i ∈ e.support, (e i : ℤ)) + k)).smul_mem c hp
  change MvPolynomial.C c • ((∏ i ∈ e.support, MvPolynomial.X i ^ e i) • x) ∈ _
  have hs : (MvPolynomial.C c : MvPolynomial (Fin (n + 1)) K) •
      ((∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ e i) • x) =
      c • ((∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ e i) • x) :=
    IsScalarTower.algebraMap_smul (R := K) (MvPolynomial (Fin (n + 1)) K) c _
  rw [hs]
  exact hc

/-- A genuine integral weighted homogeneous polynomial shifts actual Γ_* sections by its true degree. -/
theorem polynomialProjTwistedSectionPiece_homogeneous_smul
    (M : (polynomialProj K n).Modules) (a k : ℤ)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ∈ polynomialIntegralGrading (K := K) (I := Fin (n + 1)) a)
    (x : polynomialProjTwistedSectionModule K n M)
    (hx : x ∈ polynomialProjTwistedSectionPiece K n M k) :
    p • x ∈ polynomialProjTwistedSectionPiece K n M (a + k) := by
  change p.IsWeightedHomogeneous (fun _ : Fin (n + 1) => (1 : ℤ)) a at hp
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [zero_smul] using
      (polynomialProjTwistedSectionPiece K n M (a + k)).zero_mem
  | add p q hp hq ihp ihq =>
      rw [add_smul]
      exact Submodule.add_mem _ ihp ihq
  | monomial e c he =>
      simpa only [he] using polynomialProjTwistedSectionPiece_monomial_smul K n M e c k x hx

/-- The literal actual Γ_*M is a native integrally graded polynomial module. -/
instance polynomialProjTwistedSectionGradedSMul (M : (polynomialProj K n).Modules) :
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedSectionPiece K n M) where
  smul_mem := fun a k p x hp hx =>
    polynomialProjTwistedSectionPiece_homogeneous_smul K n M a k p hp x hx

end

end SGPT.Foundations.Schemes
