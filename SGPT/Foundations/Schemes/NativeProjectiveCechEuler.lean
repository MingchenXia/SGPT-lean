import SGPT.Foundations.Schemes.NativeProjectiveTwistedCechVanishing
import SGPT.Foundations.Schemes.NativeProjectiveGlobalSectionsFiniteness
import Mathlib.Algebra.Homology.EulerCharacteristic

/-! # Actual projective-twist Čech homology Euler characteristic

Only homology enters the Euler characteristic: actual affine section terms
can have infinite dimension. Genuine finite chart data produce finite actual
homology and a finite support bound before finite-dimensional readbacks.
Cover independence, additivity and intersection comparisons are separate.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)

/-- The actual normalized complex of the original coordinate-cover twist sections. -/
def polynomialProjTwistedCechComplex (m : ℕ) : CochainComplex (ModuleCat K) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    (polynomialProjModuleTensorTwist K n M m) (polynomialProjCoordinateOpen K n)
    (schemeConstantMap (polynomialProjStructureMap K n)))

/-- The actual finite coordinate cover gives genuine zero homology beyond
its cardinality, independent of any junk-value convention for dimensions. -/
theorem polynomialProjTwistedCech_homology_isZero_of_bound (m p : ℕ) (hp : n + 1 ≤ p) :
    IsZero ((polynomialProjTwistedCechComplex K n M m).homology p) :=
  subsetCechComplex_homology_isZero_of_card_le _ p (by simpa using hp)

/-- The homological Euler integer for the actual twist complex. Its actual
finite homology/support and genuine finite-sum interpretation are proved below. -/
def polynomialProjTwistedCechEuler (m : ℕ) : ℤ :=
  (polynomialProjTwistedCechComplex K n M m).homologyEulerChar

/-- The literal homological Euler sum has actual finite support from the
finite cover. Finiteness of the homology modules is a separate producer below. -/
theorem polynomialProjTwistedCechEuler_eq_sum (m : ℕ) :
    polynomialProjTwistedCechEuler K n M m =
      ∑ p ∈ Finset.range (n + 1), (-1 : ℤ) ^ p *
        (Module.finrank K ((polynomialProjTwistedCechComplex K n M m).homology p) : ℤ) := by
  rw [polynomialProjTwistedCechEuler,
    HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      _ (Finset.range (n + 1))]
  · simp
  · intro p hp
    apply Finset.mem_range.mpr
    by_contra! hle
    have hzero := polynomialProjTwistedCech_homology_isZero_of_bound K n M m p hle
    have : Subsingleton ((polynomialProjTwistedCechComplex K n M m).homology p) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact hp (Module.finrank_zero_of_subsingleton)

variable [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
    Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- ACTUAL finite quasicoherent chart data produce finite actual native
Čech homology in EVERY twist and degree, not just an eventual dimension. -/
theorem polynomialProjTwistedCech_homology_finite (m p : ℕ) :
    Module.Finite K ((polynomialProjTwistedCechComplex K n M m).homology p) := by
  let D := homogeneousCoordinateSubsetDiagram
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjChartGeneratedTwistedPiece K n M)
    (fun j ↦ (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree (m : ℤ)
  let : Module.Finite K ((subsetCechComplex D).homology p) :=
    finiteGradedPolynomialCoordinateCech_homology_finite (K := K) (I := Fin (n + 1))
      (polynomialProjChartGeneratedTwistedPiece K n M) (m : ℤ) p
  exact Module.Finite.equiv
    (nonemptySubsetCechHomologyIso
      (polynomialProjChartGeneratedTwistedAllDegreeNonemptySubsetIso K n M m) p).toLinearEquiv

/-- Genuine positive-cohomology vanishing and the ORIGINAL structural H0
comparison make the actual finite Euler integer equal actual sections. -/
theorem polynomialProjTwistedCechEuler_eventually_eq_global_finrank :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      polynomialProjTwistedCechEuler K n M m =
        (Module.finrank K (actualSchemeModuleBaseGlobalSections
          (polynomialProjModuleTensorTwist K n M m)
          (schemeConstantMap (polynomialProjStructureMap K n))) : ℤ) := by
  obtain ⟨b, hb⟩ := polynomialProjFiniteChartTwistedCech_homology_eventually_isZero K n M
  refine ⟨b, fun m hm ↦ ?_⟩
  have hfinite : ∀ p, Module.Finite K ((polynomialProjTwistedCechComplex K n M m).homology p) :=
    fun p ↦ polynomialProjTwistedCech_homology_finite K n M m p
  rw [polynomialProjTwistedCechEuler_eq_sum]
  have hz (p : ℕ) (hp : p ≠ 0) :
      Module.finrank K ((polynomialProjTwistedCechComplex K n M m).homology p) = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have : Subsingleton ((polynomialProjTwistedCechComplex K n M m).homology (j + 1)) :=
      ModuleCat.subsingleton_of_isZero (hb m hm j)
    exact Module.finrank_zero_of_subsingleton
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]
    congr 1
    exact (actualSchemeModuleBaseGlobalHomologyIso
      (polynomialProjModuleTensorTwist K n M m) (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))
      (Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates)).toLinearEquiv.finrank_eq.symm
  · intro p hp hp0
    rw [hz p hp0, Nat.cast_zero, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.zero_lt_succ n))).elim

end
end SGPT.Foundations.Schemes
