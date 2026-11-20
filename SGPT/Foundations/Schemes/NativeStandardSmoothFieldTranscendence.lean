import SGPT.Foundations.Schemes.SmoothCanonicalCharts
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Transcendence degree from an actual standard-smooth affine algebra

The existing standard-smooth relative dimension supplies an actual étale
polynomial algebra map. Its fraction-field extension is algebraic, yielding
the actual transcendence degree without a dimension certificate.
-/

open Algebra

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- An actual étale domain algebra induces an algebraic extension of its
actual fraction fields, for the explicitly compatible fraction-field tower. -/
theorem nativeEtaleFractionField_isAlgebraic
    (R A E F : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field E] [Field F] [Algebra R A] [Algebra.Etale R A]
    [Algebra A F] [IsFractionRing A F] [Algebra R F] [IsScalarTower R A F]
    [Algebra R E] [IsFractionRing R E] [Algebra E F] [IsScalarTower R E F] :
    Algebra.IsAlgebraic E F := by
  have : Algebra.FormallyUnramified A F :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallyUnramified R F := Algebra.FormallyUnramified.comp R A F
  have : Algebra.FormallyUnramified E F := Algebra.FormallyUnramified.of_restrictScalars R E F
  have : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  have : Algebra.EssFiniteType R F := Algebra.EssFiniteType.comp R A F
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp R E F
  have : Algebra.IsSeparable E F := Algebra.FormallyUnramified.isSeparable E F
  infer_instance

/-- A domain which is standard smooth of relative dimension n has actual
fraction-field transcendence degree n, for the given compatible base action. -/
theorem nativeStandardSmoothFractionField_trdeg (K A F : Type) [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Field F]
    [Algebra A F] [IsFractionRing A F] [Algebra K F] [IsScalarTower K A F]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    Algebra.trdeg K F = n := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := g.toRingHom.toAlgebra
  let : IsScalarTower K P A := IsScalarTower.of_algHom g
  have : Algebra.Etale P A := hg
  let : Algebra P F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K P F := IsScalarTower.to₁₂₄ K P A F
  have : FaithfulSMul P A := inferInstance
  have : FaithfulSMul P F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact (IsFractionRing.injective A F).comp (FaithfulSMul.algebraMap_injective P A)
  let E := FractionRing P
  let : Algebra E F := FractionRing.liftAlgebra P F
  let : IsScalarTower P E F := FractionRing.isScalarTower_liftAlgebra P F
  let : IsScalarTower K E F := IsScalarTower.to₁₃₄ K P E F
  have : Algebra.IsAlgebraic E F := nativeEtaleFractionField_isAlgebraic P A E F
  have : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have hP : Algebra.trdeg K P = n := by simp [P]
  have hE : Algebra.trdeg K E = n := by
    have h := trdeg_add_eq K P (A := E)
    rw [trdeg_eq_zero (R := P) (A := E), add_zero, hP] at h
    exact h.symm
  have h := trdeg_add_eq K E (A := F)
  rw [trdeg_eq_zero (R := E) (A := F), add_zero, hE] at h
  exact h.symm

end
end SGPT.Foundations.Schemes
