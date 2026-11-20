import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral
import SGPT.Foundations.Schemes.IntegralExtensionKrullDimension

/-! # Dimension and transcendence degree of genuine finite-type domains -/

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K A : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A]

/-- Actual Noether normalization gives the same finite natural value for
Krull dimension and transcendence degree of a genuine finite-type domain. -/
theorem finiteTypeDomain_dimension_exists :
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) ∧ Algebra.trdeg K A = (d : Cardinal) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin d) K
  let := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : IsScalarTower K P A := IsScalarTower.of_algHom g
  have hdim : ringKrullDim A = (d : WithBot ℕ∞) :=
    (integralExtension_ringKrullDim_eq P A).trans (by
      simp [P, ringKrullDim_eq_zero_of_field])
  have hzero : Algebra.trdeg P A = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htr : Algebra.trdeg K A = (d : Cardinal) := by
    simpa [hzero, P] using (trdeg_add_eq K P (A := A)).symm
  exact ⟨d, hdim, htr⟩

/-- A separately proved intrinsic transcendence degree identifies the
actual Krull dimension of a genuine finite-type domain. -/
theorem finiteTypeDomain_ringKrullDim_of_trdeg (d : ℕ)
    (hd : Algebra.trdeg K A = (d : Cardinal)) : ringKrullDim A = (d : WithBot ℕ∞) := by
  obtain ⟨a, ha, hatr⟩ := finiteTypeDomain_dimension_exists K A
  have he : a = d := by exact_mod_cast hatr.symm.trans hd
  exact he ▸ ha

end
end SGPT.Foundations.Schemes
