import SGPT.Projective.AlgebraicSmoothStalk
import SGPT.Foundations.Schemes.CotangentSmoothLocallyFree
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The ACTUAL original structural stalk cotangent rank, from genuine
original standard-smooth affine charts and exact localization.
Blueprint: algebraic-stalk-cotangent-rank.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Module
open scoped TensorProduct
open SGPT.Okounkov

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- Genuine standard-smooth affine coordinates prove actual ORIGINAL
stalk differential rank, through the SAME original germ localization. -/
theorem originalStalk_cotangent_finrank_of_chart
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (n : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op U)).hom) :
    letI := stalkComplexAlgebra f x
    finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] = n := by
  let R := Γ(X, U)
  let A := X.presheaf.stalk x
  let := affineChartAlgebra f U
  let := stalkComplexAlgebra f x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  let : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq fun c => by
    change X.presheaf.germ ⊤ x trivial
      (f.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
        X.presheaf.germ U x hx
          (X.presheaf.map U.leTop.op (f.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)))
    exact (X.presheaf.germ_res_apply U.leTop x hx _).symm
  let p := (hU.primeIdealOf (⟨x, hx⟩ : U)).asIdeal
  let : p.IsPrime := inferInstance
  let : IsLocalization.AtPrime A p := hU.isLocalization_stalk ⟨x, hx⟩
  let : Algebra.FormallyEtale R A := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  let : Nontrivial R := (algebraMap R A).domain_nontrivial
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ R := hs
  let : Algebra.IsStandardSmooth ℂ R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ R A
  calc
    finrank A Ω[A⁄ℂ] = finrank A (A ⊗[R] Ω[R⁄ℂ]) := e.finrank_eq.symm
    _ = finrank R Ω[R⁄ℂ] := Module.finrank_baseChange
    _ = n := by
      have hrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
        (R := ℂ) (S := R) n
      simp only [Module.finrank, hrank, Cardinal.toNat_natCast]

/-- Original prescribed relative dimension gives the actual rank of the
SAME original structural stalk differential module at EVERY scheme point. -/
theorem originalStalk_cotangent_finrank (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    letI := stalkComplexAlgebra f x
    finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] = n := by
  obtain ⟨U, hU, hx, hs⟩ := smooth_cotangent_affine_chart f n x
  exact originalStalk_cotangent_finrank_of_chart f U hU x hx n hs

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
