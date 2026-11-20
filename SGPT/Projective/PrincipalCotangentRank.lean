import SGPT.Projective.PrincipalCotangentSmooth
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual cotangent rank drop for the SAME original principal relation.
Blueprint: principal-cotangent-rank.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.PrincipalCotangentRank

open TensorProduct KaehlerDifferential Module
open scoped TensorProduct
open PrincipalCotangentSmooth

variable {k A B K : Type} [CommRing k] [CommRing A] [CommRing B] [Field K]
  [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Algebra B K] [Algebra A K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower k A K]
  [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]

/-- The ACTUAL original principal quotient has exactly one fewer genuine
cotangent dimension at the SAME actual field point, derived internally
from the original nonzero normal derivative and the true exact sequence. -/
theorem principal_quotient_cotangent_finrank
    (hAB : Function.Surjective (algebraMap A B))
    (g : A) (hI : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (D : Derivation k A K) (hD : D g ≠ 0) :
    finrank K (K ⊗[B] Ω[B⁄k]) = finrank A Ω[A⁄k] - 1 := by
  let : Nontrivial A := (algebraMap A K).domain_nontrivial
  let I := RingHom.ker (algebraMap A B)
  let u : K ⊗[A] I := 1 ⊗ₜ[A] principalGenerator I g hI
  let J := cotangentComplexBaseChange k B A K
  have hJu : J u ≠ 0 := by
    intro hz
    let F : K ⊗[A] Ω[A⁄k] →ₗ[K] K := D.liftKaehlerDifferential.liftBaseChange K
    have h := congrArg F hz
    apply hD
    simpa only [F, J, u, I, cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply,
      LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
      map_zero, principalGenerator] using h
  have hu : u ≠ 0 := fun hz => hJu (hz ▸ map_zero J)
  have hdimI : finrank K (K ⊗[A] I) = 1 := by
    apply (finrank_eq_one_iff_of_nonzero' u hu).mpr
    intro v
    obtain ⟨c, hc⟩ := tensor_principal_ideal_cyclic I g hI v
    exact ⟨c, hc.symm⟩
  have hJ : Function.Injective J :=
    injective_of_ne_principal_generator I g hI J hJu
  let P : Algebra.Extension k B := { Ring := A, σ := _, algebraMap_σ := Function.surjInv_eq hAB }
  let eV := AlgebraTensorModule.cancelBaseChange A B K K Ω[A⁄k]
  let eI := (AlgebraTensorModule.cancelBaseChange A B K K P.ker).symm ≪≫ₗ
    P.cotangentEquiv.baseChange (A := K)
  let F := P.cotangentComplex.baseChange K
  let G := P.toKaehler.baseChange K
  have hF : Function.Injective F := by
    dsimp only [F]
    rw [P.lTensor_cotangentComplex_eq_cotangentComplexBaseChange K]
    exact eV.symm.injective.comp (hJ.comp eI.symm.injective)
  have hdimC : finrank K (K ⊗[B] P.Cotangent) = 1 :=
    eI.finrank_eq.symm.trans hdimI
  have hexact : Function.Exact F G := by
    change Function.Exact (P.cotangentComplex.lTensor K) (P.toKaehler.lTensor K)
    exact lTensor_exact K P.exact_cotangentComplex_toKaehler P.toKaehler_surjective
  have hG : Function.Surjective G := LinearMap.lTensor_surjective K P.toKaehler_surjective
  let : Module.Finite K (K ⊗[B] P.CotangentSpace) :=
    Module.Finite.of_surjective eV.symm.toLinearMap eV.symm.surjective
  have hdimV : finrank K (K ⊗[B] P.CotangentSpace) = finrank A Ω[A⁄k] :=
    eV.finrank_eq.trans Module.finrank_baseChange
  have hker : finrank K G.ker = 1 := by
    rw [hexact.linearMap_ker_eq, LinearMap.finrank_range_of_inj hF, hdimC]
  have hdim := G.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hG, finrank_top, hker, hdimV] at hdim
  omega

end SGPT.Projective.NumEq.CompleteIntersections.PrincipalCotangentRank
