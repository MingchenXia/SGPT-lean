import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Kaehler.Basic

/-! Actual principal-relation cotangent injectivity and local quotient
smoothness from a genuine nonzero derivation of the SAME original relation.
Blueprint: principal-cotangent-smooth.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.PrincipalCotangentSmooth

open TensorProduct KaehlerDifferential IsLocalRing
open scoped TensorProduct

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- The genuine generator of the SAME actual principal ideal. -/
def principalGenerator (I : Ideal A) (g : A) (hI : I = Ideal.span {g}) : I :=
  ⟨g, by rw [hI]; exact Ideal.subset_span (Set.mem_singleton _)⟩

/-- Every actual tensor vector of the original principal ideal is an
actual scalar multiple of its SAME original generator. -/
theorem tensor_principal_ideal_cyclic (I : Ideal A) (g : A) (hI : I = Ideal.span {g})
    (x : K ⊗[A] I) :
    ∃ c : K, x = c • ((1 : K) ⊗ₜ[A] principalGenerator I g hI) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (zero_smul _ _).symm⟩
  | tmul a b =>
      have hbI : b.val ∈ Ideal.span ({g} : Set A) := hI ▸ b.property
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hbI
      have hb : b = d • principalGenerator I g hI := by
        apply Subtype.ext
        change b.val = d * g
        exact hd.trans (mul_comm g d)
      refine ⟨d • a, ?_⟩
      rw [hb, TensorProduct.tmul_smul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, (add_smul _ _ _).symm⟩

/-- A linear map on the actual base-changed principal ideal is injective
when it is nonzero on the SAME original genuine generator. -/
theorem injective_of_ne_principal_generator
    {V : Type} [AddCommGroup V] [Module K V]
    (I : Ideal A) (g : A) (hI : I = Ideal.span {g})
    (T : K ⊗[A] I →ₗ[K] V)
    (hT : T ((1 : K) ⊗ₜ[A] principalGenerator I g hI) ≠ 0) : Function.Injective T := by
  have hz : ∀ x, T x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := tensor_principal_ideal_cyclic I g hI x
    rw [map_smul] at hx
    have hc : c = 0 := (smul_eq_zero.mp hx).resolve_right hT
    rw [hc, zero_smul]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hxy, sub_self]

section LocalQuotient

variable {k A B K : Type} [CommRing k] [CommRing A] [CommRing B] [IsLocalRing B] [Field K]
  [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Algebra B K] [Algebra A K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower k A K]
  [Algebra.FormallySmooth k A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]

/-- An ACTUAL nonzero derivative of the SAME original principal relation
proves original quotient formal smoothness by the genuine local Jacobian
criterion. No quotient regularity or cotangent injection is a premise. -/
theorem formallySmooth_of_principal_relation_derivation
    (hAB : Function.Surjective (algebraMap A B))
    (g : A) (hI : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (D : Derivation k A K) (hD : D g ≠ 0)
    (hBK : maximalIdeal B ≤ RingHom.ker (algebraMap B K)) : Algebra.FormallySmooth k B := by
  have hfg : (RingHom.ker (algebraMap A B)).FG := by
    rw [hI]
    exact Submodule.fg_span_singleton g
  apply (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange A K hAB hfg hBK).mpr
  apply injective_of_ne_principal_generator (RingHom.ker (algebraMap A B)) g hI
    (cotangentComplexBaseChange k B A K)
  intro hzero
  let F : K ⊗[A] Ω[A⁄k] →ₗ[K] K := D.liftKaehlerDifferential.liftBaseChange K
  have h := congrArg F hzero
  apply hD
  simpa only [F, cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply,
    LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    map_zero, principalGenerator] using h

end LocalQuotient
end SGPT.Projective.NumEq.CompleteIntersections.PrincipalCotangentSmooth
