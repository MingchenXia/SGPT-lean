import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Genuine finite-colength cancellation through actual nested quotients.
This supplies the original affine normalization principal quotient bridge;
no infinite affine dimension or desired colength equality is supplied.
Blueprint: original-finite-colength-cancellation.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- ACTUAL first-isomorphism quotient reader for the image of a subspace
inside the SAME actual quotient ambient vector space. -/
def originalNestedQuotientImageEquiv (P Q : Submodule k V) :
    (P ⧸ Q.comap P.subtype) ≃ₗ[k] P.map Q.mkQ := by
  let f := Q.mkQ.comp P.subtype
  have hk : f.ker = Q.comap P.subtype := by simp only [f,LinearMap.ker_comp,Submodule.ker_mkQ]
  have hr : f.range = P.map Q.mkQ := by
    dsimp only [f]
    rw [LinearMap.range_comp,Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

/-- Genuine finite nested quotient arithmetic cancels the SAME finite
correction across TWO actual chains, without finite ambient V. -/
theorem originalTwoChainColength_cancel (P Q T : Submodule k V)
    (hQP : Q ≤ P) (hQT : Q ≤ T)
    [Module.Finite k (V ⧸ P)] [Module.Finite k (P ⧸ Q.comap P.subtype)]
    (e : (V ⧸ P) ≃ₗ[k] T ⧸ Q.comap T.subtype) :
    Module.Finite k (V ⧸ T) ∧
      Module.finrank k (P ⧸ Q.comap P.subtype) = Module.finrank k (V ⧸ T) := by
  let P' := P.map Q.mkQ
  let T' := T.map Q.mkQ
  let : Module.Finite k P' := Module.Finite.equiv (originalNestedQuotientImageEquiv P Q)
  let : Module.Finite k ((V ⧸ Q) ⧸ P') := Module.Finite.equiv
    (Submodule.quotientQuotientEquivQuotient Q P hQP).symm
  let : Module.Finite k (V ⧸ Q) := Module.Finite.of_submodule_quotient P'
  let : Module.Finite k (V ⧸ T) := Module.Finite.equiv
    (Submodule.quotientQuotientEquivQuotient Q T hQT)
  refine ⟨inferInstance,?_⟩
  have hp := P'.finrank_quotient_add_finrank
  have ht := T'.finrank_quotient_add_finrank
  rw [(Submodule.quotientQuotientEquivQuotient Q P hQP).finrank_eq,
    ← (originalNestedQuotientImageEquiv P Q).finrank_eq] at hp
  rw [(Submodule.quotientQuotientEquivQuotient Q T hQT).finrank_eq,
    ← (originalNestedQuotientImageEquiv T Q).finrank_eq,← e.finrank_eq] at ht
  omega

/-- Actual injectivity and SAME image maps manufacture colength equality
across a true finite-colength original subspace. No index equality input. -/
theorem originalInjectiveOperator_finiteColength (P : Submodule k V)
    (u : V →ₗ[k] V) (hu : Function.Injective u) (hP : P.map u ≤ P)
    [Module.Finite k (V ⧸ P)]
    [Module.Finite k (P ⧸ (P.map u).comap P.subtype)] :
    Module.Finite k (V ⧸ u.range) ∧
      Module.finrank k (P ⧸ (P.map u).comap P.subtype) = Module.finrank k (V ⧸ u.range) := by
  let e := LinearEquiv.ofInjective u hu
  have he : P.map e.toLinearMap = (P.map u).comap u.range.subtype := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      refine ⟨a,ha,?_⟩
      exact Subtype.ext hax
  let eqv := Submodule.Quotient.equiv P ((P.map u).comap u.range.subtype) e he
  exact originalTwoChainColength_cancel P (P.map u) u.range hP
    (by rintro _ ⟨a,_,rfl⟩; exact ⟨a,rfl⟩) eqv

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
