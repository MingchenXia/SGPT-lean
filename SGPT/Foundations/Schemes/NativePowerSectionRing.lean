import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison
import SGPT.Foundations.Schemes.SectionRingGenericEmbedding
import SGPT.Foundations.Schemes.PolynomialFiberPowerFiniteness
import Mathlib.Algebra.Polynomial.Expand
/-!
# NativePowerSectionRing

The actual iterated tensor comparison gives a genuine homomorphism from the full section ring of a tensor power to the original full section ring. Its literal generic polynomial triangle and positive-power injectivity are proved.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
open scoped DirectSum
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

private theorem inverse_global_frame_readback {X : Scheme.{u}} {M N : X.Modules}
    (E : M ≅ N) (U V : X.Opens) (i : U ⟶ V) {R : Type u}
    (α : bundleSections M U → R) (β : bundleSections N U → R)
    (hcoef : ∀ s, β (E.hom.val.app (.op U) s) = α s) (t : bundleSections N V) :
    α (M.val.map i.op (E.inv.val.app (.op V) t)) = β (N.val.map i.op t) := by
  rw [← hcoef, PresheafOfModules.naturality_apply]
  have h : E.hom.val.app (.op V) (E.inv.val.app (.op V) t) = t :=
    congr($(E.inv_hom_id).val.app (.op V) |>.hom t)
  rw [h]

variable {X : Scheme.{u}} (L : IntrinsicLineBundle X) (q : ℕ)

/-- The actual iterated tensor-power comparison sends genuine q-power sections to their original degree. -/
def IntrinsicLineBundle.nativePowerSection (m : ℕ) :
    bundlePowerGlobalSections (L.tensorPower q).sheaf m →+
      bundlePowerGlobalSections L.sheaf (q * m) :=
  ((nativeLineTensorPowerMulIso L.atlas q m).inv.val.app (.op ⊤)).hom.toAddMonoidHom

/-- Every actual subordinate chart coefficient is retained by the genuine power-section comparison. -/
theorem IntrinsicLineBundle.nativePowerSection_coefficients (m : ℕ) (i : L.atlas.I)
    (W : X.Opens) (h : W ⟶ L.atlas.opens i)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) :
    ((L.atlas.frame i).tensorPower (q * m)).coefficients h
      ((bundleTensorPower L.sheaf (q * m)).val.map W.leTop.op (L.nativePowerSection q m t)) =
    (((L.atlas.frame i).tensorPower q).tensorPower m).coefficients h
      ((bundleTensorPower (bundleTensorPower L.sheaf q) m).val.map W.leTop.op t) := by
  exact inverse_global_frame_readback (nativeLineTensorPowerMulIso L.atlas q m) W ⊤ W.leTop
    (((L.atlas.frame i).tensorPower (q * m)).coefficients h)
    ((((L.atlas.frame i).tensorPower q).tensorPower m).coefficients h)
    (fun s ↦ nativeLineTensorPowerMulIso_coefficients L.atlas q m i h s) t

variable [IsIntegral X]

/-- The actual same-frame generic coefficient is unchanged by the true iterated power comparison. -/
theorem IntrinsicLineBundle.nativePowerSection_genericCoefficient (m : ℕ)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) :
    L.genericCoefficient (q * m) (L.nativePowerSection q m t) =
      (L.tensorPower q).genericCoefficient m t := by
  rw [L.genericCoefficient_eq_germ, (L.tensorPower q).genericCoefficient_eq_germ]
  congr 1
  exact L.nativePowerSection_coefficients q m L.atlas.genericIndex _ (𝟙 _) t

/-- Genuine q-power sections give their actual homogeneous element in the full section ring. -/
def IntrinsicLineBundle.nativePowerSectionMonomial (m : ℕ) :
    bundlePowerGlobalSections (L.tensorPower q).sheaf m →+ L.sectionRing :=
  (L.ofSection (q * m)).comp (L.nativePowerSection q m)

/-- Its generic polynomial is the actual degree-qm monomial with the original genuine coefficient. -/
theorem IntrinsicLineBundle.nativePowerSectionMonomial_generic (m : ℕ)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) :
    L.genericPolynomial (L.nativePowerSectionMonomial q m t) =
      Polynomial.monomial (q * m) ((L.tensorPower q).genericCoefficient m t) := by
  exact (L.genericPolynomial_ofSection (q * m) _).trans
    (congrArg (Polynomial.monomial (q * m)) (L.nativePowerSection_genericCoefficient q m t))

/-- The actual full q-power section ring maps to the full original section ring by genuine tensor comparison. -/
def IntrinsicLineBundle.nativePowerSectionRingHom : (L.tensorPower q).sectionRing →+* L.sectionRing := by
  let := atlasPowerGradedCommRing (L.tensorPower q).atlas
  exact DirectSum.toSemiring (L.nativePowerSectionMonomial q)
    (by
      apply L.genericPolynomial_injective
      change L.genericPolynomial (L.nativePowerSectionMonomial q 0
        (bundlePowerGlobalOne (L.tensorPower q).sheaf)) = L.genericPolynomial 1
      rw [L.nativePowerSectionMonomial_generic, (L.tensorPower q).genericCoefficient_one,
        Nat.mul_zero, Polynomial.monomial_zero_one, L.genericPolynomial.map_one])
    (by
      intro m n s t
      apply L.genericPolynomial_injective
      change L.genericPolynomial (L.nativePowerSectionMonomial q (m + n)
        (atlasPowerGlobalMul (L.tensorPower q).atlas m n s t)) =
        L.genericPolynomial (L.nativePowerSectionMonomial q m s * L.nativePowerSectionMonomial q n t)
      rw [L.nativePowerSectionMonomial_generic, map_mul,
        L.nativePowerSectionMonomial_generic, L.nativePowerSectionMonomial_generic,
        (L.tensorPower q).genericCoefficient_mul, Polynomial.monomial_mul_monomial, Nat.mul_add])

/-- The true polynomial power coefficient map is ordinary polynomial expansion. -/
theorem polynomialFiberPowerHom_eq_expand (R : Type u) [CommRing R] (q : ℕ) :
    polynomialFiberPowerHom R q = (Polynomial.expand R q).toRingHom := rfl

/-- The literal polynomial coefficient map regrades genuine monomials by q. -/
theorem polynomialFiberPowerHom_monomial (R : Type u) [CommRing R] (q m : ℕ) (r : R) :
    polynomialFiberPowerHom R q (Polynomial.monomial m r) = Polynomial.monomial (q * m) r := by
  change Polynomial.expand R q (Polynomial.monomial m r) = _
  rw [Polynomial.expand_monomial, Nat.mul_comm m q]

/-- Positive polynomial powers are injective on the actual polynomial carrier. -/
theorem polynomialFiberPowerHom_injective (R : Type u) [CommRing R] (q : ℕ) (hq : 0 < q) :
    Function.Injective (polynomialFiberPowerHom R q) := Polynomial.expand_injective hq

/-- Every genuine homogeneous section retains its true tensor comparison and regraded inclusion. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_ofSection (m : ℕ)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) :
    L.nativePowerSectionRingHom q ((L.tensorPower q).ofSection m t) =
      L.ofSection (q * m) (L.nativePowerSection q m t) := by
  let := atlasPowerGradedCommRing (L.tensorPower q).atlas
  change DirectSum.toAddMonoid (L.nativePowerSectionMonomial q)
    (DirectSum.of (bundlePowerGlobalSections (L.tensorPower q).sheaf) m t) = _
  exact DirectSum.toAddMonoid_of _ m t

/-- The actual section-ring power map has its literal same-frame polynomial coefficient triangle. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_generic (x : (L.tensorPower q).sectionRing) :
    L.genericPolynomial (L.nativePowerSectionRingHom q x) =
      polynomialFiberPowerHom X.functionField q ((L.tensorPower q).genericPolynomial x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of m t =>
      change L.genericPolynomial (L.nativePowerSectionRingHom q ((L.tensorPower q).ofSection m t)) =
        polynomialFiberPowerHom X.functionField q
          ((L.tensorPower q).genericPolynomial ((L.tensorPower q).ofSection m t))
      rw [L.nativePowerSectionRingHom_ofSection, L.genericPolynomial_ofSection,
        L.nativePowerSection_genericCoefficient, (L.tensorPower q).genericPolynomial_ofSection,
        polynomialFiberPowerHom_monomial]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The genuine positive-power section-ring map is injective, derived from actual integral geometry. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_injective (hq : 0 < q) :
    Function.Injective (L.nativePowerSectionRingHom q) := by
  intro x y h
  apply (L.tensorPower q).genericPolynomial_injective
  apply polynomialFiberPowerHom_injective X.functionField q hq
  exact (L.nativePowerSectionRingHom_generic q x).symm.trans
    ((congrArg L.genericPolynomial h).trans (L.nativePowerSectionRingHom_generic q y))

end
end SGPT.Foundations.Schemes
