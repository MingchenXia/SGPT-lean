import SGPT.Unibranch.GAGA2Henselian
import SGPT.Unibranch.GAGAUnibranchAffineModel

/-!
# Unibranch complex spaces are the locally irreducible ones

Every stalk of an original reduced complex space (`SourceReducedComplexSpace`) is, through an
actual model open immersion and the chart identification
`actualSubspaceStalkChartEquiv`, a quotient `𝒪_{ℂⁿ,0}/J` of the ring of holomorphic germs.
Hence it has distinguished factorizations (Weierstrass preparation) and is Henselian, and by
`HasDistinguishedFactorization.sourceUnibranchReducedRing_iff`:

* `SourceReducedComplexSpace.henselianLocalRing_stalk`: analytic local rings are Henselian;
* `SourceReducedComplexSpace.isUnibranch_iff_isDomain_stalks`: a reduced complex space is
  unibranch (`def:unibranch:L21`) iff all its local rings are domains, i.e. iff it is locally
  irreducible. This is the identification of the book's unibranchness with the "local
  irreducibility" of [CAS] mentioned after `def:unibranch:L21`;
* `polynomialZeroSetComplexSpace_isUnibranch_iff`: for the embedded affine complex space
  `V(I) ⊆ ℂⁿ` this says that every germ vanishing ideal `modelStalkIdeal I x` is prime.

With this, the remaining implication "`𝒳` unibranch ⟹ `𝒳^An` unibranch" of
`prop:unibranch_gaga` at a closed point is the statement that the analytic germ of `𝒳` there
is irreducible.

Blueprint: `claude-serre-gaga.tex`.
-/

set_option autoImplicit false

open TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces (modelOver)
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace (actualSubspaceStalkChartEquiv)

namespace SGPT.Unibranch

noncomputable section

/-- Every stalk of an original reduced complex space has distinguished factorizations: it is
isomorphic to a quotient of the ring of holomorphic germs `𝒪_{ℂⁿ,0}`. -/
theorem SourceReducedComplexSpace.hasDistinguishedFactorization_stalk
    (X : SourceReducedComplexSpace) (x : X.obj.left) :
    HasDistinguishedFactorization (X.obj.left.presheaf.stalk x).carrier := by
  obtain ⟨n, U, C, _hC, i, hi, _hpoint, c, hcx⟩ := X.property.2.2 x
  subst x
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let e₁ := (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv
  let e₂ := actualSubspaceStalkChartEquiv (n := n) C c
  refine (hasDistinguishedFactorization_holGerm (ComplexModel n)).of_surjective
    ((e₁.symm.toRingHom.comp e₂.symm.toRingHom).comp (Ideal.Quotient.mk _)) ?_
  exact (e₁.symm.surjective.comp e₂.symm.surjective).comp Ideal.Quotient.mk_surjective

/-- **Analytic local rings are Henselian.** -/
theorem SourceReducedComplexSpace.henselianLocalRing_stalk (X : SourceReducedComplexSpace)
    (x : X.obj.left) : HenselianLocalRing (X.obj.left.presheaf.stalk x).carrier :=
  (X.hasDistinguishedFactorization_stalk x).henselianLocalRing

/-- At a single point: the stalk is unibranch iff it is a domain. -/
theorem SourceReducedComplexSpace.sourceUnibranchReducedRing_stalk_iff
    (X : SourceReducedComplexSpace) (x : X.obj.left) :
    SourceUnibranchReducedRing (X.obj.left.presheaf.stalk x).carrier ↔
      IsDomain (X.obj.left.presheaf.stalk x).carrier :=
  (X.hasDistinguishedFactorization_stalk x).sourceUnibranchReducedRing_iff

/-- **Unibranch = locally irreducible.** A reduced complex space is unibranch
(`def:unibranch:L21`) iff every local ring `𝒪_{X,x}` is a domain. -/
theorem SourceReducedComplexSpace.isUnibranch_iff_isDomain_stalks
    (X : SourceReducedComplexSpace) :
    X.IsUnibranch ↔ ∀ x : X.obj.left, IsDomain (X.obj.left.presheaf.stalk x).carrier :=
  forall_congr' fun x => X.sourceUnibranchReducedRing_stalk_iff x

variable {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))

/-- **The embedded affine complex space `V(I)`.** It is unibranch iff at every point
`x ∈ V(I)` the germ vanishing ideal `modelStalkIdeal I x ⊆ 𝒪_{ℂⁿ,x}` is prime, i.e. iff the
analytic germ of `V(I)` at every point is irreducible. -/
theorem polynomialZeroSetComplexSpace_isUnibranch_iff :
    (polynomialZeroSetComplexSpace I).IsUnibranch ↔
      ∀ x : polynomialZeroSet I, (modelStalkIdeal I x.val).IsPrime := by
  rw [SourceReducedComplexSpace.isUnibranch_iff_isDomain_stalks]
  exact forall_congr' fun x =>
    ((modelStalkEquiv I x).toMulEquiv.isDomain_iff).trans (Ideal.Quotient.isDomain_iff_prime _)

end

end SGPT.Unibranch
