import SGPT.Unibranch.NativeNov16AmbientFormRestriction

/-!
# Kähler spaces

The book (`appendix_unibranch.tex`, `sec:unib_ext`, `def:unibranch:L212`, `cor:PSH`)
works on *compact Kähler spaces*: reduced complex spaces carrying a Kähler form, i.e. a smooth
closed real `(1,1)`-form which near every point is the restriction, under a local embedding
`V ↪ Ω ⊆ ℂ^N`, of a Kähler form of `Ω` (equivalently: has local smooth strictly psh potentials
`θ = (ddᶜ g)|_V`).

The project already has this notion of Kähler form on a complex space:
`SGPT.Unibranch.SpaceForm.IsKahler` (one ambient representative, smooth, closed, of type
`(1,1)` and strictly positive, restricting to the form).  This file only names the resulting
notion of Kähler space, so that every lane uses the same one:

* `SourceReducedComplexSpace.IsKahlerSpace X`: `X` carries a Kähler form;
* `isKahlerSpace_ofClosedAnalytic`: a closed analytic subspace of a Kähler manifold is a Kähler
  space; in particular (`isKahlerSpace_wholeModel`) a Kähler manifold is a Kähler space.

A *compact Kähler space* is `CompactSpace X.obj.left ∧ X.IsKahlerSpace`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch

namespace SourceReducedComplexSpace

/-- **Kähler spaces.**  A complex space is a *Kähler space* if it carries a Kähler form: a smooth
real `2`-form which near every point is the restriction of a smooth closed strictly positive
`(1,1)`-form on the ambient domain of a local embedding (`SpaceForm.IsKahler`). -/
def IsKahlerSpace (X : SourceReducedComplexSpace) : Prop :=
  ∃ ω : SpaceForm X 2, ω.IsKahler

end SourceReducedComplexSpace

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A closed analytic subspace of a Kähler manifold is a Kähler space (with the restricted Kähler
form). -/
theorem isKahlerSpace_ofClosedAnalytic (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (omega : KahlerBackground n M) :
    (SourceReducedComplexSpace.ofClosedAnalytic C hC).IsKahlerSpace :=
  ⟨SpaceForm.ofClosedAnalytic C hC omega.form.val, SpaceForm.ofClosedAnalytic_isKahler C hC omega⟩

/-- A Kähler manifold, viewed as the complex space `(M, 𝒪_M)`, is a Kähler space. -/
theorem isKahlerSpace_wholeModel (omega : KahlerBackground n M) :
    (SourceReducedComplexSpace.ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n))).IsKahlerSpace :=
  isKahlerSpace_ofClosedAnalytic _ _ omega

end SGPT.Unibranch
