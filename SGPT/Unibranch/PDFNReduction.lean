import SGPT.Unibranch.ComplexSpaceProperFNDescent
import SGPT.Unibranch.MiscMFornaessNarasimhanManifold
import SGPT.Unibranch.FNHFinal

/-!
# The reverse descent of `cor:PSH` reduces to the Fornæss--Narasimhan theorem

`FornaessNarasimhanReverse X` is the implication (2) ⇒ (1) of `thm:FN` on the complex space `X`,
stated verbatim: an upper semicontinuous `φ : X → [-∞, ∞)`, not identically `-∞` on any
irreducible component, whose pull-back by every holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` is
subharmonic, is plurisubharmonic. It is proved on spaces with domain charts, in particular on
complex manifolds (`fornaessNarasimhanReverse_of_hasDomainCharts`), and on every complex space by
the Fornæss--Narasimhan theorem [FN80, Thm. 5.3.1] (`FNH.isPSH_of_disc`,
`fornaessNarasimhanReverse`).

`existsUnique_psh_descent_of_fornaessNarasimhanReverse`: for a proper bimeromorphic `π : Y → X`
onto a unibranch space on which `FornaessNarasimhanReverse` holds, every `u ∈ PSH(Y)` is `v ∘ π`
for a unique `v ∈ PSH(X)`. This is the case `θ = 0` of the surjectivity in `cor:PSH`; all other
ingredients (connected fibres, fibre constancy, the upper semicontinuous descent, the ramified
lifting of discs through `π` and the resulting disc criterion) are existing theorems, so
`thm:FN` (2) ⇒ (1) on singular spaces was exactly what remained; with it,
`existsUnique_psh_descent` is unconditional.

Lane PD, blueprint `pd.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric CategoryTheory

namespace SGPT.Unibranch.PD

open SourceReducedComplexSpace

/-- Source `thm:FN`, implication (2) ⇒ (1), on the complex space `X`, as a proposition. -/
def FornaessNarasimhanReverse (X : SourceReducedComplexSpace) : Prop :=
  ∀ φ : X.obj.left → EReal, (∀ x, φ x ≠ ⊤) →
    (∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) →
    UpperSemicontinuous φ →
    (∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) →
    X.IsPSH φ

/-- `thm:FN` (2) ⇒ (1) holds on complex spaces with domain charts (e.g. manifolds). -/
theorem fornaessNarasimhanReverse_of_hasDomainCharts {X : SourceReducedComplexSpace}
    (hX : X.HasDomainCharts) : FornaessNarasimhanReverse X :=
  fun _ htop hcomp husc hdisc => isPSH_of_disc_of_hasDomainCharts hX htop hcomp husc hdisc

/-- **Reduction of `cor:PSH` (`θ = 0`) to `thm:FN`.** If `thm:FN` (2) ⇒ (1) holds on the unibranch
space `X`, then for every proper bimeromorphic `π : Y → X` every `u ∈ PSH(Y)` is the pull-back of
a unique `v ∈ PSH(X)`. -/
theorem existsUnique_psh_descent_of_fornaessNarasimhanReverse {X Y : SourceReducedComplexSpace}
    (hFN : FornaessNarasimhanReverse X) (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) {u : Y.obj.left → EReal} (hu : Y.IsPSH u) :
    ∃! v : X.obj.left → EReal, X.IsPSH v ∧ ∀ y, v (π.hom.left.base y) = u y := by
  obtain ⟨v, ⟨htop, hcomp, husc, hvu, hdisc⟩, -⟩ :=
    hu.exists_unique_usc_descent_with_original_FN_hypotheses π hπ hX
  refine ⟨v, ⟨hFN v htop hcomp husc hdisc, hvu⟩, ?_⟩
  intro w hw
  funext x
  obtain ⟨y, rfl⟩ := hπ.surjective x
  rw [hw.2 y, hvu y]

/-- `thm:FN` (2) ⇒ (1) holds on every complex space (lanes FNR/FNL/FNS/FNA/FNP/FNH,
`FNH.isPSH_of_disc`). -/
theorem fornaessNarasimhanReverse (X : SourceReducedComplexSpace) : FornaessNarasimhanReverse X :=
  fun _ htop hcomp husc hdisc => FNH.isPSH_of_disc htop hcomp husc hdisc

/-- **Source `cor:PSH` for `θ = 0`, surjectivity and uniqueness of the descent.** For a proper
bimeromorphic `π : Y → X` onto a unibranch complex space, every `u ∈ PSH(Y)` is the pull-back
`v ∘ π` of a unique `v ∈ PSH(X)`. -/
theorem existsUnique_psh_descent {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) {u : Y.obj.left → EReal}
    (hu : Y.IsPSH u) :
    ∃! v : X.obj.left → EReal, X.IsPSH v ∧ ∀ y, v (π.hom.left.base y) = u y :=
  existsUnique_psh_descent_of_fornaessNarasimhanReverse (fornaessNarasimhanReverse X) π hπ hX hu

end SGPT.Unibranch.PD
