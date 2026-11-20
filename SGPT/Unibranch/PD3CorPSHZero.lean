import SGPT.Unibranch.PD3Forward
import SGPT.Unibranch.PDFNReduction

/-!
# `cor:PSH` for `θ = 0`: the pull-back bijection `PSH(X) ≃ PSH(Y)`

Source `cor:PSH` (Appendix B, `appendix_unibranch.tex`) for `θ = 0`: for a proper bimeromorphic
morphism `π : Y → X` onto a unibranch complex space, `v ↦ π^*v = v ∘ π` is a bijection
`PSH(X) → PSH(Y)` (compactness and Kähler hypotheses are not needed).

* forward map: `PD3.isPSH_comp_of_isProperBimeromorphic` (global component clause on the possibly
  singular `Y`, this lane);
* inverse: the unique psh descent `PD.existsUnique_psh_descent` (lane PD, via `thm:FN`).

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set CategoryTheory

namespace SGPT.Unibranch.PD3

open SourceReducedComplexSpace

/-- The pull-back map `π^* : PSH(X) → PSH(Y)`, `v ↦ v ∘ π`, for `π` proper bimeromorphic onto a
unibranch complex space. -/
noncomputable def pshPullback {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    {v : X.obj.left → EReal // X.IsPSH v} → {u : Y.obj.left → EReal // Y.IsPSH u} :=
  fun v => ⟨fun y => v.1 (π.hom.left.base y), isPSH_comp_of_isProperBimeromorphic π hπ hX v.2⟩

theorem pshPullback_apply {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) (v : {v : X.obj.left → EReal // X.IsPSH v})
    (y : Y.obj.left) : (pshPullback π hπ hX v).1 y = v.1 (π.hom.left.base y) := rfl

/-- **Source `cor:PSH`, `θ = 0`.** For a proper bimeromorphic morphism `π : Y → X` onto a
unibranch complex space, the pull-back `π^* : PSH(X) → PSH(Y)` is a bijection. -/
theorem pshPullback_bijective {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    Function.Bijective (pshPullback π hπ hX) := by
  refine ⟨fun v w h => Subtype.ext (pullback_injective π hπ (congrArg Subtype.val h)), ?_⟩
  intro u
  obtain ⟨v, ⟨hv, hvu⟩, -⟩ := PD.existsUnique_psh_descent π hπ hX u.2
  exact ⟨⟨v, hv⟩, Subtype.ext (funext hvu)⟩

/-- **Source `cor:PSH`, `θ = 0`**, as an equivalence `PSH(X) ≃ PSH(Y)`. -/
noncomputable def pshPullbackEquiv {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    {v : X.obj.left → EReal // X.IsPSH v} ≃ {u : Y.obj.left → EReal // Y.IsPSH u} :=
  Equiv.ofBijective _ (pshPullback_bijective π hπ hX)

end SGPT.Unibranch.PD3
