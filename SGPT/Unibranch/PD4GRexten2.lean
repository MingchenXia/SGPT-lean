import SGPT.Unibranch.PD4Metrizable
import SGPT.Unibranch.PD3CodimTwo
import SGPT.Unibranch.HironakaG11BlowupLocality

/-!
# The Grauert--Remmert extension theorem for the open subspace `X \ Z`

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`):

> Let `X` be a unibranch complex space, let `Z` be an analytic subset in `X`, and let
> `φ ∈ PSH(X \ Z)`. Then the function `φ` admits an extension to `PSH(X)` in the following two
> cases: (1) the set `Z` has codimension at least `2` everywhere; (2) the set `Z` has codimension
> at least `1` everywhere and `φ` is locally bounded from above on an open neighborhood of `Z`.
> In both cases, the extension is unique and is given by
> `φ(x) = limsup_{X \ Z ∋ y → x} φ(y)`, `x ∈ X` (`eq:GRextvarphi`).

Lane PD3 proved it (`PD3.grauertRemmert_extension`) for `X \ Z` realized by any open immersion
`j : W → X` with image `Zᶜ`. Here `X \ Z` is the library's open subspace
`HironakaG11BlowupLocality.openSubspace X V` on the open set `V = Zᶜ`, which is a complex space
because every open subset of a complex space is paracompact (`PD4.paracompactSpace_opens`, via
metrizability of complex spaces, `PD4Metrizable`); `φ` is a function on the points of `X \ Z`.

* `grauertRemmert_extension_openSubspace`: PD3's statement applied to the library open subspace
  (its inclusion is an open immersion with image `Zᶜ`), for `φ : X → [-∞, ∞]`.
* `grauertRemmert_extension`: the book's form, `φ ∈ PSH(X \ Z)` a function on `X \ Z`, item (2)
  with "locally bounded from above on an open neighbourhood of `Z`" verbatim; existence of
  `η ∈ PSH(X)` with `η|_{X \ Z} = φ`, uniqueness and `eq:GRextvarphi`
  (`η x = limsup φ (comap ι (𝓝 x))`, `ι : X \ Z → X` the inclusion).

Lane PD4, blueprint `pd4.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.PD4

open SourceReducedComplexSpace HironakaG11BlowupLocality

/-- **`thm:GRexten2` for the library's open subspace `X \ Z`** (functions on `X`; the values of `φ`
on `Z` are irrelevant). For `X` unibranch, `Z` analytic, `φ|_{X \ Z} ∈ PSH(X \ Z)`, and (1) `Z` of
codimension `≥ 2` everywhere, or (2) `interior Z = ∅` and `φ` bounded above near every point of `Z`:
a psh extension exists, it is unique, and every extension is given by `eq:GRextvarphi`. -/
theorem grauertRemmert_extension_openSubspace {X : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) {φ : X.obj.left → EReal}
    (hφ : (openSubspace X ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).IsPSH
      (fun w => φ ((openSubspaceInclusion X ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).hom.left.base w)))
    (hcase : PD3.HasCodimAtLeastTwo X Z ∨
      (interior Z = ∅ ∧ ∀ x ∈ Z, ∃ Nb ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ y ≤ C)) :
    (∃ η : X.obj.left → EReal, X.IsPSH η ∧ EqOn η φ Zᶜ) ∧
      (∀ η₁ η₂ : X.obj.left → EReal, X.IsPSH η₁ → EqOn η₁ φ Zᶜ → X.IsPSH η₂ →
        EqOn η₂ φ Zᶜ → η₁ = η₂) ∧
      ∀ η : X.obj.left → EReal, X.IsPSH η → EqOn η φ Zᶜ →
        ∀ x, η x = limsup φ (𝓝[Zᶜ] x) :=
  PD3.grauertRemmert_extension hX hZ (openSubspaceInclusion X _) inferInstance
    (range_openSubspaceInclusion X _) hφ hcase

/-- **Source `thm:GRexten2` (Grauert--Remmert), the book's form.** Let `X` be a unibranch complex
space, `Z ⊆ X` an analytic subset, `X \ Z` the open subspace of `X` on the open set `V = Zᶜ`
(`HironakaG11BlowupLocality.openSubspace`, with inclusion `ι`), and `φ ∈ PSH(X \ Z)`. Assume
(1) `Z` has codimension at least `2` everywhere (`PD3.HasCodimAtLeastTwo`), or (2) `Z` has
codimension at least `1` everywhere (`interior Z = ∅`) and `φ` is locally bounded from above on an
open neighbourhood `U` of `Z` (every point of `U` has a neighbourhood `N` and `C` with `φ ≤ C` on
`ι⁻¹ N`). Then `φ` admits an extension `η ∈ PSH(X)` (`η ∘ ι = φ`); the extension is unique; and
every extension is given by `eq:GRextvarphi`: `η(x) = limsup_{X \ Z ∋ y → x} φ(y)` for all
`x ∈ X`. -/
theorem grauertRemmert_extension {X : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (V : Opens X.obj.left)
    (hV : (V : Set X.obj.left) = Zᶜ) {φ : (openSubspace X V).obj.left → EReal}
    (hφ : (openSubspace X V).IsPSH φ)
    (hcase : PD3.HasCodimAtLeastTwo X Z ∨
      (interior Z = ∅ ∧ ∃ U : Set X.obj.left, IsOpen U ∧ Z ⊆ U ∧ ∀ y ∈ U, ∃ Nb ∈ 𝓝 y,
        ∃ C : ℝ, ∀ w, (openSubspaceInclusion X V).hom.left.base w ∈ Nb → φ w ≤ C)) :
    (∃ η : X.obj.left → EReal, X.IsPSH η ∧
        ∀ w, η ((openSubspaceInclusion X V).hom.left.base w) = φ w) ∧
      (∀ η₁ η₂ : X.obj.left → EReal,
        X.IsPSH η₁ → (∀ w, η₁ ((openSubspaceInclusion X V).hom.left.base w) = φ w) →
        X.IsPSH η₂ → (∀ w, η₂ ((openSubspaceInclusion X V).hom.left.base w) = φ w) →
        η₁ = η₂) ∧
      ∀ η : X.obj.left → EReal, X.IsPSH η →
        (∀ w, η ((openSubspaceInclusion X V).hom.left.base w) = φ w) →
        ∀ x, η x = limsup φ (comap (openSubspaceInclusion X V).hom.left.base (𝓝 x)) := by
  set ι := (openSubspaceInclusion X V).hom.left.base with hι
  have hιi : Function.Injective ι :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion
      (openSubspaceInclusion X V).hom.left).base_open.injective
  have hιr : range ι = Zᶜ := (range_openSubspaceInclusion X V).trans hV
  -- `φ` as a function on `X` (values on `Z` irrelevant)
  let φ' : X.obj.left → EReal := Function.extend ι φ ⊥
  have hφ'ι : ∀ w, φ' (ι w) = φ w := fun w => hιi.extend_apply φ ⊥ w
  have hφ'comp : (fun w => φ' (ι w)) = φ := funext hφ'ι
  have hφ' : (openSubspace X V).IsPSH (fun w => φ' (ι w)) :=
    (congrArg (openSubspace X V).IsPSH hφ'comp).mpr hφ
  have hcase' : PD3.HasCodimAtLeastTwo X Z ∨
      (interior Z = ∅ ∧ ∀ x ∈ Z, ∃ Nb ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ' y ≤ C) := by
    refine hcase.imp id fun ⟨hZi, U, _, hZU, hb⟩ => ⟨hZi, fun x hx => ?_⟩
    obtain ⟨Nb, hNb, C, hC⟩ := hb x (hZU hx)
    refine ⟨Nb, hNb, C, fun y hy hyZ => ?_⟩
    obtain ⟨w, rfl⟩ : y ∈ range ι := hιr ▸ hyZ
    rw [hφ'ι]
    exact hC w hy
  obtain ⟨⟨η, hη, hηφ⟩, huniq, hform⟩ :=
    PD3.grauertRemmert_extension hX hZ (openSubspaceInclusion X V) inferInstance hιr hφ' hcase'
  have heqOn : ∀ η : X.obj.left → EReal, (∀ w, η (ι w) = φ w) → EqOn η φ' Zᶜ := by
    intro η h y hy
    obtain ⟨w, rfl⟩ : y ∈ range ι := hιr ▸ hy
    rw [h w, hφ'ι]
  have hnhds : ∀ x, 𝓝[Zᶜ] x = map ι (comap ι (𝓝 x)) := fun x => by
    rw [map_comap, hιr]
    rfl
  refine ⟨⟨η, hη, fun w => ?_⟩, fun η₁ η₂ h₁ e₁ h₂ e₂ =>
    huniq η₁ η₂ h₁ (heqOn η₁ e₁) h₂ (heqOn η₂ e₂), fun η' hη' hη'φ x => ?_⟩
  · rw [hηφ (show ι w ∈ Zᶜ from hιr ▸ mem_range_self w), hφ'ι]
  · rw [hform η' hη' (heqOn η' hη'φ) x, hnhds x, ← limsup_comp, ← hφ'comp]
    rfl

/-- `thm:GRexten2` in the book's form, as unique existence of the extension. -/
theorem existsUnique_grauertRemmert_extension {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (V : Opens X.obj.left)
    (hV : (V : Set X.obj.left) = Zᶜ) {φ : (openSubspace X V).obj.left → EReal}
    (hφ : (openSubspace X V).IsPSH φ)
    (hcase : PD3.HasCodimAtLeastTwo X Z ∨
      (interior Z = ∅ ∧ ∃ U : Set X.obj.left, IsOpen U ∧ Z ⊆ U ∧ ∀ y ∈ U, ∃ Nb ∈ 𝓝 y,
        ∃ C : ℝ, ∀ w, (openSubspaceInclusion X V).hom.left.base w ∈ Nb → φ w ≤ C)) :
    ∃! η : X.obj.left → EReal, X.IsPSH η ∧
      ∀ w, η ((openSubspaceInclusion X V).hom.left.base w) = φ w := by
  obtain ⟨⟨η, hη, hηφ⟩, huniq, -⟩ := grauertRemmert_extension hX hZ V hV hφ hcase
  exact ⟨η, ⟨hη, hηφ⟩, fun η' h' => huniq η' η h'.1 h'.2 hη hηφ⟩

/-- PD3's item (2) for the canonical open subspace (`PD3.grauertRemmert_extension_bounded_openSubspace`
asks for the paracompactness of `Zᶜ` as an instance): the instance is now automatic. -/
theorem existsUnique_grauertRemmert_extension_bounded_openSubspace
    {X : SourceReducedComplexSpace} (hX : X.IsUnibranch) {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) {φ : X.obj.left → EReal}
    (hφ : (openSubspace X ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).IsPSH
      (fun w => φ ((openSubspaceInclusion X ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).hom.left.base w)))
    (hb : ∀ x ∈ Z, ∃ Nb ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ y ≤ C) :
    ∃! η : X.obj.left → EReal, X.IsPSH η ∧ EqOn η φ Zᶜ :=
  PD3.existsUnique_grauertRemmert_extension_bounded hX hZ hZi _ inferInstance
    (range_openSubspaceInclusion X _) hφ hb

end SGPT.Unibranch.PD4
