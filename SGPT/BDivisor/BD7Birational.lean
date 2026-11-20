import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# a birational morphism is an isomorphism over a nonempty open

Source: `rmk:bdiv:L749` (Dang–Favre's models are the normal projective varieties with a birational
morphism to `X`).  A morphism `ρ : Y → X` of integral schemes is *birational* (Stacks 01RO) if it
maps the generic point to the generic point and induces an isomorphism of the local rings there,
i.e. of the function fields.  For `ρ` locally of finite type and separated (e.g. a morphism of
varieties) this implies that `ρ` is an isomorphism over a nonempty open subset of `X`:

* `exists_isIso_morphismRestrict_of_isIso_stalkMap`: if `ρ.stalkMap (genericPoint Y)` is an
  isomorphism, then `ρ ∣_ U` is an isomorphism for some nonempty open `U ⊆ X`.

Proof: the inverse of the local ring map spreads out (Mathlib's `PartialMap.ofFromSpecStalk`) to a
section `ψ : U → ρ⁻¹(U)` of `ρ` over a dense open `U`; a section of a separated morphism is a closed
immersion, it hits the generic point of the irreducible `ρ⁻¹(U)`, so it is surjective, hence an
isomorphism onto the reduced `ρ⁻¹(U)`, and `ρ ∣_ U` is its inverse.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry IsLocalRing

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (ρ : Y ⟶ X)

/-- **A birational morphism is an isomorphism over a nonempty open.**  Let `ρ : Y → X` be a
morphism of integral schemes, locally of finite type and separated, inducing an isomorphism of
local rings `𝒪_{X, ρ(η_Y)} ≅ 𝒪_{Y, η_Y} = ℂ(Y)` at the generic point `η_Y` of `Y`.  Then there is a
nonempty open `U ⊆ X` over which `ρ` is an isomorphism (`ρ ∣_ U : ρ⁻¹(U) ≅ U`). -/
theorem exists_isIso_morphismRestrict_of_isIso_stalkMap [LocallyOfFiniteType ρ]
    [IsSeparated ρ] [IsIso (ρ.stalkMap (genericPoint Y))] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (ρ ∣_ U) := by
  set η := genericPoint Y with hη
  set x := ρ η with hx
  let s := ρ.stalkMap η
  -- the inverse of the local ring map, as a morphism `Spec 𝒪_{X,x} → Y` over `X`
  let φ : Spec (X.presheaf.stalk x) ⟶ Y := Spec.map (inv s) ≫ Y.fromSpecStalk η
  have hφ : φ ≫ ρ = X.fromSpecStalk x ≫ 𝟙 X := by
    simp only [φ, Category.assoc, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk ρ (x := η), ← Category.assoc, ← Spec.map_comp,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  -- spread it out to a section `ψ` of `ρ` over a dense open `U₀ ∋ x`
  let ψ := Scheme.PartialMap.ofFromSpecStalk (𝟙 X) ρ φ hφ
  have hψ : ψ.hom ≫ ρ = ψ.domain.ι := by
    simpa using Scheme.PartialMap.ofFromSpecStalk_comp (𝟙 X) ρ φ hφ
  have hxU : x ∈ ψ.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk (𝟙 X) ρ φ hφ
  have hψφ : ψ.domain.fromSpecStalkOfMem x hxU ≫ ψ.hom = φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (𝟙 X) ρ φ hφ
  set U₀ := ψ.domain
  set W₀ := ρ ⁻¹ᵁ U₀
  -- `ψ` lands in `ρ⁻¹(U₀)`
  have hrange : Set.range ψ.hom.base ⊆ Set.range W₀.ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ρ (ψ.hom u) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hψ]
    have hu := Set.mem_range_self (f := U₀.ι.base) u
    rwa [Scheme.Opens.range_ι] at hu
  let ψ' : U₀.toScheme ⟶ W₀.toScheme := IsOpenImmersion.lift W₀.ι ψ.hom hrange
  have hψ' : ψ' ≫ W₀.ι = ψ.hom := IsOpenImmersion.lift_fac _ _ _
  have hsec : ψ' ≫ (ρ ∣_ U₀) = 𝟙 _ := by
    rw [← cancel_mono U₀.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ', hψ,
      Category.id_comp]
  -- `ψ'` is a closed immersion
  have : IsClosedImmersion (ψ' ≫ (ρ ∣_ U₀)) := by rw [hsec]; infer_instance
  have : IsClosedImmersion ψ' := IsClosedImmersion.of_comp ψ' (ρ ∣_ U₀)
  -- `ψ'` hits the generic point of `ρ⁻¹(U₀)`
  let c : Spec (X.presheaf.stalk x) := closedPoint (X.presheaf.stalk x)
  let p₀ : U₀.toScheme := U₀.fromSpecStalkOfMem x hxU c
  have hφc : φ c = η := by
    have h1 : φ c = Y.fromSpecStalk η (Spec.map (inv s) c) := Scheme.Hom.comp_apply _ _ _
    rw [h1]
    have h2 : Spec.map (inv s) c = closedPoint (Y.presheaf.stalk η) := Spec_closedPoint
    rw [h2]
    exact Scheme.fromSpecStalk_closedPoint
  have hη_mem : W₀.ι (ψ' p₀) = η := by
    have h1 : W₀.ι (ψ' p₀) = ψ.hom p₀ := by
      rw [← Scheme.Hom.comp_apply, hψ']
    have h2 : ψ.hom p₀ = (U₀.fromSpecStalkOfMem x hxU ≫ ψ.hom) c :=
      (Scheme.Hom.comp_apply _ _ _).symm
    rw [h1, h2, hψφ, hφc]
  have hsurj : Function.Surjective ψ'.base := by
    have hcl : IsClosed (Set.range ψ'.base) := ψ'.isClosedEmbedding.isClosed_range
    intro w
    have hsp : ψ' p₀ ⤳ w := by
      rw [← W₀.ι.isOpenEmbedding.isInducing.specializes_iff]
      rw [hη_mem]
      exact genericPoint_specializes _
    exact hsp.mem_closed hcl (Set.mem_range_self _)
  have : Surjective ψ' := ⟨hsurj⟩
  have : IsIso ψ' := isIso_of_isClosedImmersion_of_surjective ψ'
  refine ⟨U₀, ⟨x, hxU⟩, ?_⟩
  have : IsIso (ψ' ≫ (ρ ∣_ U₀)) := by rw [hsec]; infer_instance
  exact IsIso.of_isIso_comp_left ψ' (ρ ∣_ U₀)

end SGPT.BDivisor.BD7
