import SGPT.Support.Alterations.StableModificationBridge.AlterationUnconditional
import SGPT.Support.Alterations.StableModification.DeJong.Dimension
import SGPT.Support.Alterations.Geometry.SNCSubdivisorComponent
import SGPT.Support.Alterations.Geometry.SNCSubdivisorTopology
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveBlowupSequence
import SGPT.Foundations.Envelope.AlgGeom.NativeProjectivityFromPolynomialFactorization
import SGPT.Support.Principalization.Scheme.IdealSheaf.Defs

/-!
# Regular models with strict normal crossings boundary

Step (a) of the reduction of the Hodge-type inequality ([BHJ17, Lemma 6.14]; blueprint
`claude-bj-hodge.tex`). De Jong's alteration theorem
(`SGPT.Support.Alterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem`,
[de Jong 1996, Thm. 4.1], proved over every field) applied to an integral projective `k`-scheme
`X` and a proper closed subset `Z` gives

* `exists_regular_snc_model`: an integral, regular, projective `k`-scheme `Y` with a surjective
  `k`-morphism `f : Y ⟶ X` (an alteration: `dim Y = dim X`) and a strict normal crossings divisor
  `B` on `Y` with support `f⁻¹ Z`. De Jong's output is an open immersion of the alteration into a
  projective compactification; since `X` is proper, so is the alteration, and the open immersion
  is an isomorphism.

On a locally Noetherian scheme the components `C` of a strict normal crossings divisor are
irreducible, have invertible (Cartier) vanishing ideals (SGPT.Support.Alterations'
`SNCSubdivisorComponent.component_isEffectiveCartierDivisor`), are not contained in one another,
and cover its support (`snc_component_*`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace SGPT.NAPotential.BJHodge

open SGPT.Support.Alterations

/-! ### De Jong's theorem for projective schemes -/

/-- **Regular alterations with strict normal crossings boundary.** For an integral projective
scheme `X` over a field `k` and a closed subset `Z ≠ X`, there are an integral, regular, projective
`k`-scheme `Y`, a surjective morphism `f : Y ⟶ X` with `dim Y = dim X`, and a strict normal
crossings divisor `B` on `Y` whose support is `f⁻¹ Z`. -/
theorem exists_regular_snc_model {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegral Y ∧ IsProjective (f ≫ p) ∧ IsRegularScheme Y ∧
      Function.Surjective f ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ B : Y.IdealSheafData, IsStrictNormalCrossings B ∧ (B.support : Set Y) = f ⁻¹' Z := by
  have hpF := SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p
  have : IsProper p := hpF.isProper
  have hvar : IsVariety p := {}
  obtain ⟨d⟩ :=
    StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem k X p hvar Z hZ
  have := d.isAlteration
  have := d.isOpenImmersion
  have := d.compactificationVariety
  have := d.sourceVariety
  have : IsProper d.compactificationStructure := d.projective.isProper
  have hsrc : IsProper d.sourceStructure := by
    rw [← d.alterationOver]
    infer_instance
  have : IsProper d.inclusion := by
    have : IsProper (d.inclusion ≫ d.compactificationStructure) := by
      rw [d.inclusionOver]
      exact hsrc
    exact IsProper.of_comp d.inclusion d.compactificationStructure
  -- the open immersion of the proper alteration into its compactification is an isomorphism
  have hrange : Set.range d.inclusion = Set.univ := by
    have hclopen : IsClopen (Set.range d.inclusion) :=
      ⟨d.inclusion.isClosedMap.isClosed_range, d.inclusion.isOpenEmbedding.isOpen_range⟩
    obtain ⟨s⟩ := (inferInstance : Nonempty d.source)
    exact hclopen.eq_univ ⟨_, ⟨s, rfl⟩⟩
  have : IsIso d.inclusion :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, ⟨Set.range_eq_univ.mp hrange⟩⟩
  let f := inv d.inclusion ≫ d.alteration
  have hfp : f ≫ p = d.compactificationStructure := by
    simp only [f, Category.assoc, d.alterationOver, ← d.inclusionOver, IsIso.inv_hom_id_assoc]
  refine ⟨d.compactification, f, inferInstance, ?_, d.regular, ?_, ?_, d.boundary,
    d.normalCrossings, ?_⟩
  · rw [hfp]
    exact SGPT.Foundations.Envelope.NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization
      _ ((SGPT.Foundations.Envelope.ProjectiveBlowupSequence.isProjectiveOver_iff _).mp d.projective)
  · exact (IsAlteration.surjective d.alteration).comp (inv d.inclusion).surjective
  · rw [← StableModification.DeJong.topologicalKrullDim_eq_of_isAlteration p d.alteration]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (d.inclusion.homeomorph.isHomeomorph)).symm
  · have h1 : ∀ s, (inv d.inclusion) (d.inclusion s) = s := fun s => by
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    have h2 : ∀ y, d.inclusion ((inv d.inclusion) y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    rw [d.boundarySupport, hrange, Set.compl_univ, Set.union_empty]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      change d.alteration (inv d.inclusion (d.inclusion s)) ∈ Z
      rwa [h1]
    · intro hy
      exact ⟨inv d.inclusion y, hy, h2 y⟩

/-! ### Components of a strict normal crossings divisor -/

section components

variable {Y : Scheme.{u}} (B : Y.IdealSheafData)

/-- The components of a divisor are irreducible. -/
theorem snc_component_isIrreducible (C : DivisorComponent B) : IsIrreducible (C.val : Set Y) :=
  Geometry.SNCLocality.divisorComponent_isIrreducible B C

/-- The components of a strict normal crossings divisor on a locally Noetherian scheme are
Cartier: their vanishing ideals are invertible. -/
theorem snc_component_isInvertible [IsLocallyNoetherian Y] (hB : IsStrictNormalCrossings B)
    (C : DivisorComponent B) : (Scheme.IdealSheafData.vanishingIdeal C.val).IsInvertible := by
  intro x
  obtain ⟨U, hxU, t, ht, heq⟩ :=
    Geometry.SNCSubdivisorComponent.component_isEffectiveCartierDivisor B hB C x
  exact ⟨U, hxU, t, ht.mem_nonZeroDivisors, heq⟩

/-- The components of a divisor lie in its support. -/
theorem snc_component_le_support (C : DivisorComponent B) : C.val ≤ B.support :=
  Geometry.SNCSubdivisorComponent.component_le_support B C

/-- No component of a divisor is contained in another one. -/
theorem snc_component_eq_of_le (C C' : DivisorComponent B) (h : C.val ≤ C'.val) : C = C' := by
  have h' : (C'.val : Set Y) ⊆ C.val :=
    Geometry.SNCSubdivisorTopology.component_maximal B C (C'.val : Set Y)
      (snc_component_isIrreducible B C') h (snc_component_le_support B C')
  exact Subtype.ext (le_antisymm h h')

/-- The support of a divisor is the union of its components. -/
theorem snc_support_eq_iUnion :
    (B.support : Set Y) = ⋃ C : DivisorComponent B, (C.val : Set Y) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨S, hS, hxS⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({⟨x, hx⟩} : Set B.support) isIrreducible_singleton
    exact Set.mem_iUnion.mpr ⟨divisorComponentOf B S hS, ⟨x, hx⟩, hxS rfl, rfl⟩
  · exact Set.iUnion_subset fun C => snc_component_le_support B C

end components

end SGPT.NAPotential.BJHodge
