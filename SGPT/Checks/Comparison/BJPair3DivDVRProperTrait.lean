import SGPT.Checks.Comparison.BJPair3DivDVRProperGraphGeneric
import SGPT.Checks.Comparison.BJPair3DivTraitPresentationStalk
import Mathlib.AlgebraicGeometry.ValuativeCriterion

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DVRProperTrait.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# The whole original DVR trait on the constructed normal proper model

The actual generic field point extends by properness over the original
coefficient field. Its entire map to the projective presentation is proved
to be the original whole trait, by separatedness and generic agreement.
No center, local ring equality or divisorial correspondence is an input.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
open SGPT.Support.Alterations SGPT.Foundations.Envelope

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsVariety p] [IsProper p]

local instance trait_baseFieldAlgebra : Algebra k X.functionField :=
  p.stalkAlgebra (genericPoint X)

variable (V : Subalgebra k X.functionField) [Algebra.EssFiniteType k V]
  [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]

omit [IsProper p] [Algebra.EssFiniteType k V] [IsDiscreteValuationRing V] in
/-- The actual original fraction-field map is dominant. -/
theorem fractionMap_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) := by
  have hp : (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)))
      (⊥ : PrimeSpectrum X.functionField) = (⊥ : PrimeSpectrum V) := by
    apply PrimeSpectrum.ext
    change RingHom.ker (algebraMap V X.functionField) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective V X.functionField)
  rw [isDominant_iff]
  change Dense (Set.range (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec (Spec (.of V))).def, genericPoint_eq_bot_of_affine]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨(⊥ : PrimeSpectrum X.functionField), hp⟩)

/-- The literal valuative square uses the actual original coefficient map. -/
def traitSquare : ValuativeCommSq (projection p V ≫ p) where
  R := V
  K := X.functionField
  i₁ := normalizedGenericPoint p V
  i₂ := Spec.map (CommRingCat.ofHom (algebraMap k V))
  commSq := ⟨by
    rw [← Category.assoc, normalizedGenericPoint_projection,
      SchemeStalkCoefficients.fromSpecStalk_structureMap, ← Spec.map_comp]
    congr 1⟩

/-- Properness internally constructs the whole original trait and BOTH
actual generic and coefficient triangles. -/
theorem exists_trait : ∃ q : Spec (.of V) ⟶ model p V,
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
      normalizedGenericPoint p V ∧
    q ≫ (projection p V ≫ p) = Spec.map (CommRingCat.ofHom (algebraMap k V)) := by
  have hp : IsProper (projection p V ≫ p) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  let l := (Classical.choice (hp.1.1.1 (traitSquare p V))).default
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/-- The actual original whole DVR trait, chosen from proved properness. -/
def trait : Spec (.of V) ⟶ model p V := (exists_trait p V).choose

@[reassoc]
theorem trait_fraction :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ trait p V =
      normalizedGenericPoint p V := (exists_trait p V).choose_spec.1

@[reassoc]
theorem trait_structure :
    trait p V ≫ (projection p V ≫ p) = Spec.map (CommRingCat.ofHom (algebraMap k V)) :=
  (exists_trait p V).choose_spec.2

instance trait_fraction_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ trait p V) := by
  rw [trait_fraction]
  infer_instance

instance trait_isDominant : IsDominant (trait p V) :=
  IsDominant.of_comp (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) _

/-- The entire presentation map, not merely its generic point, is the
original whole trait; separatedness supplies the genuine uniqueness. -/
theorem trait_presentation : trait p V ≫ presentation p V = DVRPresentation.traitPoint V := by
  let := fractionMap_isDominant p V
  apply AlgebraicGeometry.ext_of_isDominant_of_isSeparated
    (DVRPresentation.structureMap V) ?_
    (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) ?_
  · rw [Category.assoc, presentation_structure, trait_structure, DVRPresentation.traitPoint_structure]
  · rw [← Category.assoc, trait_fraction, normalizedGenericPoint_presentation,
      ← DVRPresentation.fieldPoint_eq_fraction_trait]

end SGPT.NAPotential.BJ.Pair3Div.DVRProperModel
