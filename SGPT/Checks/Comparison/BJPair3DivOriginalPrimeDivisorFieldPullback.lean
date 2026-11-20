import SGPT.Checks.Comparison.BJPair3DivOriginalPrimeDivisorRealization
import SGPT.Foundations.Envelope.Berkovich.SchemeGenericCenterValuations

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/OriginalPrimeDivisorFieldPullback.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Literal source residue pullback and actual generic projection

Naturality of the original residue map identifies the source pullback
with the actual generic-stalk pullback. Its inverse is the actual trait
field map, from the whole generic triangle, not an input equivalence.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich SGPT.NAPotential.Berkovich

universe u
/-- The canonical generic residue equivalence is the actual stalk change
followed by the original residue map. -/
theorem genericResidueEquiv_eq_stalkCongr {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hx : x = genericPoint X) :
    (SchemeValuedPoint.genericResidueEquiv X x hx).toRingHom =
      (X.residue x).hom.comp
        (X.presheaf.stalkCongr (.of_eq hx.symm)).hom.hom := by
  subst x
  ext a
  simp [SchemeValuedPoint.genericResidueEquiv, TopCat.Presheaf.stalkCongr]

variable {X : Scheme.{0}} [IsIntegral X] (E : PrimeDivisorOver X)

/-- The actual entire original generic-stalk pullback, retaining the source
prime divisor's canonical residue-field conventions. -/
def primeDivisorGenericPullback : X.functionField →+* E.Y.functionField :=
  E.pullback.comp
    (SchemeValuedPoint.genericResidueEquiv X (E.π (genericPoint E.Y)) E.isGenericPoint_image).toRingHom

/-- The literal original residue pullback equals the canonical generic-stalk
pullback, by the actual residue-field naturality square. -/
theorem primeDivisorGenericPullback_eq_stalkMap :
    primeDivisorGenericPullback E =
      (E.π.stalkMap (genericPoint E.Y)).hom.comp
        (X.presheaf.stalkCongr (.of_eq E.isGenericPoint_image.symm)).hom.hom := by
  ext a
  apply E.residueEquiv.injective
  change E.residueEquiv (E.residueEquiv.symm
    ((E.π.residueFieldMap (genericPoint E.Y))
      (SchemeValuedPoint.genericResidueEquiv X (E.π (genericPoint E.Y)) E.isGenericPoint_image a))) = _
  rw [RingEquiv.apply_symm_apply]
  change (E.π.residueFieldMap (genericPoint E.Y))
    ((SchemeValuedPoint.genericResidueEquiv X (E.π (genericPoint E.Y)) E.isGenericPoint_image).toRingHom a) = _
  rw [genericResidueEquiv_eq_stalkCongr]
  exact congrArg (fun f : X.presheaf.stalk (E.π (genericPoint E.Y)) ⟶
    E.Y.residueField (genericPoint E.Y) => f
      ((X.presheaf.stalkCongr (.of_eq E.isGenericPoint_image.symm)).hom a))
    (Scheme.residue_residueFieldMap E.π (genericPoint E.Y))

/-- The source's actual field pullback retains the entire original generic
scheme map, rather than merely an abstract field identification. -/
theorem primeDivisorGenericPullback_fromSpecStalk :
    Spec.map (CommRingCat.ofHom (primeDivisorGenericPullback E)) ≫
      X.fromSpecStalk (genericPoint X) = E.Y.fromSpecStalk (genericPoint E.Y) ≫ E.π := by
  rw [primeDivisorGenericPullback_eq_stalkMap]
  change Spec.map ((X.presheaf.stalkCongr (.of_eq E.isGenericPoint_image.symm)).hom ≫
    E.π.stalkMap (genericPoint E.Y)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The actual whole trait generic triangle DERIVES the inverse of the
literal source pullback on every original fraction. -/
theorem primeDivisorGenericPullback_fieldHom
    (g : Spec X.functionField ⟶ E.Y) [IsDominant g]
    (hg : g ≫ E.π = X.fromSpecStalk (genericPoint X)) :
    (SchemeGenericFieldGraph.fieldHom g).hom.comp (primeDivisorGenericPullback E) =
      RingHom.id X.functionField := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  change Spec.map (CommRingCat.ofHom (primeDivisorGenericPullback E) ≫
    SchemeGenericFieldGraph.fieldHom g) ≫ _ = Spec.map (𝟙 X.functionField) ≫ _
  rw [Spec.map_comp, Category.assoc, primeDivisorGenericPullback_fromSpecStalk,
    ← Category.assoc, SchemeGenericFieldGraph.fieldHom_fromSpecStalk, hg, Spec.map_id,
    Category.id_comp]

end SGPT.NAPotential.BJ.Pair3Div
