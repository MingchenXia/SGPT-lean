import SGPT.Checks.Comparison.BJPair3DivGeometricDVRRestriction
import SGPT.Support.Alterations.Geometry.AffineQuasiProjective

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DVRPresentationCompactification.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# The actual projective compactification of the finite DVR presentation

Essential finiteness selects an actual finite-type subalgebra A of V, with
V its localization. The cached affine projective immersion producer gives
an actual schematic projective closure C of Spec A. Both the whole DVR
trait and the original fraction-field point of C are constructed, with
literal coefficient and generic-point triangles. No compactification,
point correspondence or birational model is supplied by the caller.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace SGPT.NAPotential.BJ.Pair3Div.DVRPresentation
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (V : Subalgebra k K) [Algebra.EssFiniteType k V]

/-- The actual finite-type presentation selected by essential finiteness. -/
abbrev coefficientAlgebra := Algebra.EssFiniteType.subalgebra k V

/-- Its literal coefficient structure. -/
def coefficientStructure : Spec (.of (coefficientAlgebra V)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (coefficientAlgebra V)))

instance coefficientStructure_finiteType : LocallyOfFiniteType (coefficientStructure V) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

instance coefficientStructure_variety : IsVariety (coefficientStructure V) := {}

private theorem exists_immersion :
    ∃ (n : ℕ) (e : Spec (.of (coefficientAlgebra V)) ⟶ projectiveSpace k n),
      IsImmersion e ∧ e ≫ projectiveSpaceStructure k n = coefficientStructure V :=
  AffineQuasiProjective.exists_projective_immersion_spec_algebraMap

/-- The dimension of the genuine projective presentation, constructed internally. -/
def immersionDimension : ℕ := (exists_immersion V).choose

/-- The genuine finite-presentation projective immersion. -/
def immersion : Spec (.of (coefficientAlgebra V)) ⟶ projectiveSpace k (immersionDimension V) :=
  (exists_immersion V).choose_spec.choose

instance immersion_isImmersion : IsImmersion (immersion V) :=
  (exists_immersion V).choose_spec.choose_spec.1

@[reassoc]
theorem immersion_structure :
    immersion V ≫ projectiveSpaceStructure k (immersionDimension V) = coefficientStructure V :=
  (exists_immersion V).choose_spec.choose_spec.2

instance immersion_quasiCompact : QuasiCompact (immersion V) :=
  ProjectiveCompactification.immersion_isQuasiCompact (coefficientStructure V) (immersion V)

/-- The actual schematic projective closure of Spec A. -/
def compactification : Scheme.{u} := ProjectiveCompactification.closure (immersion V)

/-- Its actual proper coefficient map. -/
def structureMap : compactification V ⟶ Spec (.of k) :=
  ProjectiveCompactification.closureStructure (immersion V)

/-- The original finite-type affine scheme as an actual dense open. -/
def inclusion : Spec (.of (coefficientAlgebra V)) ⟶ compactification V :=
  ProjectiveCompactification.inclusion (immersion V)

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion V) := by
  exact ProjectiveCompactification.inclusion_isOpenImmersion (immersion V)

instance inclusion_isDominant : IsDominant (inclusion V) := by
  exact ProjectiveCompactification.inclusion_isDominant (immersion V)

instance structureMap_isProper : IsProper (structureMap V) := by
  exact ProjectiveCompactification.structure_isProper (immersion V)

instance structureMap_isVariety : IsVariety (structureMap V) :=
  ProjectiveCompactification.structure_isVariety (coefficientStructure V) (immersion V)

@[reassoc]
theorem inclusion_structure : inclusion V ≫ structureMap V = coefficientStructure V := by
  exact (ProjectiveCompactification.inclusion_structure (immersion V)).trans (immersion_structure V)

/-- The WHOLE original DVR trait, before passing to any birational model. -/
def traitPoint : Spec (.of V) ⟶ compactification V :=
  Spec.map (CommRingCat.ofHom (algebraMap (coefficientAlgebra V) V)) ≫ inclusion V

/-- The SAME actual original field point. -/
def fieldPoint : Spec (.of K) ⟶ compactification V :=
  Spec.map (CommRingCat.ofHom
    (V.val.toRingHom.comp (algebraMap (coefficientAlgebra V) V))) ≫ inclusion V

/-- The field point is exactly the generic restriction of the whole trait. -/
theorem fieldPoint_eq_fraction_trait :
    fieldPoint V = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ traitPoint V := by
  rw [traitPoint, ← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc]
theorem traitPoint_structure :
    traitPoint V ≫ structureMap V = Spec.map (CommRingCat.ofHom (algebraMap k V)) := by
  rw [traitPoint, Category.assoc, inclusion_structure, coefficientStructure, ← Spec.map_comp]
  congr 1

@[reassoc]
theorem fieldPoint_structure :
    fieldPoint V ≫ structureMap V = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [fieldPoint_eq_fraction_trait, Category.assoc, traitPoint_structure, ← Spec.map_comp]
  congr 1

end SGPT.NAPotential.BJ.Pair3Div.DVRPresentation
