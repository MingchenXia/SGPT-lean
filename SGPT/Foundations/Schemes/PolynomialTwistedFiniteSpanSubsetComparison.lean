import SGPT.Foundations.Schemes.PolynomialTwistedSubsetEvaluationScalars
import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpanCoordinateGeneration
import Mathlib.CategoryTheory.Whiskering

/-! # Genuine finite homogeneous representation on all nonempty coordinate subsets

Finite actual chart generators give native coordinate equivalences. Their
true ratio-product localizations give bijective actual intersection evaluation,
with naturality supplied by genuine homogeneous inclusion and sheaf restriction.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
attribute [local instance] MvPolynomial.gradedAlgebra

section ActualFamily
variable {A : Type} [Fintype A] [DecidableEq A] (d : A → ℕ)
  (t : ∀ a, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (d a))

/-- Genuine normalized evaluation of the literal finite homogeneous span on a true intersection. -/
def polynomialTwistedFiniteSpanSubsetMap (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    (homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedFiniteSpanPiece K n M d t)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree 0).obj S →ₗ[K]
      (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).obj S :=
  (polynomialTwistedSubsetDegreeZeroMap K n M i S hi).comp
    ((polynomialTwistedFiniteSpanSubsetInclusion K n M d t 0).app S).hom

/-- The true finite-span intersection evaluation also preserves its actual native selected-chart scalars. -/
def polynomialTwistedFiniteSpanSubsetNativeMap (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    letI := polynomialHomogeneousSubsetChartModule K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
    polynomialHomogeneousSubsetPiece K n (polynomialProjTwistedFiniteSpanPiece K n M d t) S 0 →ₗ[
      polynomialProjCoordinateRing K n i] polynomialTwistedSubsetNativeSections K n M i S hi := by
  letI := polynomialHomogeneousSubsetChartModule K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
  letI := polynomialHomogeneousSubsetChartModule K n
    (polynomialProjTwistedSectionPiece K n M) i S hi 0
  exact (polynomialTwistedSubsetNativeEvaluation K n M i S hi).comp
    (polynomialHomogeneousSubsetChartPieceMap K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t)
      (polynomialProjTwistedSectionPiece K n M)
      (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) i S hi 0)

omit [Fintype A] [DecidableEq A] in
/-- Actual homogeneous inclusions commute with genuine selected-chart-to-intersection restriction. -/
theorem polynomialTwistedFiniteSpanSubsetChartRestriction_inclusion
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)
    (z : polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i) :
    polynomialHomogeneousSubsetChartPieceMap K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t) (polynomialProjTwistedSectionPiece K n M)
      (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) i S hi 0
      (polynomialHomogeneousSubsetChartRestriction K n
        (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0 z) =
    polynomialHomogeneousSubsetChartRestriction K n (polynomialProjTwistedSectionPiece K n M) i S hi 0
      (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i z) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (actualLocalizedModuleDivisorRestriction_map
    (polynomialProjTwistedFiniteSpan K n M d t).subtype
    (MvPolynomial.X i) (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩) z.val).symm

omit [Fintype A] [DecidableEq A] in
/-- The actual finite-span evaluation square is exactly the true native section restriction square. -/
theorem polynomialTwistedFiniteSpanSubsetNativeMap_restriction
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    let _instChart := polynomialHomogeneousSubsetChartModule K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
    (polynomialTwistedFiniteSpanSubsetNativeMap K n M d t i S hi).comp
      (polynomialHomogeneousSubsetChartRestriction K n
        (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0) =
      (polynomialTwistedSubsetNativeRestriction K n M i S hi).comp
        (polynomialTwistedFiniteSpanNativeChartMap K n M d t i) := by
  let _instChart := polynomialHomogeneousSubsetChartModule K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
  apply LinearMap.ext
  intro z
  change polynomialTwistedSubsetNativeEvaluation K n M i S hi
    (polynomialHomogeneousSubsetChartPieceMap K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t) (polynomialProjTwistedSectionPiece K n M)
      (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) i S hi 0
      (polynomialHomogeneousSubsetChartRestriction K n
        (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0 z)) = _
  rw [polynomialTwistedFiniteSpanSubsetChartRestriction_inclusion,
    polynomialTwistedSubsetNativeEvaluation_apply]
  change M.presheaf.map (homOfLE (polynomialProjSubsetCoordinateOpen_le K n i S hi)).op
    (polynomialTwistedCoordinateDegreeZeroMap K n M i
      (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i z)) =
    (polynomialProjChartSubsetSectionsIso K n M i S hi).hom
      (polynomialProjChartSubsetRestriction K n M i S
        (polynomialTwistedFiniteSpanNativeChartMap K n M d t i z))
  rw [polynomialProjChartSubsetRestriction_actual]
  change _ = M.presheaf.map _
    ((polynomialProjChartTopSectionsIso M i).hom
      ((polynomialProjChartTopSectionsIso M i).inv
        (polynomialTwistedCoordinateDegreeZeroMap K n M i
          (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i z))))
  rw [Iso.inv_hom_id_apply]

omit [Fintype A] [DecidableEq A] in
/-- Genuine native chart generation makes the true finite-span intersection evaluation bijective. -/
theorem polynomialTwistedFiniteSpanSubsetNativeMap_bijective
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)
    (hgen : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    Function.Bijective (polynomialTwistedFiniteSpanSubsetNativeMap K n M d t i S hi) := by
  let _instChart := polynomialHomogeneousSubsetChartModule K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
  let g := polynomialHomogeneousSubsetChartRestriction K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
  let e := polynomialTwistedFiniteSpanNativeChartEquiv K n M d t i hgen
  let f := (polynomialTwistedSubsetNativeRestriction K n M i S hi).comp e.toLinearMap
  let P := Submonoid.powers (polynomialProjSubsetRatioProduct K n i S)
  let _instSource : IsLocalizedModule P g := polynomialHomogeneousSubsetChartRestriction_isLocalized K n
    (polynomialProjTwistedFiniteSpanPiece K n M d t) i S hi 0
  let _instTarget : IsLocalizedModule P (polynomialTwistedSubsetNativeRestriction K n M i S hi) :=
    polynomialTwistedSubsetNativeRestriction_isLocalized K n M i S hi
  let _instTargetComposite : IsLocalizedModule P f :=
    (IsLocalizedModule.comp_iff_of_bijective_right P e.toLinearMap e.bijective).mpr inferInstance
  let E := (IsLocalizedModule.iso P g).symm.trans (IsLocalizedModule.iso P f)
  have hE : E.toLinearMap.comp g = f := by
    apply LinearMap.ext
    intro z
    change (IsLocalizedModule.iso P f) ((IsLocalizedModule.iso P g).symm (g z)) = f z
    rw [IsLocalizedModule.iso_symm_apply, IsLocalizedModule.iso_mk_one]
  have hmap : polynomialTwistedFiniteSpanSubsetNativeMap K n M d t i S hi = E.toLinearMap := by
    apply IsLocalizedModule.ext P g (IsLocalizedModule.map_units f)
    rw [hE]
    exact polynomialTwistedFiniteSpanSubsetNativeMap_restriction K n M d t i S hi
  rw [hmap]
  exact E.bijective

omit [Fintype A] [DecidableEq A] in
/-- The native selected-chart linear evaluation is the genuine structural-field subset evaluation. -/
theorem polynomialTwistedFiniteSpanSubsetNativeMap_eq_subsetMap
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)
    (z : polynomialHomogeneousSubsetPiece K n (polynomialProjTwistedFiniteSpanPiece K n M d t) S 0) :
    polynomialTwistedFiniteSpanSubsetNativeMap K n M d t i S hi z =
      polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi z := by
  change polynomialTwistedSubsetNativeEvaluation K n M i S hi
    (polynomialHomogeneousSubsetChartPieceMap K n
      (polynomialProjTwistedFiniteSpanPiece K n M d t) (polynomialProjTwistedSectionPiece K n M)
      (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) i S hi 0 z) = _
  rw [polynomialTwistedSubsetNativeEvaluation_eq_degreeZeroMap]
  rfl

omit [Fintype A] [DecidableEq A] in
/-- Actual native chart generation gives bijective structural-field evaluation on every genuine selected intersection. -/
theorem polynomialTwistedFiniteSpanSubsetMap_bijective
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hi : i ∈ S)
    (hgen : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    Function.Bijective (polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi) := by
  have h := polynomialTwistedFiniteSpanSubsetNativeMap_bijective K n M d t i S hi hgen
  have hf : (fun z => polynomialTwistedFiniteSpanSubsetNativeMap K n M d t i S hi z) =
      (fun z => polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi z) :=
    funext (polynomialTwistedFiniteSpanSubsetNativeMap_eq_subsetMap K n M d t i S hi)
  change Function.Bijective (fun z => polynomialTwistedFiniteSpanSubsetMap K n M d t i S hi z)
  rw [← hf]
  exact h

/-- The genuine finite homogeneous span evaluates naturally on the actual nonempty section diagram. -/
def polynomialTwistedFiniteSpanNonemptySubsetEvaluation :
    nonemptySubsetDiagram
      (homogeneousCoordinateSubsetDiagram
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedFiniteSpanPiece K n M d t)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree 0) ⟶
      nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram M
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) :=
  Functor.whiskerLeft (nonemptySubsetInclusion (Fin (n + 1)))
    (polynomialTwistedFiniteSpanSubsetInclusion K n M d t 0) ≫
      polynomialTwistedNonemptySubsetEvaluation K n M

/-- Actual native chart generation supplies a genuine natural isomorphism on all nonempty intersections. -/
def polynomialTwistedFiniteSpanNonemptySubsetIso
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (hgen : ∀ i, Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    nonemptySubsetDiagram
      (homogeneousCoordinateSubsetDiagram
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedFiniteSpanPiece K n M d t)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree 0) ≅
      nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram M
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) := by
  let α := polynomialTwistedFiniteSpanNonemptySubsetEvaluation K n M d t
  letI : ∀ S, IsIso (α.app S) := fun S => by
    have he : Function.Bijective (α.app S).hom := by
      change Function.Bijective (polynomialTwistedFiniteSpanSubsetMap K n M d t
        S.property.choose S.val S.property.choose_spec)
      exact polynomialTwistedFiniteSpanSubsetMap_bijective K n M d t S.property.choose S.val
        S.property.choose_spec (hgen S.property.choose)
    change IsIso ((LinearEquiv.ofBijective (α.app S).hom he).toModuleIso.hom)
    infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

end ActualFamily
section GenuineChartGenerators
variable [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
  Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- Genuine finite chart-generator extensions construct the actual nonempty-intersection representation without a representation premise. -/
def polynomialProjChartGeneratedTwistedNonemptySubsetIso :
    nonemptySubsetDiagram
      (homogeneousCoordinateSubsetDiagram
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedFiniteSpanPiece K n M
          (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M))
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree 0) ≅
      nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram M
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) :=
  polynomialTwistedFiniteSpanNonemptySubsetIso K n M
    (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M)
    (polynomialProjFiniteChartGeneratorCoefficients_span K n M)

end GenuineChartGenerators

end
end SGPT.Foundations.Schemes
