import SGPT.Foundations.PublishedEnvelope.Global.IntrinsicPSHComparisonContinuationNativeFunctionField
import SGPT.Foundations.PublishedEnvelope.Global.NativeRankOneCoordinateLine

/-!
# Actual original coordinate-line frames and canonical section coefficients

The frames are constructed from the actual hyperplane kernel's proved
principal nonzerodivisor equations. The canonical section is the dual of the
actual ideal inclusion. No frame or section matching certificate is assumed.
Complete mathematical route: owned audit `native-coordinate-frames-route.tex`.
-/

open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open SGPT.Support.PublishedModularCurves
noncomputable section
universe u
namespace SGPT.Foundations.PublishedEnvelope.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (Y : Scheme.{u}) :
    ∀ U, IsMulCommutative (Y.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (Y.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private abbrev originalCoordinateAffineOpen (i : X.ChartIndex) :
    X.nativeRankOneScheme.affineOpens :=
  ⟨X.nativeRankOneCoordinateOpen (i 0), X.nativeRankOneCoordinateOpen_isAffine (i 0)⟩

private theorem originalLocalEquation_mem (i : X.ChartIndex) (j : Fin (X.M 0 + 1)) :
    X.nativeRankOneHyperplaneLocalEquation (i 0) j ∈
      (X.nativeRankOneHyperplaneInclusion j).ker.ideal (originalCoordinateAffineOpen X i) := by
  rw [X.nativeRankOneHyperplaneLocalEquation_span]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The true principal generator trivializes the actual original hyperplane ideal. -/
def nativeRankOneCoordinateIdealGeneratorIso (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    Scheme.Modules.unitObj (X.nativeRankOneCoordinateOpen (i 0)).toScheme ≅
      (SGPT.Support.PublishedModularCurves.idealModule (X.nativeRankOneHyperplaneInclusion j)).restrict
        (X.nativeRankOneCoordinateOpen (i 0)).ι :=
  SGPT.Support.PublishedModularCurves.localIdealGeneratorIso (X.nativeRankOneHyperplaneInclusion j)
    (originalCoordinateAffineOpen X i) (X.nativeRankOneHyperplaneLocalEquation (i 0) j)
    (originalLocalEquation_mem X i j) (X.nativeRankOneHyperplaneLocalEquation_span (i 0) j)
    (X.nativeRankOneHyperplaneLocalEquation_mem_nonZeroDivisors (i 0) j (hi 0) hj)

/-- The actual original dual generator frame on the entire coordinate over-site. -/
def nativeRankOneCoordinateLineOverFrame (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    (X.nativeRankOneCoordinateLine j).over (X.nativeRankOneCoordinateOpen (i 0)) ≅
      SheafOfModules.unit (X.nativeRankOneScheme.ringCatSheaf.over
        (X.nativeRankOneCoordinateOpen (i 0))) :=
  SGPT.Support.PublishedModularCurves.SheafOfModules.dualOverIsoOfIso X.nativeRankOneScheme.ringCatSheaf
    (SGPT.Support.PublishedModularCurves.idealModule (X.nativeRankOneHyperplaneInclusion j)) _
    (Scheme.Modules.overTrivializationOfRestrictIso _ _
      (X.nativeRankOneCoordinateIdealGeneratorIso i hi j hj).symm)

/-- The true dual generator frame on the ACTUAL original open subscheme. -/
def nativeRankOneCoordinateLineFrame (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    (X.nativeRankOneCoordinateLine j).restrict (X.nativeRankOneCoordinateOpen (i 0)).ι ≅
      Scheme.Modules.unitObj (X.nativeRankOneCoordinateOpen (i 0)).toScheme :=
  SGPT.Support.PublishedModularCurves.restrictTrivializationOfOverIso (X.nativeRankOneCoordinateLine j) _
    (X.nativeRankOneCoordinateLineOverFrame i hi j hj)

/-- The canonical map is the dual of the ACTUAL original hyperplane ideal inclusion. -/
def nativeRankOneCoordinatePoleUnitHom (j : Fin (X.M 0 + 1)) :
    Scheme.Modules.unitObj X.nativeRankOneScheme ⟶ X.nativeRankOneCoordinateLine j :=
  (Scheme.Modules.dualUnitObjIso (X := X.nativeRankOneScheme)).inv ≫
    Scheme.Modules.dualMapObj (SGPT.Support.PublishedModularCurves.idealModuleToUnit
      (X.nativeRankOneHyperplaneInclusion j))

/-- The canonical section of the ACTUAL original coordinate pole line. -/
def nativeRankOneCoordinatePoleSection (j : Fin (X.M 0 + 1)) :
    Γ(X.nativeRankOneCoordinateLine j, ⊤) :=
  (X.nativeRankOneCoordinatePoleUnitHom j).val.app (.op ⊤)
    (show Γ(X.nativeRankOneScheme, ⊤) from 1)

/-- The ENTIRE true dual inclusion is the original coordinate ratio in the
produced actual dual generator frame. -/
theorem nativeRankOneCoordinatePoleUnitHom_frame (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    (X.nativeRankOneCoordinatePoleUnitHom j).over (X.nativeRankOneCoordinateOpen (i 0)) ≫
      (X.nativeRankOneCoordinateLineOverFrame i hi j hj).hom =
        (SGPT.Support.PublishedModularCurves.SheafOfModules.overUnitScalarEnd X.nativeRankOneScheme.ringCatSheaf
          (X.nativeRankOneCoordinateOpen (i 0))
          (X.nativeRankOneHyperplaneLocalEquation (i 0) j)).asHom := by
  exact SGPT.Support.PublishedModularCurves.dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (SGPT.Support.PublishedModularCurves.idealModuleToUnit (X.nativeRankOneHyperplaneInclusion j)) _ _ _
    (SGPT.Support.PublishedModularCurves.localIdealGeneratorOverTrivialization_inv_comp
      (X.nativeRankOneHyperplaneInclusion j) (originalCoordinateAffineOpen X i)
      (X.nativeRankOneHyperplaneLocalEquation (i 0) j) (originalLocalEquation_mem X i j)
      (X.nativeRankOneHyperplaneLocalEquation_span (i 0) j)
      (X.nativeRankOneHyperplaneLocalEquation_mem_nonZeroDivisors (i 0) j (hi 0) hj))

/-- The true native local equation is the original degree-one homogeneous section. -/
theorem nativeRankOneHyperplaneLocalEquation_homogeneous (i : X.ChartIndex)
    (j : Fin (X.M 0 + 1)) :
    X.nativeRankOneHyperplaneLocalEquation (i 0) j =
      X.nativeRankOneOriginalHomogeneousSection i (X.coord_mem_piece 0 j) := by
  unfold nativeRankOneOriginalHomogeneousSection
  simp only [Finsupp.degree_single]
  rfl

/-- The actual original hyperplane equation has its literal original chart coefficient. -/
theorem nativeRankOneHyperplaneLocalEquation_original (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) :
    X.nativeRankOneHyperplaneLocalEquation (i 0) j =
      (X.nativeRankOneOriginalSectionsIso i hi).hom
        ⟨X.coord 0 j / X.coord 0 (i 0), X.coord_div_mem_chartAlg i 0 j⟩ := by
  rw [X.nativeRankOneHyperplaneLocalEquation_homogeneous]
  simpa only [X.chartDen_single] using
    X.nativeRankOneOriginalHomogeneousSection_eq i hi (X.coord_mem_piece 0 j)

/-- Its ACTUAL native generic germ is exactly the original coordinate coefficient ratio. -/
theorem nativeRankOneHyperplaneLocalEquation_generic (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) :
    X.nativeRankOneGenericGerm i hi (X.nativeRankOneHyperplaneLocalEquation (i 0) j) =
      X.nativeRankOneFunctionFieldEquiv i hi (X.coord 0 j / X.coord 0 (i 0)) := by
  rw [X.nativeRankOneHyperplaneLocalEquation_original i hi j]
  exact (X.nativeRankOneFunctionFieldEquiv_coefficient i hi
    ⟨X.coord 0 j / X.coord 0 (i 0), X.coord_div_mem_chartAlg i 0 j⟩).symm

/-- The actual local equation is nonzero, through its original coefficient and true generic germ. -/
theorem nativeRankOneHyperplaneLocalEquation_ne_zero (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    X.nativeRankOneHyperplaneLocalEquation (i 0) j ≠ 0 := by
  intro hz
  have he := X.nativeRankOneHyperplaneLocalEquation_generic i hi j
  rw [hz, map_zero] at he
  exact (div_ne_zero hj (hi 0)) ((X.nativeRankOneFunctionFieldEquiv i hi).injective
    (he.symm.trans (map_zero (X.nativeRankOneFunctionFieldEquiv i hi)).symm))

end SGPT.Foundations.PublishedEnvelope.MultiModel

#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateIdealGeneratorIso
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateLineOverFrame
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateLineFrame
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleUnitHom
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleSection
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleUnitHom_frame
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_homogeneous
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_original
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_generic
#check @SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_ne_zero
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateIdealGeneratorIso
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateLineOverFrame
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinateLineFrame
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleUnitHom
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleSection
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneCoordinatePoleUnitHom_frame
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_homogeneous
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_original
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_generic
#print axioms SGPT.Foundations.PublishedEnvelope.MultiModel.nativeRankOneHyperplaneLocalEquation_ne_zero
