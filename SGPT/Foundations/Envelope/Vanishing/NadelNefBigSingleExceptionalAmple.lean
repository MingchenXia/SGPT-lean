import SGPT.Foundations.Envelope.Vanishing.NadelNefBigGlobalPairBaseOpenComposition
import SGPT.Foundations.Envelope.Vanishing.ArithmeticOriginalLineGenerated
import SGPT.Foundations.Envelope.AlgGeom.PositivePowerProjectiveGeneration
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveSegrePullbackSections
import SGPT.Foundations.Envelope.AlgGeom.SchemeAmpleClosedRestriction

/-! # Actual exceptional ampleness for one original blowup

The original ample line supplies its own positive-power embedding and Serre
generators. The same original generated pair is closed, and its actual Segre
hyperplane line is the exceptional ideal tensored by a positive original
base-line power. No exceptional positivity or comparison is a premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules MvPolynomial SGPT.Support.Alterations
universe u
namespace SGPT.Foundations.Envelope.Vanishing.NadelNefBigSingleExceptionalAmple
open CanonicalGeometry NadelNefBigGlobalPairClosed
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance originalPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (D : X.IdealSheafData) (p : X ⟶ Spec (.of k))
  {m : ℕ} (j : X ⟶ projectiveSpace k m) [IsClosedImmersion j]
  (hj : j ≫ projectiveSpaceStructure k m = p)
  (B : X.Modules) (hB : IsInvertible B)
  (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I]

private theorem generatedPair_isClosedImmersion :
    IsClosedImmersion (ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j)
      (globalMap D p B hB G)
      (by rw [Category.assoc, hj, globalMap_structure])) := by
  let q := projectiveSpaceStructure k (Fintype.card G.I)
  let F := pullback.map p q (projectiveSpaceStructure k m) q j (𝟙 _) (𝟙 _)
    ((Category.comp_id p).trans hj.symm)
    ((Category.comp_id q).trans (Category.id_comp q).symm)
  have hF : IsClosedImmersion F :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion j) (inferInstance : IsClosedImmersion (𝟙 _))
      hj.symm (Category.id_comp q).symm
  let : IsClosedImmersion F := hF
  let : IsClosedImmersion (globalPair D p B hB G) :=
    NadelNefBigGlobalPairBaseOpenComposition.globalPair_isClosedImmersion D p B hB G
  have hfac : ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j)
      (globalMap D p B hB G) (by rw [Category.assoc, hj, globalMap_structure]) =
      globalPair D p B hB G ≫ F := by
    apply pullback.hom_ext
    · simp only [ProjectiveSegrePullbackSections.pair, F, q, pullback.map, globalPair,
        Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [ProjectiveSegrePullbackSections.pair, F, q, pullback.map, globalPair,
        Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [hfac]
  infer_instance

private def globalMapTwistIso :
    ProjectiveSegrePullbackSections.line (globalMap D p B hB G) ≅
      D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj B := by
  let H := NadelNefBigGlobalGenerators.comapGenerators D D.blowUpπ B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact ArithmeticOriginalLineGenerated.projectiveTwistIso (D.blowUpπ ≫ p)
    ((Scheme.IdealSheafData.blowUp.isInvertible_comap_π D).isInvertibleModule_toModules.monoidalTensor
      (hB.pullback D.blowUpπ)) H (0 : Fin (Fintype.card G.I + 1))

include hj hB G in
private theorem isVeryAmple_generated_exceptional :
    SchemeLineAmpleness.IsVeryAmple (D.blowUpπ ≫ p)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj
        (ProjectiveSegrePullbackSections.line j ⊗ B)) := by
  let q := globalMap D p B hB G
  have hq : (D.blowUpπ ≫ j) ≫ projectiveSpaceStructure k m =
      q ≫ projectiveSpaceStructure k (Fintype.card G.I) := by
    rw [Category.assoc, hj, globalMap_structure]
  let δ := ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j) q hq
  let : IsClosedImmersion δ := generatedPair_isClosedImmersion D p j hj B hB G
  refine ⟨Algebra.Segre.dimension m (Fintype.card G.I),
    ProjectiveSegrePullbackSections.morphism (D.blowUpπ ≫ j) q hq, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.comp δ (Geometry.Segre.segre k m (Fintype.card G.I))
  · exact (ProjectiveSegrePullbackSections.morphism_structure (D.blowUpπ ≫ j) q hq).trans
      ((Category.assoc D.blowUpπ j _).trans (congrArg (fun t => D.blowUpπ ≫ t) hj))
  · let A := (Scheme.Modules.pullback D.blowUpπ).obj (ProjectiveSegrePullbackSections.line j)
    let K := D.exceptionalDivisor.toModules
    let T := (Scheme.Modules.pullback D.blowUpπ).obj B
    exact ⟨ProjectiveSegrePullbackSections.lineIso (D.blowUpπ ≫ j) q hq ≪≫
      ((((pullbackComp D.blowUpπ j).app _).symm) ⊗ᵢ globalMapTwistIso D p B hB G) ≪≫
      (α_ A K T).symm ≪≫ ((β_ A K) ⊗ᵢ Iso.refl T) ≪≫ (α_ K A T) ≪≫
      (Iso.refl K ⊗ᵢ Functor.Monoidal.μIso (Scheme.Modules.pullback D.blowUpπ)
        (ProjectiveSegrePullbackSections.line j) B)⟩

omit j hj B hB G in
/-- An actual ample base line internally supplies a positive original power
whose pullback, tensored by the actual original exceptional ideal, is very
ample on the same whole blowup. -/
theorem exists_positive_isVeryAmple_exceptional_tensor_pullback [IsLocallyNoetherian X]
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple p C) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple (D.blowUpπ ≫ p)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)) := by
  obtain ⟨a, ha, m, j, hj, hjp, ⟨eA⟩⟩ := hC.2
  let : IsClosedImmersion j := hj
  obtain ⟨N, hN⟩ := NadelNefBigGlobalSerreGenerators.exists_eventual_controlled_generators
    j D D.blowUpπ (0 : Fin (m + 1))
  obtain ⟨G, hG, _⟩ := hN N (le_refl N)
  let B := (Scheme.Modules.pullback j).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (m + 1)) (N : ℤ))
  let hB := (coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) (N : ℤ)).pullback j
  let := hG
  let : Fintype G.I := Fintype.ofFinite G.I
  have hV := isVeryAmple_generated_exceptional D p j hjp B hB G
  let E : ProjectiveSegrePullbackSections.line j ⊗ B ≅ bundleTensorPower C (a + a * N) :=
    (eA ⊗ᵢ (PositivePowerProjectiveGeneration.blockTwistIso j C a
      (0 : Fin (m + 1)) eA N).symm) ≪≫
      TensorPowerBaseIdealGrading.tensorPowerAddIso C a (a * N)
  exact ⟨a + a * N, lt_of_lt_of_le ha (Nat.le_add_right _ _),
    SchemeAmpleClosedRestriction.veryAmple_of_iso hV
      (Iso.refl D.exceptionalDivisor.toModules ⊗ᵢ (Scheme.Modules.pullback D.blowUpπ).mapIso E)⟩

omit j hj B hB G in
/-- The actual exceptional ideal of the original single blowup becomes ample
after tensoring by an internally chosen positive power of the original ample
base line. All actual generators, closed maps and line comparisons are derived. -/
theorem exists_positive_isAmple_exceptional_tensor_pullback [IsLocallyNoetherian X]
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple p C) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsAmple (D.blowUpπ ≫ p)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)) := by
  obtain ⟨r, hr, hV⟩ := exists_positive_isVeryAmple_exceptional_tensor_pullback D p C hC
  let L := D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)
  let E : bundleTensorPower L 1 ≅ L :=
    (SGPT.Support.ModularCurves.monoidalTensorObjIso (bundleTensorPower L 0) L).symm ≪≫
      ((SGPT.Support.ModularCurves.monoidalUnitObjIso D.blowUp).symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L
  exact ⟨r, hr, hV.isInvertible, 1, Nat.zero_lt_one,
    SchemeAmpleClosedRestriction.veryAmple_of_iso hV E.symm⟩

end SGPT.Foundations.Envelope.Vanishing.NadelNefBigSingleExceptionalAmple
