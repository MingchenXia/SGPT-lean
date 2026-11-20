import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeTensorIdealPullback
import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeTensorUnitSections
/-! # The genuine original tensor inclusion untwists through an actual original line frame -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
universe u v
namespace SGPT.Foundations.PublishedEnvelope.Vanishing.NadelAuxiliaryBranchSectionsMonoidal
private theorem frame_ideal {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M I : C) (e : M ≅ 𝟙_ C) (i : I ⟶ 𝟙_ C) :
    M ◁ i ≫ (ρ_ M).hom ≫ e.hom = e.hom ▷ I ≫ (λ_ I).hom ≫ i := by
  rw [← rightUnitor_naturality]
  rw [← Category.assoc, ← tensorHom_def', tensorHom_def]
  rw [Category.assoc, ← unitors_equal, leftUnitor_naturality]
open Scheme.Modules
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

def untwist {X : Scheme.{u}} (M I : X.Modules) (e : M ≅ unitObj X) : Scheme.Modules.tensorObj M I ≅ I :=
  (SGPT.Support.PublishedModularCurves.monoidalTensorObjIso M I).symm ≪≫
    whiskerRightIso (e ≪≫ (SGPT.Support.PublishedModularCurves.monoidalUnitObjIso X).symm) I ≪≫ λ_ I

theorem untwist_inclusion {X : Scheme.{u}} (M I : X.Modules) (e : M ≅ unitObj X) (i : I ⟶ unitObj X) :
    SchemeTensorObjMorphisms.tensorObjIdealMap M I i ≫ e.hom = (untwist M I e).hom ≫ i := by
  apply (cancel_mono (SGPT.Support.PublishedModularCurves.monoidalUnitObjIso X).inv).mp
  apply (cancel_epi (SGPT.Support.PublishedModularCurves.monoidalTensorObjIso M I).hom).mp
  simp only [← Category.assoc]
  rw [SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  simp only [untwist, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact frame_ideal M I (e ≪≫ (SGPT.Support.PublishedModularCurves.monoidalUnitObjIso X).symm)
    (i ≫ (SGPT.Support.PublishedModularCurves.monoidalUnitObjIso X).inv)

end SGPT.Foundations.PublishedEnvelope.Vanishing.NadelAuxiliaryBranchSectionsMonoidal
