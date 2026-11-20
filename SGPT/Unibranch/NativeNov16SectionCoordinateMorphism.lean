import SGPT.Unibranch.HironakaG10GenGluing
import SGPT.Unibranch.ComplexSpaceThetaPSH
import SGPT.Foundations.Analysis.Pending.HironakaFiniteSectionGraph

/-! Actual finite quotient sections construct the full original coordinate morphism.
Blueprint: native-nov16-section-coordinate-morphism.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
open HironakaG11BlowupLocality HironakaG10GenGluing SourceReducedComplexSpace
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
open HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
open HironakaActualAnalyticSubspaceResidue HironakaActualAnalyticSubspaceLocalFunctions
open HironakaSmoothCentreRealDomainActualSheafStalk HironakaFiniteSectionGraph

private def sectionVector {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (O : Opens M)
    (t : Fin k → actualComplexSection (n := n) O) : O → ComplexModel k :=
  fun z => WithLp.toLp 2 (fun i => t i z)

private theorem sectionVector_smooth {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (O : Opens M)
    (t : Fin k → actualComplexSection (n := n) O) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ (sectionVector O t) := by
  let E := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℂ)).symm
  have ht : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Fin k → ℂ) ∞
      (fun z : O => fun i => t i z) :=
    contMDiff_pi_space.mpr fun i => smoothSheaf.contMDiff_section (t i)
  exact E.toContinuousLinearMap.contMDiff.comp ht

private theorem coordinateOpen_paracompact {n : ℕ} (P : Opens (ComplexModel n))
    (C : Set P) (W : Opens (TopCat.of C)) : ParacompactSpace W := by
  change ParacompactSpace {x : C // x ∈ W}
  infer_instance

@[implicit_reducible]
def coordinateSource {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := n) C) (W : Opens (TopCat.of C)) :
    SourceReducedComplexSpace := by
  exact @openSubspace (sourceReducedComplexSpaceModel P C hC) W
    (coordinateOpen_paracompact P C W)

theorem exists_unique_coordinate_morphism {n k : ℕ}
    (P : Opens (ComplexModel n)) (C : Set P) (hC : IsComplexAnalyticSubset (n := n) C)
    (W : Opens (TopCat.of C))
    (s : Fin k → ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier) :
    ∃! F : coordinateSource P C hC W ⟶
        domainSpace (⊤ : Opens (ComplexModel k)),
      ∀ (x : W) (i : Fin k), (F.hom.left.base x).val.val i =
        actualSubspaceStalkEval (n := n) C x.val
          ((actualSubspaceSheaf (n := n) C).presheaf.germ W x.val x.property (s i)) := by
  classical
  let : ParacompactSpace W := coordinateOpen_paracompact P C W
  let X := sourceReducedComplexSpaceModel P C hC
  let A := coordinateSource P C hC W
  let B := domainSpace (⊤ : Opens (ComplexModel k))
  let φ : A.obj.left → B.obj.left := fun x => ⟨⟨WithLp.toLp 2 (fun i =>
    actualSubspaceStalkEval (n := n) C x.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W x.val x.property (s i))),by trivial⟩,by trivial⟩
  have hlocal (a : A.obj.left) : ∃ (T : LocallyRingedSpace) (j : T ⟶ A.obj.left)
      (F : T ⟶ B.obj.left), LocallyRingedSpace.IsOpenImmersion j ∧ a ∈ range j.base ∧
      F ≫ B.obj.hom = j ≫ A.obj.hom ∧ ∀ y, F.base y = φ (j.base y) := by
    obtain ⟨O,haO,t,hOW,ht⟩ := exists_finite_ambient_sections C W s a.val a.property
    let C' : Set O := (Subtype.val : O → P) ⁻¹' C
    let T := actualSubspaceLocallyRingedSpace (n := n) C'
    let i0 : T ⟶ X.obj.left := actualOpenSubspaceMap (n := n) C O
    let j0 : A.obj.left ⟶ X.obj.left :=
      (@openSubspaceInclusion X W (coordinateOpen_paracompact P C W)).hom.left
    let : LocallyRingedSpace.IsOpenImmersion j0 :=
      @openSubspaceInclusion_isOpenImmersion X W (coordinateOpen_paracompact P C W)
    have hlands : range i0.base ⊆ range j0.base := by
      rintro _ ⟨y,rfl⟩
      exact ⟨⟨⟨y.val.val,y.property⟩,hOW ⟨y.val.val,y.property⟩ y.val.property⟩,rfl⟩
    let j : T ⟶ A.obj.left := LocallyRingedSpace.IsOpenImmersion.lift j0 i0 hlands
    have hj : j ≫ j0 = i0 := LocallyRingedSpace.IsOpenImmersion.lift_fac j0 i0 hlands
    have hjopen : LocallyRingedSpace.IsOpenImmersion j := by
      dsimp only [j,LocallyRingedSpace.IsOpenImmersion.lift]
      infer_instance
    let f : O → (⊤ : Opens (ComplexModel k)) := fun z => ⟨sectionVector O t z,by trivial⟩
    have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ f :=
      (ContMDiff.subtypeVal_comp_iff ⊤ f).mp (sectionVector_smooth O t)
    let F : T ⟶ B.obj.left := actualSubspaceMap hf (fun _ _ => mem_univ _)
    have hja : a ∈ range j.base := by
      let y : C' := ⟨⟨a.val.val,haO⟩,a.val.property⟩
      refine ⟨y,?_⟩
      have hj0 : LocallyRingedSpace.IsOpenImmersion j0 := inferInstance
      apply hj0.base_open.injective
      exact congrArg (fun q : T ⟶ X.obj.left => q.base y) hj
    have hjpoint : j ≫ A.obj.hom = subspacePointMap (n := n) C' := by
      change j ≫ (j0 ≫ X.obj.hom) = _
      rw [← Category.assoc,hj]
      exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
    refine ⟨T,j,F,hjopen,hja,?_,?_⟩
    · rw [hjpoint]
      exact actualSubspaceMap_point hf (fun _ _ => mem_univ _)
    · intro y
      let b : C := ⟨y.val.val,y.property⟩
      let bW : W := ⟨b,hOW b y.val.property⟩
      have hby : j.base y = bW := by
        apply Subtype.ext
        exact congrArg (fun q : T ⟶ X.obj.left => q.base y) hj
      rw [hby]
      apply Subtype.ext
      apply Subtype.ext
      ext i
      change t i y.val = actualSubspaceStalkEval (n := n) C b
        ((actualSubspaceSheaf (n := n) C).presheaf.germ W b (hOW b y.val.property) (s i))
      rw [ht i b y.val.property]
      exact (actualSubspaceStalkEval_inclusion_germ C O (t i) b y.val.property).symm
  obtain ⟨G,hG⟩ := exists_hom_of_local φ hlocal
  have hcoords : ∀ (x : W) (i : Fin k), (G.hom.left.base x).val.val i =
      actualSubspaceStalkEval (n := n) C x.val
        ((actualSubspaceSheaf (n := n) C).presheaf.germ W x.val x.property (s i)) := by
    intro x i
    exact congrArg (fun z : B.obj.left => z.val.val i) (hG x)
  refine ⟨G,hcoords,?_⟩
  intro G' hG'
  apply morphism_eq_of_pointwise_eq
  intro x
  apply Subtype.ext
  apply Subtype.ext
  ext i
  exact (hG' x i).trans (hcoords x i).symm

end SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
