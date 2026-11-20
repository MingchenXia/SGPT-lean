import SGPT.Unibranch.NativeNov16NormalSectionDivision
import SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
import SGPT.Unibranch.OriginalClosedSubspaceFactorization
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPresentation
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity

/-! Full original graph-lift construction; primitive affine-open step.
Blueprint: native-nov16-normal-graph-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16NormalGraphLift
open SourceReducedComplexSpace EmbeddedBlowupOpenRestriction
open HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspace
open PrimeNov16AnalyticNormalizationDenominatorGraph

abbrev affineSpace (k : ℕ) : SourceReducedComplexSpace :=
  ofClosedAnalytic (n := k) (univ : Set (ComplexModel k)) isComplexAnalyticSubset_univ

def affineInclusion {k : ℕ} (V : Opens (ComplexModel k)) : domainSpace V ⟶ affineSpace k :=
  ambientOpenInclusion (n := k) (M := ComplexModel k)
    (W := univ) (isComplexAnalyticSubset_univ (n := k)) V

instance affineInclusion_isOpenImmersion {k : ℕ} (V : Opens (ComplexModel k)) :
    LocallyRingedSpace.IsOpenImmersion (affineInclusion V).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    (actualOpenSubspaceMap (n := k) (univ : Set (ComplexModel k)) V)
  infer_instance

theorem exists_unique_affine_open_lift {k : ℕ} (V : Opens (ComplexModel k))
    (A : SourceReducedComplexSpace) (F : A ⟶ domainSpace (⊤ : Opens (ComplexModel k)))
    (hland : ∀ x : A.obj.left,(F.hom.left.base x).val.val ∈ V) :
    ∃! L : A ⟶ domainSpace V,
      L ≫ affineInclusion V=F ≫ affineInclusion (⊤ : Opens (ComplexModel k)) := by
  let j := affineInclusion V
  let G := F ≫ affineInclusion (⊤ : Opens (ComplexModel k))
  have hr : range G.hom.left.base ⊆ range j.hom.left.base := by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨⟨(F.hom.left.base x).val.val,hland x⟩,trivial⟩,rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left G.hom.left hr
  have hL : L ≫ j.hom.left=G.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left G.hom.left hr
  have hp : L ≫ (domainSpace V).obj.hom=A.obj.hom := by
    rw [← Over.w j.hom,← Category.assoc,hL,Over.w G.hom]
  let L' : A ⟶ domainSpace V := ObjectProperty.homMk (Over.homMk L hp)
  have hL' : L' ≫ j=G := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hL
  refine ⟨L',hL',?_⟩
  intro K hK
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono j.hom.left).mp
  exact (congrArg (fun q => q.hom.left) hK).trans hL.symm

theorem graph_landing_of_dense_denominator {n k : ℕ} {Y : Type} [TopologicalSpace Y]
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (F : Y → wideDomain k U) (hF : Continuous F)
    (hbase : ∀ y,basePoint U (F y) ∈ C)
    (hrel : ∀ y i,H (baseProjection n k (F y).val) * fibreProjection n k (F y).val i =
      G i (baseProjection n k (F y).val))
    (hdense : Dense {y | H (baseProjection n k (F y).val) ≠ 0}) :
    ∀ y,F y ∈ graphClosure U C H G := by
  have hgood : {y | H (baseProjection n k (F y).val) ≠ 0} ⊆
      F ⁻¹' graphClosure U C H G := by
    intro y hy
    apply subset_closure
    refine ⟨(mem_denominatorSet U C H G (F y)).mpr ⟨hbase y,hrel y⟩,?_⟩
    intro hbad
    exact hy ((mem_badSet U H (F y)).mp hbad)
  have hclosed : IsClosed (F ⁻¹' graphClosure U C H G) := isClosed_closure.preimage hF
  intro y
  exact (closure_minimal hgood hclosed) (hdense y)

end SGPT.Unibranch.NativeNov16NormalGraphLift
