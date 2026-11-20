import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound

/-! Literal local holomorphic disk relation and actual model projections.
Blueprint: complex-local-fiber-relation.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.LocalFiberRelation

/-- Literal complex coordinate for the disk factor. -/
def head (m : ℕ) : ComplexModel (m+1) →L[ℂ] ComplexModel 1 :=
  SourceReducedComplexSpace.discCoordinate.comp (EuclideanSpace.proj (0 : Fin (m+1)))

/-- Literal remaining coordinates, with their actual complex-linear topology. -/
def tail (m : ℕ) : ComplexModel (m+1) →L[ℂ] ComplexModel m :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (fun i => z i.succ)
    map_add' := by intro z w;ext i;rfl
    map_smul' := by intro a z;ext i;rfl }

/-- Literal matching pair in the SAME standard ambient coordinates. -/
def join {m : ℕ} (t : ComplexModel 1) (y : ComplexModel m) : ComplexModel (m+1) :=
  WithLp.toLp 2 (Fin.cons (t 0) (fun i => y i))

@[simp] theorem head_join {m : ℕ} (t : ComplexModel 1) (y : ComplexModel m) :
    head m (join t y) = t := by
  ext i
  fin_cases i
  simp [head,join,SourceReducedComplexSpace.discCoordinate]

@[simp] theorem tail_join {m : ℕ} (t : ComplexModel 1) (y : ComplexModel m) :
    tail m (join t y) = y := by
  ext i
  rfl

variable {m n : ℕ} (U : Opens (ComplexModel 1)) (V : Opens (ComplexModel m))

/-- The actual product-domain window in the unchanged standard coordinates. -/
def ambient : Opens (ComplexModel (m+1)) :=
  ⟨head m ⁻¹' (U : Set (ComplexModel 1)) ∩ tail m ⁻¹' (V : Set (ComplexModel m)),
    (U.isOpen.preimage (head m).continuous).inter (V.isOpen.preimage (tail m).continuous)⟩

variable (D : Set V) (F : ComplexModel 1 → ComplexModel n)
    (G : ComplexModel m → ComplexModel n)

/-- EXACT local disk-base-change equations, not an incoming fiber-product certificate. -/
def carrier : Set (ambient U V) :=
  {z | (⟨tail m z.val,z.property.2⟩ : V) ∈ D ∧ G (tail m z.val) = F (head m z.val)}

variable (hD : IsComplexAnalyticSubset (n := m) D) (hF : ContDiffOn ℂ ∞ F U)
    (hG : ContDiffOn ℂ ∞ G V)

include hD hF hG in
/-- The LITERAL matching equations internally produce an actual analytic carrier. -/
theorem analytic : IsComplexAnalyticSubset (n := m+1) (carrier U V D F G) := by
  let π : ambient U V → V := fun z => ⟨tail m z.val,z.property.2⟩
  have hπ : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel m) ∞ π := by
    apply (ContMDiff.subtypeVal_comp_iff V π).mp
    exact (tail m).contMDiff.comp contMDiff_subtype_val
  have hleft := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ hD
  let H : ambient U V → ComplexModel n := fun z => G (tail m z.val)-F (head m z.val)
  have hH : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel n) ∞ H := by
    have hGa : ContDiffOn ℂ ∞ (fun z => G (tail m z)) (ambient U V) :=
      hG.comp (tail m).contDiff.contDiffOn (fun z hz => hz.2)
    have hFa : ContDiffOn ℂ ∞ (fun z => F (head m z)) (ambient U V) :=
      hF.comp (head m).contDiff.contDiffOn (fun z hz => hz.1)
    exact (hGa.sub hFa).contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hright := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hH
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel n))
  have heq : carrier U V D F G = π ⁻¹' D ∩ H ⁻¹' {0} := by
    ext z
    simp only [carrier,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff,sub_eq_zero,π,H]
  rw [heq]
  exact hleft.inter hright

/-- The actual ORIGINAL left projection, with its real analytic sheaf morphism. -/
def leftMorphism : sourceReducedComplexSpaceModel (ambient U V) (carrier U V D F G)
    (analytic U V D F G hD hF hG) ⟶ domainSpace U :=
  SourceReducedComplexSpace.analyticModelMorphism (analytic U V D F G hD hF hG)
    isComplexAnalyticSubset_univ (head m) (head m).contDiff.contDiffOn
    (fun _ hz => hz.1) (fun _ => trivial)

/-- The actual ORIGINAL right projection to the SAME original carrier. -/
def rightMorphism : sourceReducedComplexSpaceModel (ambient U V) (carrier U V D F G)
    (analytic U V D F G hD hF hG) ⟶ sourceReducedComplexSpaceModel V D hD :=
  SourceReducedComplexSpace.analyticModelMorphism (analytic U V D F G hD hF hG)
    hD (tail m) (tail m).contDiff.contDiffOn (fun _ hz => hz.2) (fun c => c.property.1)

/-- The SAME actual projections satisfy the literal original matching equation. -/
theorem projection_relation (c : carrier U V D F G) :
    G (((rightMorphism U V D F G hD hF hG).hom.left.base c).val.val) =
      F (((leftMorphism U V D F G hD hF hG).hom.left.base c).val.val) := c.property.2

/-- Every actual matching pair is realized on the SAME original relation model. -/
theorem exists_point_of_matching_pair (t : U) (y : D) (hmatch : G y.val.val = F t.val) :
    ∃ c : carrier U V D F G,
      ((leftMorphism U V D F G hD hF hG).hom.left.base c).val.val = t.val ∧
      ((rightMorphism U V D F G hD hF hG).hom.left.base c).val.val = y.val.val := by
  have ha : join t.val y.val.val ∈ ambient U V := by
    constructor
    · change head m (join t.val y.val.val) ∈ U
      rw [head_join]
      exact t.property
    · change tail m (join t.val y.val.val) ∈ V
      rw [tail_join]
      exact y.val.property
  have hc : (⟨join t.val y.val.val,ha⟩ : ambient U V) ∈ carrier U V D F G := by
    constructor
    · have hval : (⟨tail m (join t.val y.val.val),ha.2⟩ : V) = y.val :=
        Subtype.ext (tail_join _ _)
      rw [hval]
      exact y.property
    · simpa only [tail_join,head_join] using hmatch
  exact ⟨⟨⟨join t.val y.val.val,ha⟩,hc⟩,head_join _ _,tail_join _ _⟩

end SGPT.Unibranch.LocalFiberRelation
