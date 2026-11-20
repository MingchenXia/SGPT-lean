import SGPT.Unibranch.UnibAnBirationalOpen
import SGPT.Unibranch.UnibAnNativeProjectiveReducedComparison
import SGPT.Unibranch.OriginalNativeManifoldOpenImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Set Topology
open SGPT.Okounkov SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

namespace SGPT.BDivisor.BD7

noncomputable section

/-- Pull an actual analytic map back by the good-open isomorphism. The full
factorization is over the same complex point. -/
theorem exists_morphism_lift_of_isIsoOver_bd7
    {A B T : SourceReducedComplexSpace} (π : B ⟶ A) (G : T ⟶ A)
    {S : Set A.obj.left} (hπ : IsIsoOver π S)
    (hG : ∀ x : T.obj.left, G.hom.left.base x ∈ S) :
    ∃ L : T ⟶ B, L ≫ π = G := by
  obtain ⟨V, j, _, _, hjπ, hRange⟩ := hπ
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ π.hom.left) := hjπ
  have hR : range G.hom.left.base ⊆ range (j ≫ π.hom.left).base := by
    rw [hRange]
    rintro _ ⟨x, rfl⟩
    exact hG x
  let l := LocallyRingedSpace.IsOpenImmersion.lift (j ≫ π.hom.left) G.hom.left hR
  have hl : l ≫ (j ≫ π.hom.left) = G.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hR
  have hfac : (l ≫ j) ≫ π.hom.left = G.hom.left :=
    (Category.assoc _ _ _).trans hl
  have hover : (l ≫ j) ≫ B.obj.hom = T.obj.hom := by
    rw [← Over.w π.hom, ← Category.assoc, hfac, Over.w G.hom]
  refine ⟨ObjectProperty.homMk (Over.homMk (l ≫ j) hover), ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hfac

/-- The inverse over the good algebraic open, evaluated on an arbitrary native
manifold map to the original analytification. The projected point is literally
the input complex point under the original point reader. -/
theorem exists_holomorphic_lift_over_birationalOpen_bd7
    {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)] [LocallyOfFiniteType (ρ ≫ f)]
    [SmoothOfRelativeDimension 1 (ρ ≫ f)]
    (U : X.Opens) [IsIso (ρ ∣_ U)]
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
    [IsComplexManifold m M] (G : wholeModel (n := m) M ⟶ UnibAn.analytification f)
    (hG : ∀ x : M, schemeComplexPointImage f
      (UnibAn.pointMap f (G.hom.left.base ⟨x, mem_univ x⟩)) ∈ U) :
    letI : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) := schemeAnalyticPointTopology (ρ ≫ f)
    letI : ChartedSpace (ComplexModel 1) (SchemeComplexPoint (ρ ≫ f)) :=
      schemeAnalyticTNChartedSpace (ρ ≫ f) 1
    ∃ u : M → SchemeComplexPoint (ρ ≫ f),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 1) ∞ u ∧
      ∀ x, schemeComplexPointMap (ρ ≫ f) f ρ rfl (u x) =
        UnibAn.pointMap f (G.hom.left.base ⟨x, mem_univ x⟩) := by
  let g := ρ ≫ f
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let : ChartedSpace (ComplexModel 1) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g 1
  let : IsComplexManifold 1 (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g 1
  let π : UnibAn.analytification g ⟶ UnibAn.analytification f :=
    UnibAn.analytificationMorphism ρ rfl
  obtain ⟨L, hL⟩ := exists_morphism_lift_of_isIsoOver_bd7 π G
    (UnibAn.analytificationMorphism_isIsoOver_of_isIso_restrict f ρ U) (fun x => hG x.val)
  obtain ⟨a, ha⟩ := UnibAn.exists_smoothModel_analytification_iso g 1
  let H := L ≫ a.inv
  let u := OriginalNativeManifoldOpenImage.pointMap H
  refine ⟨u, OriginalNativeManifoldOpenImage.pointMap_holomorphic H, ?_⟩
  intro x
  let t : (wholeModel (n := m) M).obj.left := ⟨x, mem_univ x⟩
  have hHa : H ≫ a.hom = L := by simp [H, Category.assoc]
  have hu : UnibAn.pointMap g (L.hom.left.base t) = u x := by
    have hpt := congrArg (fun k => k.hom.left.base t) hHa
    exact (congrArg (UnibAn.pointMap g) hpt).symm.trans (ha (u x))
  have hx := congrArg (fun k => k.hom.left.base t) hL
  rw [← hu, ← UnibAn.pointMap_analytificationMorphism ρ rfl (L.hom.left.base t)]
  exact congrArg (UnibAn.pointMap f) hx

/-- A holomorphic projective map landing pointwise in the actual good image lifts
to the very same smooth normalization model. -/
theorem exists_holomorphic_lift_of_projective_goodOpen_bd7
    {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)] [LocallyOfFiniteType (ρ ≫ f)]
    [SmoothOfRelativeDimension 1 (ρ ≫ f)]
    (E : ClosedProjectiveEmbedding f) (U : X.Opens) [IsIso (ρ ∣_ U)]
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
    [IsComplexManifold m M] :
    let n := E.ambientDimension
    let b := polynomialProjStructureMap ℂ n
    letI : TopologicalSpace (SchemeComplexPoint b) := schemeAnalyticPointTopology b
    letI : ChartedSpace (ComplexModel n) (SchemeComplexPoint b) := schemeAnalyticTNChartedSpace b n
    letI : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) := schemeAnalyticPointTopology (ρ ≫ f)
    letI : ChartedSpace (ComplexModel 1) (SchemeComplexPoint (ρ ≫ f)) :=
      schemeAnalyticTNChartedSpace (ρ ≫ f) 1
    ∀ (P : M → SchemeComplexPoint b)
      (_ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ P)
      (q : M → SchemeComplexPoint f)
      (_ : ∀ x, schemeComplexPointMap f b E.map E.over_base (q x) = P x)
      (_ : ∀ x, schemeComplexPointImage f (q x) ∈ U),
      ∃ u : M → SchemeComplexPoint (ρ ≫ f),
        ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 1) ∞ u ∧
          ∀ x, schemeComplexPointMap (ρ ≫ f) f ρ rfl (u x) = q x := by
  let n := E.ambientDimension
  let b := polynomialProjStructureMap ℂ n
  let : TopologicalSpace (SchemeComplexPoint b) := schemeAnalyticPointTopology b
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint b) := schemeAnalyticTNChartedSpace b n
  let : IsComplexManifold n (SchemeComplexPoint b) := schemeAnalyticTN_isComplexManifold b n
  let : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) := schemeAnalyticPointTopology (ρ ≫ f)
  let : ChartedSpace (ComplexModel 1) (SchemeComplexPoint (ρ ≫ f)) :=
    schemeAnalyticTNChartedSpace (ρ ≫ f) 1
  intro _ _ P hP q hq hU
  obtain ⟨hC, e, he⟩ := UnibAn.exists_projectiveAnalytification_iso_nativeReducedImage f E
  let C := schemeNativeAlgebraicTrace b (range E.map)
  let hW := isComplexAnalyticSubset_univ (n := n) (M := SchemeComplexPoint b)
  let F := nativeMorphism hP
  have hland (x : (wholeModel (n := m) M).obj.left) : (F.hom.left.base x).val ∈ C := by
    change schemeComplexPointImage b (P x.val) ∈ range E.map
    rw [← hq]
    exact ⟨schemeComplexPointImage f (q x.val), (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨K, hK, _⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization
    hC hW (subset_univ C) (wholeModel (n := m) M) F hland
  let G := K ≫ e.inv
  have hread (x : M) :
      UnibAn.pointMap f (G.hom.left.base ⟨x, mem_univ x⟩) = q x := by
    let t : (wholeModel (n := m) M).obj.left := ⟨x, mem_univ x⟩
    have hGe : G ≫ e.hom = K := by simp [G, Category.assoc]
    have hbase := congrArg (fun k => k.hom.left.base t) hGe
    have hKp := congrArg (fun k => (k.hom.left.base t).val) hK
    have hv := OriginalClosedSubspaceFactorization.inclusion_base_val hC hW
      (subset_univ C) (K.hom.left.base t)
    have hV : (K.hom.left.base t).val = P x := hv.symm.trans hKp
    have hc : (e.hom.hom.left.base (G.hom.left.base t)).val = P x :=
      (congrArg Subtype.val hbase).trans hV
    have hinj : Function.Injective (schemeComplexPointMap f b E.map E.over_base) := by
      intro p p' hp
      apply Subtype.ext
      apply (cancel_mono E.map).mp
      exact congrArg Subtype.val hp
    exact hinj ((he (G.hom.left.base t)).symm.trans (hc.trans (hq x).symm))
  obtain ⟨u, hu, hproj⟩ := exists_holomorphic_lift_over_birationalOpen_bd7 f ρ U G
    fun x => by rw [hread]; exact hU x
  exact ⟨u, hu, fun x => (hproj x).trans (hread x)⟩

end

end SGPT.BDivisor.BD7
