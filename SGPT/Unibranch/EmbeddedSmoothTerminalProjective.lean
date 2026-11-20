import SGPT.Unibranch.EmbeddedSmoothCentreRange
import SGPT.Unibranch.KSSubmanifoldModel
import SGPT.Unibranch.OriginalClosedSubspaceFactorization
import SGPT.Unibranch.OriginalSmoothDimension
import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Projective.OriginalNativePositiveChowGraph
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-! The actual terminal native model has a holomorphic projective embedding. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Unibranch

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SourceReducedComplexSpace OriginalNativeModification
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FirstPass.BlowupSequences FirstPass.RegularLocusDense FirstPass.NonKahlerLocus
open FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves
open Pending.HironakaResolutionSpaceComplex Pending.SubmanifoldChartedSpace Pending.BlowupTowers
open SGPT.Projective SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped Topology Manifold ContDiff

/-- The flattening model of a fixed-dimensional complex submanifold has the restricted ambient
projective embedding. -/
private theorem terminalSubtype_isHolomorphicEmbedding
    {n d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {S : Set M}
    (hd : d ≤ n) (hS : ∀ x ∈ S, RegularAtDim (n := n) S x d)
    {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ) :
    letI := chartedSpace hd hS
    letI := isComplexManifold_chartedSpace hd hS
    IsHolomorphicEmbedding (n := d) (Ψ ∘ (Subtype.val : S → M)) := by
  let := chartedSpace hd hS
  let := isComplexManifold_chartedSpace hd hS
  have hΨ' := SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ
  have hval := contMDiff_val hd hS
  apply originalEmbedding_of_native_mfderiv (hΨ'.comp hval) (hΨ.injective.comp Subtype.val_injective)
  intro x
  have hΨdiff := (hΨ' x.val).mdifferentiableAt (by simp)
  have hvaldiff := (hval x).mdifferentiableAt (by simp)
  have hΨinj : Function.Injective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) Ψ x.val) := by
    rw [SGPT.Bergman.SiuKodaira.mfderiv_eq_fderiv_complexChartAt hΨdiff]
    change Function.Injective
      (fderiv ℂ (chartMap Ψ x.val (ComplexProjectiveSpace.chartIndex (Ψ x.val)))
        ((complexChartAt (n := n) x.val).val x.val))
    exact hΨ.immersion x.val (ComplexProjectiveSpace.chartIndex (Ψ x.val))
      (ComplexProjectiveSpace.mem_affineChart_chartIndex _)
  have hvalinj : Function.Injective
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) (Subtype.val : S → M) x) := by
    let e := complexChartAt (n := d) x
    let e' := complexChartAt (n := n) x.val
    have hz : e.val x ∈ coordinateDomain (Subtype.val : S → M) e e' :=
      mem_coordinateDomain (mem_complexChartAt_source x) (mem_complexChartAt_source x.val)
    have hinj := Pending.SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val
      hd hS e e' (e.val x) hz
    rw [coordinateMap_fderiv_restrictScalars hval e e' hz] at hinj
    rw [SGPT.Bergman.SiuKodaira.mfderiv_eq_fderiv_complexChartAt hvaldiff]
    change Function.Injective (fderiv ℂ (coordinateMap (Subtype.val : S → M) e e') (e.val x))
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using hinj
  rw [mfderiv_comp x hΨdiff hvaldiff]
  intro a b hab
  exact hvalinj (hΨinj hab)

/-- A connected smooth compact space with a certified closed reduced embedding has a compact
native manifold model whose literal ambient point map gives a holomorphic projective embedding. -/
theorem exists_projectivelyEmbedded_nativeManifold_of_smooth_terminal
    {n N : ℕ} {A : CMfd.{0} n} {Ψ : A → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {Y : SourceReducedComplexSpace} [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left]
    (hY : Y.IsSmooth) (j : Y ⟶ wholeModel (n := n) A)
    (hj : ∃ (C : Set A) (hC : IsComplexAnalyticSubset (n := n) C)
      (e : Y ≅ ofClosedAnalytic C hC), e.hom ≫
      OriginalClosedSubspaceFactorization.inclusion hC isComplexAnalyticSubset_univ
        (Set.subset_univ C) = j) :
    ∃ (d : ℕ) (M : CMfd.{0} d) (a : wholeModel (n := d) M ≅ Y),
      CompactSpace M ∧
        IsHolomorphicEmbedding (n := d) (Ψ ∘ OriginalNativeManifoldOpenImage.pointMap (a.hom ≫ j)) := by
  obtain ⟨C, hC, e, he⟩ := hj
  let E := isoHomeomorph e
  let : IsIso e.hom.hom.left := by
    change IsIso (isoLeft e).hom
    infer_instance
  have hsurj (y : Y.obj.left) : Function.Surjective (e.hom.hom.left.stalkMap y) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
  have hsub := isClosedSubmanifold_ambientImage_of_smoothCentre hC e.hom hY E.isClosedEmbedding hsurj
  have hrange : range e.hom.hom.left.base = univ := range_eq_univ.mpr E.surjective
  have himage : (Subtype.val : C → A) '' (univ : Set C) = C := by
    ext x
    constructor
    · rintro ⟨c, _, rfl⟩
      exact c.property
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  rw [hrange, himage] at hsub
  let : ConnectedSpace C := E.surjective.connectedSpace E.continuous
  let hcompact : CompactSpace C := ⟨by
    have h := isCompact_range E.continuous
    rwa [range_eq_univ.mpr E.surjective] at h⟩
  have hCsmooth : (ofClosedAnalytic C hC).IsSmooth :=
    isSmooth_ofClosedAnalytic_of_isClosedSubmanifold hsub
  let : ConnectedSpace (ofClosedAnalytic C hC).obj.left := by
    change ConnectedSpace C
    infer_instance
  obtain ⟨d, huniform⟩ := OriginalSmoothDimension.exists_uniform_smooth_models hCsmooth
  have hreg : ∀ x ∈ C, RegularAtDim (n := n) C x d := by
    intro x hx
    let c : C := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hsub.2 x hx
    obtain ⟨V, i, hi, hip, hci⟩ := exists_native_chart C hk
    obtain ⟨W, l, hl, hlp, hcl⟩ := huniform c
    have hkd : k = d :=
      OriginalSmoothDimension.smooth_model_dimension_eq V W i l hi hl hip hlp c hci hcl
    simpa only [hkd] using hk
  obtain ⟨c⟩ := (inferInstance : Nonempty C)
  have hd : d ≤ n := (hreg c.val c.property).1
  let := chartedSpace hd hreg
  let := isComplexManifold_chartedSpace hd hreg
  let hval := contMDiff_val hd hreg
  let b : wholeModel (n := d) C ≅ ofClosedAnalytic C hC :=
    KSSubmanifoldModel.wholeModelIso hsub hval (KSSubmanifoldModel.flattening_codRestrict hd hreg)
  let a := b ≪≫ e.symm
  let incl := OriginalClosedSubspaceFactorization.inclusion hC isComplexAnalyticSubset_univ
    (Set.subset_univ C)
  have hae : a.hom ≫ e.hom = b.hom := by
    change (b.hom ≫ e.inv) ≫ e.hom = b.hom
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  have haj : a.hom ≫ j = b.hom ≫ incl := by
    rw [← he, ← Category.assoc, hae]
  have hreadSub : OriginalNativeManifoldOpenImage.pointMap (b.hom ≫ incl) =
      (Subtype.val : C → A) := by
    funext x
    change ((b.hom.hom.left.base ⟨x, mem_univ x⟩).val : A) = x.val
    exact KSSubmanifoldModel.toSubspace_base hsub hval ⟨x, mem_univ x⟩
  have hread : OriginalNativeManifoldOpenImage.pointMap (a.hom ≫ j) = (Subtype.val : C → A) :=
    (congrArg (fun F : wholeModel (n := d) C ⟶ wholeModel (n := n) A =>
      OriginalNativeManifoldOpenImage.pointMap F) haj).trans hreadSub
  refine ⟨d, CMfd.of (n := d) C, a, hcompact, ?_⟩
  change IsHolomorphicEmbedding (n := d) (Ψ ∘ OriginalNativeManifoldOpenImage.pointMap (a.hom ≫ j))
  rw [hread]
  exact terminalSubtype_isHolomorphicEmbedding hd hreg hΨ

end SGPT.Unibranch
