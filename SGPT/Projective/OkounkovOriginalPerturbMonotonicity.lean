import SGPT.Projective.OkounkovOriginalPerturbIsomorphisms
import SGPT.Projective.OkounkovOriginalBigOfIVolume
import SGPT.AlmostSemigroup.CommonConeMonotonicity

/-! Actual original ample-perturbation raw multiplier inclusions and SAME own partial-body monotonicity.
Blueprint: okounkov-original-perturb-monotonicity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbMonotonicity
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance perturbMonoTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbMonoCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbMonoManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- ONE ample degree BEFORE ALL original data gives literal raw carrier inclusion into each genuine ample augmentation. -/
theorem exists_ample_multiple_perturb_multiplier_inclusions {A : X.Modules}
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ d : ℕ, 0<d ∧ ∀ {L : X.Modules} (_a : LineBundleAtlas L) (q p m : ℕ)
      (b : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
      (b' : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A (p+d*m))))
      (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X) (_hc : IsNonnegAt v c)
      (φ : SchemeComplexPoint f → EReal),
      AlgebraicValuation.multiplierSectionSet f n E v c b φ ⊆
        AlgebraicValuation.multiplierSectionSet f n E v c b' φ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨d,hd,hraw⟩ := OriginalTensorMultiplier.exists_ample_multiple_multiplier_inclusions f n E aA P
  refine ⟨d,hd,?_⟩
  intro L a q p m b b' v c hc φ
  let aU := pairwiseTensorAtlas b (aA.tensorPower (d*m))
  exact (hraw m b aU v c hc φ).trans
    (OriginalIsoMultiplier.multiplierSectionSet_subset_iso f n E
      (OriginalPerturbIsomorphisms.perturbAddIso a aA q p (d*m)) aU b' v hc φ)

/-- Actual original section multiplication gives SAME existing own-body inclusion, without supplied target inclusions or bigness. -/
theorem exists_ample_multiple_own_partialBody_inclusions [Nonempty (SchemeComplexPoint f)]
    {A : X.Modules} (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ d : ℕ, 0<d ∧ ∀ {L : X.Modules} (_a : LineBundleAtlas L) (q p m : ℕ)
      (b : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
      (H : SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
      (b' : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A (p+d*m))))
      (H' : SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower L q) (bundleTensorPower A (p+d*m))))
      (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (_hv : Function.Surjective v)
      (c : X) (_hc : IsNonnegAt v c) (φ : SchemeComplexPoint f → EReal)
      (hφ : IsThetaPshPotential (H.curvature b).val φ)
      (_hpos : 0 < iVolume (H.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
      (hφ' : IsThetaPshPotential (H'.curvature b').val φ)
      (_hpos' : 0 < iVolume (H'.curvature b') (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ'),
      ∃ (hKc : IsCompact (okounkovBody v c b)) (hKv : Convex ℝ (okounkovBody v c b))
        (hKc' : IsCompact (okounkovBody v c b')) (hKv' : Convex ℝ (okounkovBody v c b')),
        ValGen.partialBody f n E v c b (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ ⊆
          ValGen.partialBody f n E v c b' (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨d,hd,hraw⟩ := exists_ample_multiple_perturb_multiplier_inclusions f n E aA P
  refine ⟨d,hd,?_⟩
  intro L a q p m b H b' H' v hv c hc φ hφ hpos hφ' hpos'
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f n E b H hφ hpos
  have hbig' := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f n E b' H' hφ' hpos'
  obtain ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩ :=
    OriginalBook.multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E b H hbig v hv c hφ hpos
  obtain ⟨hKc',hKv',hsub',hΓ',hvol',hbody',hvolume'⟩ :=
    OriginalBook.multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E b' H' hbig' v hv c hφ' hpos'
  refine ⟨hKc,hKv,hKc',hKv',?_⟩
  rw [hbody,hbody']
  exact CommonConeMonotonicity.bodyExtension_mono_of_carrier_subset ⟨⟨_,hsub⟩,hΓ⟩ ⟨⟨_,hsub'⟩,hΓ'⟩
    (hraw a q p m b b' v c hc φ)
end SGPT.Okounkov.OriginalPerturbMonotonicity
