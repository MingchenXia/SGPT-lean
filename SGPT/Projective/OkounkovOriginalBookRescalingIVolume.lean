import SGPT.Projective.OkounkovOriginalBookRescaling

/-! Printed prop:res under ORIGINAL I-volume positivity, in ACTUAL OWN original base/power cones.
Earlier frozen5d6 scoped NPP-positive proof retained; explicit scope erratum in work receipt.
Blueprint: okounkov-original-book-rescaling-ivolume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class SGPT.Okounkov.ValGen2
open scoped Topology ENNReal Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance originalBookRescalingIVolumeTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBookRescalingIVolumeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalBookRescalingIVolumeManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
include E hbig hv

/-- ENTIRE integer rescaling in SAME actual original base and power line bodies' OWN cones, ALL n. -/
theorem partialBody_tensorPower_eq_smul_ownBodies_of_iVolume_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      ∀ (r : ℕ) (_hr : 0<r) (b : LineBundleAtlas (bundleTensorPower L r)),
      ∃ (hKrc : IsCompact (centreOkounkovBody f v b)) (hKrv : Convex ℝ (centreOkounkovBody f v b))
        (hsubR : centreMultiplierSectionSet f n E v b (fun z => (r:EReal)*φ z) ⊆
          (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKrc hKrv).cone : Set ((Fin n → ℤ) × ℤ))),
        (⟨_,hsubR⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKrc hKrv)) ∈
          almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKrc hKrv) ∧
        ValGen.partialBody f n E v (valuationCenter f v) b (SGPT.GAGA.OkoClose.coneOver _ hKrc hKrv)
            (fun z => (r:EReal)*φ z) =
          (r:ℝ) • ValGen.partialBody f n E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  have hc := isNonnegAt_valuationCenter f v
  obtain ⟨hKc,hKv,hsub,hΓ,-⟩ :=
    centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E a H hbig v hv hφ hpos
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  refine ⟨hKc,hKv,?_⟩
  intro r hr b
  have hres := ValGen2.partialBody_tensorPower_eq_smul f n E v hc a hr b φ hsub hΓ
  obtain ⟨hsub',hΓ'⟩ := hres.1
  have hKpower : centreOkounkovBody f v b = (r:ℝ) • centreOkounkovBody f v a :=
    okounkovBody_tensorPower hc a hr b
  have hKrc : IsCompact (centreOkounkovBody f v b) := by
    rw [hKpower]
    exact IsCompact.smul (r:ℝ) hKc
  have hKrv : Convex ℝ (centreOkounkovBody f v b) := by
    rw [hKpower]
    exact hKv.smul (r:ℝ)
  let D := SGPT.GAGA.OkoClose.coneOver _ hKrc hKrv
  have hCD : ((veroneseCone C hr).cone : Set ((Fin n → ℝ) × ℝ)) ⊆ D.cone := by
    intro z hz
    have hmap := veronese_coneOver_subset_smul_coneOver (centreOkounkovBody f v a) hKc hKv hr hz
    change 0 ≤ z.2 ∧ ∃ y ∈ centreOkounkovBody f v b, z.1 = z.2 • y
    rw [hKpower]
    exact hmap
  have hsubR : centreMultiplierSectionSet f n E v b (fun z => (r:EReal)*φ z) ⊆
      (latticePoints D.cone : Set ((Fin n → ℤ) × ℤ)) := fun _ hz => hCD (hsub' hz)
  have hΓR : (⟨_,hsubR⟩ : ConeSubset D) ∈ almostSemigroupLocus D :=
    SGPT.AlmostSemigroup.ConeIndependence.includeSubset_mem_almostSemigroupLocus hCD hΓ'
  refine ⟨hKrc,hKrv,hsubR,hΓR,?_⟩
  change ValGen.setBody D (AlgebraicValuation.multiplierSectionSet f n E v c b
      (fun z => (r:EReal)*φ z)) =
    (r:ℝ) • ValGen.partialBody f n E v c a C φ
  exact (ValGen2.setBody_of_cone_le hCD hsub' hΓ').trans hres.2


end SGPT.Okounkov.OriginalBook
