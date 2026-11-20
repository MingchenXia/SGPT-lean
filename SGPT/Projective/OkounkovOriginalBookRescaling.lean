import SGPT.Projective.OkounkovOriginalBookOrderContinuity
import SGPT.Okounkov.ValGen2Res

/-! Entire integer rescaling in SAME actual ORIGINAL full-line power bodies' OWN cones, ALL dimensions.
Blueprint: okounkov-original-book-rescaling.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class SGPT.Okounkov.ValGen2
open scoped Topology ENNReal Pointwise

/-- Genuine literal cone carriers transport by x↦r*x, preserving SAME actual normalized body. -/
theorem veronese_coneOver_subset_smul_coneOver {n : ℕ} (K : Set (Fin n → ℝ))
    (hKc : IsCompact K) (hKv : Convex ℝ K) {r : ℕ} (hr : 0<r) :
    ((veroneseCone (SGPT.GAGA.OkoClose.coneOver K hKc hKv) hr).cone : Set ((Fin n → ℝ) × ℝ)) ⊆
      (SGPT.GAGA.OkoClose.coneOver ((r:ℝ) • K) (IsCompact.smul (r:ℝ) hKc) (hKv.smul (r:ℝ))).cone := by
  intro z hz
  have hz' := (mem_veroneseCone hr z).mp hz
  change 0 ≤ (r:ℝ)*z.2 ∧ ∃ x ∈ K, z.1 = ((r:ℝ)*z.2) • x at hz'
  change 0 ≤ z.2 ∧ ∃ y ∈ (r:ℝ) • K, z.1 = z.2 • y
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  refine ⟨(mul_nonneg_iff_of_pos_left hrR).mp hz'.1,?_⟩
  obtain ⟨x,hx,hzx⟩ := hz'.2
  refine ⟨(r:ℝ) • x,⟨x,hx,rfl⟩,?_⟩
  simpa only [smul_smul,mul_comm] using hzx

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance originalBookRescalingTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBookRescalingCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalBookRescalingManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
include E hbig hv

/-- Actual original positive NONPLURIPOLAR mass produces raw canonical own-body almost-space domain. -/
theorem exists_ownBody_multiplierAlmostSpace_of_mass_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hmass : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) φ hφ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (hsub : centreMultiplierSectionSet f n E v a φ ⊆
        (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set ((Fin n → ℤ) × ℤ))),
      (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
        almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  obtain ⟨hKc,hKv,_,hSL,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a n E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := hfull.2
  have hsub : centreMultiplierSectionSet f n E v a φ ⊆ (latticePoints C.cone : Set _) :=
    fun _ hz => hSL (AlgebraicValuation.multiplierSectionSet_subset a φ hz)
  refine ⟨hKc,hKv,hsub,?_⟩
  cases n with
  | succ m =>
    exact ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass
      f E Y hY a H c v hSL hG hφ hmass
  | zero =>
    have heq := PobDimZero.valuation_multiplierSectionSet_eq f E Y hY a c v hφ.quasiPshPotential
    have hN : PobDimZero.nonnegHeight ≤ latticePoints C.cone := by
      intro z hz
      apply hsub
      change z ∈ AlgebraicValuation.multiplierSectionSet f 0 E v c a φ
      exact heq.symm ▸ hz
    have hUeq : (⟨_,hsub⟩ : ConeSubset C) = sourceSubset C PobDimZero.nonnegHeight hN := Subtype.ext heq
    rw [hUeq]
    exact PobDimZero.sourceSubset_nonnegHeight_mem_almostSemigroupLocus C hN

/-- ENTIRE integer rescaling in SAME actual original base and power line bodies' OWN cones, ALL n. -/
theorem partialBody_tensorPower_eq_smul_ownBodies_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hmass : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) φ hφ) :
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
  obtain ⟨hKc,hKv,hsub,hΓ⟩ :=
    exists_ownBody_multiplierAlmostSpace_of_mass_allDimensions f n E a H hbig v hv hφ hmass
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
