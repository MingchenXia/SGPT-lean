import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.ValGenInfty
import SGPT.Okounkov.PobDimZeroCore

/-! Entire thm:Gammaasg / def:Okounkov:L687 domain / cor:POBvolume on SAME raw original objects.
Blueprint: okounkov-original-book-partial.tex. -/
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
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance originalBookPartialTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBookPartialCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalBookPartialManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

/-- Finiteness of EXISTING actual original I-volume, manufactured from real original projective geometry. -/
theorem original_iVolume_ne_top_allDimensions {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ ≠ ⊤ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  cases n with
  | succ m =>
    let F := schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY
    have hfinite := ((PartialBody.convex_isCompact_generalPartialBody (F:=F) hφ).2.measure_lt_top
      (μ := (volume : Measure (Fin (m+1) → ℝ)))).ne
    rw [PartialBody.volume_generalPartialBody_uncond (F:=F) hφ] at hfinite
    intro htop
    apply hfinite
    rw [htop]
    exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)
  | zero =>
    have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
    rw [PobDimZero.iVolume_eq_one (H.curvature a) _ hφ]
    exact ENNReal.one_ne_top

variable (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X)
include E hbig hv

/-- ENTIRE original multiplier almost-semigroup/domain/LITERAL partial-body volume, ALL dimensions. -/
theorem multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
        (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set ((Fin n → ℤ) × ℤ)))
      (hΓ : (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
        almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)),
      ConeSubset.volume (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) =
        (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
          (n.factorial:ℝ) ∧
      ValGen.partialBody f n E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        (SGPT.AlmostSemigroup.OkounkovExtension.bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) :
          Set (EuclideanSpace ℝ (Fin n))) ∧
      volume (ValGen.partialBody f n E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) =
        iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
          (n.factorial:ℝ≥0∞) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  obtain ⟨hKc,hKv,_,hSL,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a n E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := hfull.2
  have hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
      (latticePoints C.cone : Set ((Fin n → ℤ) × ℤ)) :=
    fun _ hz => hSL (AlgebraicValuation.multiplierSectionSet_subset a φ hz)
  let U : ConeSubset C := ⟨_,hsub⟩
  obtain ⟨hΓ,hvol⟩ : U ∈ almostSemigroupLocus C ∧ ConeSubset.volume U =
      (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
        (n.factorial:ℝ) := by
    cases n with
    | succ m =>
      have hpositive := AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpos
      have h := ValGen.multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H c v hSL hG hφ hpositive
      have hmass := AlgPOB.volume_real_generalPartialBody f E Y hY a H hφ
      exact ⟨h.1,h.2.1.trans hmass⟩
    | zero =>
      have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
      have heq := PobDimZero.valuation_multiplierSectionSet_eq f E Y hY a c v hφ.quasiPshPotential
      have hN : PobDimZero.nonnegHeight ≤ latticePoints C.cone := by
        intro z hz
        exact hsub (heq.symm ▸ hz)
      have hUeq : U = sourceSubset C PobDimZero.nonnegHeight hN := Subtype.ext heq
      rw [hUeq,PobDimZero.iVolume_eq_one (H.curvature a) _ hφ]
      simp only [ENNReal.toReal_one,Nat.factorial_zero,Nat.cast_one,div_one]
      exact ⟨PobDimZero.sourceSubset_nonnegHeight_mem_almostSemigroupLocus C hN,
        PobDimZero.volume_sourceSubset_nonnegHeight C hN⟩
  have hbody := ValGen.partialBody_eq a φ hsub hΓ
  have hreal := (ValGen.volume_partialBody a φ hsub hΓ).trans hvol
  have hfinite : volume (ValGen.partialBody f n E v c a C φ) ≠ ⊤ := by
    rw [hbody]
    exact (SGPT.AlmostSemigroup.OkounkovExtension.bodyExtension (⟨U,hΓ⟩ : AlmostSpace C)).isCompact.measure_lt_top.ne
  have hrightfinite := ENNReal.div_ne_top (original_iVolume_ne_top_allDimensions f n E a H hφ)
    (show (n.factorial:ℝ≥0∞) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)
  have hvolume : volume (ValGen.partialBody f n E v c a C φ) =
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
        (n.factorial:ℝ≥0∞) :=
    (ENNReal.toReal_eq_toReal_iff' hfinite hrightfinite).mp (by
      simpa only [measureReal_def,ENNReal.toReal_div,ENNReal.toReal_natCast] using hreal)
  exact ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩

/-- Printed canonical-center paired source: actual original center is manufactured from projectivity. -/
theorem centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
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
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (hsub : centreMultiplierSectionSet f n E v a φ ⊆
        (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set ((Fin n → ℤ) × ℤ)))
      (hΓ : (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
        almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)),
      ConeSubset.volume (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) =
        (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
          (n.factorial:ℝ) ∧
      ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ =
        (SGPT.AlmostSemigroup.OkounkovExtension.bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) :
          Set (EuclideanSpace ℝ (Fin n))) ∧
      volume (ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) =
        iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
          (n.factorial:ℝ≥0∞) := by
  let := E.isProper
  exact multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
    f n E a H hbig v hv (valuationCenter f v) hφ hpos

end SGPT.Okounkov.OriginalBook
