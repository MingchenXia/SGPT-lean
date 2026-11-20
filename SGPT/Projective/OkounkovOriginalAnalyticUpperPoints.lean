import SGPT.Projective.OkounkovOriginalTwistedInftyUpper
import SGPT.Projective.OkounkovOriginalScalarBodyConvergence
import SGPT.Projective.OkounkovOriginalInftyBodyLimit
import SGPT.Projective.OkounkovFixedTranslateUpperControl

/-! Genuine upper control of SAME original twisted multiplier values, arbitrary valuation.
Blueprint: okounkov-original-analytic-upper-points.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalAnalyticUpperPoints
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance analyticUpperPointsTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance analyticUpperPointsCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance analyticUpperPointsManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original Kähler-current weights have genuine compact nonempty convex partial bodies in their own cones. -/
theorem exists_kahler_partialBody_geometry {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v) (c : X)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      let K := ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ;
      IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
      volume K = iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        φ (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ) / ((m+1).factorial : ℝ≥0∞) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
  have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hpos := (PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ hθ).trans_le
    (PartialBody.diagonalPotentialMass_le_iVolume (schemeProjectiveTNKahlerBackground f (m+1) E) hθ)
  obtain ⟨hKc,hKv,hsub,hΓ,-,hext,hvol⟩ :=
    OriginalBook.multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m+1) E a H hbig v hv c hθ hpos
  let B := bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc hKv))
  refine ⟨hKc,hKv,?_,?_,?_,hvol⟩
  · rw [hext]; exact B.isCompact
  · rw [hext]; exact B.convex
  · rw [hext]; exact B.nonempty

/-- Every actual twisted multiplier value eventually approaches the SAME original own-cone partial body from outside. -/
theorem exists_analytic_twisted_values_eventually_near_partialBody {L T : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact; HasManifoldAnalyticSingularityType (n:=m+1) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop,
        ∀ x ∈ AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) k (r k) φ,
          ∃ z ∈ ValGen.partialBody f (m+1) E v (valuationCenter f v) a
              (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ,
            dist ((k:ℝ)⁻¹ • euclideanCast (m+1) x) z ≤ η := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨hKc,hKv,r₀,hr0,hr1,hscalar,hconv⟩ :=
    OriginalBook.exists_left_scalar_partialBody_convergence f E a H hbig v hv hφ
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let c := valuationCenter f v
  have hc : IsNonnegAt v c := isNonnegAt_valuationCenter f v
  let K := ValGen.partialBody f (m+1) E v c a C φ
  obtain ⟨hKc₁,hKv₁,hKcompact,hKconv,hKnonempty,hKvolume⟩ := exists_kahler_partialBody_geometry f E a H hbig v hv c hφ
  obtain ⟨s : ℚ,hs0,hs1⟩ := exists_rat_btwn hr1
  let q (i : ℕ) : ℚ := 1-(1-s)/(i+2)
  have hqi (i : ℕ) : r₀ < (q i : ℝ) ∧ (q i : ℝ)<1 := by
    have hden : (1:ℝ)<(i:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) i; linarith
    have hdiff : (0:ℝ)<1-(s:ℝ) := by linarith
    have hdiv0 := div_pos hdiff (by linarith : (0:ℝ)<(i:ℝ)+2)
    have hdiv1 : (1-(s:ℝ))/((i:ℝ)+2) < 1-(s:ℝ) :=
      (div_lt_iff₀ (by linarith : (0:ℝ)<(i:ℝ)+2)).mpr (by nlinarith)
    dsimp only [q]
    push_cast
    constructor <;> linarith
  have hq0 (i : ℕ) : 0<q i := by exact_mod_cast (hr0.trans (hqi i).1)
  have hq1 (i : ℕ) : q i<1 := by exact_mod_cast (hqi i).2
  let qr (i : ℕ) : Ioo r₀ 1 := ⟨(q i : ℝ),hqi i⟩
  have hqlim : Tendsto (fun i => (qr i).val) atTop (𝓝 1) := by
    have hd := (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (1-(s:ℝ)))
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hd
    convert hh using 1 <;> simp [qr,q]
  let ψ (i : ℕ) : SchemeComplexPoint f → EReal := fun p => ((q i : ℝ):EReal)*φ p
  let F (i : ℕ) := ValGen.partialBody f (m+1) E v c a C (ψ i)
  have hFgeom (i : ℕ) : IsCompact (F i) ∧ (F i).Nonempty := by
    obtain ⟨hKci,hKvi,hFc,hFv,hFn,hFvolume⟩ := exists_kahler_partialBody_geometry f E a H hbig v hv c (hscalar (qr i))
    exact ⟨hFc,hFn⟩
  have hlim : Tendsto (fun i => Metric.hausdorffDist (F i) K) atTop (𝓝 0) :=
    hconv ℕ atTop qr hqlim
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨j,t,ht⟩ := (exists_twisted_section_ne_zero f E Y hY a hbig hbig.volume_pos (dualAtlas aT)).exists
  let rD := pairwiseTensorAtlas (dualAtlas aT) (a.tensorPower j)
  let w := euclideanCast (m+1) (plainSectionVector v c rD t ht)
  let Q (k : ℕ) := euclideanCast (m+1) ''
    AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ
  have hupper (i : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ x ∈ Q k,
      ((k+j:ℕ):ℝ)⁻¹ • (x+w) ∈ F i := by
    obtain ⟨k₀,hk₀,hu⟩ := OriginalTwistedInftyUpper.exists_eventual_upperProduct_isInftySection
      f E a aT H (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ) hφan
        (q i) (hq0 i) (hq1 i) j t
    obtain ⟨hKci,hKvi,hbody,hdegree⟩ := OriginalInftyBodyLimit.infty_body_eq_partialBody_and_degree_limit
      f E a H hbig v hv c (hscalar (qr i))
        (TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul hφan (hq0 i).le)
    filter_upwards [eventually_ge_atTop k₀] with k hk x hx
    obtain ⟨z,⟨s,hs,hI,hz⟩,rfl⟩ := hx
    have hk0 : k≠0 := Nat.ne_of_gt (lt_of_lt_of_le hk₀ hk)
    have hinf := hu k hk s (hI.resolve_left hk0)
    obtain ⟨hp,hvec⟩ := upperProduct_vector a aT v hc k j (r k) rD hs ht
    have hmem : (z+plainSectionVector v c rD t ht,((k+j:ℕ):ℤ)) ∈ ValGen.inftySemigroup f E a c v (ψ i) :=
      ⟨k+j,upperProduct a aT k j s t,hp,hinf,
        Prod.ext ((congrArg (fun z => z+plainSectionVector v c rD t ht) hz).trans hvec.symm) rfl⟩
    have hnorm := normalizedPoint_mem_heightOne
      (closedCone (ValGen.inftySemigroup f E a c v (ψ i)))
      (z := (z+plainSectionVector v c rD t ht,((k+j:ℕ):ℤ)))
      (mem_closedCone_of_mem _ hmem)
      (by change (0:ℤ)<((k+j:ℕ):ℤ); exact_mod_cast Nat.add_pos_left (Nat.pos_of_ne_zero hk0) j)
    have hbody' : (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ''
        body (ValGen.inftySemigroup f E a c v (ψ i)) = F i := hbody
    rw [←hbody']
    refine ⟨_,hnorm,?_⟩
    change (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm
        (((k+j:ℕ):ℝ)⁻¹ • Counting.integerCast (z+plainSectionVector v c rD t ht)) =
      ((k+j:ℕ):ℝ)⁻¹ • (euclideanCast (m+1) z + euclideanCast (m+1) (plainSectionVector v c rD t ht))
    rw [map_smul]
    congr 1
    exact (euclideanCast (m+1)).map_add _ _
  have hnear := FixedTranslateUpperControl.eventually_near_of_fixed_translate hKcompact hKnonempty
    F (fun i => (hFgeom i).1) (fun i => (hFgeom i).2) hlim Q j w hupper
  refine ⟨hKc,hKv,?_⟩
  intro η hη
  filter_upwards [hnear η hη] with k hk x hx
  exact hk _ ⟨x,hx,rfl⟩
end SGPT.Okounkov.OriginalAnalyticUpperPoints
