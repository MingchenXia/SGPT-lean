import SGPT.Projective.OkounkovOriginalRationalPerturbMonotonicity
import SGPT.Projective.OkounkovOriginalBasePerturbInclusion
import SGPT.Projective.OkounkovOriginalPerturbVolume
import SGPT.Projective.OkounkovOriginalClassVolumeContinuity
import SGPT.Projective.OkounkovSetBodyGeometry

/-! Whole original rational class perturbation, canonical actual centre, arbitrary valuations, all dimensions and exact ORIGINAL I-volume domain.
Blueprint: okounkov-original-book-deltapert.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open scoped Topology Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance bookDeltapertTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookDeltapertCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookDeltapertManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual equal positive rational representations give EXACTLY the SAME normalized original own body. -/
theorem normalized_positivePerturb_partialBody_eq_of_cross_mul_eq {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (c : X) (hc : IsNonnegAt v c)
    (q₁ p₁ q₂ p₂ : ℕ) (hq₁ : 0<q₁) (hp₁ : 0<p₁) (hq₂ : 0<q₂) (hp₂ : 0<p₂)
    (heq : p₁*q₂=p₂*q₁) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hK₁c : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q₁ p₁)))
      (hK₁v : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q₁ p₁)))
      (hK₂c : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q₂ p₂)))
      (hK₂v : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q₂ p₂))),
      (q₁:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q₁ p₁)
        (SGPT.GAGA.OkoClose.coneOver _ hK₁c hK₁v) (fun x => (q₁:EReal)*φ x) =
      (q₂:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q₂ p₂)
        (SGPT.GAGA.OkoClose.coneOver _ hK₂c hK₂v) (fun x => (q₂:EReal)*φ x) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hK₁c,hK₁v,hK₂c,hK₂v,h12⟩ := normalized_positivePerturb_partialBody_mono f n E a H aA P K hK hφ
    v hv c hc q₁ p₁ q₂ p₂ hq₁ hp₁ hq₂ hp₂ heq.le
  obtain ⟨hK₂c',hK₂v',hK₁c',hK₁v',h21⟩ := normalized_positivePerturb_partialBody_mono f n E a H aA P K hK hφ
    v hv c hc q₂ p₂ q₁ p₁ hq₂ hp₂ hq₁ hp₁ heq.ge
  exact ⟨hK₁c,hK₁v,hK₂c,hK₂v,Set.Subset.antisymm h12 h21⟩

/-- ENTIRE original rational perturbation Hausdorff limit, same own bodies/ALL representations/actual canonical centre/alln0. -/
theorem tendsto_normalized_positivePerturb_partialBody_allDimensions {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    let c := valuationCenter f v
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      ∀ (I : Type*) (F : Filter I) (q p : I → ℕ) (_hq : ∀ i, 0<q i) (_hp : ∀ i, 0<p i),
      Tendsto (fun i => (p i:ℝ)/(q i:ℝ)) F (𝓝 0) →
      ∃ (hKic : ∀ i, IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA (q i) (p i))))
        (hKiv : ∀ i, Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA (q i) (p i)))),
        (∀ i, IsCompact ((q i:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA (q i) (p i))
          (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i:EReal)*φ x))) ∧
        (∀ i, ((q i:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA (q i) (p i))
          (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i:EReal)*φ x)).Nonempty) ∧
        Tendsto (fun i => Metric.hausdorffDist
          ((q i:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA (q i) (p i))
            (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i:EReal)*φ x))
          (ValGen.partialBody f n E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)) F (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  have hc : IsNonnegAt v c := isNonnegAt_valuationCenter f v
  have hbig := original_isBig_of_positive_iVolume_allDimensions f n E a H hφ hpos
  obtain ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E a H hbig v hv c hφ hpos
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let B₀ := ValGen.partialBody f n E v c a C φ
  have hB₀c : IsCompact B₀ := ValGen.isCompact_setBody _ _
  have hB₀v : Convex ℝ B₀ := ValGen.convex_setBody _ _
  have hvolume₀ : volume B₀=
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ/(n.factorial:ENNReal) := hvolume
  have hB₀pos : 0<volume B₀ := by
    rw [hvolume₀]
    exact ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hB₀fin : volume B₀≠⊤ := hB₀c.measure_lt_top.ne
  have hB₀ne : B₀.Nonempty :=
    (PartialBody.interior_nonempty_of_convex_of_measure_pos volume hB₀v hB₀pos).mono interior_subset
  have hB₀real : volume.real B₀=
      (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal/(n.factorial:ℝ) := by
    rw [measureReal_def,hvolume₀,ENNReal.toReal_div,ENNReal.toReal_natCast]
  refine ⟨hKc,hKv,?_⟩
  intro I F q p hq hp ht
  choose hφi hKic hKiv hvoli using fun i =>
    normalized_positivePerturb_partialBody_volume f n E a H aA K hK hφ v hv c (q i) (p i) (hq i) (hp i)
  let Ci i := SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)
  let Bi i := (q i:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA (q i) (p i))
    (Ci i) (fun x => (q i:EReal)*φ x)
  have hBic (i : I) : IsCompact (Bi i) := IsCompact.smul _ (ValGen.isCompact_setBody _ _)
  have hBiv (i : I) : Convex ℝ (Bi i) := (ValGen.convex_setBody _ _).smul _
  have hbase (i : I) : B₀⊆Bi i := by
    obtain ⟨hK₀c,hK₀v,hKpc,hKpv,hinc⟩ :=
      partialBody_subset_normalized_positivePerturb f n E a H aA P K hK hφ hpos v hv c hc (q i) (p i) (hq i) (hp i)
    exact hinc
  obtain ⟨hφ₁,hK₁c,hK₁v,hvol₁⟩ :=
    normalized_positivePerturb_partialBody_volume f n E a H aA K hK hφ v hv c 1 1 zero_lt_one zero_lt_one
  let C₁ := SGPT.GAGA.OkoClose.coneOver _ hK₁c hK₁v
  let B₁ := (1:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA 1 1) C₁ (fun x => (1:EReal)*φ x)
  have hB₁c : IsCompact B₁ := IsCompact.smul _ (ValGen.isCompact_setBody _ _)
  have hB₁v : Convex ℝ B₁ := (ValGen.convex_setBody _ _).smul _
  have hbase₁ : B₀⊆B₁ := by
    obtain ⟨hK₀c,hK₀v,hKpc,hKpv,hinc⟩ :=
      partialBody_subset_normalized_positivePerturb f n E a H aA P K hK hφ hpos v hv c hc 1 1 zero_lt_one zero_lt_one
    simpa only [Nat.cast_one] using hinc
  have hupper (i : I) (hi : p i≤q i) : Bi i⊆B₁ := by
    obtain ⟨hKpc,hKpv,hKtc,hKtv,hinc⟩ := normalized_positivePerturb_partialBody_mono f n E a H aA P K hK hφ
      v hv c hc (q i) (p i) 1 1 (hq i) (hp i) zero_lt_one zero_lt_one (by simpa using hi)
    simpa only [Nat.cast_one] using hinc
  let t (i : I) : NNReal := ⟨(p i:ℝ)/(q i:ℝ),div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  have htNN : Tendsto t F (𝓝[>] (0:NNReal)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall fun i => ?_⟩
    · rw [←NNReal.tendsto_coe]
      exact ht
    · change (0:NNReal)<t i
      rw [←NNReal.coe_lt_coe]
      exact div_pos (by exact_mod_cast hp i) (by exact_mod_cast hq i)
  have hmass := (tendsto_original_iVolume_add_smul_allDimensions f n E a H aA K hK hφ).comp htNN
  have hfinite := original_iVolume_ne_top_allDimensions f n E a H hφ
  have hreal := ((ENNReal.tendsto_toReal hfinite).comp hmass).div_const (n.factorial:ℝ)
  have hμreal : Tendsto (fun i => volume.real (Bi i)) F (𝓝 (volume.real B₀)) := by
    rw [hB₀real]
    convert hreal using 1
    funext i
    exact hvoli i
  have hμ : Tendsto (fun i => volume (Bi i)) F (𝓝 (volume B₀)) := by
    have hh := (ENNReal.continuous_ofReal.tendsto (volume.real B₀)).comp hμreal
    rw [show ENNReal.ofReal (volume.real B₀)=volume B₀ from ENNReal.ofReal_toReal hB₀fin] at hh
    exact hh.congr' (Eventually.of_forall fun i => ENNReal.ofReal_toReal (hBic i).measure_lt_top.ne)
  have hsmall : ∀ᶠ i in F, p i≤q i := by
    filter_upwards [ht.eventually_lt_const zero_lt_one] with i hi
    have hh : (p i:ℝ)<(q i:ℝ) := (div_lt_one (by exact_mod_cast hq i)).mp hi
    exact_mod_cast hh.le
  let Li i := if p i≤q i then Bi i else B₁
  have hLiv (i : I) : Convex ℝ (Li i) := by
    dsimp only [Li]
    split_ifs
    · exact hBiv i
    · exact hB₁v
  have hAL (i : I) : B₀⊆Li i := by
    dsimp only [Li]
    split_ifs
    · exact hbase i
    · exact hbase₁
  have hLB (i : I) : Li i⊆B₁ := by
    dsimp only [Li]
    split_ifs with hi
    · exact hupper i hi
    · exact Set.Subset.rfl
  have hμL : Tendsto (fun i => volume (Li i)) F (𝓝 (volume B₀)) :=
    hμ.congr' (hsmall.mono fun i hi => by simp only [Li,if_pos hi])
  have hH := PartialBody.tendsto_hausdorffDist_of_tendsto_measure volume hB₀v hB₀pos hB₀fin hB₁c.isBounded
    hLiv (fun i => (Set.Subset.rfl : Li i⊆Li i)) hAL hLB hμL hμL
  refine ⟨hKic,hKiv,hBic,fun i => hB₀ne.mono (hbase i),?_⟩
  change Tendsto (fun i => Metric.hausdorffDist (Bi i) B₀) F (𝓝 0)
  exact hH.congr' (hsmall.mono fun i hi => by simp only [Li,if_pos hi])
end SGPT.Okounkov.OriginalBook
