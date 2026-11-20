import SGPT.Projective.OkounkovOriginalTensorPerturbSum
import SGPT.Projective.OkounkovOriginalTensorSumIVolume
import SGPT.Projective.OkounkovOriginalBookDeltapert

/-! Original cross-class tensor sum on the actual positive ORIGINAL I-volume domain.
Blueprint: okounkov-original-tensor-sum-positive-ivolume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance tensorSumPositiveIVolTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorSumPositiveIVolCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance tensorSumPositiveIVolManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_partialBody_tensorSum_positive_iVolume {L N A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f (m+1) E N)
    (d : LineBundleAtlas (bundleTensor L N))
    (r : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (G : SchemeLineBundleMetric f (m+1) E A)
    (hG : letI := E.isSeparated;letI := E.quasiCompact;(G.curvature r).val.IsKahler)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (K.curvature b).val ψ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ →
    0 < iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ →
    ∃ (hAc : IsCompact (centreOkounkovBody f v a)) (hAv : Convex ℝ (centreOkounkovBody f v a))
      (hBc : IsCompact (centreOkounkovBody f v b)) (hBv : Convex ℝ (centreOkounkovBody f v b))
      (hDc : IsCompact (centreOkounkovBody f v d)) (hDv : Convex ℝ (centreOkounkovBody f v d)),
      ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ +
        ValGen.partialBody f (m+1) E v (valuationCenter f v) b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) ψ ⊆
      ValGen.partialBody f (m+1) E v (valuationCenter f v) d (SGPT.GAGA.OkoClose.coneOver _ hDc hDv) (fun x => φ x+ψ x) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hposφ hposψ
  let c := valuationCenter f v
  let HM := H.tensorProduct K a b
  let χ := fun x => φ x+ψ x
  obtain ⟨hχ,hposχ⟩ := original_tensorSum_iVolume_pos f E a H b K d hφ hψ hposφ
  have hbigA := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφ hposφ
  have hbigB := original_isBig_of_positive_iVolume_allDimensions f (m+1) E b K hψ hposψ
  have hbigD := original_isBig_of_positive_iVolume_allDimensions f (m+1) E d HM hχ hposχ
  obtain ⟨hAc,hAv,_,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbigA v hv c
  obtain ⟨hBc,hBv,_,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f b (m+1) E hbigB v hv c
  obtain ⟨hDc,hDv,_,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f d (m+1) E hbigD v hv c
  let CA := SGPT.GAGA.OkoClose.coneOver _ hAc hAv
  let CB := SGPT.GAGA.OkoClose.coneOver _ hBc hBv
  let CD := SGPT.GAGA.OkoClose.coneOver _ hDc hDv
  let AA := ValGen.partialBody f (m+1) E v c a CA φ
  let BB := ValGen.partialBody f (m+1) E v c b CB ψ
  let DD := ValGen.partialBody f (m+1) E v c d CD χ
  have geom {M : X.Modules} (aM : LineBundleAtlas M) (KM : SchemeLineBundleMetric f (m+1) E M)
      (hbigM : SGPT.LineBundle.IsBig f M (m+1))
      (hMc : IsCompact (okounkovBody v c aM)) (hMv : Convex ℝ (okounkovBody v c aM))
      (ρ : SchemeComplexPoint f → EReal) (hρ : IsThetaPshPotential (KM.curvature aM).val ρ)
      (hposρ : 0 < iVolume (KM.curvature aM) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ρ hρ) :
      IsCompact (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ) ∧
      (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ).Nonempty := by
    obtain ⟨_,_,_,_,_,_,hvol⟩ := multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m+1) E aM KM hbigM v hv c hρ hposρ
    have hK : IsCompact (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ) := ValGen.isCompact_setBody _ _
    have hV : Convex ℝ (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ) := ValGen.convex_setBody _ _
    have hposV : 0 < volume (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ) := by
      rw [hvol]
      exact ENNReal.div_pos hposρ.ne' (ENNReal.natCast_ne_top _)
    exact ⟨hK,(PartialBody.interior_nonempty_of_convex_of_measure_pos volume hV hposV).mono interior_subset⟩
  let q := fun j : ℕ => j+1
  let p := fun _ : ℕ => 1
  let pd := fun j : ℕ => p j+p j
  have hq : ∀j,0<q j := fun j => Nat.succ_pos j
  have hp : ∀j,0<p j := fun _ => zero_lt_one
  have hpd : ∀j,0<pd j := fun _ => by decide
  have ht : Tendsto (fun j => (p j:ℝ)/(q j:ℝ)) atTop (𝓝 0) := by
    simpa only [p,q,Nat.cast_add,Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have htd : Tendsto (fun j => (pd j:ℝ)/(q j:ℝ)) atTop (𝓝 0) := by
    simpa only [pd,p,Nat.cast_add,Nat.cast_one,mul_one_div,mul_zero] using (ht.const_mul (1+1:ℝ))
  obtain ⟨_,_,hlimA⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E a H r P G hG hφ hposφ v hv
  obtain ⟨_,_,hlimB⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E b K r P G hG hψ hposψ v hv
  obtain ⟨_,_,hlimD⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E d HM r P G hG hχ hposχ v hv
  obtain ⟨hAic,hAiv,hAic',hAine,hAlim⟩ := hlimA ℕ atTop q p hq hp ht
  obtain ⟨hBic,hBiv,hBic',hBine,hBlim⟩ := hlimB ℕ atTop q p hq hp ht
  obtain ⟨hDic,hDiv,hDic',hDine,hDlim⟩ := hlimD ℕ atTop q pd hq hpd htd
  let Ai := fun j => (q j:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v c (OkoNS.perturbAtlas a r (q j) (p j))
    (SGPT.GAGA.OkoClose.coneOver _ (hAic j) (hAiv j)) (fun x => (q j:EReal)*φ x)
  let Bi := fun j => (q j:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v c (OkoNS.perturbAtlas b r (q j) (p j))
    (SGPT.GAGA.OkoClose.coneOver _ (hBic j) (hBiv j)) (fun x => (q j:EReal)*ψ x)
  let Di := fun j => (q j:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v c (OkoNS.perturbAtlas d r (q j) (pd j))
    (SGPT.GAGA.OkoClose.coneOver _ (hDic j) (hDiv j)) (fun x => (q j:EReal)*χ x)
  have hstage (j : ℕ) : Ai j+Bi j⊆Di j := by
    obtain ⟨_,_,_,_,_,_,hinc⟩ := original_normalized_tensorPerturb_sum_inclusion f E a H b K r G hG d v hv hφ hψ (q j) (p j) (hq j) (hp j)
    exact hinc
  refine ⟨hAc,hAv,hBc,hBv,hDc,hDv,?_⟩
  have hh := SGPT.Convex.MinkowskiHausdorffLimit.weighted_sum_subset_of_hausdorff_limits
    (geom a H hbigA hAc hAv φ hφ hposφ).1 (geom a H hbigA hAc hAv φ hφ hposφ).2
    (geom b K hbigB hBc hBv ψ hψ hposψ).1 (geom b K hbigB hBc hBv ψ hψ hposψ).2
    (geom d HM hbigD hDc hDv χ hχ hposχ).1 (geom d HM hbigD hDc hDv χ hχ hposχ).2
    hAic' hAine hBic' hBine hDic' hDine hAlim hBlim hDlim 1 1
    (Eventually.of_forall fun j => by simpa only [one_smul] using hstage j)
  simpa only [one_smul,AA,BB,DD,CA,CB,CD,c,χ,centreOkounkovBody] using hh
end SGPT.Okounkov.OriginalBook
