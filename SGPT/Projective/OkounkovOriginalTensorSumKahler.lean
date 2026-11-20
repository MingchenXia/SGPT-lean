import SGPT.Projective.OkounkovOriginalTensorSumQEA
import SGPT.Projective.OkounkovOriginalKahlerQEAOwnLimit
import SGPT.Projective.OkounkovOriginalAnalyticUpperPoints
import SGPT.Okounkov.ValGen2Suba
import SGPT.Convex.MinkowskiHausdorffLimit

/-! Actual cross-class original tensor-sum geometry and arbitrary-valuation Kahler body inclusion.
Blueprint: okounkov-original-tensor-sum-kahler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
local instance tensorSumKahlerTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorSumKahlerCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance tensorSumKahlerManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_tensorSum_kahler (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    {L N : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f n E N)
    (d : LineBundleAtlas (bundleTensor L N)) {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (K.curvature b).val ψ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsKahlerCurrentPotential ((H.tensorProduct K a b).curvature d) (fun x => φ x+ψ x) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hraw := TranscendentalCore.isKahlerCurrentPotential_add_smul hφ hψ (a:=1) (b:=1) zero_lt_one zero_le_one
  simp only [one_smul,EReal.coe_one,one_mul] at hraw
  obtain ⟨κ,hκ⟩ := hraw
  refine ⟨κ,?_⟩
  have hgeo := H.curvature_tensorProduct K a b d
  have hh : (((H.tensorProduct K a b).curvature d)-κ.form).val.GeometricallyEq
      (H.curvature a+K.curvature b-κ.form).val := by
    intro c z hz
    rw [sub_eq_add_neg,sub_eq_add_neg,ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_add,hgeo c hz]
  exact (hh.thetaPshPotential_iff (fun x => φ x+ψ x)).mpr hκ

theorem original_partialBody_tensorSum_kahler [IsIntegral X] {m : ℕ}
    [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L N : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f (m+1) E N)
    (d : LineBundleAtlas (bundleTensor L N))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (K.curvature b) ψ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
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
  let c := valuationCenter f v
  let HM := H.tensorProduct K a b
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hψθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψ
  have hsum := original_tensorSum_kahler f (m+1) E a H b K d hφ hψθ
  have hbigA := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφθ
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E a H hφ)
  have hbigB := original_isBig_of_positive_iVolume_allDimensions f (m+1) E b K hψθ
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E b K hψ)
  have hbigD := original_isBig_of_positive_iVolume_allDimensions f (m+1) E d HM
    (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hsum)
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E d HM hsum)
  obtain ⟨hAc,hAv,_,hSA,hfullA⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbigA v hv c
  obtain ⟨hBc,hBv,_,hSB,hfullB⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f b (m+1) E hbigB v hv c
  obtain ⟨hDc,hDv,_,hSD,hfullD⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f d (m+1) E hbigD v hv c
  let CA := SGPT.GAGA.OkoClose.coneOver _ hAc hAv
  let CB := SGPT.GAGA.OkoClose.coneOver _ hBc hBv
  let CD := SGPT.GAGA.OkoClose.coneOver _ hDc hDv
  let A := fun ρ => ValGen.partialBody f (m+1) E v c a CA ρ
  let B := fun ρ => ValGen.partialBody f (m+1) E v c b CB ρ
  let D := fun ρ => ValGen.partialBody f (m+1) E v c d CD ρ
  have geom {M : X.Modules} (aM : LineBundleAtlas M) (KM : SchemeLineBundleMetric f (m+1) E M)
      (hbigM : SGPT.LineBundle.IsBig f M (m+1))
      (hMc : IsCompact (okounkovBody v c aM)) (hMv : Convex ℝ (okounkovBody v c aM))
      (ρ : SchemeComplexPoint f → EReal) (hρ : IsKahlerCurrentPotential (KM.curvature aM) ρ) :
      IsCompact (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ) ∧
      (ValGen.partialBody f (m+1) E v c aM (SGPT.GAGA.OkoClose.coneOver _ hMc hMv) ρ).Nonempty := by
    obtain ⟨_,_,hK,_,hne,_⟩ := OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry f E aM KM hbigM v hv c hρ
    exact ⟨hK,hne⟩
  obtain ⟨U,hU⟩ := PartialBody.exists_isKahlerQEA hφ
  obtain ⟨V,hV⟩ := PartialBody.exists_isKahlerQEA hψ
  let W := fun j x => U j x+V j x
  have hW := original_kahlerQEA_of_geometricallyEq f E (HM.curvature d) (H.curvature a+K.curvature b)
    (H.curvature_tensorProduct K a b d) (original_add_kahlerQEA f E (H.curvature a) (K.curvature b) hU hV)
  have hWK (j : ℕ) : IsKahlerCurrentPotential (HM.curvature d) (W j) :=
    original_tensorSum_kahler f (m+1) E a H b K d (hU.2 j).2 (hV.2 j).1.1
  obtain ⟨_,_,_,hlimU⟩ := original_kahlerQEA_partialBody_limit f E a H v hv hφ U hU
  obtain ⟨_,_,_,hlimV⟩ := original_kahlerQEA_partialBody_limit f E b K v hv hψ V hV
  obtain ⟨_,_,_,hlimW⟩ := original_kahlerQEA_partialBody_limit f E d HM v hv hsum W hW
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (m+1) E
  have hstage (j : ℕ) : A (U j)+B (V j)⊆D (W j) := by
    have hθW := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hWK j)
    have hmW := PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential (hWK j) hθW
    exact ValGen2.partialBody_add_subset_of_analytic f E Y hY c v (isNonnegAt_valuationCenter f v)
      a H b K d HM hSA hfullA.2 hSB hfullB.2 hSD hfullD.2
      (hU.2 j).2 (hU.1.2.1 j) (hV.2 j).2 (hV.1.2.1 j) hθW hmW
  refine ⟨hAc,hAv,hBc,hBv,hDc,hDv,?_⟩
  have hh := SGPT.Convex.MinkowskiHausdorffLimit.weighted_sum_subset_of_hausdorff_limits
    (geom a H hbigA hAc hAv φ hφ).1 (geom a H hbigA hAc hAv φ hφ).2
    (geom b K hbigB hBc hBv ψ hψ).1 (geom b K hbigB hBc hBv ψ hψ).2
    (geom d HM hbigD hDc hDv _ hsum).1 (geom d HM hbigD hDc hDv _ hsum).2
    (fun j => (geom a H hbigA hAc hAv _ (hU.2 j).2).1)
    (fun j => (geom a H hbigA hAc hAv _ (hU.2 j).2).2)
    (fun j => (geom b K hbigB hBc hBv _ (hV.2 j).2).1)
    (fun j => (geom b K hbigB hBc hBv _ (hV.2 j).2).2)
    (fun j => (geom d HM hbigD hDc hDv _ (hWK j)).1)
    (fun j => (geom d HM hbigD hDc hDv _ (hWK j)).2)
    hlimU hlimV hlimW 1 1 (Eventually.of_forall fun j => by simpa only [one_smul] using hstage j)
  simpa only [one_smul,A,B,D,CA,CB,CD,c,centreOkounkovBody] using hh
end SGPT.Okounkov.OriginalBook
