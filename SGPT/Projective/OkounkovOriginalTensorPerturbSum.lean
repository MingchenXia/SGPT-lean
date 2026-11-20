import SGPT.Projective.OkounkovOriginalTensorSumKahler
import SGPT.Projective.OkounkovOriginalPhysicalBodyTransport
import SGPT.Projective.OkounkovOriginalTensorPerturbCurvature
import SGPT.Okounkov.ValGen2Conc

/-! Actual literal normalized cross-class tensor perturbation inclusion, arbitrary original valuation.
Blueprint: okounkov-original-tensor-perturb-sum.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
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
local instance tensorPerturbSumTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorPerturbSumCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance tensorPerturbSumManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_normalized_tensorPerturb_sum_inclusion {L N A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f (m+1) E N)
    (r : LineBundleAtlas A) (G : SchemeLineBundleMetric f (m+1) E A)
    (hG : letI := E.isSeparated;letI := E.quasiCompact;(G.curvature r).val.IsKahler)
    (d : LineBundleAtlas (bundleTensor L N))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (K.curvature b).val ψ)
    (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    let aP := OkoNS.perturbAtlas a r q p
    let bP := OkoNS.perturbAtlas b r q p
    let dP := OkoNS.perturbAtlas d r q (p+p)
    ∃ (hAc : IsCompact (centreOkounkovBody f v aP)) (hAv : Convex ℝ (centreOkounkovBody f v aP))
      (hBc : IsCompact (centreOkounkovBody f v bP)) (hBv : Convex ℝ (centreOkounkovBody f v bP))
      (hDc : IsCompact (centreOkounkovBody f v dP)) (hDv : Convex ℝ (centreOkounkovBody f v dP)),
      (q:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v) aP (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) (fun x => (q:EReal)*φ x) +
        (q:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v) bP (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) (fun x => (q:EReal)*ψ x) ⊆
      (q:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v) dP (SGPT.GAGA.OkoClose.coneOver _ hDc hDv) (fun x => (q:EReal)*(φ x+ψ x)) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let aP := OkoNS.perturbAtlas a r q p
  let bP := OkoNS.perturbAtlas b r q p
  let dP := OkoNS.perturbAtlas d r q (p+p)
  let HP := originalPerturbMetric f (m+1) E a H r G q p
  let KP := originalPerturbMetric f (m+1) E b K r G q p
  let DT := pairwiseTensorAtlas aP bP
  let HT := HP.tensorProduct KP aP bP
  let HD := originalPerturbMetric f (m+1) E d (H.tensorProduct K a b) r G q (p+p)
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hcoe : ((q:ℝ):EReal)=(q:EReal) := by simp
  have hweight : (fun x => (q:EReal)*φ x+(q:EReal)*ψ x)=(fun x => (q:EReal)*(φ x+ψ x)) := by
    funext x
    rw [←hcoe,ValGen2.ereal_coe_mul_add hqR]
  obtain ⟨hφK,_⟩ := original_positivePerturbation_kahler_and_big f (m+1) E a H r G hG hφ q p hq hp
  obtain ⟨hψK,_⟩ := original_positivePerturbation_kahler_and_big f (m+1) E b K r G hG hψ q p hq hp
  have hTK := original_tensorSum_kahler f (m+1) E aP HP bP KP DT hφK
    (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψK)
  rw [hweight] at hTK
  obtain ⟨hAc,hAv,hBc,hBv,hTc,hTv,hinc⟩ := original_partialBody_tensorSum_kahler f E aP HP bP KP DT v hv hφK hψK
  rw [hweight] at hinc
  have hgeo := original_tensorPerturb_curvatures_geometricallyEq f (m+1) E a H b K r G d q p
  obtain ⟨hTc',hTv',hDc,hDv,heq⟩ := original_kahler_partialBodies_eq_of_geometricallyEq f E DT HT dP HD v hv hgeo.symm hTK
  have hraw := hinc.trans heq.subset
  refine ⟨hAc,hAv,hBc,hBv,hDc,hDv,?_⟩
  rintro z ⟨u,⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,rfl⟩
  refine ⟨x+y,hraw ⟨x,hx,y,hy,rfl⟩,?_⟩
  exact smul_add (q:ℝ)⁻¹ x y
end SGPT.Okounkov.OriginalBook
