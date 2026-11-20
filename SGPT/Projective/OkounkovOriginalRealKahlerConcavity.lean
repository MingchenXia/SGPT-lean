import SGPT.Projective.OkounkovOriginalCoefficientBodyLimit
import SGPT.Projective.OkounkovRationalCoefficientDensity

/-! Real coefficient concavity on the SAME original arbitrary-valuation bodies.
Blueprint: okounkov-original-real-kahler-concavity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance realKahlerConcTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance realKahlerConcCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance realKahlerConcManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_partialBody_real_concavity_kahler {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) ψ)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsKahlerCurrentPotential (H.curvature a) (convexComb t φ ψ) ∧
      t • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ +
        (1-t) • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ ⊆
      ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb t φ ψ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨r,hr,hlim⟩ := RationalCoefficientDensity.exists_positive_rat_sequence_from_left ht0 ht1
  let s := fun j => (r j:ℝ)
  have hs : ∀j,0<s j ∧ s j<t := fun j => ⟨by dsimp only [s];exact_mod_cast (hr j).1,(hr j).2.1⟩
  obtain ⟨hKc,hKv,hχ,hstages,hbodylim⟩ :=
    original_partialBody_left_coefficient_limit_kahler f E a H v hv hφ hψ ht0 ht1 atTop s hs hlim
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let B := fun ρ => ValGen.partialBody f (m+1) E v (valuationCenter f v) a C ρ
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H
    (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E a H hφ)
  have hgeom (ρ : SchemeComplexPoint f → EReal) (hρ : IsKahlerCurrentPotential (H.curvature a) ρ) :
      IsCompact (B ρ) ∧ Convex ℝ (B ρ) ∧ (B ρ).Nonempty := by
    obtain ⟨_,_,hBc,hBv,hBne,_⟩ := OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry
      f E a H hbig v hv (valuationCenter f v) hρ
    exact ⟨hBc,hBv,hBne⟩
  have hstage (j : ℕ) : s j • B φ+(1-s j)•B ψ⊆B (convexComb (s j) φ ψ) := by
    obtain ⟨p,q,hp,hq,hread⟩ := RationalCoefficientDensity.exists_positive_nat_ratio (r j) (hr j).1 (hr j).2.2
    obtain ⟨_,_,_,hinc⟩ := original_partialBody_rational_concavity_kahler f E a H v hv hφ hψ p q hp hq
    let τ : ℚ := (p:ℚ)/(p+q)
    change (τ:ℝ) • B φ+(1-(τ:ℝ))•B ψ⊆B (convexComb (τ:ℝ) φ ψ) at hinc
    have hτ : r j=τ := hread
    rw [←hτ] at hinc
    exact hinc
  refine ⟨hKc,hKv,hχ,?_⟩
  rintro z ⟨u,hu,w,hw,rfl⟩
  rcases hu with ⟨x,hx,rfl⟩
  rcases hw with ⟨y,hy,rfl⟩
  have hpoint : Tendsto (fun j => s j • x+(1-s j)•y) atTop (𝓝 (t•x+(1-t)•y)) :=
    (hlim.smul_const x).add ((tendsto_const_nhds.sub hlim).smul_const y)
  exact SGPT.Convex.MinkowskiHausdorffLimit.mem_of_tendsto_of_hausdorff
    (hgeom _ hχ).1 (hgeom _ hχ).2.2
    (fun j => (hgeom _ (hstages j)).1) (fun j => (hgeom _ (hstages j)).2.2)
    hbodylim hpoint (Eventually.of_forall fun j => hstage j
      ⟨s j•x,⟨x,hx,rfl⟩,(1-s j)•y,⟨y,hy,rfl⟩,rfl⟩)
end SGPT.Okounkov.OriginalBook
