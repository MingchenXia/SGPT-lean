import SGPT.Projective.OkounkovOriginalRightScalarAllDimensions
import SGPT.Projective.OkounkovOriginalShrunkPowerBody
import SGPT.Projective.OkounkovConvexBodyScalingLimit

/-! Whole original lma:Hausconvbetato0, actual rational representations/powers/own cones, all dimensions.
Blueprint: okounkov-original-book-hausconv-beta.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.Okounkov.TranscendentalCore
open scoped Topology ENNReal Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance bookHausconvBetaTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookHausconvBetaCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookHausconvBetaManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Whole printed rational shrinking limit in SAME genuine original objects, ALL representations/atlases/dimensions. -/
theorem tendsto_normalized_shrunk_power_partialBody_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (ε : ℝ), 0<ε ∧ ε<1 ∧
      (∀ β : ℚ, 0<β → (β:ℝ)<ε → IsThetaPshPotential ((1-(β:ℝ))•H.curvature a).val φ) ∧
      ∀ (I : Type*) (l : Filter I) (β : I → ℚ) (q p : I → ℕ)
        (_hq : ∀ i, 0<q i) (_hrep : ∀ i, β i=(p i:ℚ)/q i)
        (_hdom : ∀ i, 0<β i ∧ (β i:ℝ)<ε)
        (b : ∀ i, LineBundleAtlas (bundleTensorPower L (q i-p i))),
        Tendsto (fun i => (β i:ℝ)) l (𝓝 0) →
        ∃ hpq : ∀ i, p i<q i,
          Tendsto (fun i => Metric.hausdorffDist
            ((q i:ℝ)⁻¹ • ValGen.partialBody f n E v (valuationCenter f v) (b i)
              (ownPositivePowerCone f v a hKc hKv (q i-p i) (Nat.sub_pos_of_lt (hpq i)) (b i))
              (fun x => (q i:EReal)*φ x))
            (ValGen.partialBody f n E v (valuationCenter f v) a
              (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)) l (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨hKc,hKv,r₁,hr1,hscalar,hconv⟩ :=
    exists_right_scalar_partialBody_convergence_allDimensions f n E a H hbig v hv hφ
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have hrpos : 0<r₁ := zero_lt_one.trans hr1
  have hcap : 0<1-r₁⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hr1)
  let ε : ℝ := (1-r₁⁻¹)/2
  have hε0 : 0<ε := half_pos hcap
  have hε1 : ε<1 := by dsimp only [ε]; have := inv_pos.mpr hrpos; linarith
  have hrange (β : ℚ) (hβ0 : 0<β) (hβε : (β:ℝ)<ε) :
      1<(1-(β:ℝ))⁻¹ ∧ (1-(β:ℝ))⁻¹<r₁ := by
    have hβR0 : (0:ℝ)<β := by exact_mod_cast hβ0
    have hβR1 : (β:ℝ)<1 := hβε.trans hε1
    have hden : 0<1-(β:ℝ) := sub_pos.mpr hβR1
    have hcapβ : (β:ℝ)<1-r₁⁻¹ := hβε.trans (half_lt_self hcap)
    have hh : r₁⁻¹<1-(β:ℝ) := by linarith
    refine ⟨(one_lt_inv₀ hden).mpr (by linarith),?_⟩
    simpa only [inv_inv] using (inv_lt_inv₀ hden (inv_pos.mpr hrpos)).mpr hh
  let sr (β : ℚ) (hβ0 : 0<β) (hβε : (β:ℝ)<ε) : Ioo (1:ℝ) r₁ :=
    ⟨(1-(β:ℝ))⁻¹,hrange β hβ0 hβε⟩
  have hgeometry (ψ : SchemeComplexPoint f → EReal) (hψ : IsKahlerCurrentPotential (H.curvature a) ψ) :
      IsCompact (ValGen.partialBody f n E v (valuationCenter f v) a C ψ) ∧
      Convex ℝ (ValGen.partialBody f n E v (valuationCenter f v) a C ψ) ∧
      (ValGen.partialBody f n E v (valuationCenter f v) a C ψ).Nonempty := by
    have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψ
    have hpos := original_iVolume_pos_of_kahler_allDimensions f n E a H hψ
    obtain ⟨hKc₁,hKv₁,hsub,hΓ,hvol,hext,hvolK⟩ :=
      centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E a H hbig v hv hθ hpos
    let B := bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc₁ hKv₁))
    have hext' : ValGen.partialBody f n E v (valuationCenter f v) a C ψ=(B:Set (EuclideanSpace ℝ (Fin n))) := hext
    rw [hext']
    exact ⟨B.isCompact,B.convex,B.nonempty⟩
  refine ⟨hKc,hKv,ε,hε0,hε1,?_,?_⟩
  · intro β hβ0 hβε
    have hK := hscalar (sr β hβ0 hβε)
    have hs : 0<1-(β:ℝ) := sub_pos.mpr (hβε.trans hε1)
    have hh := isThetaPshPotential_nonneg_smul
      (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hK) hs.le
    have hweight : (fun x => (((1-(β:ℝ)):ℝ):EReal)*(((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x))=φ := by
      funext x
      rw [←mul_assoc,←EReal.coe_mul,mul_inv_cancel₀ hs.ne',EReal.coe_one,one_mul]
    change IsThetaPshPotential ((1-(β:ℝ))•H.curvature a).val
      (fun x => (((1-(β:ℝ)):ℝ):EReal)*(((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x)) at hh
    rwa [hweight] at hh
  · intro I l β q p hq hrep hdom b hβlim
    let r (i : I) := sr (β i) (hdom i).1 (hdom i).2
    have hr : Tendsto (fun i => (r i).val) l (𝓝 1) := by
      have hh := ((tendsto_const_nhds : Tendsto (fun _ : I => (1:ℝ)) l (𝓝 1)).sub hβlim).inv₀ (by norm_num)
      simpa only [sub_zero,inv_one,r,sr] using hh
    let Kset := ValGen.partialBody f n E v (valuationCenter f v) a C φ
    let Fi (i : I) := ValGen.partialBody f n E v (valuationCenter f v) a C
      (fun x => ((r i).val:EReal)*φ x)
    let K : ConvexBody (EuclideanSpace ℝ (Fin n)) :=
      ⟨Kset,(hgeometry φ hφ).2.1,(hgeometry φ hφ).1,(hgeometry φ hφ).2.2⟩
    let F (i : I) : ConvexBody (EuclideanSpace ℝ (Fin n)) :=
      ⟨Fi i,(hgeometry _ (hscalar (r i))).2.1,(hgeometry _ (hscalar (r i))).1,(hgeometry _ (hscalar (r i))).2.2⟩
    have hFlim : Tendsto (fun i => Metric.hausdorffDist ((F i):Set (EuclideanSpace ℝ (Fin n)))
        (K:Set (EuclideanSpace ℝ (Fin n)))) l (𝓝 0) := hconv I l r hr
    have hs : Tendsto (fun i => 1-(β i:ℝ)) l (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : I => (1:ℝ)) l (𝓝 1)).sub hβlim
    have hscaled := ConvexBodyScalingLimit.tendsto_hausdorffDist_smul l F K (fun i => 1-(β i:ℝ)) hFlim hs
    have hpower (i : I) : ∃ hpq : p i<q i,
        (q i:ℝ)⁻¹ • ValGen.partialBody f n E v (valuationCenter f v) (b i)
          (ownPositivePowerCone f v a hKc hKv (q i-p i) (Nat.sub_pos_of_lt hpq) (b i))
          (fun x => (q i:EReal)*φ x) = (1-(β i:ℝ)) • (F i:Set (EuclideanSpace ℝ (Fin n))) := by
      exact normalized_shrunk_power_partialBody_eq f n E a H hbig v hv hKc hKv φ (β i)
        ((hdom i).2.trans hε1)
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hscalar (r i)))
        (original_iVolume_pos_of_kahler_allDimensions f n E a H (hscalar (r i)))
        (q i) (p i) (hq i) (hrep i) (b i)
    choose hpq hidentity using hpower
    refine ⟨hpq,?_⟩
    apply hscaled.congr
    intro i
    exact (congrArg (fun S : Set (EuclideanSpace ℝ (Fin n)) => Metric.hausdorffDist S
      (K:Set (EuclideanSpace ℝ (Fin n)))) (hidentity i)).symm
end SGPT.Okounkov.OriginalBook
