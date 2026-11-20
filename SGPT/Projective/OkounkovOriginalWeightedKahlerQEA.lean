import SGPT.Projective.OkounkovOriginalBookPartial
import SGPT.Okounkov.ValuativeTestCurve

/-! Genuine simultaneous rational weighted QEA of the SAME original weights/representative.
Blueprint: okounkov-original-weighted-kahler-qea.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    {n : ℕ} [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance weightedKahlerQEATopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance weightedKahlerQEACharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance weightedKahlerQEAManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual prescribed sequences combine into the FULL genuine rational weighted QEA, same original theta. -/
theorem original_rational_convexComb_kahlerQEA
    (θ : letI := E.isSeparated; letI := E.quasiCompact; ClosedRealOneOneForm n (SchemeComplexPoint f))
    {φ ψ : SchemeComplexPoint f → EReal} {U V : ℕ → SchemeComplexPoint f → EReal}
    (hU : letI := E.isSeparated; letI := E.quasiCompact; PartialBody.IsKahlerQEA θ φ U)
    (hV : letI := E.isSeparated; letI := E.quasiCompact; PartialBody.IsKahlerQEA θ ψ V)
    (t : ℚ) (ht0 : 0<t) (ht1 : t<1) :
    letI := E.isSeparated
    letI := E.quasiCompact
    PartialBody.IsKahlerQEA θ (convexComb (t:ℝ) φ ψ)
      (fun j => convexComb (t:ℝ) (U j) (V j)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have scale {δ : ClosedRealOneOneForm n (SchemeComplexPoint f)}
      {χ : SchemeComplexPoint f → EReal} {W : ℕ → SchemeComplexPoint f → EReal}
      (hW : PartialBody.IsKahlerQEA δ χ W) {b : ℚ} (hb : 0<b) :
      PartialBody.IsKahlerQEA ((b:ℝ)•δ) (fun x => ((b:ℝ):EReal)*χ x)
        (fun j x => ((b:ℝ):EReal)*W j x) := by
    have hbR : (0:ℝ)<b := by exact_mod_cast hb
    obtain ⟨ω,ε,hnative⟩ := native_of_sourceQuasiEquisingularApproximation hW.1
    refine ⟨sourceQuasiEquisingularApproximation_of_native
      (QuasiEquisingularRationalScaling.isQuasiEquisingularApproximation_pos_rat_smul hnative hb),?_⟩
    intro j
    refine ⟨⟨isThetaPshPotential_nonneg_smul (hW.2 j).1.1 hbR.le,
      hasAnalyticSingularities_nonneg_rat_smul (hW.2 j).1.2 hb.le⟩,?_⟩
    obtain ⟨κ,hκ⟩ := (hW.2 j).2
    refine ⟨KahlerBackground.smul hbR κ,?_⟩
    have hh := isThetaPshPotential_nonneg_smul hκ hbR.le
    rwa [KahlerBackground.smul_form,←smul_sub]
  have hUt := scale hU ht0
  have hVt := scale hV (sub_pos.mpr ht1)
  have hsum : PartialBody.IsKahlerQEA ((t:ℝ)•θ+((1-t:ℚ):ℝ)•θ)
      (fun x => ((t:ℝ):EReal)*φ x+(((1-t:ℚ):ℝ):EReal)*ψ x)
      (fun j x => ((t:ℝ):EReal)*U j x+(((1-t:ℚ):ℝ):EReal)*V j x) := by
    refine ⟨?_,fun j => ⟨⟨isThetaPshPotential_add_from_positive_sum (hUt.2 j).1.1 (hVt.2 j).1.1,
      hasAnalyticSingularities_add (hUt.2 j).1.2 (hVt.2 j).1.2⟩,?_⟩⟩
    · obtain ⟨ω₀,ε,hu⟩ := native_of_sourceQuasiEquisingularApproximation hUt.1
      obtain ⟨ω₁,δ,hv⟩ := native_of_sourceQuasiEquisingularApproximation hVt.1
      obtain ⟨κ,hκ₀,hκ₁⟩ := QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background ω₀ ω₁
      exact sourceQuasiEquisingularApproximation_of_native
        (QuasiEquisingularAddition.isQuasiEquisingularApproximation_add
          (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination hu hκ₀)
          (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination hv hκ₁))
    · obtain ⟨κ,hκ⟩ := (hUt.2 j).2
      refine ⟨κ,?_⟩
      have hh := isThetaPshPotential_add_from_positive_sum hκ (hVt.2 j).1.1
      have hform : (t:ℝ)•θ-κ.form+((1-t:ℚ):ℝ)•θ=((t:ℝ)•θ+((1-t:ℚ):ℝ)•θ)-κ.form := by abel
      rwa [hform] at hh
  have hform : (t:ℝ)•θ+((1-t:ℚ):ℝ)•θ=θ := by
    push_cast
    module
  rw [hform] at hsum
  change PartialBody.IsKahlerQEA θ
    (fun x => ((t:ℝ):EReal)*φ x+(((1-(t:ℝ)):ℝ):EReal)*ψ x)
    (fun j x => ((t:ℝ):EReal)*U j x+(((1-(t:ℝ)):ℝ):EReal)*V j x)
  simpa only [Rat.cast_sub,Rat.cast_one] using hsum
end SGPT.Okounkov.OriginalBook
