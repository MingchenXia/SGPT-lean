import SGPT.Projective.OkounkovOriginalWeightedKahlerQEA

/-! Full prescribed cross-class original QEAs, with true physical representative transport.
Blueprint: okounkov-original-tensor-sum-qea.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    {n : ℕ} [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance tensorSumQEATopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorSumQEACharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance tensorSumQEAManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_add_kahlerQEA
    (θ σ : letI := E.isSeparated;letI := E.quasiCompact;ClosedRealOneOneForm n (SchemeComplexPoint f))
    {φ ψ : SchemeComplexPoint f → EReal} {U V : ℕ → SchemeComplexPoint f → EReal}
    (hU : letI := E.isSeparated;letI := E.quasiCompact;PartialBody.IsKahlerQEA θ φ U)
    (hV : letI := E.isSeparated;letI := E.quasiCompact;PartialBody.IsKahlerQEA σ ψ V) :
    letI := E.isSeparated
    letI := E.quasiCompact
    PartialBody.IsKahlerQEA (θ+σ) (fun x => φ x+ψ x) (fun j x => U j x+V j x) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  refine ⟨?_,fun j => ⟨⟨isThetaPshPotential_add_from_positive_sum (hU.2 j).1.1 (hV.2 j).1.1,
    hasAnalyticSingularities_add (hU.2 j).1.2 (hV.2 j).1.2⟩,?_⟩⟩
  · obtain ⟨ω₀,ε,hu⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
    obtain ⟨ω₁,δ,hv⟩ := native_of_sourceQuasiEquisingularApproximation hV.1
    obtain ⟨κ,hκ₀,hκ₁⟩ := QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background ω₀ ω₁
    exact sourceQuasiEquisingularApproximation_of_native
      (QuasiEquisingularAddition.isQuasiEquisingularApproximation_add
        (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination hu hκ₀)
        (QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination hv hκ₁))
  · obtain ⟨κ,hκ⟩ := (hU.2 j).2
    refine ⟨κ,?_⟩
    have hh := isThetaPshPotential_add_from_positive_sum hκ (hV.2 j).1.1
    have hform : θ-κ.form+σ=(θ+σ)-κ.form := by abel
    rwa [hform] at hh

theorem original_kahlerQEA_of_geometricallyEq
    (δ ρ : letI := E.isSeparated;letI := E.quasiCompact;ClosedRealOneOneForm n (SchemeComplexPoint f))
    (hgeo : letI := E.isSeparated;letI := E.quasiCompact;δ.val.GeometricallyEq ρ.val)
    {φ : SchemeComplexPoint f → EReal} {U : ℕ → SchemeComplexPoint f → EReal}
    (hU : letI := E.isSeparated;letI := E.quasiCompact;PartialBody.IsKahlerQEA ρ φ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    PartialBody.IsKahlerQEA δ φ U := by
  let := E.isSeparated
  let := E.quasiCompact
  have hpsh (τ : ClosedRealOneOneForm n (SchemeComplexPoint f)) (χ : SchemeComplexPoint f → EReal) :
      IsThetaPshPotential (ρ+τ).val χ → IsThetaPshPotential (δ+τ).val χ := by
    have hh : (δ+τ).val.GeometricallyEq (ρ+τ).val := by
      intro c z hz
      rw [ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_add,hgeo c hz]
    exact (hh.thetaPshPotential_iff χ).mpr
  refine ⟨?_,?_⟩
  · obtain ⟨hφ,ha,hd,⟨ω,ε,hε,ht⟩,hI⟩ := hU.1
    exact ⟨(hgeo.thetaPshPotential_iff φ).mpr hφ,ha,hd,⟨ω,ε,hε,fun j => hpsh _ _ (ht j)⟩,hI⟩
  · intro j
    refine ⟨⟨(hgeo.thetaPshPotential_iff (U j)).mpr (hU.2 j).1.1,(hU.2 j).1.2⟩,?_⟩
    obtain ⟨κ,hκ⟩ := (hU.2 j).2
    refine ⟨κ,?_⟩
    simpa only [sub_eq_add_neg] using hpsh (-κ.form) (U j) (by simpa only [sub_eq_add_neg] using hκ)
end SGPT.Okounkov.OriginalBook
