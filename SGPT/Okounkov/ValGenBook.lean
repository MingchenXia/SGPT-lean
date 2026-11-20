import SGPT.Okounkov.ValGenCont
import SGPT.Okounkov.ValGenBodies

/-!
# The source's ambient cone `C(Δ_ν(L))` for an arbitrary valuation

Lane VAL-GEN, blueprint `claude-val-gen.tex`. The source (chapter *The theory of Okounkov
bodies*, Section *Algebraic partial Okounkov bodies*) states `prop:GammaepsSp` and `thm:Gammaasg`
with the ambient cone `C(Δ_ν(L))` over the Okounkov body `Δ_ν(L) = Δ(Γ(L))`. The results of
`SGPT.Okounkov.ValGen` hold for every admissible cone containing `Γ(L)` in which `Γ(L)` generates
`ℤⁿ⁺¹`; by `le_latticePoints_coneOver` the cone `C(Δ_ν(L))` is one of them. This file states the
two results with this cone, for an arbitrary valuation `ν = v` under `Γ(L) ∈ 𝒮'(C)` for some
admissible cone `C` (the conclusion of source `prop:Okounbiglbdl` for `v`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.Okounkov
open scoped Topology

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance valGenBookTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenBookCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGenBookManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

include Y hY in
/-- **Source `prop:GammaepsSp` with the source's cone, for an arbitrary valuation `v`**: under
`Γ(L) ∈ 𝒮'(C)` for `v`, `Δ_ν(L)` is a convex body, `Γ(L) ⊆ C(Δ_ν(L))`, and for `φ` with analytic
singularities and `θ_φ` a Kähler current, `Γ^∞(θ, φ) ∈ 𝒮'(Δ_ν(L))` with
`vol Γ^∞(θ, φ) = (1/n!) ∫_X θ_φⁿ`. -/
theorem inftySemigroup_mem_fullSemigroupLocus_coneOver [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hSK : sectionSemigroup v c a ≤
        latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone),
      sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (inftySemigroup f E a c v φ)
          (inftySemigroup_le_cone f E a H c v hSK
            (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)) ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (inftySemigroup f E a c v φ)
          (inftySemigroup_le_cone f E a H c v hSK
            (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ))).volume =
          (DiagonalMass.diagonalPotentialMass (H.curvature a) φ
            (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
              ((m + 1).factorial : ℝ) := by
  obtain ⟨hKc, hKv, hSK⟩ := le_latticePoints_coneOver C _ hS hG
  have hGK := hG
  obtain ⟨h1, -, h3⟩ := inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v hSK hGK hφ hφan
  exact ⟨hKc, hKv, hSK, h1, h3⟩

include Y hY in
/-- **Source `thm:Gammaasg` and `cor:POBvolume` with the source's cone, for an arbitrary
valuation `v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`, for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`Γ(θ, φ) ∈ 𝒮'(Δ_ν(L))‾_{>0}` and `vol Δ_ν(θ, φ) = vol Γ(θ, φ) = vol θ_φ / n!`. -/
theorem multiplierSectionSet_mem_almostSemigroupLocus_coneOver [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) :
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hSK : sectionSemigroup v c a ≤
        latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone),
      multiplierConeSubset f E a c v hSK φ ∈
          almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        (multiplierConeSubset f E a c v hSK φ).volume = volume.real
          (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a) φ) ∧
        volume.real (partialBody f (m + 1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) =
          volume.real (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  obtain ⟨hKc, hKv, hSK⟩ := le_latticePoints_coneOver C _ hS hG
  exact ⟨hKc, hKv, hSK,
    multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a H c v hSK hG hφ hpos⟩

end SGPT.Okounkov.ValGen
