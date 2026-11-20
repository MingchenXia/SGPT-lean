import SGPT.Checks.Comparison.ThinApprox.SourceDXZ
import SGPT.Checks.Comparison.OperationBJMax
import SGPT.NAPotential.Join

/-! Original source thm:NApotential:L1352: the literal maximum operations
under the SAME actual DXZ map, including dimension zero and trivial valuations.
Blueprint: operation-correspondence-max.tex. No correspondence certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]
local instance opMaxProper : IsProper f := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance opMaxPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opMaxPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opMaxPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)


include b HM hm hθ

/-- Actual original join has the literal full-point BJ maximum, with
original primitive line/metric/Chern data and no approximation hypothesis. -/
theorem naPotentialAnAt_join (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (Γ Δ : SourceNAPotential θ) (v : BerkovichPoint f) :
    naPotentialAnAt n E (Γ.join Δ) ω v =
      max (naPotentialAnAt n E Γ ω v) (naPotentialAnAt n E Δ ω v) := by
  let F := SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω
  have hDXZ := SGPT.NAPotential.ThinApprox.BJ.SourceDXZ.source_DXZ f n E b HM hm hθ ω
  let Ψ : {ψ : BerkovichPoint f → EReal //
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ} :=
    ⟨fun w => max ((F Γ).1 w) ((F Δ).1 w),
      isModuleTopologyPSH_max f (F Γ).2 (F Δ).2⟩
  obtain ⟨Ξ, hΞ⟩ := hDXZ.2.2 Ψ
  change F Ξ = Ψ at hΞ
  have hΓ : SourceNAPOrder Γ Ξ := (hDXZ.1 Γ Ξ).mpr (by
    intro w
    change (F Γ).1 w ≤ (F Ξ).1 w
    rw [hΞ]
    exact le_max_left _ _)
  have hΔ : SourceNAPOrder Δ Ξ := (hDXZ.1 Δ Ξ).mpr (by
    intro w
    change (F Δ).1 w ≤ (F Ξ).1 w
    rw [hΞ]
    exact le_max_right _ _)
  apply le_antisymm
  · have h := (hDXZ.1 (Γ.join Δ) Ξ).mp (SourceNAPotential.join_le hΓ hΔ) v
    change (F (Γ.join Δ)).1 v ≤ max ((F Γ).1 v) ((F Δ).1 v)
    change (F (Γ.join Δ)).1 v ≤ (F Ξ).1 v at h
    rw [hΞ] at h
    exact h
  · exact max_le
      ((hDXZ.1 Γ (Γ.join Δ)).mp
        (Γ.le_join_left Δ (sourceKahlerFormRepresentative ω)) v)
      ((hDXZ.1 Δ (Γ.join Δ)).mp
        (Γ.le_join_right Δ (sourceKahlerFormRepresentative ω)) v)

/-- Equality in the SAME original BJ PSH subtype, rather than only a
divisorial equality or a differently transported operation. -/
theorem naAnalytification_join (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (Γ Δ : SourceNAPotential θ) :
    SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω (Γ.join Δ) =
      ⟨fun v => max
        ((SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).1 v)
        ((SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Δ).1 v),
        isModuleTopologyPSH_max f
          (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).2
          (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Δ).2⟩ := by
  apply Subtype.ext
  funext v
  exact naPotentialAnAt_join f n E b HM hm hθ ω Γ Δ v

/-- Every actual finite nonempty maximum from prop:NApotential:L404
has its literal finite pointwise BJ maximum on ALL original points. -/
theorem naPotentialAnAt_finiteJoin (ω : SourceKahlerForm n (SchemeComplexPoint f))
    {I : Type*} (Γ : I → SourceNAPotential θ) (s : Finset I) (hs : s.Nonempty)
    (v : BerkovichPoint f) :
    naPotentialAnAt n E (SourceNAPotential.finiteJoin
      (sourceKahlerFormRepresentative ω) Γ s hs) ω v =
      s.sup' hs (fun i => naPotentialAnAt n E (Γ i) ω v) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s his ih =>
    by_cases hsn : s.Nonempty
    · rw [SourceNAPotential.finiteJoin_insert _ _ _ _ hsn,
        naPotentialAnAt_join f n E b HM hm hθ,
        Finset.sup'_insert hsn]
      exact congrArg (max (naPotentialAnAt n E (Γ i) ω v)) (ih hsn)
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      simp only [Finset.insert_empty, SourceNAPotential.finiteJoin_singleton,
        Finset.sup'_singleton]

end SGPT.NAPotential.OperationComparison
