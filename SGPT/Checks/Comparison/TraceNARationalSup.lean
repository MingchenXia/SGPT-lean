import SGPT.Checks.Comparison.TraceNARationalSliceValues
import SGPT.Checks.Comparison.TraceNAHullCutoff
import SGPT.Checks.Comparison.TraceGFZeroRestriction

/-! Actual rational suprema and the actual original trace cutoff.
Blueprint: `trace-rational-hull-slices.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open scoped Topology Manifold ContDiff

/-- Antitonicity removes the endpoint; literal vanishing removes every
parameter above it, also when the actual trace and ambient cutoffs coincide. -/
theorem rational_parameterSup_eq_below_of_bot_above (F : ℝ → EReal) (S T : ℝ)
    (hTS : T ≤ S)
    (hanti : ∀ {s t : ℝ}, s ≤ t → t < S → F t ≤ F s)
    (hbot : ∀ q : ℚ, T < (q : ℝ) → (q : ℝ) < S → F q = ⊥) :
    (⨆ q : ℚ, ⨆ (_ : (q : ℝ) < S), F q + ((q : ℝ) : EReal)) =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < T), F q + ((q : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => ?_
    by_cases hqT : (q : ℝ) < T
    · exact le_iSup_of_le q (le_iSup_of_le hqT le_rfl)
    by_cases hTq : T < (q : ℝ)
    · rw [hbot q hTq hq, EReal.bot_add]
      exact bot_le
    have heq : (q : ℝ) = T := le_antisymm (le_of_not_gt hTq) (le_of_not_gt hqT)
    apply (add_real_le_rational_iSup (F q) (q : ℝ)).trans
    refine iSup_le fun r => iSup_le fun hr => ?_
    exact le_iSup_of_le r (le_iSup_of_le (hr.trans_eq heq)
      (add_le_add (hanti hr.le hq) le_rfl))
  · exact iSup_le fun q => iSup_le fun hq =>
      le_iSup_of_le q (le_iSup_of_le (hq.trans_le hTS) le_rfl)

section Scheme
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (EX : ClosedProjectiveEmbedding f) [IsProper f]
local instance traceSupTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceSupCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceSupManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- The analytification of ANY actual NA potential is the SAME rational
Legendre supremum. Actual slice monotonicity and whole multiplier ideals are internal. -/
theorem naPotentialAnAt_eq_rational_parameterSup (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt n EX Γ κ v =
      ⨆ q : ℚ, ⨆ (hq : (q : ℝ) < (Γ.component κ).val.max),
        potentialAn n EX ((Γ.component κ).val.potential ⟨q, hq⟩) v + ((q : ℝ) : EReal) := by
  unfold naPotentialAnAt
  apply le_antisymm
  · apply iSup_le
    intro s
    apply (add_real_le_rational_iSup
      (potentialAn n EX ((Γ.component κ).val.potential s) v) (s : ℝ)).trans
    refine iSup_le fun q => iSup_le fun hq => ?_
    apply le_iSup_of_le q
    apply le_iSup_of_le (hq.trans s.2)
    apply add_le_add _ le_rfl
    apply BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n EX
      (SGPT.GAGA.H0S.multiplierIdealAlgebraic f EX n)
      ((Γ.component κ).val.native_thetaPSH s)
      ((Γ.component κ).val.native_thetaPSH ⟨q, hq.trans s.2⟩)
    intro x
    exact (Γ.component κ).val.antitone x hq.le
  · exact iSup_le fun q => iSup_le fun hq => le_iSup
      (fun s : Iio (Γ.component κ).val.max =>
        potentialAn n EX ((Γ.component κ).val.potential s) v + ((s : ℝ) : EReal)) ⟨q, hq⟩

end Scheme

section OriginalHull
variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
local instance traceSupXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceSupYProper : IsProper (i ≫ f) := (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceSupXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceSupYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceSupXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceSupYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceSupXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceSupYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  [ConnectedSpace (SchemeComplexPoint (i ≫ f))]

include k EY

/-- Above the ACTUAL trace cutoff, the ORIGINAL rational hull analytification
is minus infinity at EVERY actual image semi-valuation. All literal physical
vanishing and zero pulled-family conclusions are manufactured internally. -/
theorem originalRationalHull_schemeAnMap_eq_bot_above_traceCutoff
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ r : ℚ, D.τ j = r)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j b, t j b ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun b => H.sectionLogNormSq a N (t j b)) p)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (q : ℚ) (hq : (q : ℝ) < D.τ 0)
    (hcut : traceCutoff (schemeComplexPointMap (i ≫ f) f i rfl) (hullNAPotential D) κX < (q : ℝ))
    (w : BerkovichPoint (i ≫ f)) :
    potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
      (schemeAnMap i rfl w) = ⊥ := by
  have hbot := originalHull_restriction_eq_bot_of_traceCutoff_lt D κX q hq hcut
  obtain ⟨Q, hQ, F, hF, heq, _hval⟩ :=
    exists_originalHull_commonSectionFamily n EX H a N K hK D hτ I t ht hA q hq.le
  rw [heq] at hbot ⊢
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    potentialAn_sectionMaximum_schemeAnMap_eq_bot_of_restriction_eq_bot f i n k EX EY
      a H (N * Q) (K * Q) (Nat.mul_pos hK hQ) F.sections hF
      (by simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using hbot) w

end OriginalHull
end SGPT.NAPotential.TraceComparison
