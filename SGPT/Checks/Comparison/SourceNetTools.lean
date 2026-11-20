import SGPT.Checks.Comparison.BJExistCurve

/-! Original grid monotonicity and numerical-topology net tools.
Blueprint: source-comparison-slices.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.SourceNet

open SGPT.NAPotential.BJ.Exist

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

/-- Grid maxima are monotone in the data. -/
theorem gridApprox_mono {F F' : ℕ → ℝ → EReal} {Flim Flim' : ℕ → EReal} {T T' : ℝ}
    (hT : T' ≤ T) (a : ℕ) (hF : ∀ t, t < T' → F' a t ≤ F a t) (hlim : Flim' a ≤ Flim a) :
    gridApprox F' Flim' T' a ≤ gridApprox F Flim T a := by
  apply max_le
  · exact (add_le_add hlim le_rfl).trans (le_gridApprox_tail F Flim T a)
  · refine iSup_le fun ⟨k, hk⟩ => ?_
    obtain ⟨h1, h2⟩ := mem_gridIndex.mp hk
    exact (add_le_add (hF _ h2) le_rfl).trans
      (le_gridApprox_grid F Flim T a (mem_gridIndex.mpr ⟨h1, h2.trans_le hT⟩))


section Net

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- **Decreasing nets of GF functions.** If `D_k ∈ H^gf_ℚ((L + ε_{ℓ(k)} H)^An)` for a directed
index `k`, with `ℓ(k) → ∞` and rational `ε_a → 0`, the `D_k` decrease and their infimum is not
identically `-∞`, then the infimum lies in `PSH(L^An)`. -/
theorem isModuleTopologyPSH_of_antitone_levelNet {κ : Type u} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] (D : κ → RationalGFPackage X) (lev : κ → ℕ) (hlev : Tendsto lev atTop atTop)
    {L H : RationalPicardSpace X} {ε : ℕ → ℚ} (hε : Tendsto (fun a => (ε a : ℝ)) atTop (𝓝 0))
    (hclass : ∀ k, (D k).picardClass = L + ε (lev k) • H)
    (hanti : ∀ v, Antitone (fun k => (D k).eval p v))
    (hne : ∃ v, (⨅ k, (D k).eval p v) ≠ ⊥) :
    IsModuleTopologyPSH.{u} p L (fun v => ⨅ k, (D k).eval p v) := by
  let N : DecreasingGFNet.{u} p :=
    { I := κ
      preorder := inferInstance
      nonempty := inferInstance
      directed := inferInstance
      term := D
      decreasing := hanti }
  refine ⟨hne, N, ?_, fun v => tendsto_atTop_iInf (hanti v)⟩
  change Tendsto (fun k : κ => (D k).numericalClass p) atTop _
  refine ((tendsto_numericalClass_add_smul p (L := L) (H := H) hε).comp hlev).congr fun k => ?_
  change numericalClass p (L + ε (lev k) • H) = numericalClass p (D k).picardClass
  rw [hclass]

end Net


variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existNetProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existNetPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existNetPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance existNetPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- Along `Γ' ≤ Γ`, the grid approximants decrease. -/
theorem gridApprox_le_of_sourceNAPOrder {J : ℕ → ℕ} (hJpos : ∀ a, 0 < J a)
    {Γ Γ' : SourceNAPotential θ} (h : SourceNAPOrder Γ' Γ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) (a : ℕ) :
    gridApprox (gridSlice f n E J Γ' ω v) (gridTail f n E J Γ' ω v) (Γ'.component ω).val.max a ≤
      gridApprox (gridSlice f n E J Γ ω v) (gridTail f n E J Γ ω v) (Γ.component ω).val.max a := by
  obtain ⟨hcut, hle⟩ := (sourceTestCurvePOrder_iff (sourceKahlerFormRepresentative ω) _ _).mp
    ((sourceNAPOrder_iff_component Γ' Γ ω).mp h)
  refine gridApprox_mono hcut a (fun t ht => ?_) ?_
  · simp only [gridSlice, dif_pos ht, dif_pos (ht.trans_le hcut)]
    exact approxVal_mono f n E ((Γ.component ω).val.native_thetaPSH _) (hle t ht) (hJpos a) v
  · simp only [gridTail]
    refine approxVal_mono f n E ((isThetaPSH_iff_nativeThetaPotential _ _).mp
      (Γ.component ω).val.limit_thetaPSH) (fun x => ?_) (hJpos a) v
    unfold sourceTestCurveLimit SGPT.PSH.uscSup
    refine uscRegularization_mono (fun y => iSup_le fun τ => ?_) x
    exact (hle τ τ.2 y).trans (le_iSup (fun j => (Γ.component ω).val.potential j y)
      ⟨τ, (τ.2 : (τ : ℝ) < _).trans_le hcut⟩)



end SGPT.NAPotential.BJ.SourceNet
