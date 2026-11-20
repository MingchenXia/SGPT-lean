import SGPT.Checks.Comparison.SourceNetTools

/-! Original pointwise decreasing infimum is PSH.
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

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance infPshProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance infPshPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance infPshPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance infPshPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **Decreasing infima of analytifications are psh**: for a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` whose cutoffs `Γ_{i,max}` are bounded below (`eq:decnetcontition`),
`inf_i Γ_i^An ∈ PSH(L^An)`. -/
theorem iInf_naPotentialAnAt_isModuleTopologyPSH {I : Type u} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (omega : KahlerBackground n (SchemeComplexPoint f))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b)
      (fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v) := by
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  let : IsDirectedOrder (I × ℕ) := ⟨fun x y => by
    obtain ⟨i, h1, h2⟩ := exists_ge_ge x.1 y.1
    exact ⟨(i, max x.2 y.2), ⟨h1, le_max_left _ _⟩, ⟨h2, le_max_right _ _⟩⟩⟩
  choose D hDcls hDev using fun x : I × ℕ => exists_gridPackage f n E b HM hm hθ (Γ x.1) ω x.2
  let J := siuLevel f n E b HM m
  have hJpos : ∀ a, 0 < J a := siuLevel_pos f n E b HM hm
  have hJsucc : ∀ a, ∃ t, 0 < t ∧ J (a + 1) = t * J a := fun a =>
    ⟨_, Nat.mul_pos two_pos (Nat.two_pow_pos _), siuLevel_succ f n E b HM m a⟩
  have hε : Tendsto (fun a => ((1 / ((m * 2 ^ a : ℕ) : ℚ) : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun a : ℕ => ((m : ℝ) * 2 ^ a)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
        (by exact_mod_cast hm)
    refine (tendsto_inv_atTop_zero.comp h2).congr fun a => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hlev : Tendsto (fun x : I × ℕ => x.2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun a => ⟨(Classical.arbitrary I, a), fun x hx => hx.2⟩
  have hanti : ∀ v, Antitone fun x : I × ℕ => (D x).eval f v := by
    intro v x y hxy
    simp only [hDev]
    exact (antitone_gridApprox_component f n E hJpos hJsucc (Γ y.1) ω v hxy.2).trans
      (gridApprox_le_of_sourceNAPOrder f n E hJpos (ha _ _ hxy.1) ω v x.2)
  have hinf : ∀ v, ⨅ x : I × ℕ, (D x).eval f v = ⨅ i, naPotentialAnAt n E (Γ i) ω v := by
    intro v
    rw [iInf_prod]
    refine iInf_congr fun i => ?_
    simp only [hDev]
    exact iInf_gridApprox_component f n E hJpos (siuLevel_strictMono f n E b HM hm) (Γ i) ω v
  -- `inf_i Γ_i^An(v_triv) ≥ inf_i Γ_{i,max} - 1 > -∞`
  have hne : ∃ v, (⨅ x : I × ℕ, (D x).eval f v) ≠ ⊥ := by
    refine ⟨BerkovichPoint.trivial f, ?_⟩
    rw [hinf]
    obtain ⟨c, hc⟩ := hb
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (c - 1)) (le_iInf fun i => ?_)
    have hci : c ≤ ((Γ i).component ω).val.max := by
      rw [← sourceNAPotentialCutoff_eq_component omega (Γ i) ω]
      exact hc ⟨i, rfl⟩
    have hτ : ((Γ i).component ω).val.max - 1 < ((Γ i).component ω).val.max := by linarith
    have hle := le_naPotentialAnAt n E (Γ i) ω (BerkovichPoint.trivial f) ⟨_, hτ⟩
    rw [Berkovich.potentialAn_trivial hA (((Γ i).component ω).val.native_thetaPSH ⟨_, hτ⟩),
      zero_add] at hle
    exact le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hle
  have h := isModuleTopologyPSH_of_antitone_levelNet.{u} f D (fun x => x.2) hlev hε hDcls hanti hne
  have hfun : (fun v => ⨅ x : I × ℕ, (D x).eval f v) =
      fun v => ⨅ i, naPotentialAnAt n E (Γ i) ω v := funext hinf
  rwa [hfun] at h



end SGPT.NAPotential.BJ.SourceNet
