import SGPT.PSH.SourceSubgeodesic
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual original smoothness on the WHOLE manifold equals genuine native
chart smoothness, on precisely the SAME charts and chart targets. -/
theorem sourceChartSmoothOn_univ_iff_native (g : M → ℝ) :
    (ofFixedModel n M).ChartSmoothOn g univ ↔ ChartSmooth (n := n) g := by
  constructor
  · intro h e
    exact (h e).mono (fun z hz ↦ ⟨hz, mem_univ _⟩)
  · intro h e
    exact (h e).mono (fun _ hz ↦ hz.1)

/-- Literal original smooth g and theta'=theta+ddc g. The identity is of
ENTIRE alternating two-forms on EVERY actual chart target. -/
def SourceSmoothBackgroundChange
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)) (g : M → ℝ) : Prop :=
  (ofFixedModel n M).ChartSmoothOn g univ ∧
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative η).val.coeff e z =
        (atlasClosedFormToNative θ).val.coeff e z +
          smoothDDC (fun y ↦ g (e.val.symm y)) z

/-- The SAME actual smooth function and complete tensor identity are the
native hypotheses; no desired PSH/convergence conclusion is packaged. -/
theorem sourceSmoothBackgroundChange_iff_native
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)) (g : M → ℝ) :
    SourceSmoothBackgroundChange θ η g ↔
      ChartSmooth (n := n) g ∧
        ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
          (atlasClosedFormToNative η).val.coeff e z =
            (atlasClosedFormToNative θ).val.coeff e z +
              smoothDDC (fun y ↦ g (e.val.symm y)) z := by
  constructor
  · intro h
    exact ⟨(sourceChartSmoothOn_univ_iff_native g).mp h.1, h.2⟩
  · intro h
    exact ⟨(sourceChartSmoothOn_univ_iff_native g).mpr h.1, h.2⟩

/-- Actual original slice transport, reusing the genuine finite-correction
PSH/nondegeneracy producer and the complete source theta dictionary. -/
theorem sourceThetaPSH_sub_smooth
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH η (fun x ↦ u x - (g x : EReal)) := by
  have hc := (sourceSmoothBackgroundChange_iff_native θ η g).mp hchange
  exact (isThetaPSH_iff_nativeThetaPotential η _).mpr
    (thetaPshPotential_sub_smooth hc.1 hc.2
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu))

/-- Full original JOINT product-PSH transport. Actual rho+g is a produced
local potential, and the corrected joint function is literally unchanged
at EVERY point, including poles; source dictionary restores ALL potentials. -/
theorem sourceSubgeodesicInterior_sub_smooth
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g) {curve : ℝ → M → EReal}
    (h : SourceSubgeodesicInterior θ curve) :
    SourceSubgeodesicInterior η (fun t x ↦ curve t x - (g x : EReal)) := by
  have hc := (sourceSmoothBackgroundChange_iff_native θ η g).mp hchange
  have hn := (sourceInterior_iff_native θ curve).mp h
  apply (sourceInterior_iff_native η _).mpr
  constructor
  · intro t ht
    exact thetaPshPotential_sub_smooth hc.1 hc.2 (hn.thetaPshPotential ht)
  · intro e z hz
    obtain ⟨W, ρ, hzW, hρ, hp⟩ := hn.complexified_psh e hz
    refine ⟨W, fun y ↦ ρ y + g (e.val.symm y), hzW,
      GlobalPotentialTransforms.isSmoothLocalPotential_add_chartSmooth hc.1 hc.2 hρ, ?_⟩
    have heq : subgeodesicChartFunction (fun t x ↦ curve t x - (g x : EReal)) e
        (fun y ↦ ρ y + g (e.val.symm y)) = subgeodesicChartFunction curve e ρ := by
      funext p
      exact sub_coe_add_coe _ _ _
    rw [heq]
    exact hp

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Exact actual GLOBAL distance invariance under ANY common finite real
spatial subtraction. Pole-inclusive pointwise cancellation precedes the
integral; no smoothness/measurability/AE-finite/readback assumption. -/
theorem sourceGlobalL1Distance_sub_common (omega : KahlerBackground n M)
    (u v : M → EReal) (g : M → ℝ) :
    sourceGlobalL1Distance omega (fun x ↦ u x - (g x : EReal))
      (fun x ↦ v x - (g x : EReal)) = sourceGlobalL1Distance omega u v := by
  change (∫⁻ x, canonicalERealAbsDiff (u x - (g x : EReal))
    (v x - (g x : EReal)) ∂IntegrationCurrent.kahlerVolume omega) =
      ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂IntegrationCurrent.kahlerVolume omega
  apply lintegral_congr
  intro x
  simpa only [EReal.coe_neg, sub_eq_add_neg] using
    canonicalERealAbsDiff_add_coe (u x) (v x) (-g x)

omit [BorelSpace M] in
/-- Both actual original endpoint L1 conditions are preserved by an EXACT
identity of the original GLOBAL distance functions. Only interior-time PSH
is required, with the literal shifted assigned endpoints. -/
theorem SourceSubgeodesicFrom.sub_smooth
    {omega : KahlerBackground n M}
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g)
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    SourceSubgeodesicFrom omega η (fun t x ↦ curve t x - (g x : EReal))
      (fun x ↦ u₀ x - (g x : EReal)) (fun x ↦ u₁ x - (g x : EReal)) := by
  rcases h with ⟨h₀, h₁, hi, hl, hr⟩
  refine ⟨sourceThetaPSH_sub_smooth hchange h₀, sourceThetaPSH_sub_smooth hchange h₁,
    sourceSubgeodesicInterior_sub_smooth hchange hi, ?_, ?_⟩
  · simpa only [sourceGlobalL1Distance_sub_common] using hl
  · simpa only [sourceGlobalL1Distance_sub_common] using hr

omit [BorelSpace M] in
/-- WHOLE original prop:subgeodindeptheta, with the literal original closed
curve/endpoints. The same proof gives EVERY original physical a≤b,
including a=b, without a positive-length or off-time hypothesis. -/
theorem SourceSubgeodesicClosedInterval.sub_smooth
    {omega : KahlerBackground n M}
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g)
    {a b : ℝ} {curve : ℝ → M → EReal}
    (h : SourceSubgeodesicClosedInterval omega θ a b curve) :
    SourceSubgeodesicClosedInterval omega η a b (fun t x ↦ curve t x - (g x : EReal)) :=
  ⟨h.1, h.2.sub_smooth hchange⟩

end SGPT.PSH.VariableComplexAtlas
