import SGPT.Foundations.Analysis.Pending.SingularTopFormChartTransport
import SGPT.Foundations.Analysis.Pending.XiaoChartLocalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularTopFormLocalization

open FirstPass SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  TopDegreeDensity ThetaPshChartLimitGluing GlobalCurrentPotentials
  XiaoChartLocalization SingularTopFormChartTransport

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A true compact tensor test is internally produced from a natural chart cutoff. -/
def localizedTensorTest (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (Φ : SmoothRealForm n M k)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    TestForm (chartTarget e) k := by
  let h := localizedCoeff_smooth_compact e χ hχ Φ hc hs
  exact ⟨localizedCoeff e χ Φ, h.1, h.2.1,
    h.2.2.trans (by rintro _ ⟨x, hx, rfl⟩; exact e.val.map_source (hs hx))⟩

/-- The original genuine potential supplies integrability for every localized top form. -/
theorem genuine_theta_potential_localized_top_form_integrable
    (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (Φ : SmoothRealForm n M (2 * n))
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    Integrable (fun x => topDensity (localizedCoeff e χ Φ x) *
      (chartFunction u e x).toReal) volume := by
  let b := (stdOrthonormalBasis ℝ (ComplexModel n)).toBasis
  have hvol : b.addHaar = volume :=
    (stdOrthonormalBasis ℝ (ComplexModel n)).addHaar_eq_volume
  have hL := quasiPsh_chart_locallyIntegrable b hn u hu.quasiPshPotential e
  rw [hvol] at hL
  exact TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hL
    (topDensityTest (localizedTensorTest e χ hχ Φ hc hs))

/-- Natural global tensor compatibility internally produces full singular chart independence. -/
theorem genuine_theta_potential_localized_top_form_chart_independent
    (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (Φ : SmoothRealForm n M (2 * n))
    (hc : IsCompact (tsupport χ)) (hse : tsupport χ ⊆ e.val.source)
    (hsf : tsupport χ ⊆ f.val.source) :
    Integrable (fun x => topDensity (localizedCoeff e χ Φ x) *
      (chartFunction u e x).toReal) volume ∧
      Integrable (fun y => topDensity (localizedCoeff f χ Φ y) *
        (chartFunction u f y).toReal) volume ∧
      (∫ x, topDensity (localizedCoeff e χ Φ x) * (chartFunction u e x).toReal) =
        ∫ y, topDensity (localizedCoeff f χ Φ y) * (chartFunction u f y).toReal := by
  let he := localizedCoeff_smooth_compact e χ hχ Φ hc hse
  let hf := localizedCoeff_smooth_compact f χ hχ Φ hc hsf
  have hαsupp : tsupport (localizedCoeff e χ Φ) ⊆ (overlapSource e f : Set _) := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := he.2.2 hz
    change e.val x ∈ (chartTransition e f).source
    refine ⟨e.val.map_source (hse hx), ?_⟩
    change e.val.symm (e.val x) ∈ f.val.source
    rw [e.val.left_inv (hse hx)]
    exact hsf hx
  have hβsupp : tsupport (localizedCoeff f χ Φ) ⊆ (overlapTarget e f : Set _) := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hf.2.2 hz
    change f.val x ∈ (chartTransition e f).target
    refine ⟨f.val.map_source (hsf hx), ?_⟩
    change f.val.symm (f.val x) ∈ e.val.source
    rw [f.val.left_inv (hsf hx)]
    exact hse hx
  let α : TestForm (overlapSource e f) (2 * n) :=
    ⟨localizedCoeff e χ Φ, he.1, he.2.1, hαsupp⟩
  let β : TestForm (overlapTarget e f) (2 * n) :=
    ⟨localizedCoeff f χ Φ, hf.1, hf.2.1, hβsupp⟩
  have hrel : OverlapTestRelated e f α β := by
    intro z hz v
    have hz' : z ∈ e.val.target ∧ e.val.symm z ∈ f.val.source := hz
    have hF : chartTransition e f z ∈ f.val.target := f.val.map_source hz'.2
    have hinv : f.val.symm (chartTransition e f z) = e.val.symm z := f.val.left_inv hz'.2
    change localizedCoeff e χ Φ z v = localizedCoeff f χ Φ (chartTransition e f z)
      (fun i => chartTransitionDerivative e f z (v i))
    simp only [localizedCoeff, indicator_of_mem hz'.1, indicator_of_mem hF,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, hinv]
    exact congrArg (fun t => χ (e.val.symm z) * t) (Φ.compatible e f z hz v)
  exact genuine_theta_potential_top_form_overlap_integral hn θ u hu e f α β hrel

end SGPT.Foundations.Analysis.Pending.SingularTopFormLocalization
