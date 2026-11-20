import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.TietzeExtension

/-! Real secant squeeze and continuous extension with closed-subtype integral transport. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PartialEnergyDifferentiability
open Set Filter MeasureTheory
open scoped Topology

/-- Both signed contact-energy inequalities and actual continuity of the
MA read produce the genuine real derivative, including the negative side. -/
theorem hasDerivAt_of_contact_bounds {E I : ℝ → ℝ} {s : ℝ}
    (hI : ContinuousAt I s)
    (hb : ∀ t, (t - s) * I t ≤ E t - E s ∧ E t - E s ≤ (t - s) * I s) :
    HasDerivAt E (I s) s := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim : Tendsto I (𝓝[≠] s) (𝓝 (I s)) := hI.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun _ : ℝ => I s) (𝓝[≠] s) (𝓝 (I s)) := tendsto_const_nhds
  have hlo : Tendsto (fun t => min (I t) (I s)) (𝓝[≠] s) (𝓝 (I s)) := by
    simpa only [min_self] using hlim.min hc
  have hup : Tendsto (fun t => max (I t) (I s)) (𝓝[≠] s) (𝓝 (I s)) := by
    simpa only [max_self] using hlim.max hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    rcases lt_or_gt_of_ne ht with hts | hst
    · have hneg : t - s < 0 := sub_neg.mpr hts
      exact (min_le_right _ _).trans ((le_div_iff_of_neg hneg).mpr (by nlinarith [(hb t).2]))
    · have hpos : 0 < t - s := sub_pos.mpr hst
      exact (min_le_left _ _).trans ((le_div_iff₀ hpos).mpr (by nlinarith [(hb t).1]))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    rcases lt_or_gt_of_ne ht with hts | hst
    · have hneg : t - s < 0 := sub_neg.mpr hts
      exact ((div_le_iff_of_neg hneg).mpr (by nlinarith [(hb t).1])).trans (le_max_left _ _)
    · have hpos : 0 < t - s := sub_pos.mpr hst
      exact ((div_le_iff₀ hpos).mpr (by nlinarith [(hb t).2])).trans (le_max_right _ _)

universe u
variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- An actual continuous extension is produced by Tietze, and SAME original
subtype MA integrals equal ambient integrals for EVERY carried measure. -/
theorem exists_continuous_extension_integral [NormalSpace X]
    {K : Set X} (hK : IsClosed K) (f : C(K, ℝ)) :
    ∃ F : C(X, ℝ), F.restrict K = f ∧ ∀ μ : Measure X, μ Kᶜ = 0 →
      (∫ x : K, f x ∂μ.comap Subtype.val) = ∫ x, F x ∂μ := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK f
  refine ⟨F, hF, fun μ hμ => ?_⟩
  have hval : (fun x : K => F x.val) = fun x => f x := by
    exact congrArg (fun g : C(K, ℝ) => (fun x => g x)) hF
  rw [← hval, integral_subtype_comap hK.measurableSet]
  have hmem : ∀ᵐ x ∂μ, x ∈ K := by
    apply ae_iff.mpr
    change μ Kᶜ = 0
    exact hμ
  rw [Measure.restrict_eq_self_of_ae_mem hmem]

end SGPT.Bergman.PartialEnergyDifferentiability
