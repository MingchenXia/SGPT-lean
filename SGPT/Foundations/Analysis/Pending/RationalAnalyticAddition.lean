import SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum
import SGPT.Foundations.Analysis.Pending.IdealWeightProducts

set_option autoImplicit false

/-! # Actual rational analytic singularities are closed under addition -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition

open FirstPass RationalAnalyticMaximum IdealWeightProducts

noncomputable section

/-- Actual product families and bounded real remainders give the original
sum presentation, including all generator-zero branches. -/
theorem logarithmicTypeAt_add_mulFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {c : ℝ} {N P : ℕ}
    {f : Fin N → E → ℂ} {g : Fin P → E → ℂ} {x : E}
    (hu : LogarithmicTypeAt u c f x) (hv : LogarithmicTypeAt v c g x) :
    LogarithmicTypeAt (fun y => u y + v y) c (mulFamily f g) x := by
  obtain ⟨hc, hf, b, hb, hueq⟩ := hu
  obtain ⟨_, hg, d, hd, hveq⟩ := hv
  obtain ⟨U, hU, hxU, hdf⟩ := hf
  obtain ⟨V, hV, hxV, hdg⟩ := hg
  have hfg : HolomorphicGeneratorsAt (mulFamily f g) x := by
    refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun k y hy => ?_⟩
    exact ((hdf (finProdFinEquiv.symm k).1 y hy.1).mono inter_subset_left).mul
      ((hdg (finProdFinEquiv.symm k).2 y hy.2).mono inter_subset_right)
  refine ⟨hc, hfg, (fun y => b y + d y), hb.add hd, ?_⟩
  filter_upwards [hueq, hveq] with y hy hy'
  rw [hy, hy', generatorLog_mulFamily,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top _),
    EReal.coe_add]
  exact add_add_add_comm _ _ _ _

/-- Distinct positive rational coefficients are synchronized by actual tensor
families internally before multiplying generators. -/
theorem hasAnalyticSingularityTypeAt_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → EReal} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (hv : HasAnalyticSingularityTypeAt v x) :
    HasAnalyticSingularityTypeAt (fun y => u y + v y) x := by
  obtain ⟨e, N, P, F, G, hu', hv'⟩ := exists_common_coefficient_presentations hu hv
  exact ⟨e, N * P, mulFamily F G, logarithmicTypeAt_add_mulFamily hu' hv'⟩

end

end SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition
