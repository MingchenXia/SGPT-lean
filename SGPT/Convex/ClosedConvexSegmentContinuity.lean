import SGPT.Convex.Semicontinuity

/-! Pointwise radial boundary continuity is produced from the actual closed
convex function and finite endpoint values; it is not an input certificate. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter Topology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine proper lsc convex function is continuous along a finite segment
as one approaches either finite endpoint from inside the segment. -/
theorem tendsto_closedConvex_segment_left {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    {p q : E} (hp : p ∈ effectiveDomain f) (hq : q ∈ effectiveDomain f) :
    Tendsto (fun t : ℝ => f ((1 - t) • p + t • q)) (𝓝[>] 0) (𝓝 (f p)) := by
  have hpf : ((f p).toReal : EReal) = f p :=
    EReal.coe_toReal (ne_of_lt hp) (hf.2.2 p)
  have hqf : ((f q).toReal : EReal) = f q :=
    EReal.coe_toReal (ne_of_lt hq) (hf.2.2 q)
  have hline : Tendsto (fun t : ℝ => (1 - t) • p + t • q) (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => (1 - t) • p + t • q) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hchord : Tendsto
      (fun t : ℝ => (((1 - t) * (f p).toReal + t * (f q).toReal : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (f p)) := by
    have hc : Continuous
        (fun t : ℝ => (((1 - t) * (f p).toReal + t * (f q).toReal : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    simpa only [sub_zero, one_mul, zero_mul, add_zero, hpf] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact hline.eventually (hlsc p a ha)
  · intro b hb
    have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
        (((1 - t) * (f p).toReal + t * (f q).toReal : ℝ) : EReal) < b :=
      hchord.eventually (Iio_mem_nhds hb)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hevent] with t ht htb
    have hpE : (p, (f p).toReal) ∈ epigraph f := hpf.ge
    have hqE : (q, (f q).toReal) ∈ epigraph f := hqf.ge
    have hh := hf.1 hpE hqE (sub_nonneg.mpr ht.2.le) ht.1.le (by ring : (1 - t) + t = 1)
    change f ((1 - t) • p + t • q) ≤
      (((1 - t) * (f p).toReal + t * (f q).toReal : ℝ) : EReal) at hh
    exact hh.trans_lt htb

end SGPT.Convex
