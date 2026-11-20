import Mathlib.Analysis.Convex.Deriv
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
namespace SGPT.Convex
open Set Filter
open scoped Topology

/-- The actual convex secant bounds give the genuine tangent inequality at zero, without differentiability elsewhere. -/
theorem convex_origin_tangent_le {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ I f) (hzero : 0 ∈ I) (hd : DifferentiableAt ℝ f 0)
    {t : ℝ} (ht : t ∈ I) : f 0 + t * deriv f 0 ≤ f t := by
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · have h := hf.slope_le_deriv ht hzero hneg hd
    simp only [slope_def_field] at h
    have hmul := (div_le_iff₀ (by linarith : 0 < 0 - t)).mp h
    nlinarith
  · simp
  · have h := hf.deriv_le_slope hzero ht hpos hd
    simp only [slope_def_field, sub_zero] at h
    have hmul := (le_div_iff₀ hpos).mp h
    nlinarith

/-- The actual complete extended-real upper limit yields genuine eventual real upper bounds, including unbounded sequences. -/
theorem eventually_lt_of_ereal_limsup_le {u : ℕ → ℝ} {b c : ℝ}
    (hlim : limsup (fun k ↦ (u k : EReal)) atTop ≤ (b : EReal)) (hbc : b < c) :
    ∀ᶠ k in atTop, u k < c := by
  have hstrict : limsup (fun k ↦ (u k : EReal)) atTop < (c : EReal) :=
    hlim.trans_lt (EReal.coe_lt_coe_iff.mpr hbc)
  exact (eventually_lt_of_limsup_lt hstrict).mono
    (fun _ hk ↦ EReal.coe_lt_coe_iff.mp hk)

/-- Exact source `lma:conc_lim_der`: actual pointwise extended-real upper limits and convergence at zero squeeze the original convex derivatives. -/
theorem tendsto_deriv_of_convex_limsup_le {I : Set ℝ} (hI : IsOpen I) (hzero : 0 ∈ I)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ k, ConvexOn ℝ I (f k))
    (hfd : ∀ k, DifferentiableAt ℝ (f k) 0) (hgd : DifferentiableAt ℝ g 0)
    (hlim : ∀ t ∈ I, limsup (fun k ↦ (f k t : EReal)) atTop ≤ (g t : EReal))
    (hvalue : Tendsto (fun k ↦ f k 0) atTop (𝓝 (g 0))) :
    Tendsto (fun k ↦ deriv (f k) 0) atTop (𝓝 (deriv g 0)) := by
  have hImem : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ I := hI.mem_nhds hzero
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hslope : Tendsto (slope g 0) (𝓝[<] 0) (𝓝 (deriv g 0)) :=
      hgd.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 0)
    have hchoose : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ I ∧ t < 0 ∧ a < slope g 0 t := by
      filter_upwards [hImem.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin, hslope.eventually_const_lt ha] with t htI ht hs
      exact ⟨htI, ht, hs⟩
    obtain ⟨t, htI, ht, hs⟩ := hchoose.exists
    simp only [slope_def_field, sub_zero] at hs
    have hgap : g t < g 0 + t * a := by
      have h := (lt_div_iff_of_neg ht).mp hs
      nlinarith
    obtain ⟨c, hgc, hc⟩ := exists_between hgap
    have hupper := eventually_lt_of_ereal_limsup_le (hlim t htI) hgc
    have hlower : ∀ᶠ k in atTop, c < f k 0 + t * a :=
      (hvalue.add_const (t * a)).eventually_const_lt hc
    filter_upwards [hupper, hlower] with k hup hlo
    have htangent := convex_origin_tangent_le (hf k) hzero (hfd k) htI
    have hmul : t * deriv (f k) 0 < t * a := by linarith
    exact (mul_lt_mul_left_of_neg ht).mp hmul
  · intro b hb
    have hslope : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 (deriv g 0)) :=
      hgd.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    have hchoose : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ I ∧ 0 < t ∧ slope g 0 t < b := by
      filter_upwards [hImem.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin, hslope.eventually_lt_const hb] with t htI ht hs
      exact ⟨htI, ht, hs⟩
    obtain ⟨t, htI, ht, hs⟩ := hchoose.exists
    simp only [slope_def_field, sub_zero] at hs
    have hgap : g t < g 0 + t * b := by
      have h := (div_lt_iff₀ ht).mp hs
      nlinarith
    obtain ⟨c, hgc, hc⟩ := exists_between hgap
    have hupper := eventually_lt_of_ereal_limsup_le (hlim t htI) hgc
    have hlower : ∀ᶠ k in atTop, c < f k 0 + t * b :=
      (hvalue.add_const (t * b)).eventually_const_lt hc
    filter_upwards [hupper, hlower] with k hup hlo
    have htangent := convex_origin_tangent_le (hf k) hzero (hfd k) htI
    have hmul : t * deriv (f k) 0 < t * b := by linarith
    exact (mul_lt_mul_iff_right₀ ht).mp (by simpa only [mul_comm] using hmul)

/-- The original open-interval derivative formulation: only differentiability within the actual interval is required. -/
theorem tendsto_derivWithin_of_convex_limsup_le {I : Set ℝ}
    (hI : IsOpen I) (hzero : 0 ∈ I) {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ k, ConvexOn ℝ I (f k))
    (hfd : ∀ k, DifferentiableWithinAt ℝ (f k) I 0)
    (hgd : DifferentiableWithinAt ℝ g I 0)
    (hlim : ∀ t ∈ I, limsup (fun k ↦ (f k t : EReal)) atTop ≤ (g t : EReal))
    (hvalue : Tendsto (fun k ↦ f k 0) atTop (𝓝 (g 0))) :
    Tendsto (fun k ↦ derivWithin (f k) I 0) atTop (𝓝 (derivWithin g I 0)) := by
  simpa only [derivWithin_of_isOpen hI hzero] using
    tendsto_deriv_of_convex_limsup_le hI hzero hf
      (fun k ↦ (hfd k).differentiableAt (hI.mem_nhds hzero))
      (hgd.differentiableAt (hI.mem_nhds hzero)) hlim hvalue

end SGPT.Convex
