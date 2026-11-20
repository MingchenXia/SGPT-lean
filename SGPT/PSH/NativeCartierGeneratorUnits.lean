import SGPT.PSH.CartierLogarithmicRemainder
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HolomorphicBoundedQuotient
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Exact ORIGINAL native readback of the genuine existing centered unit
transition between generators of the SAME FULL Cartier ideal. -/
theorem exists_native_cartier_generator_unit
    (D : EffectiveDivisor n M) (x : M) (g h : M → ℂ)
    (hg : HolomorphicAt n g x) (hh : HolomorphicAt n h x)
    (hgenG : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = g) x b)
    (hgenH : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = h) x b) :
    ∃ v : M → ℂ, HolomorphicAt n v x ∧ v x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, v y ≠ 0) ∧ g =ᶠ[𝓝 x] fun y => h y * v y := by
  obtain ⟨V, hV, hV0, hVnear, htrans⟩ :=
    exists_centered_unit_transition_of_cartier_generators D x g h hg hh hgenG hgenH
  let v : M → ℂ := fun y => V (rechart n x y)
  have hv : HolomorphicAt n v x := holomorphicAt_comp_rechart (n := n) (x := x) hV
  refine ⟨v, hv, ?_, tendsto_rechart (n := n) x hVnear, ?_⟩
  · simpa only [v, rechart_self] using hV0
  · have htrans' : (fun z => g (rechartSymm n x z)) =ᶠ[𝓝 0]
        fun z => h (rechartSymm n x z) * V z := by
      simpa only [rechartSymm, complexChartAt] using htrans
    filter_upwards [tendsto_rechart (n := n) x htrans',
      eventually_rechartSymm_rechart (n := n) x] with y hy hxy
    change g (rechartSymm n x (rechart n x y)) =
      h (rechartSymm n x (rechart n x y)) * V (rechart n x y) at hy
    rw [hxy] at hy
    exact hy

/-- ORIGINAL defining equations of the SAME full Cartier stalk and an
arbitrary ORIGINAL bounded real remainder manufacture a genuine bounded
logarithmic transition, retaining all negative-infinite poles. -/
theorem exists_native_bounded_logarithmic_generator_transition
    (D : EffectiveDivisor n M) (x : M) (g h : M → ℂ)
    (hg : HolomorphicAt n g x) (hh : HolomorphicAt n h x)
    (hgenG : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = g) x b)
    (hgenH : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = h) x b)
    (c : ℚ) (hc : 0 < c) (u : M → EReal) (R : M → ℝ) (hR : BoundedRealGermAt R x)
    (hu : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * logNormSq (g y) + (R y : EReal)) :
    ∃ b : M → ℝ, BoundedRealGermAt b x ∧
      u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * logNormSq (h y) + (b y : EReal) := by
  obtain ⟨v, hv, hv0, hvnear, hgh⟩ := exists_native_cartier_generator_unit D x g h hg hh hgenG hgenH
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlogcont : ContinuousAt (fun y => Real.log (‖v y‖ ^ 2)) x :=
    (hv.continuousAt.norm.pow 2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0))
  let b : M → ℝ := fun y => R y + (c : ℝ) * Real.log (‖v y‖ ^ 2)
  have hb : BoundedRealGermAt b x := hR.add
    (boundedRealGermAt_of_continuousAt (continuousAt_const.mul hlogcont))
  have hpair (a z : ℂ) : logNormSq (a * z) = logNormSq a + logNormSq z := by
    simpa using logNormSq_geometric_product (fun _ : Fin 1 => a) (fun _ => 1) z
  refine ⟨b, hb, ?_⟩
  filter_upwards [hu, hgh, hvnear] with y huy hgy hvy
  rw [huy, hgy, hpair, logNormSq_of_ne_zero hvy,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top (c : ℝ))]
  dsimp only [b]
  rw [EReal.coe_add, EReal.coe_mul]
  ac_rfl

end SGPT.PSH
