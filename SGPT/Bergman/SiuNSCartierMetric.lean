import SGPT.Bergman.SiuNSScalarMetric
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport

/-! Actual smooth local weights of the original Cartier metric, including
their compatibility and exact original curvature across singular zeros. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A generating atlas of the original full Cartier ideal with the actual
smooth remainders of the original divisor metric. -/
structure CartierMetricAtlas (D : EffectiveDivisor n X) (E : MeteredEffectiveQDivisor n X)
    extends CartierAtlas D where
  remainder : X → X → ℝ
  smooth : ∀ i, ChartSmoothOn (n := n) (remainder i) (dom i)
  weight_eq : ∀ i y, y ∈ dom i →
    E.weight y = generatorLog (fun _ : Fin 1 => gen i) y + (remainder i y : EReal)

/-- An actual divisor metric supplies its own genuine generating cover,
actual smooth remainders, and dense nonzero generators. -/
def cartierMetricAtlas (D : EffectiveDivisor n X) (E : MeteredEffectiveQDivisor n X)
    (hE : DivisorMetric.IsDivisorMetric D E) : CartierMetricAtlas D E := by
  have hex : ∀ x : X, ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧ ∃ g : X → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g V ∧
      (∀ W : Set X, IsOpen W → W ⊆ V → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ V, ∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ h : X → ℝ, ChartSmoothOn (n := n) h V ∧
        ∀ y ∈ V, E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal) := by
    intro x
    obtain ⟨V₀, hV₀, hx₀, g₀, hg₀, hn₀, hgen₀⟩ := D.isInvertible x
    obtain ⟨V₁, hV₁, hx₁, g, hg, hgen, h, hh, hw⟩ := hE x
    obtain ⟨V, u, hV, hxV, hsub, _, hun, heq⟩ :=
      DivisorMetric.exists_unit_of_generators hV₀ hV₁ hg₀ hg hn₀ hgen₀ hgen hx₀ hx₁
    refine ⟨V, hV, hxV, g, hg.mono (fun y hy => (hsub hy).2), ?_,
      fun y hy => hgen y (hsub hy).2, h, ?_, fun y hy => hw y (hsub hy).2⟩
    · intro W hW hWV hne
      obtain ⟨y, hy, hgy⟩ := hn₀ W hW (fun y hy => (hsub (hWV hy)).1) hne
      exact ⟨y, hy, by rw [heq y (hWV hy)]; exact mul_ne_zero (hun y (hWV hy)) hgy⟩
    · intro c
      exact (hh c).mono (fun y hy => ⟨hy.1, (hsub hy.2).2⟩)
  choose V hV hx g hg hn hgen h hh hw using hex
  exact ⟨⟨V, hV, hx, g, hg, hn, hgen⟩, h, hh, hw⟩

namespace CartierMetricAtlas
variable {D : EffectiveDivisor n X} {E : MeteredEffectiveQDivisor n X}
  (A : CartierMetricAtlas D E)

private theorem remainder_continuousAt (i : X) {p : X} (hp : p ∈ A.dom i) :
    ContinuousAt (A.remainder i) p := by
  let c := complexChartAt (n := n) p
  have hpc := mem_complexChartAt_source (n := n) p
  have hz : c.val p ∈ c.val.target ∩ c.val.symm ⁻¹' A.dom i := by
    exact ⟨c.val.map_source hpc, by simpa only [Set.mem_preimage, c.val.left_inv hpc] using hp⟩
  have h1 := ((A.smooth i c).continuousOn.continuousAt
    ((c.val.isOpen_inter_preimage_symm (A.open_dom i)).mem_nhds hz)).comp (c.val.continuousAt hpc)
  apply h1.congr
  filter_upwards [c.val.open_source.mem_nhds hpc] with y hy
  simp only [Function.comp_def, c.val.left_inv hy]

/-- Equality of the original extended-real weights determines the exact
smooth metric transformation, even at singular Cartier points. -/
theorem remainder_transition (i j : X) {p : X} (hi : p ∈ A.dom i) (hj : p ∈ A.dom j) :
    A.remainder i p = Real.log (‖A.toCartierAtlas.transition i j p‖ ^ 2) + A.remainder j p := by
  let t := A.toCartierAtlas.transition i j
  have ht := A.toCartierAtlas.transition_holomorphicAt i j ⟨hi, hj⟩
  have ht0 := A.toCartierAtlas.transition_ne_zero i j ⟨hi, hj⟩
  have hc : ContinuousAt (fun y => A.remainder i y -
      (Real.log (‖t y‖ ^ 2) + A.remainder j y)) p :=
    (A.remainder_continuousAt i hi).sub
      (((ht.continuousAt.norm.pow 2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr ht0))).add
        (A.remainder_continuousAt j hj))
  by_contra hne
  have hnear := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (hnear.and ((A.open_dom i |>.inter (A.open_dom j)).mem_nhds ⟨hi, hj⟩))
  obtain ⟨y, hyV, hgi⟩ := A.dense i V hV (fun y hy => (hVsub hy).2.1) ⟨p, hpV⟩
  have hyi := (hVsub hyV).2.1
  have hyj := (hVsub hyV).2.2
  have hty := A.toCartierAtlas.transition_ne_zero i j ⟨hyi, hyj⟩
  have hgj : A.gen j y ≠ 0 := by
    rw [A.toCartierAtlas.generator_transition i j ⟨hyi, hyj⟩]
    exact mul_ne_zero hgi hty
  have hw := (A.weight_eq i y hyi).symm.trans (A.weight_eq j y hyj)
  rw [MeteredDivisorWeightBounds.generatorLog_single_eq_coe hgi,
    MeteredDivisorWeightBounds.generatorLog_single_eq_coe hgj,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hw
  have hn : Real.log (‖A.gen j y‖ ^ 2) =
      Real.log (‖A.gen i y‖ ^ 2) + Real.log (‖t y‖ ^ 2) := by
    rw [A.toCartierAtlas.generator_transition i j ⟨hyi, hyj⟩, norm_mul, mul_pow,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hgi))
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hty))]
  exact (hVsub hyV).1 (by dsimp only [t] at hn ⊢; rw [hn] at hw; linarith)

/-- The actual Cartier metric supplies compatible smooth native weights. -/
def scalarWeights : CompatibleScalarWeights A.toCartierAtlas.toScalarCocycle where
  weight := A.remainder
  smooth := A.smooth
  compatible := fun i j _ hi hj => A.remainder_transition i j hi hj


/-- On the genuine nonzero locus, the original extended-real weight is
an honest local potential and gives the exact curvature of the remainder. -/
theorem remainder_curvature_of_ne_zero (i : X) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (hi : c.val.symm z ∈ A.dom i)
    (hg : A.gen i (c.val.symm z) ≠ 0) :
    E.curvature.val.coeff c z = -smoothDDC (fun w => A.remainder i (c.val.symm w)) z := by
  let T := c.val.target ∩ c.val.symm ⁻¹' A.dom i
  have hT : IsOpen T := c.val.isOpen_inter_preimage_symm (A.open_dom i)
  have hzT : z ∈ T := ⟨hz, hi⟩
  let g := fun w => A.gen i (c.val.symm w)
  have hgd : DifferentiableOn ℂ g T :=
    MeteredDivisorPositivity.differentiableOn_comp_chartSymm c (A.hol i)
  let U := T ∩ g ⁻¹' {a : ℂ | a ≠ 0}
  have hU : IsOpen U := hgd.continuousOn.isOpen_inter_preimage hT isOpen_ne
  have hzU : z ∈ U := ⟨hzT, hg⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (Complex.normSq (g w))) U := by
    intro w hw
    exact (MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hT hgd hw.1 hw.2).contDiffWithinAt
  have hfin : c.val.symm z ∉ E.support := by
    show E.weight (c.val.symm z) ≠ ⊥
    rw [A.weight_eq i _ hi, MeteredDivisorWeightBounds.generatorLog_single_eq_coe hg,
      ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  obtain ⟨W, hzW, hW⟩ := MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature
    E hfin c (c.val.map_target hz)
  rw [c.val.right_inv hz] at hzW
  have heq : (fun w => (E.weight (c.val.symm w)).toReal) =ᶠ[𝓝 z]
      fun w => Real.log (Complex.normSq (g w)) + A.remainder i (c.val.symm w) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    rw [A.weight_eq i _ hw.1.2, MeteredDivisorWeightBounds.generatorLog_single_eq_coe (show A.gen i (c.val.symm w) ≠ 0 from hw.2),
      ← EReal.coe_add, EReal.toReal_coe, Complex.normSq_eq_norm_sq]
  have hharm : smoothDDC (fun w => Real.log (Complex.normSq (g w))) z = 0 :=
    PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
      (Filter.eventually_of_mem (hT.mem_nhds hzT)
        (fun w hw => (hgd w hw).differentiableAt (hT.mem_nhds hw))) hg
  have hcurv := hW.2.2.2 hzW
  rw [smoothDDC_congr heq, smoothDDC_add hU hlog ((A.smooth i c).mono inter_subset_left) hzU,
    hharm, zero_add, ClosedRealOneOneForm.coeff_neg] at hcurv
  simpa only [neg_neg] using (congrArg Neg.neg hcurv).symm

variable [CompactSpace X]

/-- The manufactured physical native bundle has the original divisor
curvature on every original chart, including singular Cartier zeros. -/
theorem nativeBundle_geometricallyEq :
    (SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm
      A.scalarWeights.nativeBundle A.scalarWeights.nativeBundle_smooth).val.GeometricallyEq E.curvature.val := by
  intro c z hz
  let θ := SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm
    A.scalarWeights.nativeBundle A.scalarWeights.nativeBundle_smooth
  let p := c.val.symm z
  have hp : p ∈ c.val.source := c.val.map_target hz
  have hpi : p ∈ A.dom p := A.mem_dom p
  have hnear : ∀ᶠ y in 𝓝 p, y ∈ c.val.source ∧ y ∈ A.dom p :=
    Filter.Eventually.and (c.val.open_source.mem_nhds hp) ((A.open_dom p).mem_nhds hpi)
  have hcp : c.val p = z := c.val.right_inv hz
  have htarget : c.val p ∈ c.val.target := by simpa only [hcp] using hz
  have hc : ContinuousAt (fun y => θ.val.coeff c (c.val y) - E.curvature.val.coeff c (c.val y)) p :=
    (((θ.val.smooth c).continuousOn.continuousAt (c.val.open_target.mem_nhds htarget)).comp
      (c.val.continuousAt hp)).sub
      (((E.curvature.val.smooth c).continuousOn.continuousAt (c.val.open_target.mem_nhds htarget)).comp
        (c.val.continuousAt hp))
  by_contra hne
  have hne' : θ.val.coeff c (c.val p) - E.curvature.val.coeff c (c.val p) ≠ 0 := by
    simpa only [p, c.val.right_inv hz] using sub_ne_zero.mpr hne
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp ((hc.eventually_ne hne').and hnear)
  obtain ⟨y, hyV, hgy⟩ := A.dense p V hV (fun y hy => (hVsub hy).2.2) ⟨p, hpV⟩
  have hyc := (hVsub hyV).2.1
  have hyi := (hVsub hyV).2.2
  have hyz := c.val.map_source hyc
  have hys : c.val.symm (c.val y) = y := c.val.left_inv hyc
  have hnative := A.scalarWeights.nativeBundle_chern_coeff p c hyz (by simpa only [hys, CartierAtlas.toScalarCocycle] using hyi)
  have hdiv := A.remainder_curvature_of_ne_zero p c hyz
    (by simpa only [hys] using hyi) (by simpa only [hys] using hgy)
  exact (hVsub hyV).1 (sub_eq_zero.mpr (hnative.trans hdiv.symm))

include A in
/-- Original Cartier data manufacture the actual native line bundle and
its original Chern form; there is no supplied bundle or Chern certificate. -/
theorem exists_native_divisor_metric :
    ∃ L : SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle n X,
      SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric L ∧
      SGPT.PSH.GlobalL2.IsOwnFirstChernForm L E.curvature := by
  refine ⟨A.scalarWeights.nativeBundle, A.scalarWeights.nativeBundle_smooth, ?_⟩
  intro c e z hz he
  rw [← A.nativeBundle_geometricallyEq c hz]
  exact SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm_isOwn _ _ c e z hz he

end CartierMetricAtlas
end SGPT.BDivisor.NSKodaira
