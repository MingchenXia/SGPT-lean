import SGPT.NPP.DN3RadialConvex
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Radial means of plurisubharmonic functions with poles are convex in `log r`

Lane DN10, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Steps 5–7: "`H_u(x, eˢ)` is a strictly convex
nondecreasing function of `s` which tends to `u(x)`"; FPT proves the convexity for smooth
potentials (Step 5) and passes to the limit (Step 6)).

For the radial mean `M(t) = ∫ g(t y) χ(|y|²) dy` (`SGPT.NPP.DN3.kernel`) of a function `g`
plurisubharmonic on a ball `B(0, δ)`, `δ > 1`, poles allowed:

* `convexOn_radialMean_exp` — smooth case: `s ↦ M(eˢ)` is convex on `s ≤ 0` (the formulas
  `d/ds M(eˢ) = λ(eˢ)`, `d/ds λ(eˢ) = 4e^{2s}∫ L_g(eˢζ; ζ)χ ≥ 0`, localised to plurisubharmonicity on
  a ball);
* `convexOn_integral_of_locallyBoundedPsh` — locally bounded case: decreasing smooth approximations
  (`SGPT.Foundations.Analysis.Pending.HolomorphicPullback.exists_decreasingMollifierApproximation`),
  a cutoff and dominated convergence (the argument of
  `SGPT.Foundations.Analysis.Pending.PshRadialRegularization.integral_mono_of_locallyBoundedPsh`);
* `convexOn_integral_of_psh` — poles: truncations `max(g, -k)` and
  `PshRadialRegularization.tendsto_integral_truncation`;
* `radial_psh` — together with the submean inequality and the monotonicity of TN
  (`le_integral_of_psh`, `integral_mono_of_psh`), without any nondegeneracy hypothesis
  (if `g ≡ -∞` on the ball all radial means vanish).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.NPP.DN10

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {n : ℕ}

/-- A pointwise limit of convex functions is convex. -/
theorem convexOn_of_tendsto {D : Set ℝ} (hD : Convex ℝ D) {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hf : ∀ j, ConvexOn ℝ D (f j))
    (hlim : ∀ x ∈ D, Tendsto (fun j => f j x) atTop (𝓝 (F x))) : ConvexOn ℝ D F := by
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hlim _ (hD hx hy ha hb hab)
  have h2 : Tendsto (fun j => a • f j x + b • f j y) atTop (𝓝 (a • F x + b • F y)) :=
    ((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)
  exact le_of_tendsto_of_tendsto' h1 h2 fun j => (hf j).2 hx hy ha hb hab

/-- A function nondecreasing on `D` has a nonnegative derivative at interior points. -/
theorem deriv_nonneg_of_monotoneOn {D : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f D) {x : ℝ}
    (hx : D ∈ 𝓝 x) : 0 ≤ deriv f x := by
  rw [← derivWithin_of_mem_nhds hx]
  exact hf.derivWithin_nonneg

/-- `radialLevi g r ≥ 0` when `g` is plurisubharmonic on a ball of radius `> r`. -/
theorem radialLevi_nonneg_of_ball {g : ComplexModel n → ℝ} {R₁ : ℝ}
    (hpsh : ∀ y ∈ ball (0 : ComplexModel n) R₁, ∀ v, 0 ≤ leviForm g y v) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < R₁) : 0 ≤ DN3.radialLevi g r := by
  unfold DN3.radialLevi
  refine mul_nonneg (by positivity) (integral_nonneg fun ζ => ?_)
  by_cases hζ : ‖ζ‖ < 1
  · refine mul_nonneg (hpsh _ ?_ _) (DN3.kernel_nonneg ζ)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    calc r * ‖ζ‖ ≤ r * 1 := by gcongr
      _ < R₁ := by linarith
  · simp [DN3.kernel_eq_zero n (not_lt.mp hζ)]

/-- **Smooth case.**  For `g` of class `C²`, plurisubharmonic on `B(0, R₁)`, `R₁ > 1`, the radial
mean `s ↦ M_g(eˢ)` is convex on `s ≤ 0`. -/
theorem convexOn_radialMean_exp {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) {R₁ : ℝ}
    (hR₁ : 1 < R₁) (hpsh : ∀ y ∈ ball (0 : ComplexModel n) R₁, ∀ v, 0 ≤ leviForm g y v) :
    ConvexOn ℝ (Iic 0) (fun s => DN3.radialMean g (Real.exp s)) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hf : ∀ s, HasDerivAt (fun s => DN3.radialMean g (Real.exp s))
      (DN3.radialSlope g (Real.exp s)) s := DN3.hasDerivAt_radialMean_exp hg1
  have hf' : ∀ s, HasDerivAt (fun s => DN3.radialSlope g (Real.exp s))
      (DN3.radialLevi g (Real.exp s)) s := DN3.hasDerivAt_radialSlope_exp hg
  have hderiv : deriv (fun s => DN3.radialMean g (Real.exp s)) =
      fun s => DN3.radialSlope g (Real.exp s) := funext fun s => (hf s).deriv
  refine MonotoneOn.convexOn_of_deriv (convex_Iic 0)
    (fun s _ => (hf s).continuousAt.continuousWithinAt)
    (fun s _ => (hf s).differentiableAt.differentiableWithinAt) ?_
  rw [hderiv, interior_Iic]
  refine monotoneOn_of_deriv_nonneg (convex_Iio 0)
    (fun s _ => (hf' s).continuousAt.continuousWithinAt)
    (fun s _ => (hf' s).differentiableAt.differentiableWithinAt) fun s hs => ?_
  rw [interior_Iio] at hs
  rw [(hf' s).deriv]
  have h1 : Real.exp s < 1 := Real.exp_lt_one_iff.mpr hs
  exact radialLevi_nonneg_of_ball hpsh (Real.exp_pos s).le (by linarith)

/-- **Locally bounded case.**  For a locally bounded real plurisubharmonic `p` on `Ω ⊇ B(0, δ)`,
`δ > 1`, `s ↦ ∫ p(eˢ y) χ(|y|²) dy` is convex on `s ≤ 0`. -/
theorem convexOn_integral_of_locallyBoundedPsh {Ω : Opens (ComplexModel n)}
    {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p) {δ : ℝ} (hδ : 1 < δ)
    (hzδ : ball (0 : ComplexModel n) δ ⊆ Ω) :
    ConvexOn ℝ (Iic 0) (fun s => ∫ y, p (Real.exp s • y) * DN3.kernel n y) := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hκ : Continuous (DN3.kernel n) := DN3.continuous_kernel
  have hκc : HasCompactSupport (DN3.kernel n) := DN3.hasCompactSupport_kernel
  have hκR : tsupport (DN3.kernel n) ⊆ closedBall 0 1 := (DN3.isRadialKernel_kernel n).tsupport_subset
  have hnorm : ∀ y ∈ tsupport (DN3.kernel n), ‖y‖ ≤ 1 := fun y hy =>
    mem_closedBall_zero_iff.mp (hκR hy)
  set R1 := 1 + (δ - 1) / 4 with hR1
  set R2 := 1 + (δ - 1) / 2 with hR2
  set R3 := 1 + 3 * (δ - 1) / 4 with hR3
  have h0R1 : 0 < R1 := by rw [hR1]; linarith
  have hRR1 : 1 < R1 := by rw [hR1]; linarith
  have hR12 : R1 < R2 := by rw [hR1, hR2]; linarith
  have hR23 : R2 < R3 := by rw [hR2, hR3]; linarith
  have hR3δ : R3 < δ := by rw [hR3]; linarith
  let A : Opens (ComplexModel n) := ⟨ball 0 R3, isOpen_ball⟩
  have hAset : (A : Set (ComplexModel n)) = ball 0 R3 := rfl
  have hA : RelativelyCompactIn A Ω := by
    rw [RelativelyCompactIn, hAset, closure_ball 0 (by linarith : R3 ≠ 0)]
    exact ⟨isCompact_closedBall 0 R3, (closedBall_subset_ball hR3δ).trans hzδ⟩
  obtain ⟨f, hfs, hfa, hft⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hp hA
  obtain ⟨b, hbIn, hbOut⟩ : ∃ b : ContDiffBump (0 : ComplexModel n), b.rIn = R1 ∧ b.rOut = R2 :=
    ⟨⟨R1, R2, h0R1, hR12⟩, rfl, rfl⟩
  have hb1 : ∀ x ∈ ball (0 : ComplexModel n) R1, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (by rw [hbIn]; exact ball_subset_closedBall hx)
  have hbsupp : tsupport b ⊆ (A : Set (ComplexModel n)) := by
    rw [b.tsupport_eq, hAset, hbOut]
    exact closedBall_subset_ball hR23
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ComplexModel n → ℝ, g = fun j x => b x * f j x := ⟨_, rfl⟩
  have hg : ∀ j, ContDiff ℝ ∞ (g j) := fun j => by
    rw [hg_def]
    exact contDiff_mul_of_tsupport A.isOpen b.contDiff hbsupp (hfs j).1
  have hgf : ∀ j, ∀ x ∈ ball (0 : ComplexModel n) R1, g j x = f j x := fun j x hx => by
    simp only [hg_def, hb1 x hx, one_mul]
  have hKR1 : closedBall (0 : ComplexModel n) 1 ⊆ ball 0 R1 := closedBall_subset_ball hRR1
  have hR1A : ball (0 : ComplexModel n) R1 ⊆ (A : Set (ComplexModel n)) := by
    rw [hAset]
    exact ball_subset_ball (by linarith)
  let B1 : Opens (ComplexModel n) := ⟨ball 0 R1, isOpen_ball⟩
  have hgpsh : ∀ j, PlurisubharmonicOn (fun x => (g j x : EReal)) B1 := by
    intro j x hx
    refine ((hfs j).2.1 x (hR1A hx)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    rw [hgf j w hw]
  have hglevi : ∀ j, ∀ y ∈ ball (0 : ComplexModel n) R1, ∀ v, 0 ≤ leviForm (g j) y v :=
    fun j y hy v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := B1)
      (hg j).contDiffOn (hgpsh j) hy v
  have hconv : ∀ j, ConvexOn ℝ (Iic 0) (fun s => ∫ y, g j (Real.exp s • y) * DN3.kernel n y) :=
    fun j => convexOn_radialMean_exp ((hg j).of_le (by norm_cast)) hRR1 (hglevi j)
  obtain ⟨Cp, -, hCp⟩ := hp.exists_compact_abs_bound (isCompact_closedBall (0 : ComplexModel n) 1)
    (hKR1.trans (hR1A.trans ((ball_subset_ball hR3δ.le).trans hzδ)))
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : ComplexModel n) 1).exists_bound_of_continuousOn
    ((hfs 0).1.continuousOn.mono (hKR1.trans hR1A))
  set C := |Cp| + |C0| with hC
  have hfbound : ∀ j, ∀ x ∈ closedBall (0 : ComplexModel n) 1, |f j x| ≤ C := by
    intro j x hx
    have hxA : x ∈ (A : Set (ComplexModel n)) := hR1A (hKR1 hx)
    have h1 : p x ≤ f j x := (hfa x hxA).le_of_tendsto (hft x hxA) j
    have h2 : f j x ≤ f 0 x := hfa x hxA (Nat.zero_le j)
    have h3 := abs_le.mp ((hCp x hx).trans (le_abs_self Cp))
    have h4 := abs_le.mp (((Real.norm_eq_abs _).symm.le.trans (hC0 x hx)).trans (le_abs_self C0))
    rw [hC]
    exact abs_le.mpr ⟨by linarith [abs_nonneg C0], by linarith [abs_nonneg Cp]⟩
  refine convexOn_of_tendsto (convex_Iic 0) hconv fun s hs => ?_
  set t := Real.exp s with ht
  have ht0 : 0 ≤ t := (Real.exp_pos s).le
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr hs
  have hmem : ∀ y ∈ tsupport (DN3.kernel n), t • y ∈ closedBall (0 : ComplexModel n) 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [hnorm y hy, norm_nonneg y]
  refine tendsto_integral_of_dominated_convergence (fun y => C * DN3.kernel n y) ?_
    ((hκ.integrable_of_hasCompactSupport hκc).const_mul C) ?_ ?_
  · intro j
    exact (((hg j).continuous.comp (continuous_const_smul t)).mul hκ).aestronglyMeasurable
  · intro j
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport (DN3.kernel n)
    · rw [hgf j _ (hKR1 (hmem y hy)), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (DN3.kernel_nonneg y)]
      exact mul_le_mul_of_nonneg_right (hfbound j _ (hmem y hy)) (DN3.kernel_nonneg y)
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport (DN3.kernel n)
    · have hfun : (fun j => g j (t • y) * DN3.kernel n y) = fun j => f j (t • y) * DN3.kernel n y :=
        funext fun j => by rw [hgf j _ (hKR1 (hmem y hy))]
      rw [hfun]
      exact (hft _ (hR1A (hKR1 (hmem y hy)))).mul_const _
    · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Poles.**  For `u` plurisubharmonic on an open preconnected `U ⊇ B(0, δ)`, `δ > 1`, not
identically `-∞`, `s ↦ ∫ u(eˢ y) χ(|y|²) dy` (real representative) is convex on `s ≤ 0`. -/
theorem convexOn_integral_of_psh {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U)
    (hne : ∃ a ∈ U, u a ≠ ⊥) {δ : ℝ} (hδ : 1 < δ) (hball : ball (0 : ComplexModel n) δ ⊆ U) :
    ConvexOn ℝ (Iic 0) (fun s => ∫ y, (u (Real.exp s • y)).toReal * DN3.kernel n y) := by
  refine convexOn_of_tendsto (convex_Iic 0)
    (f := fun k s => ∫ y, (max (u (Real.exp s • y)) ((-(k : ℝ) : ℝ) : EReal)).toReal *
      DN3.kernel n y) (fun k => ?_) (fun s hs => ?_)
  · exact convexOn_integral_of_locallyBoundedPsh (Ω := ⟨U, hU⟩)
      (isLocallyBoundedPshOn_truncation hU hu (-(k : ℝ))) hδ hball
  · have h := tendsto_integral_truncation hU hUc hu hne (DN3.isRadialKernel_kernel n).continuous
      (DN3.kernel_nonneg) (z := 0) (R := 1) (DN3.isRadialKernel_kernel n).tsupport_subset
      ((closedBall_subset_ball hδ).trans hball) (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs)
    simpa only [zero_add] using h

/-- **Radial means of a plurisubharmonic function on `B(0, δ)`, `δ > 1`** (poles allowed, no
nondegeneracy): with `M(τ) = ∫ g(τ y) χ(|y|²) dy`,
`g(0) ≤ M(τ)` for `0 < τ ≤ 1`, `M` is nondecreasing on `(0, 1]` and `s ↦ M(eˢ)` is convex on
`s ≤ 0`. -/
theorem radial_psh {g : ComplexModel n → EReal} {δ : ℝ} (hδ : 1 < δ)
    (hg : PlurisubharmonicOn g (ball 0 δ)) :
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      g 0 ≤ ((∫ y, (g (τ • y)).toReal * DN3.kernel n y : ℝ) : EReal)) ∧
    MonotoneOn (fun τ : ℝ => ∫ y, (g (τ • y)).toReal * DN3.kernel n y) (Ioc (0 : ℝ) 1) ∧
    ConvexOn ℝ (Iic 0) (fun s => ∫ y, (g (Real.exp s • y)).toReal * DN3.kernel n y) := by
  have hκ := DN3.isRadialKernel_kernel n
  by_cases hne : ∃ a ∈ ball (0 : ComplexModel n) δ, g a ≠ ⊥
  · have hUc : IsPreconnected (ball (0 : ComplexModel n) δ) := (convex_ball 0 δ).isPreconnected
    refine ⟨fun τ hτ0 hτ1 => ?_, fun r hr s hs hrs => ?_,
      convexOn_integral_of_psh isOpen_ball hUc hg hne hδ subset_rfl⟩
    · have h := le_integral_of_psh isOpen_ball hUc hg hne hκ.continuous DN3.kernel_nonneg
        hκ.circle_invariant hκ.integral_eq_one (z := 0) hκ.tsupport_subset hδ subset_rfl hτ0 hτ1
      simpa only [zero_add] using h
    · have h := integral_mono_of_psh isOpen_ball hUc hg hne hκ.continuous DN3.kernel_nonneg
        hκ.circle_invariant (z := 0) hκ.tsupport_subset hδ subset_rfl hr.1 hrs hs.2
      simpa only [zero_add] using h
  · push Not at hne
    have hzero : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∫ y, (g (τ • y)).toReal * DN3.kernel n y = 0 := by
      intro τ hτ0 hτ1
      refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : ‖y‖ < 1
      · have hmem : τ • y ∈ ball (0 : ComplexModel n) δ := by
          rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
          nlinarith [norm_nonneg y]
        simp [hne _ hmem]
      · simp [DN3.kernel_eq_zero n (not_lt.mp hy)]
    refine ⟨fun τ _ _ => ?_, fun r hr s hs _ => ?_, ?_⟩
    · rw [hne 0 (mem_ball_self (by linarith))]
      exact bot_le
    · dsimp only
      rw [hzero r hr.1.le hr.2, hzero s hs.1.le hs.2]
    · refine (convexOn_const (0 : ℝ) (convex_Iic (0 : ℝ))).congr fun s hs => ?_
      exact (hzero _ (Real.exp_pos s).le (Real.exp_le_one_iff.mpr hs)).symm

end SGPT.NPP.DN10
