import SGPT.GAGA.CohDerivation
import SGPT.GAGA.CohTimeDeriv
import SGPT.GAGA.CoreClosure
import SGPT.PSH.BookRestrictionIdeal
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction
import SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient

/-!
# Circle actions by biholomorphisms and their generator

Infrastructure of lane COHERENT (source `lma:fibIeq`, `chapter_trace.tex` lines 1166--1193:
"a biholomorphic `S¹`-action on `(X, L)`"; blueprint `claude-coherent.tex`).

* `CircleAction n X`: an action `θ ↦ σ_θ` of the circle group `S¹ = ℝ/2πℤ` on the complex
  manifold `X` by holomorphic maps (biholomorphisms, with inverses `σ_{-θ}`), of class `C¹`
  jointly in `(θ, x)` (read in the preferred charts; every smooth action qualifies).
* `CircleAction.generator g y = d/dθ|_{θ=0} g(σ_θ y)`: the action of the generator of the
  action (a holomorphic vector field) on functions.
* `holomorphicAt_generator`: the generator of a holomorphic function is holomorphic.
  In the chart `e` at `x₀`, `g(σ_θ(e⁻¹ w)) = H(θ, w)` with `H` of class `C¹` and holomorphic in
  `w`; `generator g ∘ e⁻¹ = ∂_θ H(0, ·)` is a locally uniform limit of the holomorphic difference
  quotients (`CohTimeDeriv`).
* `generator_mem` (**invariant coherent ideals are stable under the generator**): if the coherent
  ideal `J` is invariant (`g ∈ J_{σ_θ y} ↔ g ∘ σ_θ ∈ J_y`) and `g ∈ J_x`, then the difference
  quotients `(m+1)(g ∘ σ_{1/(m+1)} - g)` lie in `J_x`, and so does their uniform limit
  `generator g` by Cartan's closure theorem (`GermModule.CoherentAt.mem_of_tendstoUniformlyOn`,
  read in a chart).
* `germGenerator`: the induced derivation of the local ring `𝒪_{X,x}` (`isLeibniz_germGenerator`),
  and `isStable_stalkIdeal`: the stalk of an invariant coherent ideal is stable under it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace SGPT.GAGA.Coherent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.OkaRelationSheaf

/-- **A `C¹` circle action by biholomorphisms.** An action `θ ↦ σ_θ` of the circle group
`S¹ = ℝ/2πℤ` on `X` (`σ_0 = id`, `σ_{a+b} = σ_a ∘ σ_b`, `σ_{2π} = id`) by holomorphic maps
(each `σ_θ` is biholomorphic, with inverse `σ_{-θ}`), such that `(θ, x) ↦ σ_θ x` is continuous
and of class `C¹` in the preferred charts. -/
structure CircleAction (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] where
  /-- The action map `(θ, x) ↦ σ_θ x`. -/
  act : ℝ → X → X
  act_zero : ∀ x, act 0 x = x
  act_add : ∀ a b x, act (a + b) x = act a (act b x)
  act_period : ∀ x, act (2 * Real.pi) x = x
  /-- Each `σ_θ` is holomorphic. -/
  mdifferentiable : ∀ θ, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (act θ)
  continuous : Continuous fun p : ℝ × X => act p.1 p.2
  /-- The action map is `C¹` in the preferred charts. -/
  contDiffAt_chart : ∀ (θ₀ : ℝ) (x₀ : X), ContDiffAt ℝ 1
    (fun p : ℝ × ComplexModel n => chartAt (ComplexModel n) (act θ₀ x₀)
      (act p.1 ((chartAt (ComplexModel n) x₀).symm p.2)))
    (θ₀, chartAt (ComplexModel n) x₀ x₀)

namespace CircleAction

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- `σ_θ` is a bijection, with inverse `σ_{-θ}`. -/
theorem act_neg_act (σ : CircleAction n X) (θ : ℝ) (x : X) : σ.act (-θ) (σ.act θ x) = x := by
  rw [← σ.act_add, neg_add_cancel, σ.act_zero]

theorem act_act_neg (σ : CircleAction n X) (θ : ℝ) (x : X) : σ.act θ (σ.act (-θ) x) = x := by
  rw [← σ.act_add, add_neg_cancel, σ.act_zero]

theorem continuous_act_left (σ : CircleAction n X) (x : X) : Continuous fun θ => σ.act θ x :=
  σ.continuous.comp (continuous_id.prodMk continuous_const)

/-- `σ_θ y → y` as `θ → 0`. -/
theorem tendsto_act_zero (σ : CircleAction n X) (y : X) :
    Tendsto (fun θ => σ.act θ y) (𝓝 0) (𝓝 y) := by
  have h := (σ.continuous_act_left y).tendsto 0
  rwa [σ.act_zero] at h

/-- The **generator** of the action on functions: `D g (y) = d/dθ|_{θ = 0} g(σ_θ y)`. -/
def generator (σ : CircleAction n X) (g : X → ℂ) (y : X) : ℂ :=
  deriv (fun θ : ℝ => g (σ.act θ y)) 0

/-- The generator only depends on germs. -/
theorem generator_congr (σ : CircleAction n X) {x : X} {f g : X → ℂ} (h : f =ᶠ[𝓝 x] g) :
    σ.generator f =ᶠ[𝓝 x] σ.generator g := by
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.eventually_nhds_iff.1 h
  filter_upwards [hV.mem_nhds hxV] with y hy
  have hev : (fun θ : ℝ => f (σ.act θ y)) =ᶠ[𝓝 0] fun θ => g (σ.act θ y) :=
    (σ.tendsto_act_zero y).eventually (eventually_of_mem (hV.mem_nhds hy) hVsub)
  exact hev.deriv_eq

/-! ### The action read in a chart -/

/-- The action read in the preferred chart `e` at `x₀`: `(θ, w) ↦ e(σ_θ(e⁻¹ w))`. -/
def chartFlow (σ : CircleAction n X) (x₀ : X) (p : ℝ × ComplexModel n) : ComplexModel n :=
  chartAt (ComplexModel n) x₀ (σ.act p.1 ((chartAt (ComplexModel n) x₀).symm p.2))

theorem contDiffAt_chartFlow (σ : CircleAction n X) (x₀ : X) :
    ContDiffAt ℝ 1 (σ.chartFlow x₀) ((0 : ℝ), chartAt (ComplexModel n) x₀ x₀) := by
  have h := σ.contDiffAt_chart 0 x₀
  rw [σ.act_zero] at h
  exact h

variable [IsComplexManifold n X]

/-- **Local data for the generator.** Let `g` be holomorphic near `x₀`, `e` the preferred chart at
`x₀` and `H(θ, w) = g(e⁻¹(e(σ_θ(e⁻¹ w))))`. There are `ρ > 0` and an open `Ω ⊇ closedBall
(0, e x₀) ρ` on which `H` is `C¹` and all points `(θ, w)` satisfy `w ∈ e.target`,
`σ_θ(e⁻¹ w) ∈ e.source` and `w ↦ H(θ, w)` is holomorphic near `w`. -/
theorem exists_chart_data (σ : CircleAction n X) (x₀ : X) {g : X → ℂ}
    (hg : HolomorphicAt n g x₀) :
    ∃ (Ω : Set (ℝ × ComplexModel n)) (ρ : ℝ), IsOpen Ω ∧ 0 < ρ ∧
      closedBall ((0 : ℝ), chartAt (ComplexModel n) x₀ x₀) ρ ⊆ Ω ∧
      ContDiffOn ℝ 1 (fun p => g ((chartAt (ComplexModel n) x₀).symm (σ.chartFlow x₀ p))) Ω ∧
      ∀ p ∈ Ω, p.2 ∈ (chartAt (ComplexModel n) x₀).target ∧
        σ.act p.1 ((chartAt (ComplexModel n) x₀).symm p.2) ∈ (chartAt (ComplexModel n) x₀).source ∧
        DifferentiableAt ℂ (fun w => g ((chartAt (ComplexModel n) x₀).symm
          (σ.chartFlow x₀ (p.1, w)))) p.2 := by
  set e := chartAt (ComplexModel n) x₀ with he
  set w₀ := e x₀ with hw₀
  have hx₀ : x₀ ∈ e.source := mem_chart_source (ComplexModel n) x₀
  -- `G = g ∘ e⁻¹` is holomorphic on an open `V ∋ w₀`
  have hG : HolAt (fun w => g (e.symm w)) w₀ := CartanLocalReduction.holAt_comp_chart_symm hx₀ hg
  obtain ⟨V, hVd, hV, hw₀V⟩ := _root_.eventually_nhds_iff.1 hG
  set F := σ.chartFlow x₀ with hF
  have hFc := σ.contDiffAt_chartFlow x₀
  have hF0 : σ.chartFlow x₀ ((0 : ℝ), chartAt (ComplexModel n) x₀ x₀) =
      chartAt (ComplexModel n) x₀ x₀ := by
    simp only [chartFlow, σ.act_zero]
    rw [(chartAt (ComplexModel n) x₀).left_inv (mem_chart_source (ComplexModel n) x₀)]
  -- the set of good points is a neighbourhood of `(0, w₀)`
  have hcont_act : ContinuousAt (fun p : ℝ × ComplexModel n => σ.act p.1 (e.symm p.2))
      ((0 : ℝ), w₀) := by
    have hsymm : ContinuousAt e.symm w₀ := e.continuousAt_symm (e.map_source hx₀)
    have h1 : ContinuousAt (fun p : ℝ × ComplexModel n => ((p.1, e.symm p.2) : ℝ × X))
        ((0 : ℝ), w₀) :=
      continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) (x := ((0 : ℝ), w₀)) hsymm
        continuousAt_snd)
    exact σ.continuous.continuousAt.comp h1
  have hact0 : σ.act (0 : ℝ) (e.symm w₀) = x₀ := by rw [σ.act_zero, e.left_inv hx₀]
  have hS : ∀ᶠ p in 𝓝 ((0 : ℝ), w₀), ContDiffAt ℝ 1 F p ∧ p.2 ∈ e.target ∧
      σ.act p.1 (e.symm p.2) ∈ e.source ∧ F p ∈ V := by
    refine (hFc.eventually (by simp)).and (Eventually.and ?_ (Eventually.and ?_ ?_))
    · exact continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds (e.map_source hx₀))
    · refine hcont_act.preimage_mem_nhds ?_
      rw [hact0]
      exact e.open_source.mem_nhds hx₀
    · refine hFc.continuousAt.preimage_mem_nhds ?_
      rw [hF0]
      exact hV.mem_nhds hw₀V
  set Ω := interior {p | ContDiffAt ℝ 1 F p ∧ p.2 ∈ e.target ∧
      σ.act p.1 (e.symm p.2) ∈ e.source ∧ F p ∈ V} with hΩ
  have hΩmem : Ω ∈ 𝓝 ((0 : ℝ), w₀) := interior_mem_nhds.2 hS
  obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.1 hΩmem
  refine ⟨Ω, r / 2, isOpen_interior, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans
    hrΩ, ?_, ?_⟩
  · intro p hp
    have hp' := interior_subset hp
    obtain ⟨hFp, -, hsrc, hFV⟩ := hp'
    have hGp : ContDiffAt ℝ 1 (fun w => g (e.symm w)) (F p) := by
      have hhol : HolAt (fun w => g (e.symm w)) (F p) :=
        eventually_of_mem (hV.mem_nhds hFV) hVd
      exact ((SGPT.GAGA.Core.contDiffAt_of_holAt hhol).restrict_scalars ℝ)
    exact (hGp.comp p hFp).contDiffWithinAt
  · intro p hp
    obtain ⟨-, htgt, hsrc, hFV⟩ := interior_subset hp
    refine ⟨htgt, hsrc, ?_⟩
    -- `w ↦ e(σ_θ(e⁻¹ w))` is holomorphic at `p.2`
    have hflow : DifferentiableAt ℂ (fun w => F (p.1, w)) p.2 := by
      have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm p.2 :=
        HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm htgt
      have h2 := (σ.mdifferentiable p.1 (e.symm p.2)).comp p.2 h1
      have h3 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e
          (σ.act p.1 (e.symm p.2)) :=
        HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hsrc
      have h4 := h3.comp p.2 h2
      rw [mdifferentiableAt_iff_differentiableAt] at h4
      exact h4
    have hGF : DifferentiableAt ℂ (fun w => g (e.symm w)) (F (p.1, p.2)) := hVd _ hFV
    exact DifferentiableAt.comp (g := fun w => g (e.symm w)) p.2 hGF hflow

/-- `1/(m+1) < ρ` for large `m`. -/
theorem eventually_inv_succ_lt {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1)⁻¹ < ρ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ρ⁻¹
  refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  have hm' : ρ⁻¹ < (m : ℝ) + 1 := by
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [inv_lt_comm₀ (by positivity) hρ]
  exact hm'

/-- **The generator in a chart.** For `g` holomorphic near `x₀` and `e` the preferred chart at
`x₀`, there is `ρ > 0` such that on the ball of radius `ρ` around `e x₀`: `θ ↦ g(σ_θ(e⁻¹ w))`
has derivative `generator g (e⁻¹ w)` at `0`; `w ↦ generator g (e⁻¹ w)` is holomorphic; it is
the uniform limit of the difference quotients `(m+1)(g(σ_{1/(m+1)}(e⁻¹ w)) - g(e⁻¹ w))`, which
are holomorphic for large `m`. -/
theorem exists_generator_chart (σ : CircleAction n X) (x₀ : X) {g : X → ℂ}
    (hg : HolomorphicAt n g x₀) :
    ∃ ρ > 0, (∀ w ∈ ball (chartAt (ComplexModel n) x₀ x₀) ρ,
        w ∈ (chartAt (ComplexModel n) x₀).target ∧
        HasDerivAt (fun θ : ℝ => g (σ.act θ ((chartAt (ComplexModel n) x₀).symm w)))
          (σ.generator g ((chartAt (ComplexModel n) x₀).symm w)) 0) ∧
      DifferentiableOn ℂ (fun w => σ.generator g ((chartAt (ComplexModel n) x₀).symm w))
        (ball (chartAt (ComplexModel n) x₀ x₀) ρ) ∧
      TendstoUniformlyOn (fun (m : ℕ) w => ((m : ℂ) + 1) *
          (g (σ.act ((m : ℝ) + 1)⁻¹ ((chartAt (ComplexModel n) x₀).symm w)) -
            g ((chartAt (ComplexModel n) x₀).symm w)))
        (fun w => σ.generator g ((chartAt (ComplexModel n) x₀).symm w)) atTop
        (ball (chartAt (ComplexModel n) x₀ x₀) ρ) ∧
      (∀ᶠ m : ℕ in atTop, DifferentiableOn ℂ
        (fun w => g (σ.act ((m : ℝ) + 1)⁻¹ ((chartAt (ComplexModel n) x₀).symm w)))
        (ball (chartAt (ComplexModel n) x₀ x₀) ρ)) ∧
      DifferentiableOn ℂ (fun w => g ((chartAt (ComplexModel n) x₀).symm w))
        (ball (chartAt (ComplexModel n) x₀ x₀) ρ) := by
  obtain ⟨Ω, ρ, hΩ, hρ, hK, hH, hpts⟩ := σ.exists_chart_data x₀ hg
  set e := chartAt (ComplexModel n) x₀ with he
  set w₀ := e x₀ with hw₀
  set H : ℝ × ComplexModel n → ℂ := fun p => g (e.symm (σ.chartFlow x₀ p)) with hHdef
  have hI1 : ∀ p ∈ Ω, H p = g (σ.act p.1 (e.symm p.2)) := by
    intro p hp
    simp only [hHdef, chartFlow]
    rw [e.left_inv (hpts p hp).2.1]
  have hmemΩ : ∀ w ∈ ball w₀ ρ, ∀ θ : ℝ, |θ| ≤ ρ → ((θ, w) : ℝ × ComplexModel n) ∈ Ω := by
    intro w hw θ hθ
    apply hK
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ (mem_ball.1 hw).le
    rw [Real.dist_eq, sub_zero]
    exact hθ
  have hI2 : ∀ w ∈ ball w₀ ρ, H ((0 : ℝ), w) = g (e.symm w) := by
    intro w hw
    rw [hI1 _ (hmemΩ w hw 0 (by simp [hρ.le])), σ.act_zero]
  -- the derivative
  have hderiv : ∀ w ∈ ball w₀ ρ,
      HasDerivAt (fun θ : ℝ => g (σ.act θ (e.symm w))) (timeDeriv H w) 0 := by
    intro w hw
    have hdiff : DifferentiableAt ℝ H ((0 : ℝ), w) :=
      (hH.contDiffAt (hΩ.mem_nhds (hmemΩ w hw 0 (by simp [hρ.le])))).differentiableAt
        one_ne_zero
    refine (hasDerivAt_timeDeriv hdiff).congr_of_eventuallyEq ?_
    have hball : ∀ᶠ θ : ℝ in 𝓝 0, |θ| < ρ := by
      have h0 : Metric.ball (0 : ℝ) ρ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hρ
      filter_upwards [h0] with θ hθ
      simpa [Real.dist_eq] using hθ
    filter_upwards [hball] with θ hθ
    exact (hI1 _ (hmemΩ w hw θ hθ.le)).symm
  have hgen : ∀ w ∈ ball w₀ ρ, σ.generator g (e.symm w) = timeDeriv H w :=
    fun w hw => (hderiv w hw).deriv
  -- difference quotients
  have hlimH := tendstoUniformlyOn_diffQuot hΩ hH hK
  have hevρ := eventually_inv_succ_lt hρ
  have hquot : ∀ᶠ m : ℕ in atTop, EqOn (diffQuot H m) (fun w => ((m : ℂ) + 1) *
      (g (σ.act ((m : ℝ) + 1)⁻¹ (e.symm w)) - g (e.symm w))) (ball w₀ ρ) := by
    filter_upwards [hevρ] with m hm w hw
    have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    simp only [diffQuot]
    rw [hI1 _ (hmemΩ w hw _ (by rw [abs_of_pos hpos]; exact hm.le)), hI2 w hw]
  have hslice : ∀ᶠ m : ℕ in atTop, DifferentiableOn ℂ
      (fun w => H (((m : ℝ) + 1)⁻¹, w)) (ball w₀ ρ) := by
    filter_upwards [hevρ] with m hm w hw
    have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    have hp := hpts _ (hmemΩ w hw _ (by rw [abs_of_pos hpos]; exact hm.le))
    exact hp.2.2.differentiableWithinAt
  have hslice0 : DifferentiableOn ℂ (fun w => H ((0 : ℝ), w)) (ball w₀ ρ) := by
    intro w hw
    exact (hpts _ (hmemΩ w hw 0 (by simp [hρ.le]))).2.2.differentiableWithinAt
  have hholT := differentiableOn_timeDeriv hslice hslice0 hlimH
  refine ⟨ρ, hρ, fun w hw => ⟨(hpts _ (hmemΩ w hw 0 (by simp [hρ.le]))).1, ?_⟩, ?_, ?_, ?_,
    hslice0.congr fun w hw => (hI2 w hw).symm⟩
  · rw [hgen w hw]
    exact hderiv w hw
  · exact hholT.congr fun w hw => hgen w hw
  · exact (hlimH.congr hquot).congr_right fun w hw => (hgen w hw).symm
  · filter_upwards [hslice, hquot, hevρ] with m hm _ hmρ
    refine hm.congr fun w hw => ?_
    have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    exact (hI1 _ (hmemΩ w hw _ (by rw [abs_of_pos hpos]; exact hmρ.le))).symm

/-- **The generator of a holomorphic function is holomorphic.** -/
theorem holomorphicAt_generator (σ : CircleAction n X) {x₀ : X} {g : X → ℂ}
    (hg : HolomorphicAt n g x₀) : HolomorphicAt n (σ.generator g) x₀ := by
  obtain ⟨ρ, hρ, hpt, hhol, -, -, -⟩ := σ.exists_generator_chart x₀ hg
  set e := chartAt (ComplexModel n) x₀ with he
  have hx₀ : x₀ ∈ e.source := mem_chart_source (ComplexModel n) x₀
  have hW : HolAt (fun w => σ.generator g (e.symm w)) (e x₀) :=
    eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hρ)) fun w hw =>
      hhol.differentiableAt (isOpen_ball.mem_nhds hw)
  refine (CartanLocalReduction.holomorphicAt_comp_chart hx₀ hW).congr ?_
  filter_upwards [e.open_source.mem_nhds hx₀] with p hp
  rw [e.left_inv hp]

/-- Near `x₀`, `θ ↦ g(σ_θ y)` has derivative `generator g y` at `0`. -/
theorem eventually_hasDerivAt (σ : CircleAction n X) {x₀ : X} {g : X → ℂ}
    (hg : HolomorphicAt n g x₀) :
    ∀ᶠ y in 𝓝 x₀, HasDerivAt (fun θ : ℝ => g (σ.act θ y)) (σ.generator g y) 0 := by
  obtain ⟨ρ, hρ, hpt, -, -, -, -⟩ := σ.exists_generator_chart x₀ hg
  set e := chartAt (ComplexModel n) x₀ with he
  have hx₀ : x₀ ∈ e.source := mem_chart_source (ComplexModel n) x₀
  have hT : ∀ᶠ y in 𝓝 x₀, e y ∈ ball (e x₀) ρ :=
    (e.continuousAt hx₀).preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))
  filter_upwards [hT, e.open_source.mem_nhds hx₀] with y hy hys
  have h := (hpt _ hy).2
  rwa [e.left_inv hys] at h

/-! ### Invariant coherent ideals are stable under the generator -/

/-- The ideal `J` is invariant under the action: `g ∈ J_{σ_θ y}` iff `g ∘ σ_θ ∈ J_y`. -/
def IsInvariantIdeal (σ : CircleAction n X) (J : GermIdeal n X) : Prop :=
  ∀ (θ : ℝ) (y : X) (g : X → ℂ), J.mem (σ.act θ y) g ↔ J.mem y (fun p => g (σ.act θ p))

end CircleAction

namespace CoherentIdeal

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {J : GermIdeal n X}

theorem holomorphicAt_of_mem (hJ : J.IsCoherent) {x : X} {g : X → ℂ} (hg : J.mem x g) :
    HolomorphicAt n g x := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := hJ x
  exact ((hgen x hxU g).1 hg).1

/-- A member of the stalk of a coherent ideal at `x` is a member at all nearby points. -/
theorem eventually_mem (hJ : J.IsCoherent) {x : X} {g : X → ℂ} (hg : J.mem x g) :
    ∀ᶠ y in 𝓝 x, J.mem y g := by
  obtain ⟨U, hU, hxU, N, s, -, hgen⟩ := hJ x
  have hsp := (hgen x hxU g).1 hg
  rw [CoherentIdealColon.isInSpanAt_range_iff] at hsp
  obtain ⟨hgh, c, hc, heq⟩ := hsp
  have hc' : ∀ᶠ y in 𝓝 x, ∀ i, HolomorphicAt n (c i) y :=
    eventually_all.2 fun i => (hc i).eventually_nhds
  filter_upwards [hU.mem_nhds hxU, hgh.eventually_nhds, hc', heq.eventuallyEq_nhds] with
    y hyU hgy hcy heqy
  refine (hgen y hyU g).2 ?_
  rw [CoherentIdealColon.isInSpanAt_range_iff]
  exact ⟨hgy, c, hcy, heqy⟩

/-- Membership only depends on the germ. -/
theorem mem_congr (hJ : J.IsCoherent) {x : X} {f g : X → ℂ} (hf : J.mem x f)
    (h : f =ᶠ[𝓝 x] g) : J.mem x g := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := hJ x
  exact (hgen x hxU g).2 (CoherentIdealColon.isInSpanAt_range_congr (fun _ => EventuallyEq.rfl) h
    ((hgen x hxU f).1 hf))

/-- `c (f - g) ∈ J_x` for `f, g ∈ J_x`. -/
theorem mem_const_mul_sub (hJ : J.IsCoherent) {x : X} {f g : X → ℂ} (c : ℂ) (hf : J.mem x f)
    (hg : J.mem x g) : J.mem x (fun p => c * (f p - g p)) := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := hJ x
  have h1 := RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_const (n := n) c)
    ((hgen x hxU f).1 hf)
  have h2 := RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_const (n := n) (-c))
    ((hgen x hxU g).1 hg)
  have h3 := RelativePrincipalizationSpan.IsInSpanAt.add h1 h2
  refine (hgen x hxU _).2 ?_
  have heq : (fun p => c * f p + -c * g p) = fun p => c * (f p - g p) := by
    funext p; ring
  rw [← heq]
  exact h3

/-- A coherent ideal read in the preferred chart at `x₀`, as a germ module of `𝒪^1` on `ℂⁿ`. -/
def chartModule (J : GermIdeal n X) (x₀ : X) : SGPT.GAGA.Core.GermModule (ComplexModel n) Unit where
  mem w a := J.mem ((chartAt (ComplexModel n) x₀).symm w)
    (fun p => a () (chartAt (ComplexModel n) x₀ p))

theorem inSpanAt_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Type*}
    [Fintype μ] {s : μ → E → ℂ} {y : E} {g g' : E → ℂ} (h : OkaIdealOperations.InSpanAt s y g)
    (hgg : g =ᶠ[𝓝 y] g') : OkaIdealOperations.InSpanAt s y g' := by
  obtain ⟨hg, c, hc, heq⟩ := h
  exact ⟨hg.congr hgg, c, hc, hgg.symm.trans heq⟩

theorem inSpanAt_iff_isCombinationAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {μ : Type} [Fintype μ] {s : μ → E → ℂ} {y : E} (hs : ∀ k, HolAt (s k) y) (a : Unit → E → ℂ) :
    OkaIdealOperations.InSpanAt s y (a ()) ↔ IsCombinationAt (fun k (_ : Unit) => s k) y a := by
  constructor
  · rintro ⟨-, c, hc, heq⟩
    exact ⟨c, hc, fun j => heq⟩
  · rintro ⟨c, hc, heq⟩
    refine ⟨?_, c, hc, heq ()⟩
    exact (HolAt.fintype_sum fun k => (hc k).mul (hs k)).congr (heq ()).symm

/-- The chart module of a coherent ideal is coherent at the centre of the chart. -/
theorem chartModule_coherentAt (hJ : J.IsCoherent) (x₀ : X) :
    (chartModule J x₀).CoherentAt (chartAt (ComplexModel n) x₀ x₀) := by
  obtain ⟨U, hU, hx₀U, N, s, hs, hgen⟩ := hJ x₀
  set e := chartAt (ComplexModel n) x₀ with he
  have hx₀ : x₀ ∈ e.source := mem_chart_source (ComplexModel n) x₀
  set U' := e.target ∩ e.symm ⁻¹' U with hU'
  have hU'o : IsOpen U' := e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
  have hx₀U' : e x₀ ∈ U' := ⟨e.map_source hx₀, by rw [mem_preimage, e.left_inv hx₀]; exact hx₀U⟩
  set s' : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w) with hs'
  have hs'd : ∀ i, DifferentiableOn ℂ (s' i) U' := by
    intro i w hw
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm w :=
      HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) (e.symm w) :=
      (hs i (e.symm w) hw.2).mdifferentiableAt (hU.mem_nhds hw.2)
    have h3 := h2.comp w h1
    rw [mdifferentiableAt_iff_differentiableAt] at h3
    exact h3.differentiableWithinAt
  refine ⟨U', hU'o, hx₀U', Fin N, inferInstance, fun k _ => s' k, fun k _ => hs'd k, ?_⟩
  intro w hw a
  have hws : e.symm w ∈ e.source := e.map_target hw.1
  have hsHol : ∀ k, HolAt (s' k) w := fun k =>
    holAt_of_differentiableOn hU'o (hs'd k) hw
  show J.mem (e.symm w) (fun p => a () (e p)) ↔ _
  rw [hgen (e.symm w) hw.2, ← inSpanAt_iff_isCombinationAt hsHol a]
  have hcongrS : ∀ i, s i =ᶠ[𝓝 (e.symm w)] fun p => s' i (e p) := by
    intro i
    filter_upwards [e.open_source.mem_nhds hws] with p hp
    simp only [hs', e.left_inv hp]
  have hiff : IsInSpanAt (n := n) (· ∈ range s) (e.symm w) (fun p => a () (e p)) ↔
      IsInSpanAt (n := n) (· ∈ range fun i p => s' i (e p)) (e.symm w) (fun p => a () (e p)) :=
    ⟨CoherentIdealColon.isInSpanAt_range_congr hcongrS EventuallyEq.rfl,
      CoherentIdealColon.isInSpanAt_range_congr (fun i => (hcongrS i).symm) EventuallyEq.rfl⟩
  rw [hiff, CoherentIdealColon.isInSpanAt_range_comp_chart_iff hws, e.right_inv hw.1]
  have hloc : (fun z => a () (e (e.symm z))) =ᶠ[𝓝 w] a () := by
    filter_upwards [e.open_target.mem_nhds hw.1] with z hz
    rw [e.right_inv hz]
  exact ⟨fun h => inSpanAt_congr h hloc, fun h => inSpanAt_congr h hloc.symm⟩

end CoherentIdeal

namespace CircleAction

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {J : GermIdeal n X}

theorem tendstoUniformlyOn_shift {α β : Type*} [PseudoMetricSpace β] {F : ℕ → α → β} {f : α → β}
    {s : Set α} (h : TendstoUniformlyOn F f atTop s) (k : ℕ) :
    TendstoUniformlyOn (fun m => F (m + k)) f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  exact (tendsto_add_atTop_nat k).eventually (h ε hε)

/-- **Invariant coherent ideals are stable under the generator** (Cartan's closure theorem). -/
theorem generator_mem (σ : CircleAction n X) (hJ : J.IsCoherent) (hinv : σ.IsInvariantIdeal J)
    {x₀ : X} {g : X → ℂ} (hg : J.mem x₀ g) : J.mem x₀ (σ.generator g) := by
  have hgh : HolomorphicAt n g x₀ := CoherentIdeal.holomorphicAt_of_mem hJ hg
  obtain ⟨ρ, hρ, -, hhol, hlim, hslice, hg0⟩ := σ.exists_generator_chart x₀ hgh
  set e := chartAt (ComplexModel n) x₀ with he
  have hx₀ : x₀ ∈ e.source := mem_chart_source (ComplexModel n) x₀
  -- the difference quotients lie in `J_{x₀}`
  have hθ : Tendsto (fun m : ℕ => σ.act ((m : ℝ) + 1)⁻¹ x₀) atTop (𝓝 x₀) := by
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact (σ.tendsto_act_zero x₀).comp h1
  have hmem : ∀ᶠ m : ℕ in atTop, J.mem x₀ (fun p => ((m : ℂ) + 1) *
      (g (σ.act ((m : ℝ) + 1)⁻¹ p) - g p)) := by
    filter_upwards [hθ.eventually (CoherentIdeal.eventually_mem hJ hg)] with m hm
    exact CoherentIdeal.mem_const_mul_sub hJ _ ((hinv _ x₀ g).1 hm) hg
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (hmem.and hslice)
  set a : ℕ → Unit → ComplexModel n → ℂ := fun m _ w => (((m + M₀ : ℕ) : ℂ) + 1) *
    (g (σ.act (((m + M₀ : ℕ) : ℝ) + 1)⁻¹ (e.symm w)) - g (e.symm w)) with ha
  set b : Unit → ComplexModel n → ℂ := fun _ w => σ.generator g (e.symm w) with hb
  have hMa : ∀ m j, DifferentiableOn ℂ (a m j) (ball (e x₀) ρ) := fun m _ =>
    (((hM₀ (m + M₀) (Nat.le_add_left _ _)).2.sub hg0).const_mul _)
  have hMb : ∀ j, DifferentiableOn ℂ (b j) (ball (e x₀) ρ) := fun _ => hhol
  have hmemM : ∀ m, (CoherentIdeal.chartModule J x₀).mem (e x₀) (a m) := by
    intro m
    show J.mem (e.symm (e x₀)) _
    rw [e.left_inv hx₀]
    refine CoherentIdeal.mem_congr hJ (hM₀ (m + M₀) (Nat.le_add_left _ _)).1 ?_
    filter_upwards [e.open_source.mem_nhds hx₀] with p hp
    simp only [ha, ← he, e.left_inv hp]
  have hlimM : ∀ j, TendstoUniformlyOn (fun m => a m j) (b j) atTop (ball (e x₀) ρ) :=
    fun _ => tendstoUniformlyOn_shift hlim M₀
  have hfin := (CoherentIdeal.chartModule_coherentAt hJ x₀).mem_of_tendstoUniformlyOn hρ hMa hMb
    hmemM hlimM
  change J.mem (e.symm (e x₀)) _ at hfin
  rw [e.left_inv hx₀] at hfin
  refine CoherentIdeal.mem_congr hJ hfin ?_
  filter_upwards [e.open_source.mem_nhds hx₀] with p hp
  simp only [hb, ← he, e.left_inv hp]

/-! ### The derivation of the local ring `𝒪_{X,x}` -/

open SGPT.Okounkov SGPT.PSH.IdealRestriction

theorem nativeHolGerm_mk_add {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) :
    NativeHolGerm.mk f hf + NativeHolGerm.mk g hg =
      NativeHolGerm.mk (fun y => f y + g y) (hf.add hg) := rfl

theorem nativeHolGerm_mk_mul {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) :
    NativeHolGerm.mk f hf * NativeHolGerm.mk g hg =
      NativeHolGerm.mk (fun y => f y * g y) (hf.mul hg) := rfl

/-- The generator acting on the local ring `𝒪_{X,x₀}`. -/
def germGenerator (σ : CircleAction n X) (x₀ : X) (a : NativeHolGerm n X x₀) :
    NativeHolGerm n X x₀ :=
  NativeHolGerm.mk (σ.generator (NativeHolGerm.exists_eq_mk a).choose)
    (σ.holomorphicAt_generator (NativeHolGerm.exists_eq_mk a).choose_spec.choose)

theorem germGenerator_mk (σ : CircleAction n X) {x₀ : X} (f : X → ℂ)
    (hf : HolomorphicAt n f x₀) :
    σ.germGenerator x₀ (NativeHolGerm.mk f hf) =
      NativeHolGerm.mk (σ.generator f) (σ.holomorphicAt_generator hf) := by
  have hspec := (NativeHolGerm.exists_eq_mk (NativeHolGerm.mk f hf)).choose_spec.choose_spec
  unfold germGenerator
  rw [NativeHolGerm.mk_eq_mk_iff]
  exact σ.generator_congr (NativeHolGerm.mk_eq_mk_iff.1 hspec).symm

/-- The generator is a derivation of `𝒪_{X,x₀}`. -/
theorem isLeibniz_germGenerator (σ : CircleAction n X) (x₀ : X) :
    IsLeibniz (σ.germGenerator x₀) where
  map_add a b := by
    obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := NativeHolGerm.exists_eq_mk b
    rw [nativeHolGerm_mk_add, germGenerator_mk, germGenerator_mk, germGenerator_mk,
      nativeHolGerm_mk_add, NativeHolGerm.mk_eq_mk_iff]
    filter_upwards [σ.eventually_hasDerivAt hf, σ.eventually_hasDerivAt hg] with y hfy hgy
    exact (hfy.add hgy).deriv
  map_mul a b := by
    obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := NativeHolGerm.exists_eq_mk b
    rw [nativeHolGerm_mk_mul, germGenerator_mk, germGenerator_mk, germGenerator_mk,
      nativeHolGerm_mk_mul, nativeHolGerm_mk_mul, nativeHolGerm_mk_add,
      NativeHolGerm.mk_eq_mk_iff]
    filter_upwards [σ.eventually_hasDerivAt hf, σ.eventually_hasDerivAt hg] with y hfy hgy
    have h := (hfy.mul hgy).deriv
    simp only [σ.act_zero] at h
    show σ.generator (fun p => f p * g p) y = f y * σ.generator g y + g y * σ.generator f y
    rw [generator, show (fun θ : ℝ => f (σ.act θ y) * g (σ.act θ y)) =
      ((fun θ => f (σ.act θ y)) * fun θ => g (σ.act θ y)) from rfl, h]
    ring

/-- **The stalk of an invariant coherent ideal is stable under the generator.** -/
theorem isStable_stalkIdeal (σ : CircleAction n X) (hJ : J.IsCoherent)
    (hinv : σ.IsInvariantIdeal J) (x₀ : X) :
    IsStable (σ.germGenerator x₀) (stalkIdeal J x₀) := by
  have hD := σ.isLeibniz_germGenerator x₀
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, hmem, rfl⟩ := hx
    rw [germGenerator_mk]
    exact Ideal.subset_span ⟨_, _, σ.generator_mem hJ hinv hmem, rfl⟩
  | zero => rw [hD.map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [hD.map_add]; exact Ideal.add_mem _ hx hy
  | smul r x hxmem hx =>
    rw [smul_eq_mul, hD.map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx) (Ideal.mul_mem_right _ _ hxmem)

end CircleAction

end SGPT.GAGA.Coherent
