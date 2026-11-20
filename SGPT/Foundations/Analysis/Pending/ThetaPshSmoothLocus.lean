import SGPT.Foundations.Analysis.Pending.ThetaPshContinuityLocus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The smooth locus of a theta-PSH potential

The collar construction of CT22, Lemma 4.3, Step 3 glues a LOCAL branch
`ψ + sρ` into a global one.  For the glued potential to carry analytic
singularities in the bounded-remainder convention
(`Pending.RegularizedMaxOffPoleCollarGluing`), the local branch must be a
*smooth* real germ at every chart point of the gluing set — a continuous germ is
not enough, since the convention asks the remainder to be `C^∞` off the poles
and the local branch has no poles at all.

So the gluing set is the **smooth locus**: the points near which `ψ` equals a
smooth real function read in every holomorphic chart.  Three facts are needed
and proved here.

* The condition is chart-independent, because chart transitions are `C^∞`.  This
  is what makes the locus open and what lets the clause-(ii) hypothesis — stated
  in the ONE chart at `P.center` — enter.
* On the locus `ψ` is finite, immediately, since it equals a real function there.
* The clause-(ii) hypothesis of CT22, Lemma 4.3 puts the parameter's image in the
  locus.  This is the one place where local finiteness has to be *earned*: the
  hypothesis is smoothness of `toReal ψ`, which is blind to poles, and the
  argument of `Pending.ThetaPshContinuityLocus` (upper semicontinuity against
  local nondegeneracy) is what converts it into `ψ = coe` of that smooth
  function on a neighbourhood.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ThetaPshSmoothLocus

open FirstPass FirstPass.HolomorphicMaps FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.ThetaPshContinuityLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `u` agrees, near `x`, with a smooth real function read in EVERY holomorphic
chart around `x`. -/
def SmoothGermAt (u : M → EReal) (x : M) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target → e.val.symm z = x →
    ∃ g : ComplexModel n → ℝ, (∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ g w) ∧
      chartFunction u e =ᶠ[𝓝 z] fun w => (g w : EReal)

/-- The set of points at which `u` is a smooth real germ. -/
def smoothLocus (u : M → EReal) : Set M := {x | SmoothGermAt (n := n) u x}

/-- **Chart independence.**  A smooth real germ in ONE chart is a smooth real
germ in every chart, at every nearby point.  The transported witness is
`g ∘ (chart transition)`, which is `C^∞` because the transition is. -/
theorem eventually_smoothGermAt_of_chart {u : M → EReal} (e : ComplexChart n M)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) {g : ComplexModel n → ℝ}
    (hg : ∀ᶠ w in 𝓝 z₀, ContDiffAt ℝ ∞ g w)
    (heq : chartFunction u e =ᶠ[𝓝 z₀] fun w => (g w : EReal)) :
    ∀ᶠ y in 𝓝 (e.val.symm z₀), SmoothGermAt (n := n) u y := by
  -- one honest open neighbourhood carrying both clauses, inside the chart target
  obtain ⟨V₀, hV₀sub, hV₀, hz₀V₀⟩ := mem_nhds_iff.mp (hg.and heq)
  set V : Set (ComplexModel n) := V₀ ∩ e.val.target with hVdef
  have hV : IsOpen V := hV₀.inter e.val.open_target
  have hz₀V : z₀ ∈ V := ⟨hz₀V₀, hz₀⟩
  set O : Set M := e.val.source ∩ e.val ⁻¹' V with hOdef
  have hO : IsOpen O := e.val.continuousOn.isOpen_inter_preimage e.val.open_source hV
  have hxO : e.val.symm z₀ ∈ O := by
    refine ⟨e.val.map_target hz₀, ?_⟩
    show e.val (e.val.symm z₀) ∈ V
    rw [e.val.right_inv hz₀]; exact hz₀V
  filter_upwards [hO.mem_nhds hxO] with y hy
  intro f z hz hfz
  -- the neighbourhood of `z` on which the transition lands in `V`
  set Z : Set (ComplexModel n) := f.val.target ∩ f.val.symm ⁻¹' O with hZdef
  have hZ : IsOpen Z := f.val.continuousOn_symm.isOpen_inter_preimage f.val.open_target hO
  have hzZ : z ∈ Z := ⟨hz, by show f.val.symm z ∈ O; rw [hfz]; exact hy⟩
  have htrans : ∀ w ∈ Z, w ∈ (chartTransition f e).source := by
    intro w hw
    exact ⟨hw.1, hw.2.1⟩
  have hmapsV : ∀ w ∈ Z, chartTransition f e w ∈ V := fun w hw => hw.2.2
  refine ⟨fun w => g (chartTransition f e w), ?_, ?_⟩
  · filter_upwards [hZ.mem_nhds hzZ] with w hw
    have h1 : ContDiffAt ℝ ∞ g (chartTransition f e w) :=
      (hV₀sub (hmapsV w hw).1).1
    exact h1.comp w (chartTransition_contDiffAt_real f e (htrans w hw))
  · filter_upwards [hZ.mem_nhds hzZ] with w hw
    have hsrc : f.val.symm w ∈ e.val.source := hw.2.1
    have hval : chartFunction u e (chartTransition f e w) = ((g (chartTransition f e w) : ℝ) : EReal) :=
      (hV₀sub (hmapsV w hw).1).2
    show u (f.val.symm w) = ((g (chartTransition f e w) : ℝ) : EReal)
    have hchart : chartFunction u e (chartTransition f e w) = u (f.val.symm w) := by
      show u (e.val.symm (chartTransition f e w)) = u (f.val.symm w)
      congr 1
      show e.val.symm (e.val (f.val.symm w)) = f.val.symm w
      exact e.val.left_inv hsrc
    rw [← hchart, hval]

theorem isOpen_smoothLocus (u : M → EReal) : IsOpen (smoothLocus (n := n) u) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hsymm : e.val.symm (e.val x) = x := e.val.left_inv hxs
  obtain ⟨g, hg, heq⟩ := hx e (e.val x) hz hsymm
  have := eventually_smoothGermAt_of_chart (u := u) e hz hg heq
  rwa [hsymm] at this

/-- **`u` is finite on its smooth locus**, immediately: it equals a real function
there. -/
theorem ne_bot_of_mem_smoothLocus {u : M → EReal} {x : M}
    (hx : x ∈ smoothLocus (n := n) u) : u x ≠ ⊥ := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hsymm : e.val.symm (e.val x) = x := e.val.left_inv hxs
  obtain ⟨g, -, heq⟩ := hx e (e.val x) hz hsymm
  have h := heq.eq_of_nhds
  rw [show chartFunction u e (e.val x) = u x by
    show u (e.val.symm (e.val x)) = u x; rw [hsymm]] at h
  rw [h]
  exact EReal.coe_ne_bot _

/-- A smooth real germ is in particular a continuous one. -/
theorem mem_continuityLocus_of_mem_smoothLocus {u : M → EReal} {x : M}
    (hx : x ∈ smoothLocus (n := n) u) : x ∈ continuityLocus u := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hsymm : e.val.symm (e.val x) = x := e.val.left_inv hxs
  obtain ⟨g, hg, heq⟩ := hx e (e.val x) hz hsymm
  have hev : (fun w' => (u (e.val.symm w')).toReal) =ᶠ[𝓝 (e.val x)] g := by
    filter_upwards [heq] with w hw
    show (chartFunction u e w).toReal = g w
    rw [hw]
    exact EReal.toReal_coe _
  have hcd : ∀ᶠ w in 𝓝 (e.val x),
      ContDiffAt ℝ ∞ (fun w' => (u (e.val.symm w')).toReal) w := by
    filter_upwards [hg, hev.eventuallyEq_nhds] with w hw hwev
    exact hw.congr_of_eventuallyEq hwev
  have h := mem_continuityLocus_of_eventually_contDiffAt (u := u) e hz hcd
  rwa [hsymm] at h

/-- Continuity of `toReal u` at a point of the smooth locus. -/
theorem continuousAt_toReal_of_mem_smoothLocus {u : M → EReal} {x : M}
    (hx : x ∈ smoothLocus (n := n) u) : ContinuousAt (fun y => (u y).toReal) x :=
  continuousAt_toReal_of_mem_continuityLocus (mem_continuityLocus_of_mem_smoothLocus hx)

/-- **The hypothesis of CT22, Lemma 4.3, clause (ii) puts the point in the smooth
locus.**  Smoothness of `toReal u` in one chart is turned into
`u = coe` of that smooth function by local finiteness, which
`Pending.ThetaPshContinuityLocus` supplies from upper semicontinuity and local
nondegeneracy. -/
theorem mem_smoothLocus_of_eventually_contDiffAt {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (e : ComplexChart n M)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target)
    (hsm : ∀ᶠ w in 𝓝 z₀, ContDiffAt ℝ ∞ (fun w' => (u (e.val.symm w')).toReal) w) :
    e.val.symm z₀ ∈ smoothLocus (n := n) u := by
  -- local finiteness, on a whole neighbourhood
  have hloc : e.val.symm z₀ ∈ continuityLocus u :=
    mem_continuityLocus_of_eventually_contDiffAt e hz₀
      (hsm.mono fun _ hw => hw)
  have hnbhd : ∀ᶠ y in 𝓝 (e.val.symm z₀), u y ≠ ⊥ := by
    filter_upwards [(isOpen_continuityLocus u).mem_nhds hloc] with y hy
    exact ne_bot_of_mem_continuityLocus hu hy
  have hcont : ContinuousAt e.val.symm z₀ := e.val.continuousAt_symm hz₀
  have hfin : ∀ᶠ w in 𝓝 z₀, chartFunction u e w = ((u (e.val.symm w)).toReal : EReal) := by
    filter_upwards [hcont.eventually hnbhd] with w hw
    exact (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top _) hw).symm
  have h := eventually_smoothGermAt_of_chart (u := u) e hz₀ hsm hfin
  exact h.self_of_nhds

end

end SGPT.Foundations.Analysis.Pending.ThetaPshSmoothLocus
