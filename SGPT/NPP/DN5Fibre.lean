import SGPT.NPP.DN5Defs

/-!
# The glued fibre map `F`: existence of gluing data, normalisation, chart change, regularity

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 192–214: "We now glue the
local jet maps … The resulting map `F = F̂_{ν₀}` is defined on `X` for `|ζ| < r₁` … Since
`F(x, 0) = x` and `D_ζ F(x, 0)` is the identity …"), with the flat chart maps of lane DN3 (§2).

* `exists_fibreAtlas` — gluing data exist on a compact complex manifold.
* `fibreMap_zero` — `F(x, 0) = x`.
* `fibreMap_chart_change` — the coordinate expressions in two charts are related by the
  coordinate change and its derivative (exactly, for every tangent vector).
* `isLocalFibreMap_goodSet` — in every chart `e`, `(z, ξ) ↦ e(F(e⁻¹ z, ξ))` is a local fibre map
  (smooth, holomorphic in `ξ`, `Φ(z, 0) = z`, `D_ξ Φ(z, 0) = id`) on an open set `goodSet A e`
  containing `target e × {0}`, on which `F` takes values in the chart.

The proof of regularity is FPT's induction over the gluing steps: after `k` steps the map is
good near every point where one of the first `k` cutoffs is `1` (where the new step equals the
flat map of its chart), the convex combination of two good maps being good.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Coordinate changes -/

section Transition

theorem mem_transition_source_iff {e κ : ComplexChart N Y} {z : ComplexModel N} :
    z ∈ (chartTransition e κ).source ↔ z ∈ e.val.target ∧ e.val.symm z ∈ κ.val.source := by
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]

theorem transition_apply (e κ : ComplexChart N Y) (z : ComplexModel N) :
    chartTransition e κ z = κ.val (e.val.symm z) := rfl

theorem transition_contDiffAt {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ (chartTransition e κ).source) : ContDiffAt ℝ ∞ (chartTransition e κ) z :=
  HolomorphicMaps.chartTransition_contDiffAt_real e κ hz

theorem transition_differentiableAt_complex {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ (chartTransition e κ).source) : DifferentiableAt ℂ (chartTransition e κ) z :=
  (HolomorphicMaps.chartTransition_contDiffAt e κ hz).differentiableAt (by simp)

theorem transitionDerivative_eq_complex {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ (chartTransition e κ).source) :
    chartTransitionDerivative e κ z =
      (fderiv ℂ (chartTransition e κ) z).restrictScalars ℝ :=
  (transition_differentiableAt_complex hz).fderiv_restrictScalars ℝ

theorem contDiffOn_transition (e κ : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (chartTransition e κ) (chartTransition e κ).source :=
  fun _ hz => (transition_contDiffAt hz).contDiffWithinAt

theorem contDiffOn_transitionDerivative (e κ : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (chartTransitionDerivative e κ) (chartTransition e κ).source :=
  (contDiffOn_transition e κ).fderiv_of_isOpen (chartTransition e κ).open_source (by simp)

/-- The chain rule for coordinate changes at a point of a triple overlap. -/
theorem transitionDerivative_comp {e g f : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hg : e.val.symm z ∈ g.val.source)
    (hf : e.val.symm z ∈ f.val.source) :
    chartTransitionDerivative e f z =
      (chartTransitionDerivative g f (chartTransition e g z)).comp
        (chartTransitionDerivative e g z) := by
  have hzg : z ∈ (chartTransition e g).source := mem_transition_source_iff.mpr ⟨hz, hg⟩
  have hzf : z ∈ (chartTransition e f).source := mem_transition_source_iff.mpr ⟨hz, hf⟩
  have hev : (chartTransition e f : ComplexModel N → ComplexModel N) =ᶠ[𝓝 z]
      (chartTransition g f) ∘ (chartTransition e g) := by
    filter_upwards [((chartTransition e g).open_source.inter
      (chartTransition e f).open_source).mem_nhds ⟨hzg, hzf⟩] with w hw
    have hw1 := mem_transition_source_iff.mp hw.1
    simp only [Function.comp_apply, transition_apply, g.val.left_inv hw1.2]
  have hgz : chartTransition e g z ∈ (chartTransition g f).source := by
    refine mem_transition_source_iff.mpr ⟨g.val.map_source hg, ?_⟩
    rw [transition_apply, g.val.left_inv hg]
    exact hf
  have hd1 : DifferentiableAt ℝ (chartTransition e g) z :=
    (transition_contDiffAt hzg).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (chartTransition g f) (chartTransition e g z) :=
    (transition_contDiffAt hgz).differentiableAt (by simp)
  rw [chartTransitionDerivative, hev.fderiv_eq, fderiv_comp z hd2 hd1]
  rfl

theorem transition_self_eventually {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) : (chartTransition e e : ComplexModel N → ComplexModel N) =ᶠ[𝓝 z] id := by
  filter_upwards [e.val.open_target.mem_nhds hz] with w hw
  simp only [transition_apply, id, e.val.right_inv hw]

theorem transitionDerivative_self {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) :
    chartTransitionDerivative e e z = ContinuousLinearMap.id ℝ (ComplexModel N) := by
  rw [chartTransitionDerivative, (transition_self_eventually hz).fderiv_eq, fderiv_id]

/-- `D(e ∘ κ⁻¹)(κ x) ∘ D(κ ∘ e⁻¹)(e x) = id`. -/
theorem transitionDerivative_inv_comp {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hκ : e.val.symm z ∈ κ.val.source) :
    (chartTransitionDerivative κ e (chartTransition e κ z)).comp
        (chartTransitionDerivative e κ z) = ContinuousLinearMap.id ℝ (ComplexModel N) := by
  rw [← transitionDerivative_comp hz hκ (e.val.map_target hz), transitionDerivative_self hz]

theorem transition_inv_apply {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hκ : e.val.symm z ∈ κ.val.source) :
    chartTransition κ e (chartTransition e κ z) = z := by
  simp only [transition_apply, κ.val.left_inv hκ, e.val.right_inv hz]

theorem transition_mem_inv_source {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hκ : e.val.symm z ∈ κ.val.source) :
    chartTransition e κ z ∈ (chartTransition κ e).source := by
  refine mem_transition_source_iff.mpr ⟨κ.val.map_source hκ, ?_⟩
  rw [transition_apply, κ.val.left_inv hκ]
  exact e.val.map_target hz

/-- The derivative of a coordinate change is complex linear. -/
theorem transitionDerivative_apply_eq_complex {e κ : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ (chartTransition e κ).source) (ξ : ComplexModel N) :
    chartTransitionDerivative e κ z ξ = fderiv ℂ (chartTransition e κ) z ξ := by
  rw [transitionDerivative_eq_complex hz]
  rfl

end Transition

/-! ### Local fibre maps -/

section LocalFibreMap

variable {Φ Φ' : ComplexModel N → ComplexModel N → ComplexModel N}
  {O O' : Set (ComplexModel N × ComplexModel N)}

theorem slice_eventually_mem {O : Set (ComplexModel N × ComplexModel N)} (hO : IsOpen O)
    {q : ComplexModel N × ComplexModel N} (hq : q ∈ O) : ∀ᶠ ξ in 𝓝 q.2, (q.1, ξ) ∈ O := by
  have hc : Continuous fun ξ : ComplexModel N => (q.1, ξ) := continuous_const.prodMk continuous_id
  exact hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hq)

/-- Restriction of a local fibre map to an open subset, up to equality there. -/
theorem IsLocalFibreMap.mono_congr (h : IsLocalFibreMap Φ O) (hO' : IsOpen O') (hsub : O' ⊆ O)
    (heq : ∀ q ∈ O', Φ' q.1 q.2 = Φ q.1 q.2) : IsLocalFibreMap Φ' O' where
  isOpen := hO'
  contDiffOn := (h.contDiffOn.mono hsub).congr heq
  holo q hq := by
    have hev : Φ q.1 =ᶠ[𝓝 q.2] Φ' q.1 := by
      filter_upwards [slice_eventually_mem hO' hq] with ξ hξ
      exact (heq (q.1, ξ) hξ).symm
    exact (h.holo q (hsub hq)).congr_of_eventuallyEq hev.symm
  map_zero z hz := by
    rw [heq (z, 0) hz]
    exact h.map_zero z (hsub hz)
  fderiv_zero z hz := by
    have hev : Φ' z =ᶠ[𝓝 0] Φ z := by
      filter_upwards [slice_eventually_mem hO' hz] with ξ hξ
      exact heq (z, ξ) hξ
    rw [hev.fderiv_eq]
    exact h.fderiv_zero z (hsub hz)

/-- Being a local fibre map is a local property. -/
theorem IsLocalFibreMap.of_local (hO : IsOpen O)
    (h : ∀ q ∈ O, ∃ O' : Set (ComplexModel N × ComplexModel N), q ∈ O' ∧ IsLocalFibreMap Φ O') :
    IsLocalFibreMap Φ O where
  isOpen := hO
  contDiffOn q hq := by
    obtain ⟨O', hq', hΦ⟩ := h q hq
    exact (hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hq')).contDiffWithinAt
  holo q hq := by
    obtain ⟨O', hq', hΦ⟩ := h q hq
    exact hΦ.holo q hq'
  map_zero z hz := by
    obtain ⟨O', hq', hΦ⟩ := h (z, 0) hz
    exact hΦ.map_zero z hq'
  fderiv_zero z hz := by
    obtain ⟨O', hq', hΦ⟩ := h (z, 0) hz
    exact hΦ.fderiv_zero z hq'

end LocalFibreMap

/-! ### Good fibre families -/

/-- `G` is good at `z₀` in the chart `e`: on an open neighbourhood `O` of `(z₀, 0)` the
coordinate expression `(z, ξ) ↦ e(G e z ξ)` is a local fibre map, with values in the chart. -/
def IsGoodAt (G : FibreFamily N Y) (e : ComplexChart N Y) (z₀ : ComplexModel N) : Prop :=
  ∃ O : Set (ComplexModel N × ComplexModel N), (z₀, 0) ∈ O ∧
    IsLocalFibreMap (fun z ξ => e.val (G e z ξ)) O ∧
    ∀ q ∈ O, q.1 ∈ e.val.target ∧ G e q.1 q.2 ∈ e.val.source

section Step

variable {κ e : ComplexChart N Y} {ϑ : Y → ℝ} {G : FibreFamily N Y} {z₀ : ComplexModel N}

theorem isOpen_target_inter_preimage_symm (e : ComplexChart N Y) {V : Set Y} (hV : IsOpen V) :
    IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := by
  simpa using e.val.symm.isOpen_inter_preimage hV

/-- **Step, case 1**: where the cutoff is `1`, the new map is the flat map of the chart `κ`. -/
theorem isGoodAt_fibreStep_of_eventually_one (hsupp : tsupport ϑ ⊆ κ.val.source)
    (hz₀ : z₀ ∈ e.val.target) (hone : ∀ᶠ y in 𝓝 (e.val.symm z₀), ϑ y = 1) :
    IsGoodAt (fibreStep κ ϑ G) e z₀ := by
  set V : Set Y := interior {y | ϑ y = 1} with hVdef
  have hx₀V : e.val.symm z₀ ∈ V := mem_interior_iff_mem_nhds.mpr hone
  have hVone : ∀ y ∈ V, ϑ y = 1 := fun y hy => by
    have h := interior_subset (s := {y | ϑ y = 1}) hy
    exact h
  have hVsupp : V ⊆ tsupport ϑ := fun y hy => subset_tsupport _ (by
    change ϑ y ≠ 0
    rw [hVone y hy]; norm_num)
  set τ := chartTransition e κ
  set σ := chartTransition κ e
  set D := chartTransitionDerivative e κ
  set S1 : Set (ComplexModel N) := e.val.target ∩ e.val.symm ⁻¹' V
  have hS1 : IsOpen S1 := isOpen_target_inter_preimage_symm e isOpen_interior
  have hS1τ : S1 ⊆ τ.source := fun z hz =>
    mem_transition_source_iff.mpr ⟨hz.1, hsupp (hVsupp hz.2)⟩
  let a : ComplexModel N × ComplexModel N → ComplexModel N := fun q => τ q.1 + D q.1 q.2
  have ha : ∀ q ∈ S1 ×ˢ (univ : Set (ComplexModel N)), ContDiffAt ℝ ∞ a q := by
    intro q hq
    have h1 : q.1 ∈ τ.source := hS1τ hq.1
    have hτ : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => τ q.1) q :=
      (transition_contDiffAt h1).comp q contDiffAt_fst
    have hD : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => D q.1) q :=
      ((contDiffOn_transitionDerivative e κ).contDiffAt (τ.open_source.mem_nhds h1)).comp q
        contDiffAt_fst
    exact hτ.add (hD.clm_apply contDiffAt_snd)
  have haC : ContinuousOn a (S1 ×ˢ univ) := fun q hq => (ha q hq).continuousAt.continuousWithinAt
  set O := (S1 ×ˢ (univ : Set (ComplexModel N))) ∩ a ⁻¹' σ.source with hOdef
  have hO : IsOpen O := haC.isOpen_inter_preimage (hS1.prod isOpen_univ) σ.open_source
  have hx₀ : e.val.symm z₀ ∈ κ.val.source := hsupp (hVsupp hx₀V)
  have hmem : (z₀, (0 : ComplexModel N)) ∈ O := by
    refine ⟨⟨⟨hz₀, hx₀V⟩, mem_univ _⟩, ?_⟩
    change τ z₀ + D z₀ 0 ∈ σ.source
    rw [map_zero, add_zero]
    exact transition_mem_inv_source hz₀ hx₀
  -- the step is the flat map on `O`
  have hstep : ∀ q ∈ O, fibreStep κ ϑ G e q.1 q.2 = κ.val.symm (a q) := by
    intro q hq
    have hV : e.val.symm q.1 ∈ V := hq.1.1.2
    have h1 : ϑ (e.val.symm q.1) = 1 := hVone _ hV
    simp only [fibreStep, if_pos (hVsupp hV), h1, sub_self, zero_smul, add_zero]
    rfl
  have hrep : ∀ q ∈ O, e.val (fibreStep κ ϑ G e q.1 q.2) = σ (a q) := by
    intro q hq
    rw [hstep q hq]
    rfl
  refine ⟨O, hmem, ?_, ?_⟩
  · have hσa : IsLocalFibreMap (fun z ξ => σ (a (z, ξ))) O := by
      refine ⟨hO, ?_, ?_, ?_, ?_⟩
      · intro q hq
        exact ((transition_contDiffAt hq.2).comp q (ha q hq.1)).contDiffWithinAt
      · intro q hq
        have h1 : q.1 ∈ τ.source := hS1τ hq.1.1
        have hlin : DifferentiableAt ℂ (fun ξ => τ q.1 + D q.1 ξ) q.2 := by
          have : (fun ξ => τ q.1 + D q.1 ξ) = fun ξ => τ q.1 + fderiv ℂ τ q.1 ξ := by
            funext ξ
            rw [transitionDerivative_apply_eq_complex h1]
          rw [this]
          exact (differentiableAt_const _).add (fderiv ℂ τ q.1).differentiableAt
        exact (transition_differentiableAt_complex hq.2).comp q.2 hlin
      · intro z hz
        have hz1 := hz.1.1
        change σ (τ z + D z 0) = z
        rw [map_zero, add_zero]
        exact transition_inv_apply hz1.1 (hsupp (hVsupp hz1.2))
      · intro z hz
        have hz1 := hz.1.1
        have hx : e.val.symm z ∈ κ.val.source := hsupp (hVsupp hz1.2)
        have hτz : z ∈ τ.source := hS1τ hz1
        have hlin : HasFDerivAt (fun ξ : ComplexModel N => τ z + D z ξ) (D z) 0 :=
          ((D z).hasFDerivAt).const_add _
        have hσ : HasFDerivAt σ (chartTransitionDerivative κ e (τ z)) (τ z + D z 0) := by
          rw [map_zero, add_zero]
          exact ((transition_contDiffAt (transition_mem_inv_source hz1.1 hx)).differentiableAt
            (by simp)).hasFDerivAt
        have H := hσ.comp (0 : ComplexModel N) hlin
        exact H.fderiv.trans (transitionDerivative_inv_comp hz1.1 hx)
    exact hσa.mono_congr hO subset_rfl (fun q hq => hrep q hq)
  · intro q hq
    refine ⟨hq.1.1.1, ?_⟩
    rw [hstep q hq]
    have h2 := hq.2
    exact (mem_transition_source_iff.mp h2).2

/-- **Step, case 2**: off the support of the cutoff the step does not change the map. -/
theorem isGoodAt_fibreStep_of_not_mem (hz₀ : z₀ ∈ e.val.target)
    (hx₀ : e.val.symm z₀ ∉ tsupport ϑ) (hG : IsGoodAt G e z₀) :
    IsGoodAt (fibreStep κ ϑ G) e z₀ := by
  obtain ⟨O, hmem, hΦ, hO⟩ := hG
  set S : Set (ComplexModel N) := e.val.target ∩ e.val.symm ⁻¹' (tsupport ϑ)ᶜ
  have hS : IsOpen S := isOpen_target_inter_preimage_symm e (isClosed_tsupport ϑ).isOpen_compl
  set O' := O ∩ (S ×ˢ (univ : Set (ComplexModel N)))
  have hO' : IsOpen O' := hΦ.isOpen.inter (hS.prod isOpen_univ)
  have heq : ∀ q ∈ O', fibreStep κ ϑ G e q.1 q.2 = G e q.1 q.2 := by
    intro q hq
    simp only [fibreStep, if_neg hq.2.1.2]
  refine ⟨O', ⟨hmem, ⟨hz₀, hx₀⟩, mem_univ _⟩,
    hΦ.mono_congr hO' inter_subset_left (fun q hq => by simp only [heq q hq]), ?_⟩
  intro q hq
  rw [heq q hq]
  exact hO q hq.1

/-- **Step, case 3**: on the support of the cutoff the convex combination (in the chart `κ`) of
a good map and the flat map of `κ` is good. -/
theorem isGoodAt_fibreStep_of_mem (hsupp : tsupport ϑ ⊆ κ.val.source)
    (hϑ : ChartSmooth (n := N) ϑ) (hz₀ : z₀ ∈ e.val.target)
    (hx₀ : e.val.symm z₀ ∈ tsupport ϑ) (hG : IsGoodAt G e z₀) :
    IsGoodAt (fibreStep κ ϑ G) e z₀ := by
  obtain ⟨OG, hmemG, hΦ, hOG⟩ := hG
  set τ := chartTransition e κ
  set σ := chartTransition κ e
  set D := chartTransitionDerivative e κ
  set Φ : ComplexModel N × ComplexModel N → ComplexModel N := fun q => e.val (G e q.1 q.2)
  set c : ComplexModel N → ℝ := fun z => 1 - ϑ (e.val.symm z)
  have hc : ContDiffOn ℝ ∞ c e.val.target := contDiffOn_const.sub (hϑ e)
  have hΦc : ∀ q ∈ OG, ContDiffAt ℝ ∞ Φ q := fun q hq =>
    hΦ.contDiffOn.contDiffAt (hΦ.isOpen.mem_nhds hq)
  set O1 := (OG ∩ (τ.source ×ˢ (univ : Set (ComplexModel N)))) ∩ Φ ⁻¹' τ.source
  have hO1 : IsOpen O1 :=
    ContinuousOn.isOpen_inter_preimage
      (fun q hq => (hΦc q hq.1).continuousAt.continuousWithinAt)
      (hΦ.isOpen.inter (τ.open_source.prod isOpen_univ)) τ.open_source
  let a : ComplexModel N × ComplexModel N → ComplexModel N := fun q =>
    τ q.1 + D q.1 q.2 + c q.1 • (τ (Φ q) - τ q.1 - D q.1 q.2)
  have ha : ∀ q ∈ O1, ContDiffAt ℝ ∞ a q := by
    intro q hq
    have h1 : q.1 ∈ τ.source := hq.1.2.1
    have hτ : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => τ q.1) q :=
      (transition_contDiffAt h1).comp q contDiffAt_fst
    have hD : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => D q.1 q.2) q :=
      (((contDiffOn_transitionDerivative e κ).contDiffAt (τ.open_source.mem_nhds h1)).comp q
        contDiffAt_fst).clm_apply contDiffAt_snd
    have hcq : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ComplexModel N => c q.1) q :=
      (hc.contDiffAt (e.val.open_target.mem_nhds (hOG q hq.1.1).1)).comp q contDiffAt_fst
    have hτΦ : ContDiffAt ℝ ∞ (fun q => τ (Φ q)) q :=
      (transition_contDiffAt hq.2).comp q (hΦc q hq.1.1)
    exact (hτ.add hD).add (hcq.smul ((hτΦ.sub hτ).sub hD))
  set O := O1 ∩ a ⁻¹' σ.source
  have hO : IsOpen O := ContinuousOn.isOpen_inter_preimage
    (fun q hq => (ha q hq).continuousAt.continuousWithinAt) hO1 σ.open_source
  have hx₀κ : e.val.symm z₀ ∈ κ.val.source := hsupp hx₀
  have hz₀τ : z₀ ∈ τ.source := mem_transition_source_iff.mpr ⟨hz₀, hx₀κ⟩
  have hΦ0 : ∀ z, (z, (0 : ComplexModel N)) ∈ OG → Φ (z, 0) = z := fun z hz => hΦ.map_zero z hz
  have ha0 : ∀ z, (z, (0 : ComplexModel N)) ∈ OG → a (z, 0) = τ z := by
    intro z hz
    change τ z + D z 0 + c z • (τ (Φ (z, 0)) - τ z - D z 0) = τ z
    rw [hΦ0 z hz, map_zero]
    simp
  have hmem : (z₀, (0 : ComplexModel N)) ∈ O := by
    refine ⟨⟨⟨hmemG, hz₀τ, mem_univ _⟩, ?_⟩, ?_⟩
    · change Φ (z₀, 0) ∈ τ.source
      rw [hΦ0 z₀ hmemG]
      exact hz₀τ
    · change a (z₀, 0) ∈ σ.source
      rw [ha0 z₀ hmemG]
      exact transition_mem_inv_source hz₀ hx₀κ
  -- the step is `κ⁻¹ ∘ a` on `O`
  have hstep : ∀ q ∈ O, fibreStep κ ϑ G e q.1 q.2 = κ.val.symm (a q) := by
    intro q hq
    have hqG := hOG q hq.1.1.1
    have hΦτ : Φ q ∈ τ.source := hq.1.2
    have hGκ : G e q.1 q.2 ∈ κ.val.source := by
      have := (mem_transition_source_iff.mp hΦτ).2
      simpa only [Φ, e.val.left_inv hqG.2] using this
    have hτΦ : τ (Φ q) = κ.val (G e q.1 q.2) := by
      change κ.val (e.val.symm (e.val (G e q.1 q.2))) = κ.val (G e q.1 q.2)
      rw [e.val.left_inv hqG.2]
    by_cases hs : e.val.symm q.1 ∈ tsupport ϑ
    · simp only [fibreStep, if_pos hs]
      congr 1
      change _ = τ q.1 + D q.1 q.2 + c q.1 • (τ (Φ q) - τ q.1 - D q.1 q.2)
      rw [hτΦ]
      rfl
    · simp only [fibreStep, if_neg hs]
      have hϑ0 : ϑ (e.val.symm q.1) = 0 := image_eq_zero_of_notMem_tsupport hs
      have hc1 : c q.1 = 1 := by simp only [c, hϑ0, sub_zero]
      have : a q = κ.val (G e q.1 q.2) := by
        change τ q.1 + D q.1 q.2 + c q.1 • (τ (Φ q) - τ q.1 - D q.1 q.2) = _
        rw [hc1, one_smul, hτΦ]
        abel
      rw [this, κ.val.left_inv hGκ]
  have hrep : ∀ q ∈ O, e.val (fibreStep κ ϑ G e q.1 q.2) = σ (a q) := by
    intro q hq
    rw [hstep q hq]
    rfl
  refine ⟨O, hmem, ?_, ?_⟩
  · have hσa : IsLocalFibreMap (fun z ξ => σ (a (z, ξ))) O := by
      refine ⟨hO, ?_, ?_, ?_, ?_⟩
      · intro q hq
        exact ((transition_contDiffAt hq.2).comp q (ha q hq.1)).contDiffWithinAt
      · intro q hq
        have h1 : q.1 ∈ τ.source := hq.1.1.2.1
        have hlin : ∀ ξ, D q.1 ξ = fderiv ℂ τ q.1 ξ :=
          fun ξ => transitionDerivative_apply_eq_complex h1 ξ
        have hΦh : DifferentiableAt ℂ (fun ξ => Φ (q.1, ξ)) q.2 := hΦ.holo q hq.1.1.1
        have hτΦ : DifferentiableAt ℂ (fun ξ => τ (Φ (q.1, ξ))) q.2 :=
          (transition_differentiableAt_complex hq.1.2).comp q.2 hΦh
        have hfun : (fun ξ => a (q.1, ξ)) = fun ξ => τ q.1 + fderiv ℂ τ q.1 ξ +
            ((c q.1 : ℝ) : ℂ) • (τ (Φ (q.1, ξ)) - τ q.1 - fderiv ℂ τ q.1 ξ) := by
          funext ξ
          change τ q.1 + D q.1 ξ + c q.1 • (τ (Φ (q.1, ξ)) - τ q.1 - D q.1 ξ) = _
          rw [hlin ξ, Complex.coe_smul]
        have ha' : DifferentiableAt ℂ (fun ξ => a (q.1, ξ)) q.2 := by
          rw [hfun]
          have hin : DifferentiableAt ℂ
              (fun ξ => τ (Φ (q.1, ξ)) - τ q.1 - fderiv ℂ τ q.1 ξ) q.2 := by
            apply DifferentiableAt.sub
            · exact hτΦ.sub_const _
            · exact (fderiv ℂ τ q.1).differentiableAt
          have hin' : DifferentiableAt ℂ
              (fun ξ => ((c q.1 : ℝ) : ℂ) • (τ (Φ (q.1, ξ)) - τ q.1 - fderiv ℂ τ q.1 ξ)) q.2 :=
            hin.const_smul ((c q.1 : ℝ) : ℂ)
          have hfirst : DifferentiableAt ℂ (fun ξ => τ q.1 + fderiv ℂ τ q.1 ξ) q.2 :=
            (fderiv ℂ τ q.1).differentiableAt.const_add _
          exact hfirst.add hin'
        exact (transition_differentiableAt_complex hq.2).comp q.2 ha'
      · intro z hz
        change σ (a (z, 0)) = z
        rw [ha0 z hz.1.1.1]
        have hzτ : z ∈ τ.source := hz.1.1.2.1
        exact transition_inv_apply (mem_transition_source_iff.mp hzτ).1
          (mem_transition_source_iff.mp hzτ).2
      · intro z hz
        have hzG : (z, (0 : ComplexModel N)) ∈ OG := hz.1.1.1
        have hzτ : z ∈ τ.source := hz.1.1.2.1
        have hzt := mem_transition_source_iff.mp hzτ
        -- derivative of the slice of `Φ`
        have hΦd : HasFDerivAt (fun ξ => Φ (z, ξ)) (ContinuousLinearMap.id ℝ _) 0 := by
          have hdiff : DifferentiableAt ℝ (fun ξ => Φ (z, ξ)) 0 := by
            have h := (hΦc (z, 0) hzG).differentiableAt (by simp)
            exact h.comp (0 : ComplexModel N)
              ((differentiableAt_const z).prodMk differentiableAt_id)
          have := hdiff.hasFDerivAt
          rwa [show fderiv ℝ (fun ξ => Φ (z, ξ)) 0 = ContinuousLinearMap.id ℝ _ from
            hΦ.fderiv_zero z hzG] at this
        have hτd : HasFDerivAt τ (D z) (Φ (z, 0)) := by
          rw [hΦ0 z hzG]
          exact ((transition_contDiffAt hzτ).differentiableAt (by simp)).hasFDerivAt
        have hτΦd : HasFDerivAt (fun ξ => τ (Φ (z, ξ))) (D z) 0 := by
          have := hτd.comp (0 : ComplexModel N) hΦd
          rw [ContinuousLinearMap.comp_id] at this
          exact this
        have had : HasFDerivAt (fun ξ => a (z, ξ)) (D z) 0 := by
          have h1 : HasFDerivAt (fun ξ : ComplexModel N => τ z + D z ξ) (D z) 0 :=
            (D z).hasFDerivAt.const_add _
          have h2 : HasFDerivAt (fun ξ => τ (Φ (z, ξ)) - τ z - D z ξ) (D z - D z) 0 :=
            (hτΦd.sub_const _).sub (D z).hasFDerivAt
          have h3 := h1.add (h2.const_smul (c z))
          have hD : D z + c z • (D z - D z) = D z := by simp
          rw [hD] at h3
          exact h3
        have hσd : HasFDerivAt σ (chartTransitionDerivative κ e (τ z)) (a (z, 0)) := by
          rw [ha0 z hzG]
          exact ((transition_contDiffAt (transition_mem_inv_source hzt.1 hzt.2)).differentiableAt
            (by simp)).hasFDerivAt
        have H := hσd.comp (0 : ComplexModel N) had
        exact H.fderiv.trans (transitionDerivative_inv_comp hzt.1 hzt.2)
    exact hσa.mono_congr hO subset_rfl (fun q hq => hrep q hq)
  · intro q hq
    refine ⟨(hOG q hq.1.1.1).1, ?_⟩
    rw [hstep q hq]
    exact (mem_transition_source_iff.mp hq.2).2

end Step

/-! ### The glued map -/

section Glued

variable (A : FibreAtlas N Y)

theorem fibreFamilyUpTo_succ (k : ℕ) (h : k < A.card) :
    fibreFamilyUpTo A (k + 1) = fibreStep (A.chart ⟨k, h⟩) (A.cutoff ⟨k, h⟩) (fibreFamilyUpTo A k) := by
  simp only [fibreFamilyUpTo, dif_pos h]

theorem fibreFamilyUpTo_succ_of_le (k : ℕ) (h : ¬ k < A.card) :
    fibreFamilyUpTo A (k + 1) = fibreFamilyUpTo A k := by
  simp only [fibreFamilyUpTo, dif_neg h]

/-- `F̂_k(x, 0) = x`. -/
theorem fibreFamilyUpTo_zero (k : ℕ) (e : ComplexChart N Y) (z : ComplexModel N) :
    fibreFamilyUpTo A k e z 0 = e.val.symm z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < A.card
    · rw [fibreFamilyUpTo_succ A k hk]
      unfold fibreStep
      split_ifs with hs
      · rw [ih, map_zero, add_zero, sub_self, sub_zero, smul_zero, add_zero,
          (A.chart ⟨k, hk⟩).val.left_inv (A.tsupport_subset _ hs)]
      · exact ih
    · rw [fibreFamilyUpTo_succ_of_le A k hk]
      exact ih

/-- **`F(x, 0) = x`.** -/
theorem fibreMap_zero (e : ComplexChart N Y) (z : ComplexModel N) :
    fibreMap A e z 0 = e.val.symm z :=
  fibreFamilyUpTo_zero A A.card e z

/-- The coordinate expressions of `F̂_k` in two charts are related by the coordinate change. -/
theorem fibreFamilyUpTo_chart_change (k : ℕ) {e e' : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hz' : e.val.symm z ∈ e'.val.source) (ξ : ComplexModel N) :
    fibreFamilyUpTo A k e z ξ =
      fibreFamilyUpTo A k e' (chartTransition e e' z) (chartTransitionDerivative e e' z ξ) := by
  have hx : e'.val.symm (chartTransition e e' z) = e.val.symm z := by
    rw [transition_apply, e'.val.left_inv hz']
  induction k with
  | zero =>
    change e.val.symm z = e'.val.symm (chartTransition e e' z)
    rw [hx]
  | succ k ih =>
    by_cases hk : k < A.card
    · rw [fibreFamilyUpTo_succ A k hk]
      unfold fibreStep
      rw [hx]
      split_ifs with hs
      · have hκ := A.tsupport_subset ⟨k, hk⟩ hs
        rw [ih, transitionDerivative_comp hz hz' hκ]
        rfl
      · exact ih
    · rw [fibreFamilyUpTo_succ_of_le A k hk]
      exact ih

/-- **Chart change for `F`**: `F(e; z, ξ) = F(e'; τ(z), Dτ(z) ξ)` for `τ = e' ∘ e⁻¹`. -/
theorem fibreMap_chart_change {e e' : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (hz' : e.val.symm z ∈ e'.val.source) (ξ : ComplexModel N) :
    fibreMap A e z ξ =
      fibreMap A e' (chartTransition e e' z) (chartTransitionDerivative e e' z ξ) :=
  fibreFamilyUpTo_chart_change A A.card hz hz' ξ

/-- After `k` steps the map is good near every point where one of the first `k` cutoffs is `1`. -/
theorem isGoodAt_fibreFamilyUpTo (k : ℕ) {e : ComplexChart N Y} {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ e.val.target)
    (hk : ∃ i : Fin A.card, (i : ℕ) < k ∧ ∀ᶠ y in 𝓝 (e.val.symm z₀), A.cutoff i y = 1) :
    IsGoodAt (fibreFamilyUpTo A k) e z₀ := by
  induction k with
  | zero =>
    obtain ⟨i, hi, _⟩ := hk
    exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    obtain ⟨i, hi, hione⟩ := hk
    by_cases hkc : k < A.card
    · rw [fibreFamilyUpTo_succ A k hkc]
      by_cases hone : ∀ᶠ y in 𝓝 (e.val.symm z₀), A.cutoff ⟨k, hkc⟩ y = 1
      · exact isGoodAt_fibreStep_of_eventually_one (A.tsupport_subset _) hz₀ hone
      · have hik : (i : ℕ) < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · exfalso
            apply hone
            have hieq : i = ⟨k, hkc⟩ := Fin.ext h
            rw [← hieq]
            exact hione
        have hG := ih ⟨i, hik, hione⟩
        by_cases hx₀ : e.val.symm z₀ ∈ tsupport (A.cutoff ⟨k, hkc⟩)
        · exact isGoodAt_fibreStep_of_mem (A.tsupport_subset _) (A.cutoff_smooth _) hz₀ hx₀ hG
        · exact isGoodAt_fibreStep_of_not_mem hz₀ hx₀ hG
    · rw [fibreFamilyUpTo_succ_of_le A k hkc]
      exact ih ⟨i, lt_of_lt_of_le i.isLt (not_lt.mp hkc), hione⟩

/-- **`F` is good at every point of every chart.** -/
theorem isGoodAt_fibreMap {e : ComplexChart N Y} {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ e.val.target) : IsGoodAt (fibreMap A) e z₀ := by
  obtain ⟨i, hi⟩ := A.cover (e.val.symm z₀)
  exact isGoodAt_fibreFamilyUpTo A A.card hz₀ ⟨i, i.isLt, hi⟩

/-- The set of `(z, ξ)` near which `F` is good in the chart `e`. -/
def goodSet (e : ComplexChart N Y) : Set (ComplexModel N × ComplexModel N) :=
  {q | ∃ O : Set (ComplexModel N × ComplexModel N), q ∈ O ∧
    IsLocalFibreMap (fun z ξ => e.val (fibreMap A e z ξ)) O ∧
    ∀ q' ∈ O, q'.1 ∈ e.val.target ∧ fibreMap A e q'.1 q'.2 ∈ e.val.source}

theorem isOpen_goodSet (e : ComplexChart N Y) : IsOpen (goodSet A e) := by
  rw [isOpen_iff_forall_mem_open]
  rintro q ⟨O, hq, hΦ, hO⟩
  exact ⟨O, fun q' hq' => ⟨O, hq', hΦ, hO⟩, hΦ.isOpen, hq⟩

/-- **Regularity of `F` in a chart**: `(z, ξ) ↦ e(F(e⁻¹ z, ξ))` is a local fibre map on the open
set `goodSet A e`. -/
theorem isLocalFibreMap_goodSet (e : ComplexChart N Y) :
    IsLocalFibreMap (fun z ξ => e.val (fibreMap A e z ξ)) (goodSet A e) :=
  IsLocalFibreMap.of_local (isOpen_goodSet A e) fun _ ⟨O, hq, hΦ, _⟩ => ⟨O, hq, hΦ⟩

theorem mem_goodSet_of_mem_target {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) : (z, (0 : ComplexModel N)) ∈ goodSet A e := by
  obtain ⟨O, hmem, hΦ, hO⟩ := isGoodAt_fibreMap A hz
  exact ⟨O, hmem, hΦ, hO⟩

theorem goodSet_target {e : ComplexChart N Y} {q : ComplexModel N × ComplexModel N}
    (hq : q ∈ goodSet A e) : q.1 ∈ e.val.target ∧ fibreMap A e q.1 q.2 ∈ e.val.source := by
  obtain ⟨O, hmem, _, hO⟩ := hq
  exact hO q hmem

end Glued

/-! ### Existence of gluing data -/

/-- **Gluing data exist on every compact complex manifold** (finitely many chart-smooth bumps,
equal to `1` near a point and supported in a chart, by compactness). -/
theorem exists_fibreAtlas [CompactSpace Y] : Nonempty (FibreAtlas N Y) := by
  classical
  have hbump (x : Y) := Pending.ChartPartition.exists_chartSmooth_bump (n := N) x
    ⟨(complexChartAt (n := N) x).val.source, (complexChartAt (n := N) x).val.open_source⟩
    (mem_complexChartAt_source x)
  choose h hsm hnonneg hle hsupp hcpt hone using hbump
  set U : Y → Set Y := fun x => interior {y | h x y = 1}
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hone x)⟩)
  let pt : Fin s.card → Y := fun i => (s.equivFin.symm i).val
  refine ⟨{ card := s.card
            chart := fun i => complexChartAt (n := N) (pt i)
            cutoff := fun i => h (pt i)
            cutoff_smooth := fun i => hsm (pt i)
            cutoff_nonneg := fun i => hnonneg (pt i)
            cutoff_le_one := fun i => hle (pt i)
            tsupport_subset := fun i => hsupp (pt i)
            isCompact_tsupport := fun i => hcpt (pt i)
            cover := ?_ }⟩
  intro y
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
  obtain ⟨hxs, hy⟩ := mem_iUnion.mp hx
  refine ⟨s.equivFin ⟨x, hxs⟩, ?_⟩
  have hpt : pt (s.equivFin ⟨x, hxs⟩) = x := by simp [pt]
  rw [hpt]
  exact mem_interior_iff_mem_nhds.mp hy

end SGPT.NPP.DN5
