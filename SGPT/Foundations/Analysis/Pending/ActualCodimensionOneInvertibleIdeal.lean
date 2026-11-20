import SGPT.Foundations.Analysis.Pending.ActualCodimensionOneLocalEquations
import SGPT.Foundations.Analysis.Pending.ActualReducedHypersurfaceNeighbourhood
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction

set_option autoImplicit false

/-! # The actual ideal of a singular codimension-one subvariety is invertible

All equations and all-stalk local generators are constructed internally.
No regularity-at-every-point or invertibility certificate is assumed.
-/

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace SGPT.Foundations.Analysis.Pending.ActualCodimensionOneInvertibleIdeal
open FirstPass AnalyticDescendingChain OkaRelationSheaf OkaIdealOperations

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

/-- The actual geometric subvariety internally has a single generator for
every nearby chart stalk, on a ball INSIDE the actual chart target. -/
theorem exists_principal_chart_neighbourhood
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n)
    (x : M) :
    ∃ (ε : ℝ) (r : ComplexModel (n + 1) → ℂ), 0 < ε ∧
      DifferentiableOn ℂ r (ball 0 ε) ∧
      (∀ W : Set (ComplexModel (n + 1)), IsOpen W → W ⊆ ball 0 ε → W.Nonempty →
        ∃ y ∈ W, r y ≠ 0) ∧
      (∀ y ∈ ball 0 ε, ∀ a : ComplexModel (n + 1) → ℂ,
        vanishingIdealF (chartGerm V.carrier x) y a ↔
          InSpanAt (fun _ : Fin 1 => r) y a) ∧
      (∀ y ∈ ball 0 ε, (y ∈ chartGerm V.carrier x ↔ r y = 0)) ∧
      ∀ y ∈ ball 0 ε, y + (complexChartAt (n := n + 1) x).val x ∈
        (complexChartAt (n := n + 1) x).val.target := by
  obtain ⟨f, hf, hF, hzero⟩ :=
    ActualCodimensionOneLocalEquations.exists_nonzero_local_equation V hdim x
  obtain ⟨ε, r, hε, hr, hnonzero, hgen, hfr⟩ :=
    ActualReducedHypersurfaceNeighbourhood.exists_principal_vanishing_ideal_neighbourhood
      f hf hF
  let e := (complexChartAt (n := n + 1) x).val
  have ht : ∀ᶠ z in 𝓝 (0 : ComplexModel (n + 1)), z + e x ∈ e.target :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _) |>.eventually
      (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))
  have hev := (CartanIrreducibleReduction.vanishingIdealF_congr_eventually hzero).and
    ((eventuallyEq_set.mp hzero).and ht)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε δ, r, lt_min hε hδ, hr.mono (ball_subset_ball (min_le_left _ _)),
    fun W hW hWsub hWne => hnonzero W hW
      (hWsub.trans (ball_subset_ball (min_le_left _ _))) hWne, ?_, ?_, ?_⟩
  · intro y hy a
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).1 a |>.trans
      (hgen y (ball_subset_ball (min_le_left _ _) hy) a)
  · intro y hy
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).2.1 |>.trans
      (hfr y (ball_subset_ball (min_le_left _ _) hy))
  · intro y hy
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).2.2

private theorem holomorphicAt_comp_centered {x y : M}
    (hy : y ∈ (chartAt (ComplexModel (n + 1)) x).source)
    {r : ComplexModel (n + 1) → ℂ}
    (hr : HolAt r ((chartAt (ComplexModel (n + 1)) x y) -
      (chartAt (ComplexModel (n + 1)) x x))) :
    HolomorphicIdealSheaves.HolomorphicAt (n + 1)
      (fun p => r ((chartAt (ComplexModel (n + 1)) x p) -
        (chartAt (ComplexModel (n + 1)) x x))) y := by
  exact CartanLocalReduction.holomorphicAt_comp_chart hy
    (hr.comp (φ := fun z : ComplexModel (n + 1) =>
        z - (chartAt (ComplexModel (n + 1)) x x))
      (y := chartAt (ComplexModel (n + 1)) x y)
      (continuous_id.sub continuous_const)
      (fun _ => differentiableAt_id.sub (differentiableAt_const _)))

/-- The actual full manifold ideal of a geometric codimension-one
subvariety is invertible, including at its singular points. -/
theorem isInvertible_vanishingIdeal
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n) :
    (HolomorphicIdealSheaves.vanishingIdeal (n := n + 1) V.carrier).IsInvertible := by
  intro x
  obtain ⟨ε, r, hε, hr, hnonzero, hgen, hzero, htarget⟩ :=
    exists_principal_chart_neighbourhood V hdim x
  let e := chartAt (ComplexModel (n + 1)) x
  let q := e x
  let c : M → ComplexModel (n + 1) := fun y => e y - q
  let U : Set M := e.source ∩ e ⁻¹' ((fun w => w - q) ⁻¹' ball 0 ε)
  let h : M → ℂ := fun y => r (c y)
  have hU : IsOpen U :=
    e.isOpen_inter_preimage ((isOpen_ball : IsOpen (ball (0 : ComplexModel (n + 1)) ε)).preimage
      (continuous_id.sub continuous_const))
  have hxU : x ∈ U := by
    refine ⟨mem_chart_source _ x, ?_⟩
    change e x - e x ∈ ball (0 : ComplexModel (n + 1)) ε
    simpa only [sub_self] using
      (mem_ball_self hε : (0 : ComplexModel (n + 1)) ∈ ball 0 ε)
  have hhol : ∀ y ∈ U, HolomorphicIdealSheaves.HolomorphicAt (n + 1) h y :=
    fun y hy => holomorphicAt_comp_centered hy.1 (holAt_of_differentiableOn isOpen_ball hr hy.2)
  have hVzero : ∀ y ∈ U, (y ∈ V.carrier ↔ h y = 0) := by
    intro y hy
    have hcg : (c y ∈ chartGerm V.carrier x ↔ y ∈ V.carrier) := by
      change ((e y - q) + q ∈ e.target ∧ e.symm ((e y - q) + q) ∈ V.carrier) ↔ _
      rw [sub_add_cancel, e.left_inv hy.1]
      exact and_iff_right (e.map_source hy.1)
    exact hcg.symm.trans (hzero (c y) hy.2)
  refine ⟨U, hU, hxU, h, fun y hy => (hhol y hy).mdifferentiableAt.mdifferentiableWithinAt,
    ?_, ?_⟩
  · intro W hW hWU hWne
    let T : Set (ComplexModel (n + 1)) :=
      (fun z => z + q) ⁻¹' (e.target ∩ e.symm ⁻¹' W)
    have hT : IsOpen T :=
      (e.symm.isOpen_inter_preimage hW).preimage (continuous_add_const q)
    have hTsub : T ⊆ ball 0 ε := by
      intro z hz
      have hp := hWU hz.2
      have hec : c (e.symm (z + q)) = z := by
        dsimp only [c]
        rw [e.right_inv hz.1, add_sub_cancel_right]
      have hp2 : c (e.symm (z + q)) ∈ ball 0 ε := hp.2
      rwa [hec] at hp2
    have hTne : T.Nonempty := by
      obtain ⟨y, hy⟩ := hWne
      have hys := (hWU hy).1
      refine ⟨c y, ?_, ?_⟩
      · simpa only [c, sub_add_cancel] using e.map_source hys
      · change e.symm (c y + q) ∈ W
        simpa only [c, sub_add_cancel, e.left_inv hys] using hy
    obtain ⟨z, hz, hrz⟩ := hnonzero T hT hTsub hTne
    refine ⟨e.symm (z + q), hz.2, ?_⟩
    change r (e (e.symm (z + q)) - q) ≠ 0
    simpa only [e.right_inv hz.1, add_sub_cancel_right] using hrz
  · intro y hy g
    constructor
    · intro hg
      let G : ComplexModel (n + 1) → ℂ := fun z => g (e.symm (z + q))
      have hgchart : HolAt (fun w => g (e.symm w)) (c y + q) := by
        simpa only [c, sub_add_cancel] using
          CartanLocalReduction.holAt_comp_chart_symm hy.1 hg.1
      have hGhol : HolAt G (c y) :=
        hgchart.comp (φ := fun z : ComplexModel (n + 1) => z + q) (y := c y)
          (continuous_add_const q)
          (fun _ => differentiableAt_id.add_const q)
      have hadd : Tendsto (fun z : ComplexModel (n + 1) => z + q)
          (𝓝 (c y)) (𝓝 (e y)) := by
        simpa only [c, sub_add_cancel] using (continuous_add_const q).tendsto (c y)
      have hInv : Tendsto (fun z => e.symm (z + q)) (𝓝 (c y)) (𝓝 y) := by
        simpa only [Function.comp_def, e.left_inv hy.1] using
          (e.continuousAt_symm (e.map_source hy.1)).tendsto.comp hadd
      have hG : vanishingIdealF (chartGerm V.carrier x) (c y) G := by
        refine ⟨hGhol, ?_⟩
        filter_upwards [hInv.eventually hg.2] with z hz hzV
        exact hz hzV.2
      obtain ⟨_, a, ha, hGa⟩ := (hgen (c y) hy.2 G).mp hG
      apply HolomorphicIdealSheaves.isInSpanAt_eq_iff.mpr
      refine ⟨hg.1, fun p => a 0 (c p), holomorphicAt_comp_centered hy.1 (ha 0), ?_⟩
      have hC : Tendsto c (𝓝 y) (𝓝 (c y)) :=
        (e.continuousAt hy.1).sub_const q
      filter_upwards [e.open_source.mem_nhds hy.1, hC.eventually hGa] with p hp hpa
      simpa only [G, h, c, sub_add_cancel, e.left_inv hp, Fin.sum_univ_one] using hpa
    · intro hg
      obtain ⟨hghol, a, _, heq⟩ := HolomorphicIdealSheaves.isInSpanAt_eq_iff.mp hg
      refine ⟨hghol, ?_⟩
      filter_upwards [heq, hU.mem_nhds hy] with p hp hpU hpV
      rw [hp, (hVzero p hpU).mp hpV, mul_zero]

end SGPT.Foundations.Analysis.Pending.ActualCodimensionOneInvertibleIdeal
