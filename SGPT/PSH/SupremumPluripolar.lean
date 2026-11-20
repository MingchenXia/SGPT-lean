import SGPT.PSH.LocalCompactExtension
import SGPT.PSH.Choquet
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationLocality

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.SupremumPluripolar

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff Classical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending FlatComplexTorus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure

private theorem iSup_add_real {I : Type*} (f : I → EReal) (c : ℝ) :
    (⨆ i, f i + (c : EReal)) = (⨆ i, f i) + (c : EReal) := by
  apply le_antisymm
  · exact iSup_le fun i => add_le_add (le_iSup f i) le_rfl
  · have h : (⨆ i, f i) ≤ (⨆ i, f i + (c : EReal)) - (c : EReal) := by
      refine iSup_le fun i => ?_
      rw [← (EReal.addLECancellable_coe c).add_le_add_iff_right,
        EReal.sub_add_cancel]
      exact le_iSup (fun i => f i + (c : EReal)) i
    have h' := add_le_add h (le_rfl : (c : EReal) ≤ (c : EReal))
    rwa [EReal.sub_add_cancel] at h'

/-- Actual original compact theta-PSH families have a genuine local pole
witness for the exceptional set, using the existing sequence producer. -/
theorem manifoldLocallyPluripolar_sup_exceptional {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
    {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (u : I → M → EReal) (C : ℝ)
    (hu : ∀ i, IsThetaPshPotential theta.val (u i))
    (hC : ∀ i x, u i x ≤ (C : EReal)) :
    ManifoldLocallyPluripolar (n := n) {x | (⨆ i, u i x) < uscSup u x} := by
  obtain ⟨s, hs, heq⟩ := exists_seq_uscRegularization_iSup_eq (Set.range_nonempty u)
  have hsPSH : ∀ j, IsThetaPshPotential theta.val (s j) := by
    intro j
    obtain ⟨i, hi⟩ := hs j
    exact hi ▸ hu i
  have hsC : ∀ j x, s j x ≤ (C : EReal) := by
    intro j x
    obtain ⟨i, hi⟩ := hs j
    simpa only [← hi] using hC i x
  have hsle : ∀ x, (⨆ j, s j) x ≤ ⨆ i, u i x := by
    intro x
    rw [iSup_apply]
    refine iSup_le fun j => ?_
    obtain ⟨i, hi⟩ := hs j
    simpa only [← hi] using le_iSup (fun i => u i x) i
  have hreg : uscRegularization (⨆ j, s j) = uscSup u := by
    rw [heq]
    exact congrArg uscRegularization (sSup_range_eq u)
  have hnegl : ManifoldLocallyPluripolar (n := n)
      {x | ¬ uscRegularization (⨆ j, s j) x ≤ (⨆ j, s j) x} :=
    NegligibleSetsPluripolarProof.negligibleSetsPluripolar omega theta s C hsPSH hsC
  apply ManifoldLocallyPluripolar.mono hnegl
  intro x hx
  change ¬ uscRegularization (⨆ j, s j) x ≤ (⨆ j, s j) x
  rw [hreg]
  exact not_le.mpr ((hsle x).trans_lt hx)

/-- A genuine local family with one common upper bound has a pluripolar
strict-supremum exceptional set on the inner chart ball. Compactness is
used only for the internally supplied auxiliary flat torus. -/
theorem locallyPluripolarOn_sup_exceptional_inner_ball
    {n : ℕ} {I : Type*} [Nonempty I]
    (e : ComplexChart n (Torus n)) (p : ComplexModel n)
    {r C : ℝ} (hr : 0 < r) (hchart : closedBall p (3 * r) ⊆ e.val.target)
    (u : I → ComplexModel n → EReal)
    (hu : ∀ i, PlurisubharmonicOn (u i) (ball p (3 * r)))
    (hC : ∀ i z, z ∈ ball p (3 * r) → u i z ≤ (C : EReal)) :
    LocallyPluripolarOn {z | (⨆ i, u i z) < uscSup u z} (ball p r) := by
  let S : ℕ → Set (ComplexModel n) := fun k =>
    {z | z ∈ ball p r ∧ (⨆ i, u i z) < uscSup u z ∧ ((-(k : ℝ) : ℝ) : EReal) < uscSup u z}
  have hS : ∀ k, LocallyPluripolarOn (S k) (ball p r) := by
    intro k
    let L : ℝ := -(k : ℝ)
    let B : ℝ := max C L
    let a : ℝ := (B - L + 2) / (3 * r ^ 2)
    let b : ℝ := L - 1 - a * r ^ 2
    let q : ComplexModel n → ℝ := fun z => a * ‖z - p‖ ^ 2 + b
    have ha : 0 < a / Real.pi := by
      dsimp only [a, B]
      exact div_pos (div_pos (by linarith [le_max_right C L]) (by positivity)) Real.pi_pos
    let omega := KahlerBackground.smul ha (flatKahlerBackground n)
    have hproduced : ∀ i, ∃ w : Torus n → EReal,
        IsThetaPshPotential omega.form.val w ∧
        (∀ x, 0 ≤ w x ∧ w x ≤ ((max (B - b) 0 : ℝ) : EReal)) ∧
        ∀ z ∈ ball p r, w (e.val.symm z) + (q z : EReal) = max (u i z) (L : EReal) := by
      intro i
      obtain ⟨ha', w, hw, hwb, heq⟩ :=
        LocalCompactExtension.exists_compact_flat_extension e p hr hchart (hu i) (hC i)
      exact ⟨w, hw, hwb, heq⟩
    choose w hw hwb heq using hproduced
    have hE := manifoldLocallyPluripolar_sup_exceptional omega omega.form w (max (B - b) 0)
      hw (fun i x => (hwb i x).2)
    let f : ComplexModel n → EReal := fun z => ⨆ i, max (u i z) (L : EReal)
    let g : ComplexModel n → EReal := fun z => (⨆ i, w i (e.val.symm z)) + (q z : EReal)
    have hfg : EqOn f g (ball p r) := by
      intro z hz
      dsimp only [f, g]
      rw [← iSup_add_real]
      exact iSup_congr fun i => (heq i z hz).symm
    have hsupmax (z : ComplexModel n) : f z = max (⨆ i, u i z) (L : EReal) := by
      refine le_antisymm (iSup_le fun i => max_le_max (le_iSup (fun i => u i z) i) le_rfl) ?_
      exact max_le (iSup_mono fun i => le_max_left _ _)
        (le_iSup_of_le (Classical.arbitrary I) (le_max_right _ _))
    have hq : Continuous q := by
      exact (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).add continuous_const
    intro z hz
    have hzt : z ∈ e.val.target := hchart (mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by linarith)))
    apply (hE e z hzt).mono
    intro y hy
    have hyt : y ∈ e.val.target :=
      hchart (mem_closedBall.mpr ((mem_ball.mp hy.1).le.trans (by linarith)))
    refine ⟨hyt, ?_⟩
    have hlocal : uscRegularization f y = uscRegularization g y :=
      uscRegularization_congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy.1) hfg)
    have hreg : uscRegularization f y = uscSup w (e.val.symm y) + (q y : EReal) := by
      rw [hlocal, uscRegularization_add_coe_continuousAt_apply _ hq.continuousAt]
      have hc := uscRegularization_comp_openPartialHomeomorph_apply
        (fun x => ⨆ i, w i x) e.val.symm hyt
      exact congrArg (fun t => t + (q y : EReal)) hc
    have hmono : uscSup u y ≤ uscRegularization f y :=
      uscRegularization_mono (fun t => iSup_mono fun i => le_max_left _ _) y
    have hgap : f y < uscRegularization f y := by
      rw [hsupmax]
      exact (max_lt hy.2.1 hy.2.2).trans_le hmono
    rw [hfg hy.1, hreg] at hgap
    change (⨆ i, w i (e.val.symm y)) < uscSup w (e.val.symm y)
    exact lt_of_not_ge (fun h => hgap.not_ge (add_le_add h le_rfl))
  have hunion := locallyPluripolarOn_iUnion isOpen_ball hS
  intro z hz
  apply locallyPluripolarAt_of_inter_subset (hunion z hz) (isOpen_ball.mem_nhds hz)
  intro y hy
  obtain ⟨A, _, hA⟩ := EReal.lt_iff_exists_real_btwn.mp hy.1
  obtain ⟨k, hk⟩ := exists_nat_gt (-A)
  refine mem_iUnion.mpr ⟨k, hy.2, hy.1, ?_⟩
  exact (show ((-(k : ℝ) : ℝ) : EReal) < (A : EReal) by
    exact_mod_cast (by linarith : -(k : ℝ) < A)).trans hA

/-- The original arbitrary open model domain needs only a locally uniform
upper bound. The compact manifold used in the proof is purely auxiliary. -/
theorem locallyPluripolarOn_sup_exceptional
    {n : ℕ} {I : Type*} [Nonempty I] {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (u : I → ComplexModel n → EReal)
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hb : LocallyUniformlyBoundedAbove u Ω) :
    LocallyPluripolarOn {z | (⨆ i, u i z) < uscSup u z} Ω := by
  intro x hx
  obtain ⟨V, hV, C, hC⟩ := hb x hx
  rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx)] at hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hΩ.mem_nhds hx) hV)
  let M := Torus n
  let e := complexChartAt (n := n) (0 : M)
  let p := e.val (0 : M)
  have hpt : p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source (0 : M))
  obtain ⟨η, hη, heball⟩ := Metric.isOpen_iff.mp e.val.open_target p hpt
  let r : ℝ := min δ η / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have h3δ : 3 * r < δ := by dsimp only [r]; linarith [min_le_left δ η]
  have h3η : 3 * r < η := by dsimp only [r]; linarith [min_le_right δ η]
  let c := p - x
  let τ := (Homeomorph.addRight c).toOpenPartialHomeomorph
  have hτs : τ.source = univ := rfl
  have hτx : τ x = p := by change x + (p - x) = p; abel
  have hτ : DifferentiableOn ℂ τ τ.source := by
    change DifferentiableOn ℂ (fun y : ComplexModel n => y + c) univ
    exact differentiableOn_id.add_const c
  have htrans (y : ComplexModel n) : τ.symm y - x = y - p := by
    change (y + -(p - x)) - x = y - p
    abel
  have hnear {y : ComplexModel n} (hy : y ∈ ball p (3 * r)) :
      τ.symm y ∈ Ω ∩ V := by
    apply hball
    rw [mem_ball, dist_eq_norm, htrans]
    exact (show ‖y - p‖ < 3 * r by simpa only [mem_ball, dist_eq_norm] using hy).trans h3δ
  have hchart : closedBall p (3 * r) ⊆ e.val.target := by
    intro y hy
    exact heball (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt h3η))
  let v : I → ComplexModel n → EReal := fun i => u i ∘ τ.symm
  have hv : ∀ i, PlurisubharmonicOn (v i) (ball p (3 * r)) := by
    intro i y hy
    have hpsh := (hu i).comp_affine (ContinuousLinearMap.id ℂ (ComplexModel n)) (-c)
    have hpre : -c + y ∈ Ω := by
      have h := (hnear hy).1
      change y + -c ∈ Ω at h
      simpa only [add_comm] using h
    change PlurisubharmonicAt (fun t => u i (t + -c)) y
    simpa only [ContinuousLinearMap.id_apply, add_comm] using hpsh y hpre
  have hvC : ∀ i y, y ∈ ball p (3 * r) → v i y ≤ (C : EReal) := by
    intro i y hy
    exact hC i _ ⟨(hnear hy).2, (hnear hy).1⟩
  have hlocal := locallyPluripolarOn_sup_exceptional_inner_ball e p hr hchart v hv hvC
    p (mem_ball_self hr)
  have hpull := locallyPluripolarAt_preimage hτ
    (by rw [hτs]; exact mem_univ x) (hτx.symm ▸ hlocal)
  apply hpull.mono
  intro y hy
  refine ⟨by rw [hτs]; exact mem_univ y, ?_⟩
  have hreg : uscSup v (τ y) = uscSup u y := by
    change uscRegularization ((fun z => ⨆ i, u i z) ∘ (Homeomorph.addRight c).symm)
      (τ y) = uscSup u y
    rw [uscRegularization_comp_homeomorph_apply]
    change uscSup u (τ.symm (τ y)) = uscSup u y
    rw [τ.left_inv (by rw [hτs]; exact mem_univ y)]
  change (⨆ i, v i (τ y)) < uscSup v (τ y)
  rw [hreg]
  change (⨆ i, u i (τ.symm (τ y))) < uscSup u y
  rw [τ.left_inv (by rw [hτs]; exact mem_univ y)]
  exact hy

end SGPT.PSH.SupremumPluripolar

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- SGPT prop:supsupstardiff: actual original arbitrary nonempty PSH
families have a genuine pluripolar strict-supremum exceptional set. -/
theorem locallyPluripolar_sup_exceptional {I : Type*} [Nonempty I]
    {v : I → X → EReal} (hv : ∀ i, A.IsPSH (v i))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range v) Set.univ) :
    A.LocallyPluripolar {x | (⨆ i, v i x) < uscSup v x} := by
  apply A.locallyPluripolar_of_in_chart
  intro i
  have h := SupremumPluripolar.locallyPluripolarOn_sup_exceptional (A.chart i).open_target
    (fun j => A.coordinate (v j) i) (fun j => (hv j).chartPlurisubharmonic i)
    (A.locallyBounded_coordinateFamily hb i)
  apply h.mono_set
  intro z hz
  change (⨆ j, A.coordinate (v j) i z) < uscSup (fun j => A.coordinate (v j) i) z
  rw [A.uscSup_coordinateFamily v i hz.1]
  exact hz.2

/-- The entire source's Lebesgue-null conclusion is genuine Haar outer
measure zero in every original chart, without set measurability. -/
theorem measure_sup_exceptional_in_chart_eq_zero {I : Type*} [Nonempty I]
    {v : I → X → EReal} (hv : ∀ j, A.IsPSH (v j))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range v) Set.univ) (i : A.Index)
    (μ : Measure (ComplexModel (A.dimension i))) [μ.IsAddHaarMeasure] :
    μ (A.pluripolarChartSet {x | (⨆ j, v j x) < uscSup v x} i) = 0 :=
  (locallyPluripolar_sup_exceptional hv hb).chart_measure_eq_zero i μ

/-- The entire source's almost-everywhere conclusion retains every original
chart's actual Haar measure, without an exceptional-set measurability premise. -/
theorem ae_notMem_sup_exceptional_in_chart {I : Type*} [Nonempty I]
    {v : I → X → EReal} (hv : ∀ j, A.IsPSH (v j))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range v) Set.univ) (i : A.Index)
    (μ : Measure (ComplexModel (A.dimension i))) [μ.IsAddHaarMeasure] :
    ∀ᵐ z ∂μ.restrict (A.chart i).target,
      (A.chart i).symm z ∉ {x | (⨆ j, v j x) < uscSup v x} :=
  (locallyPluripolar_sup_exceptional hv hb).ae_notMem_in_chart i μ

end SGPT.PSH.VariableComplexAtlas
