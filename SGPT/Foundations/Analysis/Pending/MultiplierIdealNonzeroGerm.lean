import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold

set_option autoImplicit false

/-! # Natural nonzero germs of genuine multiplier ideals -/

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealNonzeroGerm

open FirstPass FirstPass.HolomorphicIdealSheaves

noncomputable section

/-- A frequent non-pole locus selects one actual member of a finite weighted family. -/
theorem exists_multiplierIntegrableAt_frequently_ne_zero {n : ℕ}
    [i : MeasurableSpace (ComplexModel n)] [hi : BorelSpace (ComplexModel n)]
    (W : Set (ComplexModel n)) (P : ComplexModel n → EReal) (hW : IsOpen W)
    (hP : PlurisubharmonicOn P W) (z : ComplexModel n) (hz : z ∈ W)
    (c : ℝ) (hc : 0 < c) (hfinite : ∃ᶠ y in 𝓝 z, P y ≠ ⊥) :
    ∃ g : ComplexModel n → ℂ,
      MultiplierIntegrableAt P c g z volume ∧ ∃ᶠ y in 𝓝 z, g y ≠ 0 := by
  classical
  obtain rfl : i = borel _ := hi.measurable_eq
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨O, hO, hzO, hOW, N, g, C, _, hg, hint, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators W
      (fun y => (c : EReal) * P y) hW (hP.const_mul hc) z hz 1 zero_lt_one
  have hsome : ∃ᶠ y in 𝓝 z, ∃ l : Fin N, g l y ≠ 0 := by
    apply (hfinite.and_eventually (hO.mem_nhds hzO)).mono
    intro y hy
    by_contra! hzero
    have hval : EReal.exp ((c : EReal) * P y) ≠ 0 := by
      rw [← EReal.coe_toReal (hP y (hOW hy.2)).ne_top hy.1,
        ← EReal.coe_mul, EReal.exp_coe]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    have hle := hdom y hy.2
    simp only [Nat.cast_one, one_mul] at hle
    simp [hzero] at hle
    exact hval (by rw [hle, EReal.exp_bot])
  obtain ⟨l, hl⟩ := Filter.frequently_exists.mp hsome
  refine ⟨g l, ⟨hc, O, hO, hzO, (hg l).differentiableOn, ?_⟩, hl⟩
  have hden : multiplierDensity (fun y => (c : EReal) * P y) 1 (g l) =
      multiplierDensity P c (g l) := by
    funext y
    simp only [multiplierDensity, multiplierWeight, EReal.coe_one, one_mul]
  simpa only [WeightedL2On, Nat.cast_one, hden] using hint l

/-- Every point of a genuine multiplier ideal has an actual nonzero germ. -/
theorem exists_nonzero_germ_of_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : IsThetaPshPotential θ u)
    {c : ℝ} (hc : 0 < c) (x : M) :
    ∃ g : M → ℂ, (multiplierIdeal (n := n) c u).mem x g ∧
      ∃ᶠ y in 𝓝 x, g y ≠ 0 := by
  classical
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu.1 e (e.val x) (e.val.map_source hxs)
  let P : ComplexModel n → EReal := fun z => chartFunction u e z + (ρ z : EReal)
  have hfinite : ∃ᶠ z in 𝓝 (e.val x), P z ≠ ⊥ := by
    apply Filter.frequently_iff_forall_eventually_exists_and.mpr
    intro q hq
    obtain ⟨T, hTsub, hTopen, hzT⟩ := mem_nhds_iff.mp hq
    have hVopen : IsOpen (e.val.source ∩ e.val ⁻¹' T) :=
      e.val.isOpen_inter_preimage hTopen
    obtain ⟨y, hy, hny⟩ := hu.2 x _ hVopen ⟨hxs, hzT⟩
    refine ⟨e.val y, ?_, hTsub hy.2⟩
    change u (e.val.symm (e.val y)) + (ρ (e.val y) : EReal) ≠ ⊥
    rw [e.val.left_inv hy.1]
    exact EReal.add_ne_bot_iff.mpr ⟨hny, EReal.coe_ne_bot _⟩
  obtain ⟨h, hh, hnz⟩ :=
    exists_multiplierIntegrableAt_frequently_ne_zero W P hρ.1 hpsh
      (e.val x) hzW c hc hfinite
  have hρc : ContinuousOn ρ W := hρ.2.2.1.continuousOn
  have hmore : MoreSingularAt P (chartFunction u e) (e.val x) := by
    have hcont : ContinuousAt ρ (e.val x) :=
      (hρc _ hzW).continuousAt (hρ.1.mem_nhds hzW)
    refine ⟨ρ (e.val x) + 1, ?_⟩
    filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one (ρ (e.val x))))] with z hz
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hz.le)
  have hraw : MultiplierIntegrableAt (chartFunction u e) c h (e.val x) volume :=
    multiplierIntegrableAt_of_moreSingularAt
      (hu.1.quasiPlurisubharmonic e (e.val x) (e.val.map_source hxs)) hmore hh
  have hhol : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ h z := by
    obtain ⟨_, O, hO, hzO, hd, _⟩ := hh
    filter_upwards [hO.mem_nhds hzO] with z hz
    exact hd.differentiableAt (hO.mem_nhds hz)
  let g : M → ℂ := fun y => h (e.val y)
  have hchart : h =ᶠ[𝓝 (e.val x)] fun z => g (e.val.symm z) := by
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hxs)] with z hz
    simp only [g, e.val.right_inv hz]
  have hT : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
    have ht := e.val.continuousAt_symm (e.val.map_source hxs)
    rw [ContinuousAt, e.val.left_inv hxs] at ht
    exact ht
  refine ⟨g, ⟨MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart hxs hhol,
    hraw.congr (EventuallyEq.refl _ _) hchart⟩, ?_⟩
  apply Filter.frequently_iff_forall_eventually_exists_and.mpr
  intro q hq
  have hnear : ∀ᶠ z in 𝓝 (e.val x), z ∈ e.val.target ∧ q (e.val.symm z) :=
    (show ∀ᶠ z in 𝓝 (e.val x), z ∈ e.val.target from
      e.val.open_target.mem_nhds (e.val.map_source hxs)).and (hT.eventually hq)
  obtain ⟨z, hz, hzT, hzq⟩ := (hnz.and_eventually hnear).exists
  refine ⟨e.val.symm z, ?_, hzq⟩
  simpa only [g, e.val.right_inv hzT] using hz

end
end SGPT.Foundations.Analysis.Pending.MultiplierIdealNonzeroGerm
