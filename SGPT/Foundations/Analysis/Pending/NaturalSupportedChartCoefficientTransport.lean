import SGPT.Foundations.Analysis.Pending.NaturalSupportedSmoothCompleteness
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Continuous supported coefficient transport in actual charts

The actual inverse chart constructs the output support. Boundary zero extension
and every derivative seminorm estimate are proved internally. A natural smooth
field of continuous linear coefficient maps supplies no continuity certificate
for the output operator. All real normed coefficient spaces are allowed.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalSupportedChartCoefficientTransport

open FirstPass FirstPass.HolomorphicMaps

private theorem uniform_jet_bound {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : IsOpen S) (L : Compacts E) (hL : (L : Set E) ⊆ S)
    {g : E → G} (hg : ContDiffOn ℝ ∞ g S) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ m, ∀ x ∈ L, ‖iteratedFDeriv ℝ i g x‖ ≤ B := by
  have hc : ContinuousOn (fun x => (Finset.range (m + 1)).sup'
      Finset.nonempty_range_add_one (fun i => ‖iteratedFDerivWithin ℝ i g S x‖)) S :=
    ContinuousOn.finset_sup'_apply Finset.nonempty_range_add_one fun i _ =>
      (hg.continuousOn_iteratedFDerivWithin
        (by exact WithTop.coe_le_coe.mpr le_top) hS.uniqueDiffOn).norm
  obtain ⟨B, hB⟩ := L.isCompact.exists_bound_of_continuousOn (hc.mono hL)
  refine ⟨|B|, abs_nonneg B, fun i hi x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen i hS (hL hx)]
  exact (Finset.le_sup' _ (Finset.mem_range_succ_iff.mpr hi)).trans
    ((Real.le_norm_self _).trans ((hB x hx).trans (Real.le_norm_self B)))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual inverse-chart image of the prescribed compact support. -/
def reverseCompact (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target) :
    Compacts (ComplexModel n) :=
  ⟨(chartTransition e f).symm '' K,
    K.isCompact.image_of_continuousOn ((chartTransition e f).symm.continuousOn.mono hK)⟩

omit [IsComplexManifold n M] in
private theorem reverseCompact_subset (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target) :
    (reverseCompact e f K hK : Set (ComplexModel n)) ⊆ (chartTransition e f).source := by
  rintro _ ⟨x, hx, rfl⟩
  exact (chartTransition e f).map_target (hK hx)

private def weightedPullFun (e f : ComplexChart n M)
    (P : ComplexModel n → V →L[ℝ] W) (A : ComplexModel n → V) : ComplexModel n → W :=
  (chartTransition e f).source.indicator (fun z => P z (A (chartTransition e f z)))

omit [IsComplexManifold n M] in
private theorem weightedPullFun_zero (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target)
    (P : ComplexModel n → V →L[ℝ] W) (A : 𝓓_{K}(ComplexModel n, V))
    {x : ComplexModel n} (hx : x ∉ reverseCompact e f K hK) :
    weightedPullFun e f P A x = 0 := by
  by_cases hs : x ∈ (chartTransition e f).source
  · have hFx : chartTransition e f x ∉ (K : Set (ComplexModel n)) := by
      intro hz
      exact hx ⟨chartTransition e f x, hz, (chartTransition e f).left_inv hs⟩
    simp only [weightedPullFun, indicator_of_mem hs, A.zero_on_compl hFx, Pi.zero_apply, map_zero]
  · simp only [weightedPullFun, indicator_of_notMem hs]

private theorem contDiff_weightedPullFun (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target)
    (P : ComplexModel n → V →L[ℝ] W)
    (hP : ContDiffOn ℝ ∞ P (chartTransition e f).source)
    (A : 𝓓_{K}(ComplexModel n, V)) : ContDiff ℝ ∞ (weightedPullFun e f P A) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (chartTransition e f).source
  · have hev : weightedPullFun e f P A =ᶠ[𝓝 x]
        fun z => P z (A (chartTransition e f z)) := by
      filter_upwards [(chartTransition e f).open_source.mem_nhds hx] with z hz
      exact indicator_of_mem hz _
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (hP.contDiffAt ((chartTransition e f).open_source.mem_nhds hx)).clm_apply
      (A.contDiff.contDiffAt.comp x (chartTransition_contDiffAt_real e f hx))
  · have hxL : x ∉ reverseCompact e f K hK :=
      fun h => hx (reverseCompact_subset e f K hK h)
    have hev : weightedPullFun e f P A =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(reverseCompact e f K hK).isCompact.isClosed.isOpen_compl.mem_nhds hxL]
        with z hz
      exact weightedPullFun_zero e f K hK P A hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The actual whole supported transport is continuous in all derivative seminorms. -/
def weightedPullCLM (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target)
    (P : ComplexModel n → V →L[ℝ] W)
    (hP : ContDiffOn ℝ ∞ P (chartTransition e f).source) :
    𝓓_{K}(ComplexModel n, V) →L[ℝ] 𝓓_{reverseCompact e f K hK}(ComplexModel n, W) := by
  let F := chartTransition e f
  let S := F.source
  let L := reverseCompact e f K hK
  have hLs : (L : Set (ComplexModel n)) ⊆ S := reverseCompact_subset e f K hK
  have hF : ContDiffOn ℝ ∞ F S := fun x hx =>
    (chartTransition_contDiffAt_real e f hx).contDiffWithinAt
  refine ContDiffMapSupportedIn.mkCLM ℝ (fun A => weightedPullFun e f P A)
    (fun A A' x => ?_) (fun c A x => ?_)
    (contDiff_weightedPullFun e f K hK P hP)
    (fun A x hx => weightedPullFun_zero e f K hK P A hx) (fun m _ => ?_)
  · by_cases hx : x ∈ F.source <;> simp [weightedPullFun, F, hx, map_add]
  · by_cases hx : x ∈ F.source <;> simp [weightedPullFun, F, hx, map_smul]
  · obtain ⟨B, hB, hb⟩ := uniform_jet_bound F.open_source L hLs hP m
    obtain ⟨D₀, _, hd⟩ := uniform_jet_bound F.open_source L hLs hF m
    let D := max D₀ 1
    have hD1 : 1 ≤ D := le_max_right _ _
    let C : ℝ := ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * B * ((m - i).factorial * D ^ (m - i))
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
    refine ⟨Finset.Iic m, C, hC, fun A x hx => ?_⟩
    let N := ((Finset.Iic m).sup fun j =>
      ContDiffMapSupportedIn.seminorm ℝ (ComplexModel n) V ⊤ K j) A
    have hcomp : ContDiffOn ℝ ∞ (fun z => A (F z)) S :=
      A.contDiff.comp_contDiffOn hF
    have hp (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i A (F x)‖ ≤ N :=
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hi))
    have hdf (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i F S x‖ ≤ D ^ i := by
      rw [iteratedFDerivWithin_of_isOpen i F.open_source (hLs hx)]
      exact (hd i him x hx).trans ((le_max_left D₀ 1).trans (le_self_pow₀ hD1 (by omega)))
    have hcg (i : ℕ) (hi : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i (fun z => A (F z)) S x‖ ≤ i.factorial * N * D ^ i := by
      apply norm_iteratedFDerivWithin_comp_le A.contDiff.contDiffOn hF
        (by exact WithTop.coe_le_coe.mpr le_top) uniqueDiffOn_univ F.open_source.uniqueDiffOn
        (mapsTo_univ _ _) (hLs hx)
      · intro j hj
        rw [iteratedFDerivWithin_univ]
        exact hp j (hj.trans hi)
      · intro j hj hji
        exact hdf j hj (hji.trans hi)
    have heq : EqOn (weightedPullFun e f P A) (fun z => P z (A (F z))) S :=
      fun z hz => indicator_of_mem hz _
    rw [← iteratedFDerivWithin_of_isOpen m F.open_source (hLs hx),
      iteratedFDerivWithin_congr heq (hLs hx) m]
    calc
      ‖iteratedFDerivWithin ℝ m (fun z => P z (A (F z))) S x‖ ≤
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i P S x‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (fun z => A (F z)) S x‖ :=
        norm_iteratedFDerivWithin_clm_apply hP hcomp F.open_source.uniqueDiffOn (hLs hx)
          (by exact WithTop.coe_le_coe.mpr le_top)
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B *
          ((m - i).factorial * N * D ^ (m - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · rw [iteratedFDerivWithin_of_isOpen i F.open_source (hLs hx)]
          exact hb i (Finset.mem_range_succ_iff.mp hi) x hx
        · exact hcg (m - i) (Nat.sub_le m i)
      _ = C * N := by
        dsimp [C]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros
        ring

/-- Exact readback of the constructed whole supported coefficient function. -/
theorem weightedPullCLM_apply (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target)
    (P : ComplexModel n → V →L[ℝ] W)
    (hP : ContDiffOn ℝ ∞ P (chartTransition e f).source)
    (A : 𝓓_{K}(ComplexModel n, V)) (z : ComplexModel n) :
    weightedPullCLM e f K hK P hP A z =
      (chartTransition e f).source.indicator (fun y => P y (A (chartTransition e f y))) z := rfl

end SGPT.Foundations.Analysis.Pending.NaturalSupportedChartCoefficientTransport
