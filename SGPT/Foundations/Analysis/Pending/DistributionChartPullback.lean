import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.Pending.DDCOverlap
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.DistributionChartPullback
open FirstPass FirstPass.HolomorphicMaps ThetaPshChartLimitGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem uniform_jet_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set (ComplexModel n)} (hS : IsOpen S) (L : Compacts (ComplexModel n))
    (hL : (L : Set (ComplexModel n)) ⊆ S) {g : ComplexModel n → G}
    (hg : ContDiffOn ℝ ∞ g S) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ m, ∀ x ∈ L, ‖iteratedFDeriv ℝ i g x‖ ≤ B := by
  have hc : ContinuousOn (fun x => (Finset.range (m+1)).sup'
      Finset.nonempty_range_add_one (fun i => ‖iteratedFDerivWithin ℝ i g S x‖)) S :=
    ContinuousOn.finset_sup'_apply Finset.nonempty_range_add_one fun i _ =>
      (hg.continuousOn_iteratedFDerivWithin (by exact WithTop.coe_le_coe.mpr le_top) hS.uniqueDiffOn).norm
  obtain ⟨B, hB⟩ := L.isCompact.exists_bound_of_continuousOn (hc.mono hL)
  refine ⟨|B|, abs_nonneg B, fun i hi x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen i hS (hL hx)]
  exact (Finset.le_sup' _ (Finset.mem_range_succ_iff.mpr hi)).trans
    ((Real.le_norm_self _).trans ((hB x hx).trans (Real.le_norm_self B)))

private def reverseCompact (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target) :
    Compacts (ComplexModel n) :=
  ⟨(chartTransition e f).symm '' K,
    K.isCompact.image_of_continuousOn ((chartTransition e f).symm.continuousOn.mono hK)⟩

omit [IsComplexManifold n M] in
private theorem reverseCompact_subset (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆
      (chartTransition e f).target) :
    (reverseCompact e f K hK : Set (ComplexModel n)) ⊆ (chartTransition e f).source := by
  rintro _ ⟨x, hx, rfl⟩
  exact (chartTransition e f).map_target (hK hx)

private def fixedPullCLM (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target) :
    ContDiffMapSupportedIn (ComplexModel n) ℝ ⊤ K →L[ℝ]
      ContDiffMapSupportedIn (ComplexModel n) ℝ ⊤ (reverseCompact e f K hK) := by
  let F := chartTransition e f
  let S := F.source
  let L := reverseCompact e f K hK
  have hLs : (L : Set (ComplexModel n)) ⊆ S := reverseCompact_subset e f K hK
  have hF : ContDiffOn ℝ ∞ F S := fun x hx =>
    (chartTransition_contDiffAt_real e f hx).contDiffWithinAt
  have hJ := contDiffOn_transitionJac e f
  refine ContDiffMapSupportedIn.mkCLM ℝ (fun φ => pullFun e f φ)
    (fun φ ψ x => ?_) (fun c φ x => ?_)
    (fun φ => contDiff_pullFun e f φ.contDiff φ.hasCompactSupport (φ.tsupport_subset.trans hK))
    (fun φ x hx => ?_) (fun m _ => ?_)
  · by_cases hx : x ∈ F.source <;> simp [ThetaPshChartLimitGluing.pullFun, F, hx, mul_add]
  · by_cases hx : x ∈ F.source <;> simp [ThetaPshChartLimitGluing.pullFun, F, hx, mul_left_comm]
  · exact pullFun_eq_zero_of_notMem_image e f fun h => hx
      (image_mono φ.tsupport_subset h)
  · obtain ⟨B, hB, hb⟩ := uniform_jet_bound F.open_source L hLs hJ m
    obtain ⟨D₀, hD₀, hd⟩ := uniform_jet_bound F.open_source L hLs hF m
    let D := max D₀ 1
    have hD1 : 1 ≤ D := le_max_right _ _
    have hD0 : 0 ≤ D := zero_le_one.trans hD1
    let C : ℝ := ∑ i ∈ Finset.range (m+1),
      (m.choose i : ℝ) * B * ((m-i).factorial * D^(m-i))
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
    refine ⟨Finset.Iic m, C, hC, fun φ x hx => ?_⟩
    let P := ((Finset.Iic m).sup fun j =>
      ContDiffMapSupportedIn.seminorm ℝ (ComplexModel n) ℝ ⊤ K j) φ
    have hP : 0 ≤ P := apply_nonneg _ _
    have hcomp : ContDiffOn ℝ ∞ (fun z => φ (F z)) S :=
      φ.contDiff.comp_contDiffOn hF
    have hp (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i φ (F x)‖ ≤ P :=
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hi))
    have hdf (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i F S x‖ ≤ D^i := by
      rw [iteratedFDerivWithin_of_isOpen i F.open_source (hLs hx)]
      exact (hd i him x hx).trans ((le_max_left D₀ 1).trans (le_self_pow₀ hD1 (by omega)))
    have hcg (i : ℕ) (hi : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i (fun z => φ (F z)) S x‖ ≤ i.factorial * P * D^i := by
      apply norm_iteratedFDerivWithin_comp_le φ.contDiff.contDiffOn hF (by exact WithTop.coe_le_coe.mpr le_top)
        uniqueDiffOn_univ F.open_source.uniqueDiffOn (mapsTo_univ _ _) (hLs hx)
      · intro j hj
        rw [iteratedFDerivWithin_univ]
        exact hp j (hj.trans hi)
      · intro j hj hji
        exact hdf j hj (hji.trans hi)
    have heq : EqOn (pullFun e f φ) (fun z => transitionJac e f z * φ (F z)) S :=
      fun z hz => pullFun_of_mem e f φ hz
    rw [← iteratedFDerivWithin_of_isOpen m F.open_source (hLs hx),
      iteratedFDerivWithin_congr heq (hLs hx) m]
    calc
      ‖iteratedFDerivWithin ℝ m (fun z => transitionJac e f z * φ (F z)) S x‖ ≤
          ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (transitionJac e f) S x‖ *
            ‖iteratedFDerivWithin ℝ (m-i) (fun z => φ (F z)) S x‖ := by
        simpa only [smul_eq_mul] using norm_iteratedFDerivWithin_smul_le
          hJ hcomp F.open_source.uniqueDiffOn (hLs hx) (by exact WithTop.coe_le_coe.mpr le_top : (m : ℕ∞ω) ≤ ∞)
      _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * B *
          ((m-i).factorial * P * D^(m-i)) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · rw [iteratedFDerivWithin_of_isOpen i F.open_source (hLs hx)]
          exact hb i (Finset.mem_range_succ_iff.mp hi) x hx
        · exact hcg (m-i) (Nat.sub_le m i)
      _ = C * P := by dsimp [C]; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring

/-- Actual Jacobian-weighted transport on the original LF test spaces. -/
def weightedTestCLM (e f : ComplexChart n M) :
    𝓓(⟨(chartTransition e f).target, (chartTransition e f).open_target⟩, ℝ) →L[ℝ]
      𝓓(⟨(chartTransition e f).source, (chartTransition e f).open_source⟩, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ => pullTest e f φ φ.tsupport_subset
      (image_tsupport_subset_source e f φ.tsupport_subset))
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ (reverseCompact_subset e f K hK)).comp
      (fixedPullCLM e f K hK))
    (fun _ _ _ => by apply TestFunction.ext; intro x; rfl)

/-- Pullback of ANY signed original real distribution, by the actual inverse-chart transpose. -/
def scalarPullback (e f : ComplexChart n M)
    (T : 𝓓'(⟨(chartTransition e f).target, (chartTransition e f).open_target⟩, ℝ)) :
    𝓓'(⟨(chartTransition e f).source, (chartTransition e f).open_source⟩, ℝ) := by
  have hsource : (chartTransition f e).source = (chartTransition e f).target := by
    ext z; simp [chartTransition]
  have htarget : (chartTransition f e).target = (chartTransition e f).source := by
    ext z; simp [chartTransition]
  have hs : (⟨(chartTransition f e).source, (chartTransition f e).open_source⟩ : Opens (ComplexModel n)) =
      ⟨(chartTransition e f).target, (chartTransition e f).open_target⟩ := Opens.ext hsource
  have ht : (⟨(chartTransition f e).target, (chartTransition f e).open_target⟩ : Opens (ComplexModel n)) =
      ⟨(chartTransition e f).source, (chartTransition e f).open_source⟩ := Opens.ext htarget
  have R := weightedTestCLM f e
  rw [hs, ht] at R
  exact T.comp R

end SGPT.Foundations.Analysis.Pending.DistributionChartPullback
