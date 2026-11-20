import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartTensorPullback
import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials

/-!
# Whole weighted full tensor transport between arbitrary actual charts

Input support lies only in the input chart's target. The original smooth global
cutoff internally constructs compact output support inside the actual overlap.
Boundary extension and every derivative seminorm bound are proved, giving the
actual continuous linear transport without an incoming output certificate.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCrossChartWeightedTensorTransport

open FirstPass FirstPass.HolomorphicMaps NaturalSupportedChartTensorPullback

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

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual output compact support, without restricting the input to the overlap. -/
def outputCompact (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hs : tsupport χ ⊆ f.val.source) : Compacts (ComplexModel n) :=
  ⟨f.val '' ((e.val.symm '' (K : Set (ComplexModel n))) ∩ tsupport χ),
    ((K.isCompact.image_of_continuousOn (e.val.symm.continuousOn.mono hK)).inter_right
      (isClosed_tsupport χ)).image_of_continuousOn
      (f.val.continuousOn.mono fun _ hx => hs hx.2)⟩

omit [IsComplexManifold n M] in
/-- The internally produced output support lies inside the actual overlap. -/
theorem outputCompact_subset (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hs : tsupport χ ⊆ f.val.source) :
    (outputCompact e f K hK χ hs : Set (ComplexModel n)) ⊆
      (chartTransition f e).source := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨f.val.map_source (hs hx.2), ?_⟩
  change f.val.symm (f.val x) ∈ e.val.source
  rw [f.val.left_inv (hs hx.2)]
  obtain ⟨y, hy, rfl⟩ := hx.1
  exact e.val.map_target (hK hy)

private def weightedTensorField (e f : ComplexChart n M) (χ : M → ℝ)
    (z : ComplexModel n) :
    ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ :=
  χ (f.val.symm z) • ContinuousAlternatingMap.compContinuousLinearMapCLM
    (chartTransitionDerivative f e z)

private theorem contDiffOn_weightedTensorField (e f : ComplexChart n M)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) :
    ContDiffOn ℝ ∞ (weightedTensorField (q := q) e f χ) (chartTransition f e).source := by
  let : IsBoundedSMul ℝ
      (((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) := .of_norm_smul_le fun r A => ContinuousLinearMap.opNorm_smul_le r A
  exact ((hχ f).mono fun _ hx => hx.1).smul (contDiffOn_tensor_field (q := q) f e)

private def weightedPullFun (e f : ComplexChart n M) (χ : M → ℝ)
    (A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ :=
  (chartTransition f e).source.indicator
    (fun z => weightedTensorField e f χ z (A (chartTransition f e z)))

omit [IsComplexManifold n M] in
private theorem weightedPullFun_zero (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hs : tsupport χ ⊆ f.val.source)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    {x : ComplexModel n} (hx : x ∉ outputCompact e f K hK χ hs) :
    weightedPullFun e f χ A x = 0 := by
  by_cases ho : x ∈ (chartTransition f e).source
  · by_cases hk : chartTransition f e x ∈ (K : Set (ComplexModel n))
    · have hc : χ (f.val.symm x) = 0 := by
        by_contra hne
        have hmem : f.val.symm x ∈ tsupport χ := by
          by_contra hnot
          exact hne (image_eq_zero_of_notMem_tsupport hnot)
        exact hx ⟨f.val.symm x,
          ⟨⟨chartTransition f e x, hk, e.val.left_inv ho.2⟩, hmem⟩,
          f.val.right_inv ho.1⟩
      simp only [weightedPullFun, indicator_of_mem ho, weightedTensorField, hc,
        smul_apply, zero_smul]
    · simp only [weightedPullFun, indicator_of_mem ho, A.zero_on_compl hk,
        Pi.zero_apply, map_zero]
  · simp only [weightedPullFun, indicator_of_notMem ho]

private theorem contDiff_weightedPullFun (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hs : tsupport χ ⊆ f.val.source)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) :
    ContDiff ℝ ∞ (weightedPullFun e f χ A) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (chartTransition f e).source
  · have hev : weightedPullFun e f χ A =ᶠ[𝓝 x]
        fun z => weightedTensorField e f χ z (A (chartTransition f e z)) := by
      filter_upwards [(chartTransition f e).open_source.mem_nhds hx] with z hz
      exact indicator_of_mem hz _
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((contDiffOn_weightedTensorField e f χ hχ).contDiffAt
      ((chartTransition f e).open_source.mem_nhds hx)).clm_apply
      (A.contDiff.contDiffAt.comp x (chartTransition_contDiffAt_real f e hx))
  · have hxL : x ∉ outputCompact e f K hK χ hs :=
      fun h => hx (outputCompact_subset e f K hK χ hs h)
    have hev : weightedPullFun e f χ A =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(outputCompact e f K hK χ hs).isCompact.isClosed.isOpen_compl.mem_nhds
        hxL] with z hz
      exact weightedPullFun_zero e f K hK χ hs A hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Actual continuous full tensor transport, with internally constructed output support. -/
def chartWeightedPullCLM (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hs : tsupport χ ⊆ f.val.source) :
    𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      𝓓_{outputCompact e f K hK χ hs}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) := by
  let F := chartTransition f e
  let S := F.source
  let L := outputCompact e f K hK χ hs
  let P := weightedTensorField (q := q) e f χ
  have hP : ContDiffOn ℝ ∞ P S := contDiffOn_weightedTensorField e f χ hχ
  have hLs : (L : Set (ComplexModel n)) ⊆ S := outputCompact_subset e f K hK χ hs
  have hF : ContDiffOn ℝ ∞ F S := fun x hx =>
    (chartTransition_contDiffAt_real f e hx).contDiffWithinAt
  refine ContDiffMapSupportedIn.mkCLM ℝ (fun A => weightedPullFun e f χ A)
    (fun A A' x => ?_) (fun c A x => ?_)
    (contDiff_weightedPullFun e f K hK χ hχ hs)
    (fun A x hx => weightedPullFun_zero e f K hK χ hs A hx) (fun m _ => ?_)
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
      ContDiffMapSupportedIn.seminorm ℝ (ComplexModel n) ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) ⊤ K j) A
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
    have heq : EqOn (weightedPullFun e f χ A) (fun z => P z (A (F z))) S :=
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

/-- Full pointwise readback, with the actual input-to-output chart direction. -/
theorem chartWeightedPullCLM_apply (e f : ComplexChart n M)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hs : tsupport χ ⊆ f.val.source)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (z : ComplexModel n) :
    chartWeightedPullCLM e f K hK χ hχ hs A z =
      (chartTransition f e).source.indicator (fun y => χ (f.val.symm y) •
        (A (chartTransition f e y)).compContinuousLinearMap
          (chartTransitionDerivative f e y)) z := rfl

end SGPT.Foundations.Analysis.Pending.NaturalCrossChartWeightedTensorTransport
