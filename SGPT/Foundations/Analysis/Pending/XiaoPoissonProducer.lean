import SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability

set_option autoImplicit false

/-!
# The genuine mean-zero Poisson producer

Project the inverse of the proved actual Kähler Laplacian isomorphism to its
mean-zero component. Actual Stokes removes the constant for mean-zero data;
actual elliptic regularity gives smooth solutions for smooth data.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace SGPT.Foundations.Analysis.Pending.XiaoPoissonProducer

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses IntegrationCurrent
  KahlerLaplacianChart KahlerLaplacianStokes KahlerLaplacianSolvability
  HolderAtlas.HolderMap

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] {r : ℝ≥0}

/-- The actual bounded inverse, projected onto its genuine mean-zero function component. -/
def meanZeroPoissonCLM (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    A.HolderMap k r ℝ →L[ℝ]
      (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker :=
  (ContinuousLinearMap.fst ℝ
    (integralCLM (A := A) (k := k + 2) (r := r) (kahlerVolume w)).ker ℝ).comp
      (laplacianConstEquiv w A hr0 hr1 k).symm.toContinuousLinearMap

@[simp] theorem meanZeroPoissonCLM_apply (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) (h : A.HolderMap k r ℝ) :
    meanZeroPoissonCLM w A hr0 hr1 k h = ((laplacianConstEquiv w A hr0 hr1 k).symm h).1 := rfl

/-- The produced actual function has actual mean zero by membership in the kernel. -/
theorem integral_meanZeroPoissonCLM_eq_zero (w : KahlerBackground n M) (A : HolderAtlas n M)
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) (h : A.HolderMap k r ℝ) :
    (∫ x, (meanZeroPoissonCLM w A hr0 hr1 k h).val x ∂(kahlerVolume w)) = 0 :=
  (meanZeroPoissonCLM w A hr0 hr1 k h).property

/-- Genuine Stokes removes the constant in the actual Laplacian inverse for mean-zero data. -/
theorem laplacian_meanZeroPoissonCLM_eq_of_integral_eq_zero
    (w : KahlerBackground n M) (A : HolderAtlas n M) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) (h : A.HolderMap k r ℝ) (hh : ∫ x, h x ∂(kahlerVolume w) = 0) :
    ∀ y, laplacian w.form.val (meanZeroPoissonCLM w A hr0 hr1 k h).val y = h y := by
  let p := (laplacianConstEquiv w A hr0 hr1 k).symm h
  have hback : laplacianConstEquiv w A hr0 hr1 k p = h :=
    (laplacianConstEquiv w A hr0 hr1 k).apply_symm_apply h
  have hp : ∀ y, laplacian w.form.val p.1.val y - p.2 = h y := by
    intro y
    have hy := congrArg (fun f : A.HolderMap k r ℝ => f y) hback
    rw [laplacianConstEquiv_apply] at hy
    exact hy
  have hiL : Integrable (laplacian w.form.val p.1.val) (kahlerVolume w) := by
    have heq : (fun y => laplacianCLMk w.isKahler.1 hr0 hr1 k p.1.val y) =
        laplacian w.form.val p.1.val :=
      funext fun y => laplacianCLMk_apply w.isKahler.1 hr0 hr1 k p.1.val y
    rw [← heq]
    exact integrable_holderMap (kahlerVolume w) _
  have hi := integral_congr_ae (μ := kahlerVolume w) (Filter.Eventually.of_forall hp)
  rw [integral_sub hiL (integrable_const p.2), integral_laplacian_holderMap w hr1,
    integral_const, smul_eq_mul, hh, zero_sub] at hi
  have hσ : p.2 = 0 := by
    have hm : (kahlerVolume w).real univ * p.2 = 0 := neg_eq_zero.mp hi
    exact (mul_eq_zero.mp hm).resolve_left (kahlerVolume_real_univ_pos w).ne'
  intro y
  change laplacian w.form.val p.1.val y = h y
  simpa only [hσ, sub_zero] using hp y

/-- Genuine global elliptic regularity makes the produced mean-zero solution smooth. -/
theorem chartSmooth_meanZeroPoissonCLM_of_chartSmooth (w : KahlerBackground n M)
    (A : HolderAtlas n M) (hr0 : 0 < r) (hr1 : r < 1)
    (h : M → ℝ) (hf : ChartSmooth (n := n) h)
    (hh : ∫ x, h x ∂(kahlerVolume w) = 0) :
    ChartSmooth (n := n) (meanZeroPoissonCLM w A hr0 hr1 0
      (ofChartSmooth (A := A) (k := 0) hr1.le h hf)).val := by
  let h0 := ofChartSmooth (A := A) (k := 0) hr1.le h hf
  let u0 := (meanZeroPoissonCLM w A hr0 hr1 0 h0).val
  have hEq : ∀ y, laplacian w.form.val u0 y = h y :=
    laplacian_meanZeroPoissonCLM_eq_of_integral_eq_zero w A hr0 hr1 0 h0 hh
  intro e
  apply contDiffOn_infty.mpr
  intro j
  let hj := ofChartSmooth (A := A) (k := j) hr1.le h hf
  obtain ⟨v, hv⟩ := exists_holderMap_of_laplacian_eq w.isKahler.1 hr0 hr1 u0 hj hEq
  have hc : ContDiffOn ℝ (j + 2) (fun z => u0 (e.val.symm z)) e.val.target := by
    have hc : ContDiffOn ℝ (j + 2) (fun z => v (e.val.symm z)) e.val.target :=
      fun z hz => (HolderGerm.holderAt_comp_symm hr1.le v e hz).contDiffAt.contDiffWithinAt
    simpa only [hv] using hc
  exact hc.of_le (by exact_mod_cast Nat.le_add_right j 2)

/-- Two actual smooth mean-zero functions with the same actual Laplacian agree. -/
theorem eq_of_smooth_mean_zero_laplacian_eq (w : KahlerBackground n M)
    (A : HolderAtlas n M) (hr0 : 0 < r) (hr1 : r < 1)
    (u v : M → ℝ) (hu : ChartSmooth (n := n) u) (hv : ChartSmooth (n := n) v)
    (hmu : ∫ x, u x ∂(kahlerVolume w) = 0) (hmv : ∫ x, v x ∂(kahlerVolume w) = 0)
    (hLap : ∀ y, laplacian w.form.val u y = laplacian w.form.val v y) : u = v := by
  let S := (integralCLM (A := A) (k := 2) (r := r) (kahlerVolume w)).ker
  let uh := ofChartSmooth (A := A) (k := 2) hr1.le u hu
  let vh := ofChartSmooth (A := A) (k := 2) hr1.le v hv
  have hum : uh ∈ S := hmu
  have hvm : vh ∈ S := hmv
  let p : S × ℝ := (⟨uh, hum⟩, 0)
  let q : S × ℝ := (⟨vh, hvm⟩, 0)
  have himg : laplacianConstEquiv w A hr0 hr1 0 p =
      laplacianConstEquiv w A hr0 hr1 0 q := by
    apply HolderAtlas.HolderMap.ext
    intro y
    rw [laplacianConstEquiv_apply, laplacianConstEquiv_apply]
    change laplacian w.form.val u y - 0 = laplacian w.form.val v y - 0
    rw [hLap y]
  have hpq := (laplacianConstEquiv w A hr0 hr1 0).injective himg
  funext y
  exact congrArg (fun t : S × ℝ => t.1.val y) hpq

/-- Every actual smooth mean-zero input has a unique actual smooth mean-zero Poisson solution. -/
theorem exists_unique_smooth_mean_zero_poisson (w : KahlerBackground n M)
    (h : M → ℝ) (hf : ChartSmooth (n := n) h)
    (hh : ∫ x, h x ∂(kahlerVolume w) = 0) :
    ∃ u : M → ℝ, ChartSmooth (n := n) u ∧
      (∫ x, u x ∂(kahlerVolume w)) = 0 ∧
      (∀ y, laplacian w.form.val u y = h y) ∧
      ∀ v : M → ℝ, ChartSmooth (n := n) v →
        (∫ x, v x ∂(kahlerVolume w)) = 0 →
        (∀ y, laplacian w.form.val v y = h y) → v = u := by
  obtain ⟨A⟩ := HolderAtlas.nonempty (n := n) (M := M)
  have hr0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num
  let h0 := ofChartSmooth (A := A) (k := 0) hr1.le h hf
  let u := (meanZeroPoissonCLM w A hr0 hr1 0 h0).val
  have hs : ChartSmooth (n := n) u :=
    chartSmooth_meanZeroPoissonCLM_of_chartSmooth w A hr0 hr1 h hf hh
  have hm : (∫ x, u x ∂(kahlerVolume w)) = 0 :=
    integral_meanZeroPoissonCLM_eq_zero w A hr0 hr1 0 h0
  have hEq : ∀ y, laplacian w.form.val u y = h y :=
    laplacian_meanZeroPoissonCLM_eq_of_integral_eq_zero w A hr0 hr1 0 h0 hh
  refine ⟨u, hs, hm, hEq, ?_⟩
  intro v hv hmv hveq
  exact eq_of_smooth_mean_zero_laplacian_eq w A hr0 hr1 v u hv hs hmv hm
    fun y => (hveq y).trans (hEq y).symm

end

end SGPT.Foundations.Analysis.Pending.XiaoPoissonProducer
