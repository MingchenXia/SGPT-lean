import SGPT.NPP.DN3Divergence
import SGPT.Foundations.Analysis.Pending.WirtingerIntegrationByParts
import SGPT.Foundations.Analysis.Pending.WeightedWirtingerAdjoint

/-!
# The kernel-square identity: integrations by parts in the fibre variable

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 4, the evaluation of `T₂` and
`T₃`).  In the fibre variable `s ∈ ℂⁿ` FPT moves the derivatives of the weight onto the integrand
`G` by integrations by parts, so that only the complex Hessian `H_{k l̄} = ∂_{s̄_l}∂_{s_k} G`
of the (plurisubharmonic) integrand remains.  Here, with TN's directional Wirtinger derivatives
`∂_v = CauchyGreen.dDir v`, `∂̄_v = CauchyGreen.dbarDir v`:

* `integral_mul_dDir_dbarDir` (the `T₃` step, two integrations by parts):
  `∫ G ∂_m ∂̄_l N = ∫ (∂̄_l ∂_m G) N` for compactly supported `N`;
* `integral_dDir_mul_dDir_dbarDir` (the `T₂` step, one integration by parts in `s̄_l`): if the
  vector field `y` is holomorphic on a neighbourhood of the support of `M`, then
  `∫ (∂_{y} G) ∂_m ∂̄_l M = -∑_k ∫ y_k (∂̄_l ∂_k G) ∂_m M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff InnerProductSpace ComplexConjugate

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen

variable {n : ℕ}

theorem hasCompactSupport_dbarDir {N : ComplexModel n → ℂ} (hN : HasCompactSupport N)
    (v : ComplexModel n) : HasCompactSupport (dbarDir v N) :=
  hN.mono' (subset_tsupport _ |>.trans (OTChen.tsupport_dbarDir_subset v N))

theorem tsupport_dDir_subset (v : ComplexModel n) (h : ComplexModel n → ℂ) :
    tsupport (dDir v h) ⊆ tsupport h := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport h)
  by_contra hxs
  apply hx
  have hev : h =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
  simp only [dDir, hev.fderiv_eq, fderiv_const_apply]
  simp

theorem hasCompactSupport_dDir {N : ComplexModel n → ℂ} (hN : HasCompactSupport N)
    (v : ComplexModel n) : HasCompactSupport (dDir v N) :=
  hN.mono' (subset_tsupport _ |>.trans (tsupport_dDir_subset v N))

/-- **The `T₃` step**: `∫ G ∂_m ∂̄_l N = ∫ (∂̄_l ∂_m G) N` for compactly supported `N`. -/
theorem integral_mul_dDir_dbarDir {G N : ComplexModel n → ℂ} (hG : ContDiff ℝ 2 G)
    (hN : ContDiff ℝ 2 N) (hNs : HasCompactSupport N) (u v : ComplexModel n) :
    ∫ s, G s * dDir u (dbarDir v N) s = ∫ s, dbarDir v (dDir u G) s * N s := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hN1 : ContDiff ℝ 1 N := hN.of_le (by norm_num)
  have hdN : ContDiff ℝ 1 (dbarDir v N) := contDiff_dbarDir (k := 1) hN
  have hdG : ContDiff ℝ 1 (dDir u G) := contDiff_dDir (k := 1) hG
  rw [integral_mul_dDir_eq_neg hG1 hdN (Or.inr (hasCompactSupport_dbarDir hNs v)) u,
    integral_mul_dbarDir_eq_neg hdG hN1 (Or.inr hNs) v, neg_neg]

/-- The coordinates of a vector field holomorphic at `s` are holomorphic at `s`. -/
theorem differentiableAt_coord {y : ComplexModel n → ComplexModel n} {s : ComplexModel n}
    (hy : DifferentiableAt ℂ y s) (k : Fin n) : DifferentiableAt ℂ (fun t => y t k) s := by
  have hL : DifferentiableAt ℂ (fun z : ComplexModel n => z k) (y s) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiableAt
  exact hL.comp s hy

/-- **The `T₂` step** (one integration by parts in `s̄_l`): if the vector field `y` is holomorphic
on the support of `M`, then
`∫ (∑_k y_k ∂_k G) ∂_m ∂̄_l M = -∫ (∑_k y_k ∂̄_l ∂_k G) ∂_m M`. -/
theorem integral_dDir_mul_dDir_dbarDir {G M : ComplexModel n → ℂ}
    {y : ComplexModel n → ComplexModel n} (hG : ContDiff ℝ 2 G) (hy : ContDiff ℝ 1 y)
    (hM : ContDiff ℝ 2 M) (hMs : HasCompactSupport M)
    (hyh : ∀ s ∈ tsupport M, DifferentiableAt ℂ y s) (u v : ComplexModel n) :
    ∫ s, (∑ k, y s k * dDir (coordinateVector k) G s) * dDir u (dbarDir v M) s =
      -∫ s, (∑ k, y s k * dbarDir v (dDir (coordinateVector k) G) s) * dDir u M s := by
  have hyk : ∀ k, ContDiff ℝ 1 (fun t => y t k) := fun k =>
    ((EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ).contDiff.comp hy
  have hdG : ∀ k, ContDiff ℝ 1 (dDir (coordinateVector k) G) := fun k =>
    contDiff_dDir (k := 1) hG
  have hf : ContDiff ℝ 1 (fun s => ∑ k, y s k * dDir (coordinateVector k) G s) :=
    ContDiff.sum fun k _ => (hyk k).mul (hdG k)
  have hdM : ContDiff ℝ 1 (dDir u M) := contDiff_dDir (k := 1) hM
  have hcomm : ∀ s, dDir u (dbarDir v M) s = dbarDir v (dDir u M) s := fun s =>
    (dbarDir_dDir_comm (hM.contDiffAt)).symm
  simp_rw [hcomm]
  rw [integral_mul_dbarDir_eq_neg hf hdM (Or.inr (hasCompactSupport_dDir hMs u)) v]
  congr 1
  congr 1
  funext s
  by_cases hs : s ∈ tsupport M
  · congr 1
    rw [dbarDir_finset_sum_fun (g := fun k t => y t k * dDir (coordinateVector k) G t)
      Finset.univ fun k _ =>
      ((hyk k).differentiable one_ne_zero s).mul ((hdG k).differentiable one_ne_zero s)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dbarDir_mul ((hyk k).differentiable one_ne_zero s) ((hdG k).differentiable one_ne_zero s),
      OTChen.dbarDir_eq_zero_of_differentiableAt (differentiableAt_coord (hyh s hs) k), zero_mul,
      zero_add]
  · have h0 : dDir u M s = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hs (tsupport_dDir_subset u M h))
    rw [h0, mul_zero, mul_zero]

end SGPT.NPP.DN3
