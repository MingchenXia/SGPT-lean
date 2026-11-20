import SGPT.Bergman.SiuNSIntegralCocycle
import SGPT.Foundations.Analysis.Pending.SlotFormCompactIBP

/-! Actual native Cartier line bundles and arbitrary finite signed integral
Cartier combinations, with the original prescribed curvature as an output. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Actual original Cartier data manufacture a smooth native line bundle
with the original divisor curvature. -/
theorem exists_native_divisor_metric (D : EffectiveDivisor n X)
    (E : MeteredEffectiveQDivisor n X) (hE : DivisorMetric.IsDivisorMetric D E) :
    ∃ L : HermitianHolomorphicLineBundle n X, IsSourceSmoothHermitianMetric L ∧
      IsOwnFirstChernForm L E.curvature :=
  (cartierMetricAtlas D E hE).exists_native_divisor_metric

/-- Original smooth divisor remainders recover their original curvature
at every original point, including zeros of every local generator. -/
theorem CartierMetricAtlas.remainder_curvature {D : EffectiveDivisor n X}
    {E : MeteredEffectiveQDivisor n X} (A : CartierMetricAtlas D E)
    (i : X) (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hi : c.val.symm z ∈ A.dom i) :
    E.curvature.val.coeff c z = -smoothDDC (fun w => A.remainder i (c.val.symm w)) z :=
  (A.nativeBundle_geometricallyEq c hz).symm.trans
    (A.scalarWeights.nativeBundle_chern_coeff i c hz hi)

omit [CompactSpace X] in
/-- Coefficients commute with actual finite sums of original closed forms. -/
theorem coeff_sum_smul {N : ℕ} (θ : Fin N → ClosedRealOneOneForm n X)
    (b : Fin N → ℝ) (c : ComplexChart n X) (z : ComplexModel n) :
    (∑ k, b k • θ k).val.coeff c z = ∑ k, b k • (θ k).val.coeff c z := by
  let ev : ClosedRealOneOneForm n X →ₗ[ℝ] ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) :=
    { toFun := fun t => t.val.coeff c z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (map_sum ev _ _).trans (Finset.sum_congr rfl (fun k _ => ev.map_smul _ _))

/-- The signed integral tensor/dual products of actual original Cartier
transitions produce an actual native bundle with the exact signed curvature.
Neither a native bundle nor its Chern identity is supplied as an assumption. -/
theorem exists_native_integral_divisor_metric {N : ℕ}
    (D : Fin N → EffectiveDivisor n X) (E : Fin N → MeteredEffectiveQDivisor n X)
    (hE : ∀ k, DivisorMetric.IsDivisorMetric (D k) (E k)) (b : Fin N → ℤ) :
    ∃ L : HermitianHolomorphicLineBundle n X, IsSourceSmoothHermitianMetric L ∧
      IsOwnFirstChernForm L (∑ k, (b k : ℝ) • (E k).curvature) := by
  let A := fun k => cartierMetricAtlas (D k) (E k) (hE k)
  let C := fun k => (A k).toCartierAtlas.toScalarCocycle
  let W := CompatibleScalarWeights.integralProduct (fun k => (A k).scalarWeights) b
  refine ⟨W.nativeBundle, W.nativeBundle_smooth, ?_⟩
  have hcoeff : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      (sourceNativeFirstChernForm W.nativeBundle W.nativeBundle_smooth).val.coeff c z =
        (∑ k, (b k : ℝ) • (E k).curvature).val.coeff c z := by
    intro c z hz
    let p := c.val.symm z
    let U := c.val.target ∩ c.val.symm ⁻¹' (⋂ k, (A k).dom p)
    have hU : IsOpen U := c.val.isOpen_inter_preimage_symm
      (isOpen_iInter_of_finite fun k => (A k).open_dom p)
    have hzU : z ∈ U := ⟨hz, mem_iInter.mpr fun k => (A k).mem_dom p⟩
    have hs : ∀ k : Fin N, ContDiffOn ℝ ∞ (fun w => A k |>.remainder p (c.val.symm w)) U :=
      fun k => ((A k).smooth p c).mono (fun w hw => ⟨hw.1, mem_iInter.mp hw.2 k⟩)
    have hchern := W.nativeBundle_chern_coeff p c hz
      (show c.val.symm z ∈ (ScalarLineCocycle.integralProduct C b).dom p from hzU.2)
    change _ = -smoothDDC (fun w => ∑ k, (b k : ℝ) * (A k).remainder p (c.val.symm w)) z at hchern
    rw [SlotFormCompactIBP.smoothDDC_finset_sum Finset.univ hU
      (fun k _ => contDiffOn_const.mul (hs k)) hzU] at hchern
    simp_rw [show ∀ k : Fin N,
      smoothDDC (fun w => (b k : ℝ) * (A k).remainder p (c.val.symm w)) z =
        (b k : ℝ) • smoothDDC (fun w => (A k).remainder p (c.val.symm w)) z from
      fun k => smoothDDC_smul hU (hs k) (b k : ℝ) hzU] at hchern
    rw [hchern, coeff_sum_smul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [(A k).remainder_curvature p c hz ((A k).mem_dom p), smul_neg]
  intro c e z hz he
  rw [← hcoeff c z hz]
  exact sourceNativeFirstChernForm_isOwn _ _ c e z hz he

end SGPT.BDivisor.NSKodaira
