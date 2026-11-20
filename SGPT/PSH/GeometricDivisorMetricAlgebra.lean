import SGPT.PSH.ActualGeometricLogMetric
import SGPT.Okounkov.DivisorMetricAddition

/-! Genuine Cartier metric algebra with exact curvature, for subsequent
original finite divisor current/class normalization. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [TopologicalSpace M] in
private theorem singleton_log (g : M → ℂ) (y : M) :
    generatorLog (fun _ : Fin 1 => g) y=logNormSq (g y) := by
  rw [generatorLog_eq_log_sum]
  simp [logNormSq]

/-- The actual zero metered divisor is a genuine metric of the actual
zero Cartier divisor, with its literal zero weight and zero curvature. -/
theorem isDivisorMetric_actual_zero :
    DivisorMetric.IsDivisorMetric (0 : EffectiveDivisor n M) (MeteredDivisorOperations.zero n M) := by
  intro x
  refine ⟨univ,isOpen_univ,mem_univ _,(fun _ => (1 : ℂ)),mdifferentiableOn_const,?_,
    (fun _ => (0 : ℝ)),(fun _ => contDiffOn_const),?_⟩
  · intro y _ b
    simpa only [HironakaEffectiveDivisorSum.ideal_zero,IdealWeightPowers.unitIdeal] using
      (MemberPullback.isInSpanAt_one_iff b).symm
  · intro y _
    change (0 : EReal)=generatorLog (fun _ : Fin 1 => fun _ : M => (1 : ℂ)) y+(0 : ℝ)
    rw [singleton_log]
    simp [logNormSq]

/-- Integral scaling metrizes the SAME actual Cartier multiple; full ideal
powers and original poles are retained, including coefficient zero. -/
theorem isDivisorMetric_actual_nat_smul (D : EffectiveDivisor n M)
    (E : MeteredEffectiveQDivisor n M) (hE : DivisorMetric.IsDivisorMetric D E) (k : ℕ) :
    DivisorMetric.IsDivisorMetric (k • D)
      (MeteredDivisorScaling.smul (show (0 : ℚ)≤(k : ℚ) from Nat.cast_nonneg _) E) := by
  intro x
  obtain ⟨V,hV,hxV,g,hg,hgen,h,hh,hw⟩ := hE x
  refine ⟨V,hV,hxV,(fun y => g y ^ k),hg.pow k,?_,
    (fun y => (k : ℝ)*h y),?_,?_⟩
  · intro y hy b
    rw [HironakaEffectiveDivisorSum.ideal_nsmul]
    exact HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hg hy) (hgen y hy) k b
  · intro e
    simpa only [smul_eq_mul] using (hh e).const_smul (k : ℝ)
  · intro y hy
    have hpow : logNormSq (g y ^ k)=((k : ℝ) : EReal)*logNormSq (g y) := by
      simpa [logNormSq] using logNormSq_geometric_product (fun _ : Fin 1 => g y) (fun _ => k) 1
    rw [MeteredDivisorScaling.weight_smul,hw y hy,singleton_log,singleton_log,hpow]
    simp only [Rat.cast_natCast]
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr (Nat.cast_nonneg k)) (EReal.coe_ne_top (k : ℝ)),←EReal.coe_mul]

/-- Actual finite integral Cartier sums admit genuine metrics whose curvature
is the EXACT finite weighted original metric curvature. No metric or class
for the sum is a premise. -/
theorem exists_actual_metric_finite_cartier_sum {ι : Type*} (s : Finset ι)
    (D : ι → EffectiveDivisor n M) (E : ι → MeteredEffectiveQDivisor n M)
    (hE : ∀ i∈s,DivisorMetric.IsDivisorMetric (D i) (E i)) (a : ι → ℕ) :
    ∃ H : MeteredEffectiveQDivisor n M,
      DivisorMetric.IsDivisorMetric (∑ i∈s,a i • D i) H ∧
      H.curvature=∑ i∈s,(a i : ℝ) • (E i).curvature := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨MeteredDivisorOperations.zero n M,?_,?_⟩
    · simpa only [Finset.sum_empty] using isDivisorMetric_actual_zero (n := n) (M := M)
    · rfl
  | @insert i s hi ih =>
    obtain ⟨H,hH,hcurv⟩ := ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))
    let Ei := MeteredDivisorScaling.smul (show (0 : ℚ)≤(a i : ℚ) from Nat.cast_nonneg _) (E i)
    have hEi := isDivisorMetric_actual_nat_smul (D i) (E i) (hE i (Finset.mem_insert_self i s)) (a i)
    refine ⟨MeteredDivisorOperations.add Ei H,?_,?_⟩
    · rw [Finset.sum_insert hi]
      exact SGPT.Okounkov.isDivisorMetric_meteredAdd (a i • D i) (∑ j∈s,a j • D j) Ei H hEi hH
    · change Ei.curvature+H.curvature=∑ j∈insert i s,(a j : ℝ) • (E j).curvature
      rw [hcurv,Finset.sum_insert hi]
      change (((a i : ℚ) : ℝ) • (E i).curvature)+_=((a i : ℝ) • (E i).curvature)+_
      simp only [Rat.cast_natCast]

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
