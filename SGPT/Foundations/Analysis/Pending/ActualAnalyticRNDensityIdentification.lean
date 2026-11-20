import SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization

set_option autoImplicit false
/-! Complete NEW mathematics and ENTIRE proof precede this import baseline. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff Manifold
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticRNDensityIdentification
open FirstPass FirstPass.MongeAmpere FirstPass.NumericalRestrictedVolumeScaffold
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue LocalCurrentDeterminant
  LocalCurrentDensityMatrix LocalCurrentPullbackDdc LocalBedfordTaylorLocality
  ActualAnalyticCurrentLocalDensity NaturalThetaPshGeometricCurrent
  GlobalCurrentPotentials CanonicalCurrentFrame
attribute [local instance] addCommGroupFormSpan

private theorem ae_acForm_eq_of_local_pairing
    {m : ℕ} {U W : Opens (ComplexModel (m + 1))}
    {T : LocalProductCurrent (m + 1) U m} (hT : IsPositive T) (hW : W ≤ U)
    (α : ComplexModel (m + 1) → RealForm (m + 1) 2)
    (hαc : ContinuousOn α W) (hα : ∀ x ∈ W, IsOneOne (α x))
    (hpair : ∀ (γ : formSpan (m + 1) m) (χ : 𝓓(W, ℝ)),
      restrict hW (acPart hT) γ χ = ∫ x, χ x * formDensity (α x) γ) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))),
      x ∈ W → acForm hT x = α x := by
  classical
  have hγ (γ : formSpan (m + 1) m) :
      ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))), x ∈ W →
        acWeight hT x * densityForm hT x γ = formDensity (α x) γ := by
    let f : ComplexModel (m + 1) → ℝ := fun x => acWeight hT x * densityForm hT x γ
    let g : ComplexModel (m + 1) → ℝ := fun x => formDensity (α x) γ
    have hf : LocallyIntegrableOn f W volume :=
      (locallyIntegrableOn_acDensity hT γ).mono_set hW
    have hg : LocallyIntegrableOn g W volume :=
      (continuousOn_formDensity hαc γ).locallyIntegrableOn W.isOpen.measurableSet
    have hp (χ : 𝓓(W, ℝ)) : ∫ x, χ x * f x = ∫ x, χ x * g x := by
      have h := hpair γ χ
      simpa only [LocalBedfordTaylorLocality.restrict_apply, acPart_apply, extTest_apply, f, g] using h
    have hz := W.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
      (μ := volume) (fun ψ hψ hc hs => by
        let χ : 𝓓(W, ℝ) := ⟨ψ, hψ, hc, hs⟩
        have hif : Integrable (fun x => χ x * f x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf
        have hig : Integrable (fun x => χ x * g x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
        change (∫ x, χ x * (f x - g x)) = 0
        simp only [mul_sub]
        rw [integral_sub hif hig, hp χ, sub_self])
    filter_upwards [hz] with x hx hxW
    exact sub_eq_zero.mp (hx hxW)
  have hb := ae_all_iff.mpr (fun i => hγ (formBasis (m + 1) m i))
  filter_upwards [hb] with x hx hxW
  have hL : (acWeight hT x) • densityForm hT x = formDensity (α x) := by
    apply (formBasis (m + 1) m).ext
    intro i
    exact hx i hxW
  apply acForm_eq_of_forall hT x (hα x hxW)
  intro γ
  exact DFunLike.congr_fun hL γ

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The canonical RN density of the original positive current is the SAME
original smooth two-form almost everywhere on the entire chart target. -/
theorem ae_acForm_eq_original_reader (θ : ClosedRealOneOneForm (m + 1) M)
    (u : M → EReal) (hu : IsThetaPshPotential θ.val u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (e : ComplexChart (m + 1) M) :
    ∀ᵐ y ∂(volume : Measure (ComplexModel (m + 1))), y ∈ e.val.target →
      acForm (isPositive_chartSpanCurrent θ.val u hu e) y =
        θ.val.coeff e y + smoothDDC (fun w => (chartFunction u e w).toReal) y := by
  classical
  let hS := isPositive_chartSpanCurrent θ.val u hu e
  let f : ComplexModel (m + 1) → ℝ := fun w => (chartFunction u e w).toReal
  have hlocal : ∀ z ∈ {y | y ∈ e.val.target ∧ chartFunction u e y ≠ ⊥},
      ∃ r > 0, ∀ᵐ y ∂(volume : Measure (ComplexModel (m + 1))),
        y ∈ ball z r → acForm hS y = θ.val.coeff e y + smoothDDC f y := by
    intro z hz
    obtain ⟨W, hzW, hW, g, hg, hEq, hac, hpair⟩ :=
      exists_nonpolar_local_density θ u hu han e z hz.1 hz.2
    let α : ComplexModel (m + 1) → RealForm (m + 1) 2 :=
      fun y => θ.val.coeff e y + smoothDDC g y
    have hαc : ContinuousOn α W :=
      ((θ.val.smooth e).continuousOn.mono hW).add
        (LogWeightFactorization.smoothDDC_contDiffOn W.isOpen hg).continuousOn
    have hα : ∀ y ∈ W, IsOneOne (α y) := by
      intro y hy a b
      simp only [α, ContinuousAlternatingMap.add_apply]
      rw [θ.property.2 e y (hW hy) a b,
        smoothDDC_isOneOne ((hg.contDiffAt (W.isOpen.mem_nhds hy)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a b]
    have hp : ∀ (γ : formSpan (m + 1) m) (χ : 𝓓(W, ℝ)),
        restrict hW (acPart hS) γ χ = ∫ x, χ x * formDensity (α x) γ := by
      intro γ χ
      rw [hac]
      exact hpair γ χ
    have hae := ae_acForm_eq_of_local_pairing hS hW α hαc hα hp
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp W.isOpen z hzW
    refine ⟨r, hr, ?_⟩
    filter_upwards [hae] with y hy hyB
    have hyW := hball hyB
    have heq : f =ᶠ[𝓝 y] g := by
      filter_upwards [W.isOpen.mem_nhds hyW] with w hw
      change (chartFunction u e w).toReal = g w
      rw [hEq w hw, EReal.toReal_coe]
    rw [hy hyW]
    exact congrArg (fun A => θ.val.coeff e y + A) (smoothDDC_congr heq).symm
  have hnonpolar := LocalCurrentSemicontinuity.ae_of_forall_ball hlocal
  have hfin := quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
    (Nat.succ_pos m) u hu.quasiPshPotential e
  rw [addHaar_canonicalBasis] at hfin
  have hfin' := (ae_restrict_iff' e.val.open_target.measurableSet).mp hfin
  filter_upwards [hnonpolar, hfin'] with y hy hfy hye
  exact hy ⟨hye, (hfy hye).2⟩

end SGPT.Foundations.Analysis.Pending.ActualAnalyticRNDensityIdentification
