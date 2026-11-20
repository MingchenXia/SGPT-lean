import SGPT.Foundations.Analysis.Pending.ClosedDistributionTwoFormLocalPrimitive
import SGPT.Foundations.Analysis.Pending.ActualLocallyIntegrableFormDensityUniqueness
import SGPT.Foundations.Analysis.FirstPass.HermitianGeometry

set_option autoImplicit false

/-! Full smooth form differentiation and reflection on genuine open domains.
The complete mathematical statements and ENTIRE proofs precede this source.
No globally smooth extension, positivity or geometric conclusion is assumed. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology
namespace SGPT.Foundations.Analysis.Pending.OpenSmoothFormDistributionReflection
open _root_.SGPT.Foundations.Analysis.LocalCurrents



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E} (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual exterior derivative of a field smooth on an open domain is
smooth on that same domain, with no global extension premise. -/
theorem contDiffOn_extDeriv {r : ℕ} {a : E → E [⋀^Fin r]→L[ℝ] ℝ}
    (ha : ContDiffOn ℝ ∞ a Ω) : ContDiffOn ℝ ∞ (extDeriv a) Ω := by
  let C : (E →L[ℝ] E [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin (r+1)]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ
  exact C.contDiff.comp_contDiffOn
    ((contDiffOn_infty_iff_fderiv_of_isOpen Ω.isOpen).mp ha).2

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
private theorem regularForm_coefficient {r : ℕ}
    (a : E → E [⋀^Fin r]→L[ℝ] ℝ) (hL : LocallyIntegrableOn a Ω μ)
    (v : Fin r → E) (hv : LocallyIntegrableOn (fun z => a z v) Ω μ) :
    regularFormDistribution μ a hL v =
      regularDistribution μ (fun z => a z v) hv := by
  ext φ
  rw [regularFormDistribution_apply, regularDistribution_apply]
  have hi : Integrable (fun z => φ z • a z) μ :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hL
  change (formEvaluationCLM v) (∫ z, φ z • a z ∂μ) = _
  rw [← (formEvaluationCLM v).integral_comp_comm hi]
  simp only [map_smul, formEvaluationCLM_apply, smul_eq_mul]

private theorem lineDeriv_regular_apply {u : E → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (v : E) (φ : 𝓓(Ω, ℝ)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
      (regularDistribution μ u
        (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)) φ =
      ∫ z, φ z * fderiv ℝ u z v ∂μ := by
  have huL : LocallyIntegrableOn u Ω μ :=
    hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hduL : LocallyIntegrableOn (fun z => fderiv ℝ u z v) Ω μ :=
    (((contDiffOn_infty_iff_fderiv_of_isOpen Ω.isOpen).mp hu).2.clm_apply contDiffOn_const).continuousOn
      |>.locallyIntegrableOn Ω.isOpen.measurableSet
  let ψ : 𝓓(Ω, ℝ) := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ
  have hψ : ∀ z, ψ z = fderiv ℝ φ z v :=
    fun z => testFunction_lineDerivCLM_apply_eq_fderiv φ v z
  have hψu : Integrable (fun z => ψ z * u z) μ :=
    ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL
  have hdφu : Integrable (fun z => fderiv ℝ φ z v * u z) μ := by
    simpa only [hψ] using hψu
  have hφdu : Integrable (fun z => φ z * fderiv ℝ u z v) μ :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hduL
  have hφu : Integrable (fun z => φ z * u z) μ :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdφu hφdu hφu
    (fun z _ => φ.contDiff.differentiable (by simp) z)
    (fun z hz => (hu z (φ.tsupport_subset hz)).contDiffAt
      (Ω.isOpen.mem_nhds (φ.tsupport_subset hz)) |>.differentiableAt (by simp))
  rw [Distribution.lineDerivCLM_apply, regularDistribution_apply]
  simpa only [testFunction_lineDerivCLM_apply_eq_fderiv] using hibp.symm

private theorem exteriorDerivative_regular_apply {r : ℕ}
    (a : E → E [⋀^Fin r]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω)
    (v : Fin (r+1) → E) (φ : 𝓓(Ω, ℝ)) :
    exteriorDerivative (regularFormDistribution μ a
      (ha.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)) v φ =
      ∫ z, φ z * extDeriv a z v ∂μ := by
  have hs (i : Fin (r+1)) (t : ℝ) : (-1 : ℤ)^i.val • t = (-1 : ℝ)^i.val * t := by
    simp [zsmul_eq_mul]
  have hscalar (i : Fin (r+1)) : ContDiffOn ℝ ∞ (fun z => a z (i.removeNth v)) Ω :=
    (formEvaluationCLM (i.removeNth v)).contDiff.comp_contDiffOn ha
  have hd (i : Fin (r+1)) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v i)
        (regularFormDistribution μ a
          (ha.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) (i.removeNth v)) φ =
        ∫ z, φ z * fderiv ℝ (fun y => a y (i.removeNth v)) z (v i) ∂μ := by
    rw [regularForm_coefficient μ a _ (i.removeNth v)
      ((hscalar i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)]
    exact lineDeriv_regular_apply μ (hscalar i) (v i) φ
  rw [exteriorDerivative_apply]
  simp only [sum_apply, _root_.smul_apply]
  simp_rw [hd, hs, ← integral_const_mul]
  have hI (i : Fin (r+1)) : Integrable (fun z => (-1 : ℝ)^i.val *
      (φ z * fderiv ℝ (fun y => a y (i.removeNth v)) z (v i))) μ := by
    have hl : LocallyIntegrableOn (fun z =>
        fderiv ℝ (fun y => a y (i.removeNth v)) z (v i)) Ω μ :=
      (((contDiffOn_infty_iff_fderiv_of_isOpen Ω.isOpen).mp (hscalar i)).2.clm_apply
        contDiffOn_const).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
    exact (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hl).const_mul _
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ Ω
  · rw [extDeriv_apply ((ha z hz).contDiffAt (Ω.isOpen.mem_nhds hz)
      |>.differentiableAt (by simp)) v]
    simp_rw [hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (φ.tsupport_subset ht))
    simp only [hz0, zero_mul, mul_zero, Finset.sum_const_zero]

/-- Equality on every original tuple and compact test identifies the open-domain
regular exterior derivative with the genuine classical exterior derivative. -/
theorem exteriorDerivative_regularForm_eq {r : ℕ}
    (a : E → E [⋀^Fin r]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω) :
    exteriorDerivative (regularFormDistribution μ a
      (ha.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)) =
      regularFormDistribution μ (extDeriv a)
        ((contDiffOn_extDeriv ha).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) := by
  ext v φ
  have hv : LocallyIntegrableOn (fun z => extDeriv a z v) Ω μ :=
    ((formEvaluationCLM v).contDiff.comp_contDiffOn (contDiffOn_extDeriv ha)).continuousOn
      |>.locallyIntegrableOn Ω.isOpen.measurableSet
  rw [exteriorDerivative_regular_apply μ a ha v φ,
    regularForm_coefficient μ (extDeriv a) _ v hv, regularDistribution_apply]

private theorem regularForm_zero {r : ℕ} :
    regularFormDistribution μ (fun _ : E => (0 : E [⋀^Fin r]→L[ℝ] ℝ))
      (continuousOn_const.locallyIntegrableOn Ω.isOpen.measurableSet) = 0 := by
  ext v φ
  simp [regularFormDistribution_apply]

/-- The original distribution is closed exactly when the actual classical
exterior derivative vanishes at every point of the declared open domain. -/
theorem isClosed_regularForm_iff {r : ℕ}
    (a : E → E [⋀^Fin r]→L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω) :
    IsClosed (regularFormDistribution μ a
      (ha.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)) ↔
      ∀ z ∈ Ω, extDeriv a z = 0 := by
  have hDa := contDiffOn_extDeriv ha
  have hLD : LocallyIntegrableOn (extDeriv a) Ω μ :=
    hDa.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hL0 : LocallyIntegrableOn
      (fun _ : E => (0 : E [⋀^Fin (r+1)]→L[ℝ] ℝ)) Ω μ :=
    continuousOn_const.locallyIntegrableOn Ω.isOpen.measurableSet
  constructor
  · intro hc
    have hEq : regularFormDistribution μ (extDeriv a) hLD =
        regularFormDistribution μ (fun _ => 0) hL0 := by
      rw [regularForm_zero]
      exact (exteriorDerivative_regularForm_eq μ a ha).symm.trans hc
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq
      (ActualLocallyIntegrableFormDensityUniqueness.ae_eq_of_regularFormDistribution_eq
        μ hLD hL0 hEq) Ω.isOpen hDa.continuousOn continuousOn_const
  · intro hzero
    rw [_root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed, exteriorDerivative_regularForm_eq μ a ha]
    ext v φ
    rw [regularFormDistribution_apply]
    have hi : (∫ z, φ z • extDeriv a z ∂μ) = 0 := by
      have hfun : (fun z => φ z • extDeriv a z) =
          (fun _ : E => (0 : E [⋀^Fin (r+1)]→L[ℝ] ℝ)) := by
        funext z
        by_cases hz : z ∈ Ω
        · rw [hzero z hz, smul_zero]
        · have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport
            (fun ht => hz (φ.tsupport_subset ht))
          rw [hz0, zero_smul]
      rw [hfun, integral_zero]
    rw [hi]
    simp

section Complex
open FirstPass
variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The full original type-(1,1) equation forces the genuine pointwise smooth
geometric type, including complex dimension zero. -/
theorem isOneOne_of_regularForm_isOneOne
    (ν : Measure (ComplexModel n)) [ν.IsAddHaarMeasure]
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U)
    (hType : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne
      (regularFormDistribution ν a
        (ha.continuousOn.locallyIntegrableOn U.isOpen.measurableSet))) :
    ∀ z ∈ U, FirstPass.IsOneOne (a z) := by
  let J : ComplexModel n →L[ℝ] ComplexModel n :=
    ((Complex.I : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ
  let C : ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM J
  have hCApply (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (v w : ComplexModel n) :
      C A ![v,w] = A ![Complex.I • v, Complex.I • w] := by
    change A (J ∘ ![v,w]) = _
    congr 1
    funext i
    fin_cases i <;> simp [J]
  let b : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ := fun z => C (a z)
  have hb : ContDiffOn ℝ ∞ b U := C.contDiff.comp_contDiffOn ha
  have hLa : LocallyIntegrableOn a U ν :=
    ha.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hLb : LocallyIntegrableOn b U ν :=
    hb.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have heq : regularFormDistribution ν b hLb = regularFormDistribution ν a hLa := by
    ext v φ
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    have hI : Integrable (fun z => φ z • a z) ν :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hLa
    rw [regularFormDistribution_apply, regularFormDistribution_apply]
    change (∫ z, φ z • C (a z) ∂ν) ![v 0, v 1] = _
    have hi := C.integral_comp_comm hI
    have hci : (∫ z, φ z • C (a z) ∂ν) = C (∫ z, φ z • a z ∂ν) := by
      simpa only [map_smul] using hi
    rw [hci]
    rw [hCApply]
    have ht := congrArg (fun D : 𝓓'(U, ℝ) => D φ) (hType (v 0) (v 1))
    simpa only [regularFormDistribution_apply] using ht
  have hp := MeasureTheory.Measure.eqOn_open_of_ae_eq
    (ActualLocallyIntegrableFormDensityUniqueness.ae_eq_of_regularFormDistribution_eq
      ν hLb hLa heq) U.isOpen hb.continuousOn ha.continuousOn
  intro z hz v w
  have hv := congrArg (fun A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ => A ![v,w]) (hp hz)
  change C (a z) ![v,w] = a z ![v,w] at hv
  rw [hCApply] at hv
  exact hv

end Complex
end SGPT.Foundations.Analysis.Pending.OpenSmoothFormDistributionReflection
