import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition
import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure

set_option autoImplicit false

/-! Singular positive addition preserves the genuine canonical AC form and
entire top measure. The complete mathematical statement and ENTIRE proof
precede the import baseline in the owned blueprint. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.SingularPositiveCurrentACInvariance
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentDeterminant LocalCurrentDensityMatrix LocalBedfordTaylorLocality
  ActualPositiveCurrentLebesgueUniqueness ActualPositiveCurrentLebesgueACAddition
  PositiveCurrentACTopMeasure
attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem acPart_add_singular
    {D T : LocalProductCurrent (m + 1) U m} (hD : IsPositive D) (hT : IsPositive T)
    (hDs : hD.traceMeasure ⟂ₘ volume) : acPart (hD.add hT) = acPart hT := by
  obtain ⟨_, hSs, _, hAa⟩ := part_trace_classes hT
  let hS := isPositive_sgPart hT
  let hA := isPositive_acPart hT
  have hQs : (hD.add hS).traceMeasure ⟂ₘ volume := by
    rw [traceMeasure_add hD hS]
    exact hDs.add_left hSs
  have hparts := parts_of_singular_add_absolutelyContinuous (hD.add hS) hA hQs hAa
  have heq : (D + sgPart hT) + acPart hT = D + T := by
    rw [add_assoc, sgPart_add_acPart]
  simpa only [heq] using hparts.2

private theorem ae_acForm_eq_of_acPart_eq
    {S T : LocalProductCurrent (m + 1) U m} (hS : IsPositive S) (hT : IsPositive T)
    (hpart : acPart hS = acPart hT) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))),
      x ∈ U → acForm hS x = acForm hT x := by
  classical
  have hγ (γ : formSpan (m + 1) m) :
      ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))), x ∈ U →
        acWeight hS x * densityForm hS x γ = acWeight hT x * densityForm hT x γ := by
    let f : ComplexModel (m + 1) → ℝ := fun x => acWeight hS x * densityForm hS x γ
    let g : ComplexModel (m + 1) → ℝ := fun x => acWeight hT x * densityForm hT x γ
    have hf : LocallyIntegrableOn f U volume := locallyIntegrableOn_acDensity hS γ
    have hg : LocallyIntegrableOn g U volume := locallyIntegrableOn_acDensity hT γ
    have hp (χ : 𝓓(U, ℝ)) : ∫ x, χ x * f x = ∫ x, χ x * g x := by
      have h := congrArg (fun C : LocalProductCurrent (m + 1) U m => C γ χ) hpart
      simpa only [acPart_apply, f, g] using h
    have hz := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
      (μ := volume) (fun ψ hψ hc hs => by
        let χ : 𝓓(U, ℝ) := ⟨ψ, hψ, hc, hs⟩
        have hif : Integrable (fun x => χ x * f x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf
        have hig : Integrable (fun x => χ x * g x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
        change (∫ x, χ x * (f x - g x)) = 0
        simp only [mul_sub]
        rw [integral_sub hif hig, hp χ, sub_self])
    filter_upwards [hz] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  have hb := ae_all_iff.mpr (fun i => hγ (formBasis (m + 1) m i))
  filter_upwards [hb] with x hx hxU
  have hL : (acWeight hS x) • densityForm hS x =
      (acWeight hT x) • densityForm hT x := by
    apply (formBasis (m + 1) m).ext
    intro i
    exact hx i hxU
  apply acForm_eq_of_forall hS x (isOneOne_acForm hT x)
  intro γ
  rw [← acWeight_mul_densityForm_eq hT x γ]
  exact DFunLike.congr_fun hL γ

/-- Natural trace singularity of the positive added current internally
preserves the actual canonical RN density form of any positive current.
No coefficient identity or analytic hypothesis is supplied. -/
theorem ae_acForm_add_singular
    {D T : LocalProductCurrent (m + 1) U m} (hD : IsPositive D) (hT : IsPositive T)
    (hDs : hD.traceMeasure ⟂ₘ volume) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))),
      x ∈ U → acForm (hD.add hT) x = acForm hT x :=
  ae_acForm_eq_of_acPart_eq (hD.add hT) hT (acPart_add_singular hD hT hDs)

/-- Equality of the entire actual AC top measures, including infinite mass
and the empty open set, after singular positive addition. -/
theorem acTopMeasure_add_singular_eq
    {D T : LocalProductCurrent (m + 1) U m} (hD : IsPositive D) (hT : IsPositive T)
    (hDs : hD.traceMeasure ⟂ₘ volume) :
    acTopMeasure (hD.add hT) = acTopMeasure hT := by
  unfold acTopMeasure
  rw [restrict_withDensity U.isOpen.measurableSet,
    restrict_withDensity U.isOpen.measurableSet]
  apply withDensity_congr_ae
  filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).2
    (ae_acForm_add_singular hD hT hDs)] with x hx
  rw [hx]

end SGPT.Foundations.Analysis.Pending.SingularPositiveCurrentACInvariance
