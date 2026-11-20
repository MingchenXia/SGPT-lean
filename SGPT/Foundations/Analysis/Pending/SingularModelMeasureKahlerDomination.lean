import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.RelativeFullMass

set_option autoImplicit false

/-!
# Actual singular model measure domination by an enlarged Kahler volume

An independent background-enlargement consequence of Xia SGPT PDF0100--0101,
Theorem 3.1.1. Actual model-envelope contact, actual background monotonicity,
and actual ordered contact comparison produce the measure domination.
The model may be unbounded and theta need not be semipositive.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelMeasureKahlerDomination

open FirstPass FirstPass.PositiveClasses DiagonalMass GlobalNonPluripolar
  IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual model measure is dominated by every dominating genuine Kahler background's volume. -/
theorem diagonalPotentialMeasure_model_le_kahlerVolume (Ω : KahlerBackground n M)
    (hdom : (Ω.form - θ).val.IsSemipositive) :
    diagonalPotentialMeasure θ φ hφ.plurisubharmonic ≤ kahlerVolume Ω := by
  classical
  have hφ0 : φ ≤ 0 := by
    rw [hφ.envelope_eq]
    exact singularityEnvelope_le_zero θ.val φ
  have hP : IsThetaPshPotential θ.val (singularityEnvelope θ.val φ) := by
    rw [← hφ.envelope_eq]
    exact hφ.plurisubharmonic
  have hnull : diagonalPotentialMeasure θ φ hφ.plurisubharmonic {x | φ x < 0} = 0 := by
    have h := SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
      Ω θ hφ.plurisubharmonic hP
    simpa only [← hφ.envelope_eq] using h
  have hform : θ + (Ω.form - θ) = Ω.form := by abel
  have hφΩ : IsThetaPshPotential Ω.form.val φ := by
    rw [← hform]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hφ.plurisubharmonic hdom
  have h0Ω : IsThetaPshPotential Ω.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff Ω.form).mpr Ω.isSemipositive
  have hbg : diagonalPotentialMeasure θ φ hφ.plurisubharmonic ≤
      diagonalPotentialMeasure Ω.form φ hφΩ := by
    exact NefBoundedMixedMass.globalMixedMeasure_le_of_add_smul_on
      (Finset.univ : Finset (Fin n)) hdom one_pos
      (θ' := fun _ => Ω.form) (by simp [hform])
      (fun _ => hφ.plurisubharmonic.1) (fun _ _ => hφ.plurisubharmonic)
      (fun _ => hφΩ.1)
  let K : Set M := {x | φ x = 0}
  have hrestrict : (diagonalPotentialMeasure θ φ hφ.plurisubharmonic).restrict K =
      diagonalPotentialMeasure θ φ hφ.plurisubharmonic := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply measure_mono_null ?_ hnull
    intro x hx
    change φ x ≠ 0 at hx
    have hle0 : φ x ≤ (0 : EReal) := hφ0 x
    exact lt_of_le_of_ne hle0 hx
  have hcontact : (diagonalPotentialMeasure Ω.form φ hφΩ).restrict K ≤
      (kahlerVolume Ω).restrict K := by
    rw [Measure.le_iff]
    intro E hE
    rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
    exact MaxMassDecomposition.contact_measure_le Ω hφΩ h0Ω hφ0 hE
  calc
    diagonalPotentialMeasure θ φ hφ.plurisubharmonic =
        (diagonalPotentialMeasure θ φ hφ.plurisubharmonic).restrict K := hrestrict.symm
    _ ≤ (diagonalPotentialMeasure Ω.form φ hφΩ).restrict K :=
      Measure.restrict_mono_measure hbg K
    _ ≤ (kahlerVolume Ω).restrict K := hcontact
    _ ≤ kahlerVolume Ω := Measure.restrict_le_self

/-- Actual compact Kahler domination produces a positive scaled background and model measure bound. -/
theorem exists_pos_scaled_kahlerVolume_model_domination (omega : KahlerBackground n M) :
    ∃ (A : ℝ) (hA : 0 < A),
      ((KahlerBackground.smul hA omega).form - θ).val.IsSemipositive ∧
      diagonalPotentialMeasure θ φ hφ.plurisubharmonic ≤
        kahlerVolume (KahlerBackground.smul hA omega) := by
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  have hdom' : ((KahlerBackground.smul hA omega).form - θ).val.IsSemipositive := by
    rw [KahlerBackground.smul_form]
    simpa only [sub_eq_add_neg, add_comm] using hdom
  exact ⟨A, hA, hdom', diagonalPotentialMeasure_model_le_kahlerVolume (hφ := hφ) _ hdom'⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelMeasureKahlerDomination
