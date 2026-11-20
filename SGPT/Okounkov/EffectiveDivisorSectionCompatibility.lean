import SGPT.Okounkov.EffectiveDivisorLocalSections
import SGPT.Okounkov.EffectiveDivisorDimensionZero
import SGPT.Okounkov.EffectiveDivisorCurrentCompatibility

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open scoped NNReal
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- The literal original section recursion records the actual maximal
vanishing order, genuine local section quotient and its tail restriction. -/
def OriginalCartierSectionFlagValuation : (n : ℕ) → (F : OriginalFlagGeometry.{u} n) →
    EffectiveDivisor n F.carrier → (Fin n → ℕ) → Prop
  | 0, _, _, _ => True
  | m + 1, F, D, ν => ∃ Dtail : EffectiveDivisor m F.tail.carrier,
      OriginalCartierFlagStep F D (ν 0) Dtail ∧
      OriginalCartierSectionStep F D (ν 0) Dtail ∧
      OriginalCartierSectionFlagValuation m F.tail Dtail (fun i => ν i.succ)

/-- Actual local division and restriction are produced at every stage,
so the ideal recursion has exactly the literal source section semantics. -/
theorem originalCartierSectionFlagValuation_iff_ideal :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (D : EffectiveDivisor n F.carrier)
      (ν : Fin n → ℕ),
      OriginalCartierSectionFlagValuation n F D ν ↔ OriginalCartierFlagValuation n F D ν := by
  intro n
  induction n with
  | zero => intro F D ν; rfl
  | succ m ih =>
      intro F D ν
      constructor
      · rintro ⟨Dtail, hstep, _hsections, htail⟩
        exact ⟨Dtail, hstep, (ih F.tail Dtail (fun i => ν i.succ)).mp htail⟩
      · rintro ⟨Dtail, hstep, htail⟩
        exact ⟨Dtail, hstep, originalCartierSectionStep_of_ideal_step F D (ν 0) Dtail hstep,
          (ih F.tail Dtail (fun i => ν i.succ)).mpr htail⟩

/-- Original divisor data internally supply the complete section flag vector. -/
theorem exists_originalCartierSectionFlagValuation (n : ℕ)
    (F : OriginalFlagGeometry.{u} n) (D : EffectiveDivisor n F.carrier) :
    ∃ ν, OriginalCartierSectionFlagValuation n F D ν := by
  obtain ⟨ν, hν⟩ := exists_originalCartierFlagValuation n F D
  exact ⟨ν, (originalCartierSectionFlagValuation_iff_ideal n F D ν).mpr hν⟩

/-- The original Cartier-section vector, with genuine quotient/restriction
witnesses at each stage and no chosen current or potential representation. -/
def cartierSectionFlagValuation {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (D : EffectiveDivisor n F.carrier) : Fin n → ℕ :=
  Classical.choose (exists_originalCartierSectionFlagValuation n F D)

theorem cartierSectionFlagValuation_spec {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (D : EffectiveDivisor n F.carrier) :
    OriginalCartierSectionFlagValuation n F D (cartierSectionFlagValuation F D) :=
  Classical.choose_spec (exists_originalCartierSectionFlagValuation n F D)

/-- The literal source divisor/current compatibility: the original whole
integration current has precisely the actual Cartier-section flag vector. -/
theorem currentFlagValuation_effectiveDivisor_eq_section_vector {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (D : EffectiveDivisor (m + 1) F.carrier) :
    currentFlagValuation F (effectiveDivisorIntegrationCurrent F D)
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.2 =
      (fun i => (cartierSectionFlagValuation F D i : ℝ≥0)) := by
  obtain ⟨ν, hν, heq⟩ := exists_currentFlagValuation_effectiveDivisor_eq_integer_vector F D
  have hchosen := (originalCartierSectionFlagValuation_iff_ideal (m + 1) F D
    (cartierSectionFlagValuation F D)).mp (cartierSectionFlagValuation_spec F D)
  have hνeq := originalCartierFlagValuation_unique F D hchosen hν
  simpa only [hνeq] using heq

/-- The genuine source empty-vector base; the unit-ideal theorem separately
rules out any nonzero Cartier divisor here, without a degree-two current. -/
theorem cartierSectionFlagValuation_dimension_zero
    (F : OriginalFlagGeometry.{u} 0) (D : EffectiveDivisor 0 F.carrier) :
    cartierSectionFlagValuation F D = (fun _ => 0) := by
  funext i
  exact Fin.elim0 i

end SGPT.Okounkov
