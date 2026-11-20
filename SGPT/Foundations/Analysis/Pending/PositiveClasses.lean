import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# Consequences of smooth local potentials for positive classes

These proofs introduce no new holes. They consume the smooth local dd-bar
existence theorem and the earlier smooth theta-PSH criterion through
`Pending.LocalPotentials`. All positivity predicates remain explicitly
potential-based; no comparison with the full positive-current cone is claimed.
-/

namespace SGPT.Foundations.Analysis.Pending.PositiveClasses

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The zero potential witnesses pseudoeffectivity of a semipositive form. -/
theorem pseudoeffectiveViaPotentials_of_semipositive
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) :
    PseudoeffectiveViaPotentials θ :=
  ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hθ⟩

/-- A positive semipositive margin provides a big potential class. -/
theorem bigWithRespectToViaPotentials_of_semipositive_difference
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {ε : ℝ} (hε : 0 < ε) (hθ : (θ - ε • omega.form).val.IsSemipositive) :
    BigWithRespectToViaPotentials omega θ :=
  ⟨ε, hε, pseudoeffectiveViaPotentials_of_semipositive hθ⟩

/-- A background is big relative to itself, with margin one half. -/
theorem kahlerBackground_bigWithRespectToViaPotentials (omega : KahlerBackground n M) :
    BigWithRespectToViaPotentials omega omega.form := by
  apply bigWithRespectToViaPotentials_of_semipositive_difference omega
    (ε := (1 / 2 : ℝ)) (by norm_num)
  have heq : omega.form - (1 / 2 : ℝ) • omega.form =
      (1 / 2 : ℝ) • omega.form := by
    calc
      omega.form - (1 / 2 : ℝ) • omega.form =
          (1 - (1 / 2 : ℝ)) • omega.form := by rw [sub_smul, one_smul]
      _ = (1 / 2 : ℝ) • omega.form := by norm_num
  rw [heq]
  intro e z hz
  exact coefficientSemipositive_smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (omega.isSemipositive e z hz)

/-- Enlarge the background without changing the potential or its non-poles. -/
theorem pseudoeffectiveViaPotentials_of_big (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : BigWithRespectToViaPotentials omega θ) :
    PseudoeffectiveViaPotentials θ := by
  obtain ⟨ε, hε, u, hu⟩ := hθ
  have hpos : (ε • omega.form).val.IsSemipositive := by
    intro e z hz
    exact coefficientSemipositive_smul hε.le (omega.isSemipositive e z hz)
  refine ⟨u, ?_⟩
  simpa only [sub_add_cancel] using
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu hpos

theorem classPseudoeffectiveViaPotentials_of_semipositive
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) :
    ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) :=
  pseudoeffectiveViaPotentials_of_semipositive hθ

theorem classPseudoeffectiveViaPotentials_of_big (omega : KahlerBackground n M)
    {α : RealBottChern n M} (hα : ClassBigWithRespectToViaPotentials omega α) :
    ClassPseudoeffectiveViaPotentials α := by
  revert hα
  refine Quotient.inductionOn α ?_
  intro θ hθ
  exact pseudoeffectiveViaPotentials_of_big omega hθ

theorem kahlerBackground_classBigWithRespectToViaPotentials (omega : KahlerBackground n M) :
    ClassBigWithRespectToViaPotentials omega (RealBottChern.ofRepresentative omega.form) :=
  kahlerBackground_bigWithRespectToViaPotentials omega

end

end SGPT.Foundations.Analysis.Pending.PositiveClasses
