import SGPT.PSH.HermitianVolumePositive
import SGPT.PSH.HermitianGlobalProductConstants
import SGPT.PSH.HermitianComparisonSublevel
import SGPT.PSH.HermitianComparisonTraceAlgebra

/-!
# Genuine constant competitors for bounded-mass comparison

The constant comparison potential has the actual smooth background
measure, with positive mass on every nonempty open set. The comparison
open set is manufactured from the original bounded potential and an
arbitrarily small positive gap.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBoundedMass

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianExtremalCurrentAlgebra HermitianComparisonSublevel
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A finite constant is PSH relative to every actual smooth semipositive
one-one form, whether or not that form is closed. -/
theorem isFormPSH_const {θ : SmoothRealForm (m + 1) M 2}
    (hθ11 : θ.IsTypeOneOne) (hθpos : θ.IsSemipositive) (c : ℝ) :
    IsFormPSH θ (fun _ : M => (c : EReal)) := by
  let hc := isGlobalQuasiPshPotential_const (n := m + 1) (M := M) c
  refine ⟨hc, ?_⟩
  rw [potentialCurrent, ddcCurrent_const c hc, add_zero]
  exact isPositiveCurrent_smooth θ hθ11 hθpos

def constantPotentials (c : ℝ) : Fin (m + 1) → M → EReal := fun _ _ => (c : EReal)

theorem constantPotentials_isHermitianPSH (omega : Background (m + 1) M)
    (c : ℝ) (i : Fin (m + 1)) : IsHermitianPSH omega (constantPotentials c i) :=
  isFormPSH_const omega.isTypeOneOne omega.isSemipositive c

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem constantPotentials_bounded (c : ℝ) (i : Fin (m + 1)) :
    ∃ a b : ℝ, ∀ x : M, (a : EReal) ≤ constantPotentials c i x ∧
      constantPotentials c i x ≤ (b : EReal) := ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
private theorem globalMixedMeasure_congr_functions
    (omega : Background (m + 1) M) (u v : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i)) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (hbv : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (heq : u = v) : globalMixedMeasure omega u hu hb = globalMixedMeasure omega v hv hbv := by
  cases heq
  rfl

omit [BorelSpace M] in
/-- The canonical measure of the constant competitor is exactly the
canonical zero-potential background measure on every set. -/
theorem globalMixedMeasure_const_eq_zero (omega : Background (m + 1) M) (c : ℝ) :
    globalMixedMeasure omega (constantPotentials c) (constantPotentials_isHermitianPSH omega c)
      (constantPotentials_bounded c) =
    globalMixedMeasure omega zeroPotentials (zeroPotentials_isHermitianPSH omega)
      zeroPotentials_bounded := by
  calc
    _ = globalMixedMeasure omega (fun i x => zeroPotentials i x + (c : EReal))
        (fun i => isFormPSH_add_const (zeroPotentials_isHermitianPSH omega i) c)
        (fun i => boundedPotential_add_const (zeroPotentials_bounded i) c) := by
      apply globalMixedMeasure_congr_functions
      funext i x
      exact (zero_add (c : EReal)).symm
    _ = _ := globalMixedMeasure_add_constants zeroPotentials
      (zeroPotentials_isHermitianPSH omega) zeroPotentials_bounded (fun _ => c)

/-- The constant comparison product has strictly positive real mass on
every original nonempty open set. -/
theorem constant_globalMixedMeasure_open_toReal_pos (omega : Background (m + 1) M)
    (c : ℝ) {E : Set M} (hE : IsOpen E) (hne : E.Nonempty) :
    0 < (globalMixedMeasure omega (constantPotentials c)
      (constantPotentials_isHermitianPSH omega c) (constantPotentials_bounded c) E).toReal := by
  rw [globalMixedMeasure_const_eq_zero]
  exact zero_globalMixedMeasure_open_toReal_pos omega hE hne

/-- The original bounded potential supplies a genuine nonempty comparison
open set with any prescribed small gap and positive constant-product mass. -/
theorem exists_positive_constant_comparison_open [Nonempty M]
    (omega : Background (m + 1) M) {h : M → EReal} (hh : IsHermitianPSH omega h)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ h x ∧ h x ≤ (b : EReal))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, IsOpen {x | h x < (c : EReal)} ∧ {x | h x < (c : EReal)}.Nonempty ∧
      (∀ x, h x < (c : EReal) → 0 < c - (h x).toReal ∧ c - (h x).toReal ≤ δ) ∧
      0 < (globalMixedMeasure omega (constantPotentials c)
        (constantPotentials_isHermitianPSH omega c) (constantPotentials_bounded c)
        {x | h x < (c : EReal)}).toReal := by
  obtain ⟨c, hcOpen, hcne, hgap⟩ := exists_small_hermitian_sublevel hh hb hδ
  exact ⟨c, hcOpen, hcne, hgap, constant_globalMixedMeasure_open_toReal_pos omega c hcOpen hcne⟩

end SGPT.PSH.HermitianBoundedMass
