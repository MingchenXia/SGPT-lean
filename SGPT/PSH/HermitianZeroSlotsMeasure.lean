import SGPT.PSH.HermitianProductsZeroSlots
import SGPT.PSH.HermitianGlobalMeasure
import SGPT.PSH.HermitianExtremalPoleAlternative

/-!
# The same global Hermitian measure with actual zero slots

Selected original potentials are followed by genuine zero potentials.
Their corrected representatives append repeated copies of the original
smooth correction. The actual slot identity identifies their full mixed
measure with the original lower current wedged with the Hermitian power.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorForms LocalBedfordTaylorCollar LocalBedfordTaylorSmoothProductDensity
  TopDegreeDensity
open Hermitian HermitianProducts SGPT.PSH.HermitianComparisonTraceDomination

variable {m p l : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- Selected original slots, in their displayed order, followed by actual
zero potentials and transported along the displayed length equality. -/
def completeWithZeros (hpl : p + l = m + 1) (u : Fin p → M → EReal) :
    Fin (m + 1) → M → EReal :=
  fun i => Fin.append u (fun _ : Fin l => fun _ : M => (0 : EReal)) (Fin.cast hpl.symm i)

theorem completeWithZeros_isHermitianPSH (hpl : p + l = m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i)) :
    ∀ i, IsHermitianPSH omega (completeWithZeros hpl u i) := by
  have h (i : Fin (p + l)) : IsHermitianPSH omega
      (Fin.append u (fun _ : Fin l => fun _ : M => (0 : EReal)) i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hu j
    · simpa only [Fin.append_right] using HermitianExtremal.isHermitianPSH_zero omega
  exact fun i => h (Fin.cast hpl.symm i)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem completeWithZeros_bounded (hpl : p + l = m + 1) (u : Fin p → M → EReal)
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ completeWithZeros hpl u i x ∧
      completeWithZeros hpl u i x ≤ (b : EReal) := by
  have h (i : Fin (p + l)) : ∃ a b : ℝ, ∀ x,
      (a : EReal) ≤ Fin.append u (fun _ : Fin l => fun _ : M => (0 : EReal)) i x ∧
        Fin.append u (fun _ : Fin l => fun _ : M => (0 : EReal)) i x ≤ (b : EReal) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hb j
    · exact ⟨0, 0, fun _ => by simp only [Fin.append_right, EReal.coe_zero, le_refl, and_self]⟩
  exact fun i => h (Fin.cast hpl.symm i)

private theorem backgroundExpansion_unit_reindex {n a b r : ℕ}
    {U : Opens (ComplexModel n)} (hab : a = b) (ha : r + a = n) (hb : r + b = n)
    (v : Fin a → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    backgroundExpansion b r (fun i => v (Fin.cast hab.symm i)) hσ (oneCurrentOf (U := U) hb) =
      backgroundExpansion a r v hσ (oneCurrentOf (U := U) ha) := by
  cases hab
  rfl

private theorem cast_oneCurrentOf {n a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (ha : a = n) (hb : b = n) :
    castLPC hab (oneCurrentOf (U := U) ha) = oneCurrentOf (U := U) hb := by
  cases hab
  rfl

private theorem cast_backgroundExpansion_unit {n k a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (ha : a + k = n) (hb : b + k = n)
    (v : Fin k → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    castLPC hab (backgroundExpansion k a v hσ (oneCurrentOf (U := U) ha)) =
      backgroundExpansion k b v hσ (oneCurrentOf (U := U) hb) := by
  cases hab
  rfl

private theorem append_correction_unit_top {n k d : ℕ} {U : Opens (ComplexModel n)}
    (hkd : k + d = n) (v : Fin k → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hqp : PlurisubharmonicOn (fun z => (q z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (k + d) 0 (Fin.append v (fun _ : Fin d => q)) hσ
      (oneCurrentOf (U := U) (by omega : 0 + (k + d) = n)) =
      wedgeForm (by omega : 0 + d = d)
        (backgroundExpansion k d v hσ (oneCurrentOf (U := U) (by omega : d + k = n)))
        (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) d) := by
  have heq := backgroundExpansion_append_correction k d 0
    (oneCurrentOf (U := U) (by omega : 0 + (k + d) = n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) v hv hq hqp hσ hσS
  have hcast : 0 + (k + d) = (0 + d) + k := by omega
  rw [cast_oneCurrentOf (n := n) hcast (by omega) (by omega)] at heq
  rw [← SGPT.PSH.HermitianComparisonOneFactor.wedgeForm_castLPC (Nat.zero_add d) rfl
    (backgroundExpansion k (0 + d) v hσ (oneCurrentOf (U := U) (by omega)))
    (contDiffOn_formPower ((contDiffOn_ddcForm hq).add hσ) d),
    cast_backgroundExpansion_unit (Nat.zero_add d) (by omega) (by omega) v hσ] at heq
  exact heq

namespace BackgroundPatch

/-- The original smooth correction is itself genuinely PSH: correct the
actual zero Hermitian potential by this same majorant. -/
theorem correction_plurisubharmonicOn (P : BackgroundPatch omega) :
    PlurisubharmonicOn (fun z => (P.correction z : EReal)) P.geometry.domain := by
  have h := chart_add_smooth_plurisubharmonicOn omega.isTypeOneOne
    (HermitianExtremal.isHermitianPSH_zero omega) P.geometry.chart
    P.geometry.domain_le_target P.smooth P.dominates
  simpa only [chartFunction, zero_add] using h

/-- Inserting actual zero potentials into the same full product equals
wedging the original selected mixed current with the actual Hermitian power. -/
theorem current_completeWithZeros (P : BackgroundPatch omega) (hpl : p + l = m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    P.current (completeWithZeros hpl u) =
      wedgeForm (n := m + 1) (U := P.geometry.domain) (r := 0) (k := l) (m := l) (by omega : 0 + l = l) (P.currentOfDegree p l (by omega) u)
        (contDiffOn_formPower (n := m + 1) (U := P.geometry.domain)
          ((omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target) l) := by
  let v : Fin p → ComplexModel (m + 1) → ℝ := fun i => P.correctedReal (u i)
  have hreader (i : Fin (p + l)) :
      P.correctedReal (Fin.append u (fun _ : Fin l => fun _ : M => (0 : EReal)) i) =
        Fin.append v (fun _ : Fin l => P.correction) i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
      funext z
      simp only [correctedReal, chartFunction, EReal.toReal_zero, zero_add]
  have htuple : (fun i => P.correctedReal (completeWithZeros hpl u i)) =
      (fun i => Fin.append v (fun _ : Fin l => P.correction) (Fin.cast hpl.symm i)) := by
    funext i
    exact hreader (Fin.cast hpl.symm i)
  have hmain := append_correction_unit_top (n := m + 1) hpl v
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i))
    P.smooth P.correction_plurisubharmonicOn P.residual_smooth
    (fun z hz => oneOne_mem_formSpan (P.residual_isOneOne z hz))
  change backgroundExpansion (m + 1) 0 (fun i => P.correctedReal (completeWithZeros hpl u i))
    P.residual_smooth (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1))) = _
  rw [htuple, backgroundExpansion_unit_reindex (n := m + 1) (r := 0) hpl (by omega) (Nat.zero_add (m + 1))]
  rw [hmain]
  change wedgeForm (n := m + 1) (U := P.geometry.domain) (r := 0) (k := l) (m := l) (by omega : 0 + l = l)
      (P.currentOfDegree p l (by omega) u) _ = _
  apply wedgeForm_congr
  intro z _
  change formPower (smoothDDC P.correction z +
    (omega.form.coeff P.geometry.chart z - smoothDDC P.correction z)) l = _
  have heq : smoothDDC P.correction z +
      (omega.form.coeff P.geometry.chart z - smoothDDC P.correction z) =
        omega.form.coeff P.geometry.chart z := by abel
  rw [heq]

end BackgroundPatch
variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

private theorem traceMeasure_congr {n r : ℕ} {U : Opens (ComplexModel n)}
    {S T : LocalProductCurrent n U r} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : hS.traceMeasure = hT.traceMeasure := by
  subst T
  rfl

/-- The canonical global mixed measure of selected original potentials
followed by actual zeros reads on every patch as the original lower mixed
current wedged with the actual Hermitian power. -/
theorem globalMixedMeasure_completeWithZeros_restrict_patch
    (hpl : p + l = m + 1) (u : Fin p → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) :
    (globalMixedMeasure omega (completeWithZeros hpl u)
      (completeWithZeros_isHermitianPSH hpl u hu) (completeWithZeros_bounded hpl u hb)).restrict
        P.geometry.source =
      P.geometry.pushMeasure (powerTraceMeasure (P.currentOfDegree p l (by omega) u)
        (P.currentOfDegree_isPositive p l (by omega) u hu hb)
        ((omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target)
        (fun z hz => ⟨omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz),
          omega.isSemipositive P.geometry.chart z (P.geometry.domain_le_target hz)⟩)) := by
  let homega := (omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target
  have homegaP : ∀ z ∈ P.geometry.domain,
      IsSemipositiveOneOne (omega.form.coeff P.geometry.chart z) :=
    fun z hz => ⟨omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz),
      omega.isSemipositive P.geometry.chart z (P.geometry.domain_le_target hz)⟩
  let hT := P.currentOfDegree_isPositive p l (by omega) u hu hb
  let hPow := isPositive_wedgeForm (by omega : 0 + l = l) hT
    (contDiffOn_formPower homega l) (fun z hz => formPower_mem_spCone (homegaP z hz) l)
  have ht := traceMeasure_congr
    (P.current_isPositive (completeWithZeros hpl u)
      (completeWithZeros_isHermitianPSH hpl u hu) (completeWithZeros_bounded hpl u hb))
    hPow (P.current_completeWithZeros hpl u hu hb)
  calc
    _ = P.geometry.pushMeasure
        (P.current_isPositive (completeWithZeros hpl u)
          (completeWithZeros_isHermitianPSH hpl u hu)
          (completeWithZeros_bounded hpl u hb)).traceMeasure :=
      globalMixedMeasure_restrict_patch _ _ _ P
    _ = _ := congrArg P.geometry.pushMeasure ht

end SGPT.PSH.HermitianGlobalProducts
