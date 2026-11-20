import SGPT.PSH.HermitianBalayageTraceDomination
import SGPT.PSH.HermitianProductFactors
import SGPT.PSH.HermitianProductsDomination
import SGPT.PSH.HermitianProductsCorrectionShift

/-!
# Actual nonclosed-background patch measures for the frozen argument

The measure is the Riesz trace of the literal positive background
expansion. Dominating corrections give ordinary canonical measure
domination. Restriction and changing a genuine smooth correction preserve
the same background current, through the proved local expansion algebra.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalBedfordTaylorCanonicalTraceMeasure MixedMongeAmpere StronglyPositiveForms LocalBedfordTaylorCollar
open Hermitian HermitianGlobalProducts
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The actual diagonal background measure on the original coordinate patch. -/
def backgroundDiagonalMeasure (P : BackgroundPatch omega) (u : M → EReal)
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    Measure (ComplexModel (m + 1)) :=
  (P.current_isPositive (fun _ => u) (fun _ => hu) (fun _ => hb)).traceMeasure

/-- The correction's actual residual is negative semipositive. -/
theorem backgroundPatch_neg_residual_isSemipositive (P : BackgroundPatch omega)
    {z : ComplexModel (m + 1)} (hz : z ∈ P.geometry.domain) :
    IsSemipositiveOneOne (-P.residual z) := by
  constructor
  · intro v w
    simp only [ContinuousAlternatingMap.neg_apply]
    rw [P.residual_isOneOne z hz v w]
  · intro v
    simp only [BackgroundPatch.residual, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.sub_apply]
    linarith [P.dominates z hz v]

/-- The actual nonclosed-background patch measure is dominated by the
canonical ordinary measure of the actual corrected bounded PSH potential. -/
theorem backgroundDiagonalMeasure_le_canonical (P : BackgroundPatch omega) (u : M → EReal)
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    backgroundDiagonalMeasure P u hu hb ≤
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure P.geometry.domain
        (P.correctedReal u) (P.correctedReal_isLocallyBoundedPshOn hu hb) := by
  let v : Fin (m + 1) → ComplexModel (m + 1) → ℝ := fun _ => P.correctedReal u
  have hv : ∀ i, IsLocallyBoundedPshOn P.geometry.domain (v i) :=
    fun _ => P.correctedReal_isLocallyBoundedPshOn hu hb
  have hdiag := canonicalMixedBedfordTaylorMeasure_diagonal P.geometry.domain (P.correctedReal u)
    (P.correctedReal_isLocallyBoundedPshOn hu hb)
  have htrace := canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hv
  have heq := hdiag.symm.trans htrace
  rw [heq]
  exact HermitianProducts.traceMeasure_backgroundExpansion_le_btProduct (m + 1) 0 _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun _ => P.correctedReal u)
    (fun _ => P.correctedReal_isLocallyBoundedPshOn hu hb) P.residual_smooth P.residual_isOneOne
    (fun _ => P.factor_isPositive hu hb) (fun _ hz => backgroundPatch_neg_residual_isSemipositive P hz)

/-- Restricting a genuine background patch retains its actual correction. -/
def restrictBackgroundPatch (P : BackgroundPatch omega)
    (D : Opens (ComplexModel (m + 1))) (hD : D ≤ P.geometry.domain) : BackgroundPatch omega where
  geometry := ⟨P.geometry.chart, D, fun _ hz => P.geometry.domain_le_target (hD hz)⟩
  correction := P.correction
  smooth := P.smooth.mono hD
  dominates := fun z hz v => P.dominates z (hD hz) v

/-- A different actual smooth majorizing correction defines the same
geometric background patch. No current or measure conclusion is stored. -/
def changeBackgroundCorrection (P : BackgroundPatch omega)
    (q : ComplexModel (m + 1) → ℝ) (hq : ContDiffOn ℝ ∞ q P.geometry.domain)
    (hdom : ∀ z ∈ P.geometry.domain, ∀ v : ComplexModel (m + 1),
      omega.form.coeff P.geometry.chart z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v]) :
    BackgroundPatch omega where
  geometry := P.geometry
  correction := q
  smooth := hq
  dominates := hdom

private theorem restrict_oneCurrentOf_eq {n k : ℕ} {W D : Opens (ComplexModel n)}
    (hD : D ≤ W) (hk : k = n) :
    restrict hD (oneCurrentOf (U := W) hk) = oneCurrentOf (U := D) hk := by
  subst hk
  change restrict hD (oneCurrent W) = oneCurrent D
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, oneCurrent_apply]
  have hφ : (extTest hD φ : ComplexModel k → ℝ) = φ := funext (extTest_apply hD φ)
  rw [hφ]

/-- The actual background current commutes with open restriction in the
same chart, with its correction retained. -/
theorem backgroundPatch_current_restrict (P : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (D : Opens (ComplexModel (m + 1))) (hD : D ≤ P.geometry.domain) :
    restrict hD (P.current u) = (restrictBackgroundPatch P D hD).current u := by
  have hOne := restrict_oneCurrentOf_eq hD (Nat.zero_add (m + 1))
  change restrict hD (HermitianProducts.backgroundExpansion (m + 1) 0
      (fun i => P.correctedReal (u i)) P.residual_smooth _) = _
  rw [HermitianProducts.backgroundExpansion_restrict hD (m + 1) 0 _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) P.residual_smooth, hOne]
  rfl

/-- Changing to any other actual smooth dominating correction preserves
the original background current, through the genuine expansion identity. -/
theorem backgroundPatch_current_changeCorrection (P : BackgroundPatch omega)
    (q : ComplexModel (m + 1) → ℝ) (hq : ContDiffOn ℝ ∞ q P.geometry.domain)
    (hdom : ∀ z ∈ P.geometry.domain, ∀ v : ComplexModel (m + 1),
      omega.form.coeff P.geometry.chart z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v])
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    (changeBackgroundCorrection P q hq hdom).current u = P.current u := by
  let Q := changeBackgroundCorrection P q hq hdom
  let g := fun z => q z - P.correction z
  have hg : ContDiffOn ℝ ∞ g P.geometry.domain := hq.sub P.smooth
  have hshift (i : Fin (m + 1)) :
      (fun z => P.correctedReal (u i) z + g z) = Q.correctedReal (u i) := by
    funext z
    dsimp [g, Q, changeBackgroundCorrection, BackgroundPatch.correctedReal]
    ring
  have hvg (i : Fin (m + 1)) : IsLocallyBoundedPshOn P.geometry.domain
      (fun z => P.correctedReal (u i) z + g z) := by
    rw [hshift]
    exact Q.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)
  have hres : EqOn (fun z => P.residual z - smoothDDC g z) Q.residual P.geometry.domain := by
    intro z hz
    change P.residual z - smoothDDC (fun y => q y - P.correction y) z =
      omega.form.coeff P.geometry.chart z - smoothDDC q z
    rw [PositiveClasses.smoothDDC_sub P.geometry.domain.isOpen hq P.smooth hz]
    dsimp only [BackgroundPatch.residual]
    abel
  have hfull := HermitianProducts.backgroundExpansion_add_smooth (m + 1) 0
    (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1)))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) hg hvg P.residual_smooth
    (fun z hz => oneOne_mem_formSpan (P.residual_isOneOne z hz))
  have hcongr := HermitianProducts.backgroundExpansion_congr (m + 1) 0
    (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1)))
    (fun i z => P.correctedReal (u i) z + g z) (fun i => Q.correctedReal (u i))
    (fun i z _ => congrFun (hshift i) z)
    (P.residual_smooth.sub (contDiffOn_ddcForm hg)) Q.residual_smooth hres
  exact hcongr.symm.trans hfull

private theorem trace_eq_of_current_eq {W : Opens (ComplexModel (m + 1))}
    {A B : LocalProductCurrent (m + 1) W 0} (hA : IsPositive A) (hB : IsPositive B) (h : A = B) :
    hA.traceMeasure = hB.traceMeasure := by subst h; rfl

/-- The actual diagonal measures are independent of the chosen smooth
majorizing correction on the original patch. -/
theorem backgroundDiagonalMeasure_changeCorrection (P : BackgroundPatch omega)
    (q : ComplexModel (m + 1) → ℝ) (hq : ContDiffOn ℝ ∞ q P.geometry.domain)
    (hdom : ∀ z ∈ P.geometry.domain, ∀ v : ComplexModel (m + 1),
      omega.form.coeff P.geometry.chart z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v])
    (u : M → EReal) (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    backgroundDiagonalMeasure (changeBackgroundCorrection P q hq hdom) u hu hb =
      backgroundDiagonalMeasure P u hu hb :=
  trace_eq_of_current_eq _ _ (backgroundPatch_current_changeCorrection P q hq hdom
    (fun _ => u) (fun _ => hu) (fun _ => hb))

/-- Open restriction preserves the actual original background diagonal
measure; finiteness and positivity are produced by the current itself. -/
theorem backgroundDiagonalMeasure_restrict (P : BackgroundPatch omega)
    (u : M → EReal) (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (D : Opens (ComplexModel (m + 1))) (hD : D ≤ P.geometry.domain) :
    (backgroundDiagonalMeasure P u hu hb).restrict (D : Set (ComplexModel (m + 1))) =
      backgroundDiagonalMeasure (restrictBackgroundPatch P D hD) u hu hb := by
  have hT := P.current_isPositive (fun _ => u) (fun _ => hu) (fun _ => hb)
  exact (traceMeasure_restrict hT hD).symm.trans (trace_eq_of_current_eq _ _
    (backgroundPatch_current_restrict P (fun _ => u) (fun _ => hu) (fun _ => hb) D hD))

/-- Canonical scalar measures depend only on the actual bounded PSH
data on their original coordinate domain. -/
theorem canonicalScalarMeasure_congrOn {N : ℕ} {W : Opens (ComplexModel N)}
    {f g : ComplexModel N → ℝ} (hf : IsLocallyBoundedPshOn W f)
    (hg : IsLocallyBoundedPshOn W g) (heq : EqOn f g W) :
    SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure W f hf =
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure W g hg :=
  (canonicalMixedBedfordTaylorMeasure_diagonal W f hf).symm.trans
    ((canonicalMixedMeasure_congrOn (fun _ => hf) (fun _ => hg) (fun _ => heq)).trans
      (canonicalMixedBedfordTaylorMeasure_diagonal W g hg))

/-- On any smaller coordinate domain the fixed original background
measure is dominated by the ordinary canonical measure for any genuine
smooth majorizing correction there. The corrected PSH reader is produced. -/
theorem backgroundDiagonalMeasure_restrict_le_corrected (P : BackgroundPatch omega)
    (u : M → EReal) (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (D : Opens (ComplexModel (m + 1))) (hD : D ≤ P.geometry.domain)
    (q : ComplexModel (m + 1) → ℝ) (hq : ContDiffOn ℝ ∞ q D)
    (hdom : ∀ z ∈ D, ∀ v : ComplexModel (m + 1),
      omega.form.coeff P.geometry.chart z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v]) :
    ∃ hF : IsLocallyBoundedPshOn D (fun z => (chartFunction u P.geometry.chart z).toReal + q z),
      (backgroundDiagonalMeasure P u hu hb).restrict (D : Set (ComplexModel (m + 1))) ≤
        SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure D
          (fun z => (chartFunction u P.geometry.chart z).toReal + q z) hF := by
  let R := restrictBackgroundPatch P D hD
  let Q := changeBackgroundCorrection R q hq hdom
  have hF : IsLocallyBoundedPshOn D (Q.correctedReal u) :=
    Q.correctedReal_isLocallyBoundedPshOn hu hb
  refine ⟨hF, ?_⟩
  have h := backgroundDiagonalMeasure_le_canonical Q u hu hb
  rw [backgroundDiagonalMeasure_changeCorrection R q hq hdom u hu hb,
    ← backgroundDiagonalMeasure_restrict P u hu hb D hD] at h
  exact h

end SGPT.PSH.HermitianBalayage
