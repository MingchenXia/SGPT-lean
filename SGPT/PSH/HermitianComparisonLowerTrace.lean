import SGPT.PSH.HermitianComparisonMetricBound
import SGPT.PSH.HermitianProductsResidualSplitting

/-!
# Corrected ordinary traces and the actual lower Hermitian traces

The equalities here concern native trace measures of the actual positive
currents. The residual splitting supplies Hermitian subproducts; the
smooth correction and coordinate forms are dominated using positivity.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonLowerTrace

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.PSH.HermitianComparisonTraceDomination SGPT.PSH.HermitianComparisonCutoff
  SGPT.PSH.HermitianProducts
open scoped Distributions ContDiff Topology CompactlySupported

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem wedgeSpan_scalarUnit_left {q : ℕ} (β : formSpan n q) :
    wedgeSpan n (by omega : 0 + q = q) scalarUnit β = β := by
  apply Subtype.ext
  rw [coe_wedgeSpan_apply _ _ _ (by omega : 2 * 0 + 2 * q = 2 * q),
    scalarUnit, wedgeTo_unit_left _ rfl]
  rfl

theorem wedgeForm_constant_scalarUnit {q : ℕ}
    (T : LocalProductCurrent n U q) (β : formSpan n q) (φ : 𝓓(U, ℝ)) :
    wedgeForm (by omega : 0 + q = q) T
      (contDiffOn_const (c := (β : RealForm n (2 * q)))) scalarUnit φ = T β φ := by
  rw [wedgeForm_apply_eq (by omega : 0 + q = q) T contDiffOn_const
    (fun _ _ => β.property) (fun _ : Unit => fun _ : ComplexModel n => (1 : ℝ))
    (fun _ => contDiffOn_const) (fun _ => β) (by intro _ _; simp) scalarUnit φ]
  simp only [Fintype.sum_unique, wedgeSpan_scalarUnit_left]
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply, mul_one]

/-- Native trace measures agree whenever their actual trace distributions
agree, even when the two currents have different bidimensions. -/
theorem traceMeasure_eq_of_trace_tests {q r : ℕ}
    {S : LocalProductCurrent n U q} {T : LocalProductCurrent n U r}
    (hS : IsPositive S) (hT : IsPositive T)
    (h : ∀ φ : 𝓓(U, ℝ), S (kahlerPower n q) φ = T (kahlerPower n r) φ) :
    hS.traceMeasure = hT.traceMeasure := by
  let := hS.isLocallyFiniteMeasure_traceMeasureOn
  let := hT.isLocallyFiniteMeasure_traceMeasureOn
  have he : hS.traceMeasureOn = hT.traceMeasureOn := by
    apply SmoothTestMeasureSeparation.Measure.eq_of_testFunction_integral_sub_eq_zero
    intro φ
    rw [hS.integral_traceMeasureOn, hT.integral_traceMeasureOn, h φ, sub_self]
  exact congrArg (fun μ : Measure U => μ.map (Subtype.val : U → ComplexModel n)) he

/-- The ordinary coordinate trace is precisely the native top measure of
wedging the actual positive current with the fixed coordinate Kähler form. -/
theorem powerTraceMeasure_kahler_eq_traceMeasure {q : ℕ}
    (T : LocalProductCurrent n U q) (hT : IsPositive T) :
    powerTraceMeasure T hT (contDiffOn_const (c := kahlerForm n))
      (fun _ _ => isSemipositiveOneOne_kahlerForm) = hT.traceMeasure := by
  apply traceMeasure_eq_of_trace_tests
  intro φ
  change wedgeForm (by omega : 0 + q = q) T
    (contDiffOn_const (c := formPower (kahlerForm n) q)) scalarUnit φ = _
  exact wedgeForm_constant_scalarUnit T (kahlerPower n q) φ

theorem isPositive_finite_sum {ι : Type*} [Fintype ι] {q : ℕ}
    (S : ι → LocalProductCurrent n U q) (hS : ∀ i, IsPositive (S i)) :
    IsPositive (∑ i, S i) := by
  classical
  intro κ _ γ φ hφ
  simp only [LinearMap.sum_apply, _root_.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg (fun i _ => hS i κ γ φ hφ)

/-- The actual trace measure commutes with a finite sum of genuine positive
currents. The measure equality is proved by their native smooth tests. -/
theorem traceMeasure_finite_sum {ι : Type*} [Fintype ι] {q : ℕ}
    (S : ι → LocalProductCurrent n U q) (hS : ∀ i, IsPositive (S i)) :
    (isPositive_finite_sum S hS).traceMeasure = ∑ i, (hS i).traceMeasure := by
  classical
  let hp := isPositive_finite_sum S hS
  let _ (i : ι) : IsLocallyFiniteMeasure (hS i).traceMeasureOn :=
    (hS i).isLocallyFiniteMeasure_traceMeasureOn
  let : IsLocallyFiniteMeasure (∑ i, (hS i).traceMeasureOn) :=
    Measure.isLocallyFiniteMeasure_finset_sum Finset.univ (fun i => (hS i).traceMeasureOn)
      (fun i _ => (hS i).isLocallyFiniteMeasure_traceMeasureOn)
  let := hp.isLocallyFiniteMeasure_traceMeasureOn
  have he : hp.traceMeasureOn = ∑ i, (hS i).traceMeasureOn := by
    apply SmoothTestMeasureSeparation.Measure.eq_of_testFunction_integral_sub_eq_zero
    intro φ
    have hint (i : ι) : Integrable (fun x : U => φ x) (hS i).traceMeasureOn := by
      let g : C_c(U, ℝ) := testFunctionToCompactlySupportedLM U φ
      exact (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).congr
        (Eventually.of_forall fun x => by simp [g])
    rw [integral_finsetSum_measure (fun i _ => hint i), hp.integral_traceMeasureOn]
    simp only [IsPositive.integral_traceMeasureOn, LinearMap.sum_apply, _root_.sum_apply,
      sub_self]
  change hp.traceMeasureOn.map Subtype.val = ∑ i, (hS i).traceMeasureOn.map Subtype.val
  rw [he, Measure.map_finset_sum' measurable_subtype_coe.aemeasurable]

def residualSplitTraceMeasure {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hminus : ∀ z ∈ U, IsSemipositiveOneOne (-σ z)) (s : Finset (Fin p)) :
    Measure (ComplexModel (m + 1)) :=
  (isPositive_residualSplitTerm p r T hT hTc v hv hσ hσ.neg hσ11 hfactor hminus s).traceMeasure

/-- The corrected ordinary trace is exactly the finite sum of the native
positive measures of Hermitian subproducts and fixed correction powers.
All positive subproducts and the measure equality are produced internally. -/
theorem btProduct_traceMeasure_eq_residualSplitTrace_sum
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hminus : ∀ z ∈ U, IsSemipositiveOneOne (-σ z)) :
    (isPositive_btProduct p r v T hT hTc hv).1.traceMeasure =
      ∑ s, residualSplitTraceMeasure p r T hT hTc v hv hσ hσ11 hfactor hminus s := by
  classical
  let S := fun s : Finset (Fin p) => residualSplitTerm p r v hσ hσ.neg T s
  have hS : ∀ s, IsPositive (S s) := fun s =>
    isPositive_residualSplitTerm p r T hT hTc v hv hσ hσ.neg hσ11 hfactor hminus s
  have he : (isPositive_btProduct p r v T hT hTc hv).1.traceMeasure =
      (isPositive_finite_sum S hS).traceMeasure := by
    apply traceMeasure_eq_of_trace_tests
    intro φ
    rw [btProduct_eq_sum_backgroundExpansion p r T hT hTc v hv hσ
      (fun z hz => oneOne_mem_formSpan (hσ11 z hz))]
  exact he.trans (traceMeasure_finite_sum S hS)

def correctionTraceForms (d r : ℕ) (gamma : ComplexModel n → RealForm n 2) :
    Fin (d + r) → ComplexModel n → RealForm n 2 :=
  Fin.append (fun _ => gamma) (fun _ _ => kahlerForm n)

theorem correctionTraceForms_smooth (d r : ℕ)
    {gamma : ComplexModel n → RealForm n 2} (hgamma : ContDiffOn ℝ ∞ gamma U) :
    ∀ i, ContDiffOn ℝ ∞ (correctionTraceForms d r gamma i) U := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [correctionTraceForms, Fin.append_left] using hgamma
  · simpa only [correctionTraceForms, Fin.append_right] using
      (contDiffOn_const (c := kahlerForm n) : ContDiffOn ℝ ∞ (fun _ : ComplexModel n => kahlerForm n) U)

theorem correctionTraceForms_positive (d r : ℕ)
    {gamma : ComplexModel n → RealForm n 2}
    (hgamma : ∀ x ∈ U, IsSemipositiveOneOne (gamma x)) :
    ∀ i x, x ∈ U → IsSemipositiveOneOne (correctionTraceForms d r gamma i x) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [correctionTraceForms, Fin.append_left] using hgamma
  · intro x _
    simpa only [correctionTraceForms, Fin.append_right] using
      (isSemipositiveOneOne_kahlerForm (n := n))

theorem correctionTraceForms_apply (d r : ℕ)
    (gamma : ComplexModel n → RealForm n 2) (x : ComplexModel n) :
    (fun i => correctionTraceForms d r gamma i x) =
      Fin.append (fun _ : Fin d => gamma x) (fun _ : Fin r => kahlerForm n) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [correctionTraceForms, Fin.append_left, Fin.append_right]

/-- Smooth-wedge association with the actual intermediate degree made
explicit. This also covers output degree zero without implicit degree casts. -/
theorem wedgeForm_wedge_of_degrees {s r k l m : ℕ}
    (h₁ : r + k = m) (h₂ : s + l = r) (h₃ : s + (k + l) = m)
    (T : LocalProductCurrent n U m)
    {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n (2 * l)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U)
    (hαS : ∀ x ∈ U, α x ∈ formSpan n k)
    (hβS : ∀ x ∈ U, β x ∈ formSpan n l) :
    wedgeForm h₂ (wedgeForm h₁ T hα) hβ = wedgeForm h₃ T
      (HermitianSmoothWedgeAssociation.contDiffOn_wedgeTo
        (by omega : 2 * k + 2 * l = 2 * (k + l)) hα hβ) := by
  subst r
  exact HermitianSmoothWedgeAssociation.wedgeForm_wedge h₁ T hα hβ hαS hβS

/-- The native ordinary trace of a correction wedge of a Hermitian
subproduct. All positivity is supplied by the actual coefficient current. -/
def correctionWedgeTraceMeasure (d r : ℕ) (T : LocalProductCurrent n U (d + r))
    (hT : IsPositive T) {gamma : ComplexModel n → RealForm n 2}
    (hgamma : ContDiffOn ℝ ∞ gamma U)
    (hgammaP : ∀ x ∈ U, IsSemipositiveOneOne (gamma x)) : Measure (ComplexModel n) :=
  (isPositive_wedgeForm (by omega : r + d = d + r) hT (contDiffOn_formPower hgamma d)
    (fun x hx => formPower_mem_spCone (hgammaP x hx) d)).traceMeasure

/-- The ordinary trace of the correction wedge is exactly the mixed trace
with correction factors followed by the fixed coordinate Kähler factors. -/
theorem correctionWedgeTraceMeasure_eq_mixedTraceMeasure (d r : ℕ)
    (T : LocalProductCurrent n U (d + r)) (hT : IsPositive T)
    {gamma : ComplexModel n → RealForm n 2} (hgamma : ContDiffOn ℝ ∞ gamma U)
    (hgammaP : ∀ x ∈ U, IsSemipositiveOneOne (gamma x)) :
    correctionWedgeTraceMeasure d r T hT hgamma hgammaP =
      mixedTraceMeasure T hT (correctionTraceForms d r gamma)
        (correctionTraceForms_smooth d r hgamma) (correctionTraceForms_positive d r hgammaP) := by
  let W := wedgeForm (by omega : r + d = d + r) T (contDiffOn_formPower hgamma d)
  have hW : IsPositive W := isPositive_wedgeForm (by omega : r + d = d + r) hT
    (contDiffOn_formPower hgamma d) (fun x hx => formPower_mem_spCone (hgammaP x hx) d)
  change hW.traceMeasure = _
  rw [← powerTraceMeasure_kahler_eq_traceMeasure W hW]
  apply traceMeasure_eq_of_trace_tests
  intro φ
  change wedgeForm (by omega : 0 + r = r)
      (wedgeForm (by omega : r + d = d + r) T (contDiffOn_formPower hgamma d))
      (contDiffOn_formPower (contDiffOn_const (c := kahlerForm n)) r) scalarUnit φ = _
  rw [wedgeForm_wedge_of_degrees (by omega : r + d = d + r)
    (by omega : 0 + r = r) (by omega : 0 + (d + r) = d + r) T
    (contDiffOn_formPower hgamma d) (contDiffOn_formPower (contDiffOn_const (c := kahlerForm n)) r)
    (fun x hx => mem_formSpan_of_mem_spCone (formPower_mem_spCone (hgammaP x hx) d))
    (fun _ _ => (kahlerPower n r).property)]
  apply congrArg (fun S : LocalProductCurrent n U 0 => S scalarUnit φ)
  apply wedgeForm_congr
  intro x _
  change wedgeTo (by omega : 2 * d + 2 * r = 2 * (d + r))
      (formPower (gamma x) d) (formPower (kahlerForm n) r) =
    wedgeProd (d + r) (fun i => correctionTraceForms d r gamma i x)
  rw [correctionTraceForms_apply, formPower_eq_wedgeProd, formPower_eq_wedgeProd,
    wedgeProd_append]

/-- Every corrected ordinary trace is bounded by the actual Hermitian trace
of the selected Hermitian subproduct. Both fixed correction and coordinate
trace factors are replaced, with no closedness condition on the subproduct. -/
theorem correctionWedgeTraceMeasure_le_powerTraceMeasure (d r : ℕ)
    (T : LocalProductCurrent n U (d + r)) (hT : IsPositive T)
    {gamma omega : ComplexModel n → RealForm n 2}
    (hgamma : ContDiffOn ℝ ∞ gamma U) (homega : ContDiffOn ℝ ∞ omega U)
    (hgammaP : ∀ x ∈ U, IsSemipositiveOneOne (gamma x))
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x)) (C : NNReal)
    (hgammaDom : ∀ x ∈ U, IsSemipositiveOneOne ((C : ℝ) • omega x - gamma x))
    (hcoordinateDom : ∀ x ∈ U, IsSemipositiveOneOne ((C : ℝ) • omega x - kahlerForm n)) :
    correctionWedgeTraceMeasure d r T hT hgamma hgammaP ≤
      C ^ (d + r) • powerTraceMeasure T hT homega homegaP := by
  rw [correctionWedgeTraceMeasure_eq_mixedTraceMeasure]
  apply mixedTraceMeasure_le_powerTraceMeasure
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [correctionTraceForms, Fin.append_left] using hgammaDom
  · simpa only [correctionTraceForms, Fin.append_right] using hcoordinateDom

/-- The selected genuine Hermitian subproduct, transported only along the
displayed equality of its native complementary degree. -/
def selectedBackgroundCurrent (p r : ℕ) (v : Fin p → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (T : LocalProductCurrent n U (r + p)) (s : Finset (Fin p)) :
    LocalProductCurrent n U (p - s.card + r) := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  exact castLPC (by omega : r + (p - s.card) = p - s.card + r)
    (backgroundExpansion s.card (r + (p - s.card))
      (fun i => v (s.orderEmbOfFin rfl i)) hσ
      (castLPC (by omega : r + p = r + (p - s.card) + s.card) T))

theorem isPositive_selectedBackgroundCurrent
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (s : Finset (Fin p)) : IsPositive (selectedBackgroundCurrent p r v hσ T s) := by
  unfold selectedBackgroundCurrent
  apply isPositive_castLPC
  exact isPositive_backgroundExpansion s.card (r + (p - s.card)) _
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) _ (fun i => hv _)
    hσ hσ11 (fun i => hfactor _)

theorem residualSplitTraceMeasure_eq_correctionWedgeTraceMeasure
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hminus : ∀ z ∈ U, IsSemipositiveOneOne (-σ z)) (s : Finset (Fin p)) :
    residualSplitTraceMeasure p r T hT hTc v hv hσ hσ11 hfactor hminus s =
      correctionWedgeTraceMeasure (p - s.card) r (selectedBackgroundCurrent p r v hσ T s)
        (isPositive_selectedBackgroundCurrent p r T hT hTc v hv hσ hσ11 hfactor s) hσ.neg hminus := by
  apply traceMeasure_eq_of_trace_tests
  intro φ
  change residualSplitTerm p r v hσ hσ.neg T s (kahlerPower (m + 1) r) φ =
    wedgeForm (by omega : r + (p - s.card) = p - s.card + r)
      (selectedBackgroundCurrent p r v hσ T s) (contDiffOn_formPower hσ.neg (p - s.card))
      (kahlerPower (m + 1) r) φ
  unfold residualSplitTerm selectedBackgroundCurrent
  rw [SGPT.PSH.HermitianComparisonOneFactor.wedgeForm_castLPC
    (by omega : r + (p - s.card) = p - s.card + r) rfl _
    (contDiffOn_formPower hσ.neg (p - s.card))]
  apply congrArg (fun S : LocalProductCurrent (m + 1) U r => S (kahlerPower (m + 1) r) φ)
  apply wedgeForm_congr
  intro x _
  exact (formPower_eq_wedgeProd (-σ x) (p - s.card)).symm

/-- The actual corrected ordinary BT trace is dominated by the finite sum
of genuine lower Hermitian trace measures. Positivity, subset splitting,
and smooth coordinate-to-Hermitian domination are all proved internally. -/
theorem btProduct_traceMeasure_le_hermitian_trace_sum
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ omega : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (homega : ContDiffOn ℝ ∞ omega U)
    (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hminus : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    (homegaP : ∀ x ∈ U, IsSemipositiveOneOne (omega x)) (C : NNReal)
    (hgammaDom : ∀ x ∈ U, IsSemipositiveOneOne ((C : ℝ) • omega x - -σ x))
    (hcoordinateDom : ∀ x ∈ U, IsSemipositiveOneOne ((C : ℝ) • omega x - kahlerForm (m + 1))) :
    (isPositive_btProduct p r v T hT hTc hv).1.traceMeasure ≤
      ∑ s : Finset (Fin p), C ^ (p - s.card + r) •
        powerTraceMeasure (selectedBackgroundCurrent p r v hσ T s)
          (isPositive_selectedBackgroundCurrent p r T hT hTc v hv hσ hσ11 hfactor s)
          homega homegaP := by
  classical
  rw [btProduct_traceMeasure_eq_residualSplitTrace_sum p r T hT hTc v hv hσ hσ11 hfactor hminus]
  apply Finset.sum_le_sum
  intro s _
  rw [residualSplitTraceMeasure_eq_correctionWedgeTraceMeasure]
  exact correctionWedgeTraceMeasure_le_powerTraceMeasure (p - s.card) r _ _
    hσ.neg homega hminus homegaP C hgammaDom hcoordinateDom

end SGPT.PSH.HermitianComparisonLowerTrace
