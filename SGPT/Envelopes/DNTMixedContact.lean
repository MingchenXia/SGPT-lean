import SGPT.Okounkov.TranscendentalWNRegDNTEnvelope
import SGPT.Envelopes.SourceMixedEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.MixedProductIntegralPolarization
import SGPT.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler

/-!
# The Di Nezza–Trapani contact formula for mixed products (smooth obstacles)

Source `thm:DNTcontact` (chapter_npp): let `X` be a compact Kähler manifold of dimension `n`,
`θ₁, …, θₙ` closed real `(1,1)`-forms, `φᵢ ∈ PSH(X, θᵢ)` and `fᵢ` functions with `φᵢ ≤ fᵢ`.
With `E = ⋂ᵢ {φᵢ = fᵢ}`,

  `𝟙_E θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ} = 𝟙_E θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`.

This file proves it for **smooth** `fᵢ` (the book allows `fᵢ ∈ C^{1,1̄}`), following the book's
Step 1: polarization from the diagonal case, which is
`TranscendentalWNReg.diagonalPotentialMeasure_restrict_contact_eq`.

* `topRatio_slotForm_nonneg_of_mixedContact`: on `E` every slot `θᵢ + ddᶜfᵢ` is semipositive
  (`TranscendentalWN.coefficientSemipositive_of_contact`), so the density of the smooth mixed
  product `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}` against `ωⁿ` is `≥ 0` there; hence the measure
  `topFormMeasure ω (θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ})` (density truncated at `0`) restricted to `E` is the
  genuine signed measure of the smooth top form restricted to `E`
  (`topFormMeasure_slotForm_restrict_mixedContact_toReal`).
* `topRatio_formPow_subsetSum`: for `S ⊆ {1, …, n}` and `θ_S = ∑_{i∈S} θᵢ`, `f_S = ∑_{i∈S} fᵢ`,
  the density of `(θ_S + ddᶜf_S)ⁿ` is `∑_{g : [n] → S}` of the densities of
  `θ_{g(1),f_{g(1)}} ∧ ⋯ ∧ θ_{g(n),f_{g(n)}}` (multilinear expansion of the smooth mixed density).
* `globalMixedMeasure_restrict_mixedContact_eq` (native) and
  `sourceMixedNonPluripolarMeasure_restrict_mixedContact_eq` (source-facing): the theorem.

## Proof (the book's Step 1)

For every `S`, `φ_S = ∑_{i∈S} φᵢ ∈ PSH(X, θ_S)`, `φ_S ≤ f_S` and `E ⊆ {φ_S = f_S}`, so the diagonal
case gives `𝟙_E (θ_S + ddᶜφ_S)ⁿ = 𝟙_E (θ_S + ddᶜf_S)ⁿ`.  Both sides expand over the maps
`g : [n] → S` (`MixedProductIntegralPolarization.diagonal_subsetSum_eq_sum_selected` for the
non-pluripolar side, `topRatio_formPow_subsetSum` for the smooth side).  Inclusion–exclusion over
`S` (`PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul`) isolates the bijective `g`, and
slot symmetry of both sides (`GlobalSlotPerm.globalMixedMeasure_perm`,
`actualMixedTopDensity_perm`) gives `n!` times the identity for `g = id`.  (The book extracts the
coefficient of `λ₁⋯λₙ` from the identity for `∑ λⱼθⱼ`, `λ ∈ ℝ_{>0}ⁿ`; with `λ` restricted to
indicator vectors of subsets this coefficient extraction is the inclusion–exclusion formula.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNT

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
open SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
open SGPT.Okounkov

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The common contact set -/

/-- The common contact set `⋂ᵢ {φᵢ = fᵢ}` of potentials `φᵢ` with real obstacles `fᵢ`. -/
def mixedContactSet (u : Fin n → M → EReal) (f : Fin n → M → ℝ) : Set M :=
  {x | ∀ i, u i x = (f i x : EReal)}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem mixedContactSet_eq_iInter (u : Fin n → M → EReal) (f : Fin n → M → ℝ) :
    mixedContactSet u f = ⋂ i, {x | u i x = (f i x : EReal)} := by
  ext x
  simp [mixedContactSet]

/-- The common contact set is closed. -/
theorem isClosed_mixedContactSet {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal)) :
    IsClosed (mixedContactSet u f) := by
  rw [mixedContactSet_eq_iInter]
  exact isClosed_iInter fun i => TranscendentalWN.isClosed_contact (hu i) (hf i) (hle i)

/-! ### Positivity of the smooth mixed density on the contact set -/

/-- **On the common contact set the smooth mixed product is nonnegative**: its density
`(θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}) / ωⁿ` is `≥ 0` at every point of `⋂ᵢ {φᵢ = fᵢ}`. -/
theorem topRatio_slotForm_nonneg_of_mixedContact (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    (g : Fin n → Fin n) {x : M} (hx : x ∈ mixedContactSet u f) :
    0 ≤ topRatio w.form.val
      (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j))) x := by
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz := e.val.map_source hxe
  have hsemi : ∀ i, IsSemipositiveOneOne ((θ i + ddcClosedForm (f i) (hf i)).val.coeff e (e.val x)) :=
    fun i => ⟨(θ i + ddcClosedForm (f i) (hf i)).2.2 e _ hz,
      TranscendentalWN.coefficientSemipositive_of_contact (θ i) (hu i) (hf i)
        (Eventually.of_forall (hle i)) (hx i) e hxe⟩
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff]
  exact div_nonneg (actualMixedTopDensity_nonneg fun j => hsemi (g j))
    (topDensity_formPow_pos w.isKahler.1 hz).le

/-! ### Multilinear expansion of the smooth densities -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The real-to-extended-real coercion commutes with finite sums. -/
theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ s, a i : ℝ) : EReal) = ∑ i ∈ s, (a i : EReal) :=
  map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) a s

/-- The coefficients of `∑_{i∈S} 1 • αᵢ` are the sums of the coefficients. -/
theorem sumForm_one_coeff {ι : Type*} (S : Finset ι) (α : ι → ClosedRealOneOneForm n M)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (sumForm S (fun _ => (1 : ℝ)) α).val.coeff e z = ∑ i ∈ S, (α i).val.coeff e z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sumForm]
  | insert a s ha ih =>
    simp only [sumForm] at ih ⊢
    rw [Finset.sum_insert ha, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      one_smul, ih, Finset.sum_insert ha]

/-- A finite sum of chart-smooth functions is chart-smooth. -/
theorem chartSmooth_finset_sum {ι : Type*} (S : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) :
    ChartSmooth (n := n) (fun x => ∑ i ∈ S, f i x) :=
  fun e => ContDiffOn.sum fun i _ => hf i e

/-- The coefficients of `θ_S + ddᶜf_S` are the sums of the coefficients of the `θᵢ + ddᶜfᵢ`,
`i ∈ S`. -/
theorem coeff_subsetSum_add_ddc {ι : Type*} (S : Finset ι) (θ : ι → ClosedRealOneOneForm n M)
    {f : ι → M → ℝ} (hf : ∀ i, ChartSmooth (n := n) (f i))
    (hfS : ChartSmooth (n := n) (fun x => ∑ i ∈ S, f i x)) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (sumForm S (fun _ => (1 : ℝ)) θ + ddcClosedForm (fun x => ∑ i ∈ S, f i x) hfS).val.coeff e z =
      ∑ i ∈ S, (θ i + ddcClosedForm (f i) (hf i)).val.coeff e z := by
  rw [ClosedRealOneOneForm.coeff_add, sumForm_one_coeff, ddcClosedForm_coeff]
  simp only [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  rw [smoothDDC_sum S e.val.open_target (fun i _ => hf i e) hz, ← Finset.sum_add_distrib]

/-- **Multilinear expansion of the smooth densities.**  For `S ⊆ {1, …, n}`,
`(θ_S + ddᶜf_S)ⁿ = ∑_{g : [n] → S} θ_{g(1),f_{g(1)}} ∧ ⋯ ∧ θ_{g(n),f_{g(n)}}` (as densities
against `ωⁿ`). -/
theorem topRatio_formPow_subsetSum (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (S : Finset (Fin n))
    (hfS : ChartSmooth (n := n) (fun x => ∑ i ∈ S, f i x)) (x : M) :
    topRatio w.form.val
        (formPow (sumForm S (fun _ => (1 : ℝ)) θ + ddcClosedForm (fun x => ∑ i ∈ S, f i x) hfS).val
          n) x =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        topRatio w.form.val (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j))) x := by
  set e := complexChartAt (n := n) x with he
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  simp only [topRatio, chartRatio]
  rw [← Finset.sum_div]
  congr 1
  rw [← he, formPow_coeff, topDensity_formPower, ← actualMixedTopDensity_const,
    coeff_subsetSum_add_ddc S θ hf hfS e hz]
  simp_rw [topDensity_slotForm_coeff]
  rw [← actualMixedTopDensityMultilinear_apply,
    SymmetricMultilinearDiagonal.map_diagonal_sum actualMixedTopDensityMultilinear
      (fun i => (θ i + ddcClosedForm (f i) (hf i)).val.coeff e (e.val x)) S]
  rfl

/-! ### The theorem -/

section Measures

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [CompactSpace M] in
theorem measurable_ofReal_topRatio (w : KahlerBackground n M) (Φ : SmoothRealForm n M (2 * n)) :
    Measurable fun x => ENNReal.ofReal (topRatio w.form.val Φ x) :=
  ENNReal.measurable_ofReal.comp (continuous_topRatio w.isKahler.1 Φ).measurable

theorem isFiniteMeasure_topFormMeasure (w : KahlerBackground n M)
    (Φ : SmoothRealForm n M (2 * n)) : IsFiniteMeasure (TranscendentalWN.topFormMeasure w Φ) :=
  isFiniteMeasure_withDensity_ofReal (NefMixedMass.integrable_topRatio w Φ).2

/-- **The smooth mixed measure restricted to the contact set is the genuine signed measure**: for
measurable `A`, `(𝟙_E θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ})(A) = ∫_{A ∩ E} (θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}) / ωⁿ dωⁿ`
(the integral of the signed density; no truncation takes place on `E`). -/
theorem topFormMeasure_slotForm_restrict_mixedContact_toReal (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    ((TranscendentalWN.topFormMeasure w
        (slotForm fun i => θ i + ddcClosedForm (f i) (hf i))).restrict (mixedContactSet u f) A).toReal =
      ∫ x in A ∩ mixedContactSet u f,
        topRatio w.form.val (slotForm fun i => θ i + ddcClosedForm (f i) (hf i)) x
          ∂(kahlerVolume w) := by
  have hEm : MeasurableSet (mixedContactSet u f) :=
    (isClosed_mixedContactSet hu hf hle).measurableSet
  have hm := hA.inter hEm
  have hnn : 0 ≤ᵐ[(kahlerVolume w).restrict (A ∩ mixedContactSet u f)]
      fun x => topRatio w.form.val (slotForm fun i => θ i + ddcClosedForm (f i) (hf i)) x := by
    refine (ae_restrict_iff' hm).mpr (Eventually.of_forall fun x hx => ?_)
    exact topRatio_slotForm_nonneg_of_mixedContact w θ hu hf hle id hx.2
  rw [Measure.restrict_apply hA, TranscendentalWN.topFormMeasure, withDensity_apply _ hm,
    integral_eq_lintegral_of_nonneg_ae hnn
      (continuous_topRatio w.isKahler.1 _).aestronglyMeasurable]

/-- The smooth side of the subset identity: on measurable subsets of the contact set,
`(θ_S + ddᶜf_S)ⁿ` is the sum of the mixed measures of the slot selections `g : [n] → S`. -/
theorem positiveTopMeasure_subsetSum_apply (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    (S : Finset (Fin n)) (hfS : ChartSmooth (n := n) (fun x => ∑ i ∈ S, f i x))
    {A : Set M} (hA : MeasurableSet A) :
    TranscendentalWNReg.positiveTopMeasure w
        (sumForm S (fun _ => (1 : ℝ)) θ + ddcClosedForm (fun x => ∑ i ∈ S, f i x) hfS)
        (A ∩ mixedContactSet u f) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        TranscendentalWN.topFormMeasure w
          (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j)))
          (A ∩ mixedContactSet u f) := by
  have hEm : MeasurableSet (mixedContactSet u f) :=
    (isClosed_mixedContactSet hu hf hle).measurableSet
  have hm := hA.inter hEm
  simp only [TranscendentalWN.topFormMeasure, TranscendentalWNReg.positiveTopMeasure]
  rw [withDensity_apply _ hm]
  simp_rw [withDensity_apply _ hm]
  rw [← lintegral_finsetSum _ fun g _ => measurable_ofReal_topRatio w _]
  refine setLIntegral_congr_fun hm fun x hx => ?_
  rw [topRatio_formPow_subsetSum w θ hf S hfS x,
    ENNReal.ofReal_sum_of_nonneg fun g _ =>
      topRatio_slotForm_nonneg_of_mixedContact w θ hu hf hle g hx.2]

/-- **The subset identity**: for every `S ⊆ {1, …, n}` and measurable `A`,
`∑_{g : [n] → S} ⟨θ_{g(1),φ_{g(1)}} ∧ ⋯⟩(A ∩ E) = ∑_{g : [n] → S} (θ_{g(1),f_{g(1)}} ∧ ⋯)(A ∩ E)`,
from the diagonal contact formula for `θ_S`, `φ_S`, `f_S`. -/
theorem sum_selected_globalMixedMeasure_eq (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    (S : Finset (Fin n)) {A : Set M} (hA : MeasurableSet A) :
    ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        globalMixedMeasure (fun j => θ (g j)) (fun j => u (g j)) (fun j => (hu (g j)).1)
          (A ∩ mixedContactSet u f) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        TranscendentalWN.topFormMeasure w
          (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j)))
          (A ∩ mixedContactSet u f) := by
  set E := mixedContactSet u f with hE
  have hEm : MeasurableSet E := (isClosed_mixedContactSet (fun i => (hu i).1) hf hle).measurableSet
  have hfS := chartSmooth_finset_sum (n := n) S hf
  have hleS : ∀ x, sumPot S (fun _ => (1 : ℝ)) u x ≤ ((∑ i ∈ S, f i x : ℝ) : EReal) := by
    intro x
    simp only [sumPot, EReal.coe_one, one_mul]
    rw [ereal_coe_finset_sum]
    exact Finset.sum_le_sum fun i _ => hle i x
  have hES : E ⊆ {x | sumPot S (fun _ => (1 : ℝ)) u x = ((∑ i ∈ S, f i x : ℝ) : EReal)} := by
    intro x hx
    simp only [mem_ofPred_eq, sumPot, EReal.coe_one, one_mul]
    rw [ereal_coe_finset_sum]
    exact Finset.sum_congr rfl fun i _ => hx i
  have hdnt := TranscendentalWNReg.diagonalPotentialMeasure_restrict_contact_eq w
    (sumForm S (fun _ => (1 : ℝ)) θ)
    (MixedProductIntegralPolarization.isThetaPshPotential_subsetSum hu S) hfS hleS
  have h2 := congrArg (fun μ : Measure M => μ (A ∩ E)) hdnt
  simp only at h2
  rw [Measure.restrict_apply (hA.inter hEm), Measure.restrict_apply (hA.inter hEm),
    inter_eq_left.mpr (inter_subset_right.trans hES),
    MixedProductIntegralPolarization.diagonal_subsetSum_eq_sum_selected w hu S,
    Measure.finsetSum_apply] at h2
  rw [h2]
  exact positiveTopMeasure_subsetSum_apply w θ (fun i => (hu i).1) hf hle S hfS hA

/-- **The Di Nezza–Trapani contact formula for mixed products, smooth obstacles** (source
`thm:DNTcontact` with `fᵢ` smooth).  On a compact complex manifold with a Kähler form `ω`, for
closed real `(1,1)`-forms `θᵢ`, `φᵢ ∈ PSH(X, θᵢ)` and smooth `fᵢ ≥ φᵢ`, with
`E = ⋂ᵢ {φᵢ = fᵢ}`:

  `𝟙_E ⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩ = 𝟙_E θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`.

The right-hand side is the measure of the smooth top form `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}` (density against
`ωⁿ`, truncated at `0`; on `E` the density is `≥ 0`, `topRatio_slotForm_nonneg_of_mixedContact`). -/
theorem globalMixedMeasure_restrict_mixedContact_eq (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal)) :
    (globalMixedMeasure θ u fun i => (hu i).1).restrict (mixedContactSet u f) =
      (TranscendentalWN.topFormMeasure w
        (slotForm fun i => θ i + ddcClosedForm (f i) (hf i))).restrict (mixedContactSet u f) := by
  set E := mixedContactSet u f with hE
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  set μ : (Fin n → Fin n) → Measure M := fun g =>
    globalMixedMeasure (fun j => θ (g j)) (fun j => u (g j)) (fun j => (hu (g j)).1) with hμ
  set ν : (Fin n → Fin n) → Measure M := fun g =>
    TranscendentalWN.topFormMeasure w
      (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j))) with hν
  have hfin1 : ∀ g, μ g (A ∩ E) ≠ ⊤ := fun g => by
    have := globalMixedMeasure_isFiniteMeasure w (fun j => (hu (g j)).1)
    exact measure_ne_top _ _
  have hfin2 : ∀ g, ν g (A ∩ E) ≠ ⊤ := fun g => by
    have := isFiniteMeasure_topFormMeasure w
      (slotForm fun j => θ (g j) + ddcClosedForm (f (g j)) (hf (g j)))
    exact measure_ne_top _ _
  set d : (Fin n → Fin n) → ℝ := fun g => (μ g (A ∩ E)).toReal - (ν g (A ∩ E)).toReal with hd
  have hd0 : ∀ S : Finset (Fin n), ∑ g : Fin n → Fin n with ∀ j, g j ∈ S, d g = 0 := by
    intro S
    simp only [hd, Finset.sum_sub_distrib]
    rw [← ENNReal.toReal_sum fun g _ => hfin1 g, ← ENNReal.toReal_sum fun g _ => hfin2 g, sub_eq_zero]
    exact congrArg ENNReal.toReal (sum_selected_globalMixedMeasure_eq w θ hu hf hle S hA)
  have hperm : ∀ σ : Equiv.Perm (Fin n), d σ = d id := by
    intro σ
    have h1 : μ σ = μ id := GlobalSlotPerm.globalMixedMeasure_perm (fun i => (hu i).1) σ
    have h2 : ν σ = ν id := by
      simp only [hν, TranscendentalWN.topFormMeasure]
      congr 1
      funext x
      congr 1
      simp only [topRatio, chartRatio, topDensity_slotForm_coeff]
      congr 1
      exact actualMixedTopDensity_perm
        (fun i => (θ i + ddcClosedForm (f i) (hf i)).val.coeff (complexChartAt (n := n) x)
          ((complexChartAt (n := n) x).val x)) σ
    simp only [hd, h1, h2]
  have hpol := PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul d hperm
  simp only [hd0, mul_zero, Finset.sum_const_zero] at hpol
  have hdid : d id = 0 := by
    have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    exact (mul_eq_zero.mp hpol.symm).resolve_left hn
  have heq : (μ id (A ∩ E)).toReal = (ν id (A ∩ E)).toReal := sub_eq_zero.mp hdid
  exact (ENNReal.toReal_eq_toReal_iff' (hfin1 id) (hfin2 id)).mp heq

end Measures

/-! ### Source-facing statement -/

section Source

open SGPT.PSH.VariableComplexAtlas

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **`thm:DNTcontact` for smooth obstacles, source-facing form**: for source closed real
`(1,1)`-forms `θᵢ`, source `θᵢ`-psh `φᵢ` and smooth `fᵢ ≥ φᵢ`,
`𝟙_E θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ} = 𝟙_E θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}` on `E = ⋂ᵢ {φᵢ = fᵢ}`, the left side
being the source mixed non-pluripolar product `sourceMixedNonPluripolarMeasure`. -/
theorem sourceMixedNonPluripolarMeasure_restrict_mixedContact_eq (w : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, ChartSmooth (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal)) :
    (sourceMixedNonPluripolarMeasure θ u hu).restrict (mixedContactSet u f) =
      (TranscendentalWN.topFormMeasure w
        (slotForm fun i => atlasClosedFormToNative (θ i) + ddcClosedForm (f i) (hf i))).restrict
        (mixedContactSet u f) :=
  globalMixedMeasure_restrict_mixedContact_eq w (fun i => atlasClosedFormToNative (θ i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) hf hle

end Source

end SGPT.Envelopes.DNT
