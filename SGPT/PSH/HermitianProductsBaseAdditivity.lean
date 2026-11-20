import SGPT.PSH.HermitianProducts

/-!
# Additivity in the positive base of bounded Bedford--Taylor products

The underlying Borel multiplication is defined on positive currents and has
a junk value elsewhere. The identities here therefore prove additivity from
the actual coefficient measures on positive bases. They do not distribute
that operation over arbitrary signed-current decompositions. The coefficient
measure argument follows the private pullback-additivity proof in
`ActualPositiveCurrentPullbackAdditivity` and makes the resulting current and
Bedford--Taylor identities available independently of pullback geometry.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentPullback LocalCurrentPullbackDdc
  LocalBedfordTaylorForms LocalBedfordTaylorLocality BedfordTaylor
  LocalBedfordTaylorProducts
  LocalBedfordTaylorCollar
open scoped Topology Distributions ENNReal ContDiff

attribute [local instance] addCommGroupFormSpan

variable {n q : ℕ} {U : Opens (ComplexModel n)}

private theorem integrable_coefficient_weight {T : LocalProductCurrent n U q}
    (hT : IsPositive T) (γ : formSpan n q) {w : ComplexModel n → ℝ}
    (hw : IsTestWeight (U := U) w) : Integrable w (coeffMeasure hT γ) := by
  obtain ⟨M, hM⟩ := hw.bounded
  obtain ⟨K, hK, hKU, hsupp⟩ := hw.support
  exact integrable_of_bounded_of_vanishing (coeffMeasure_lt_top hT γ K hK hKU)
    hw.measurable hM hsupp

private theorem coefficient_measure_add {S T : LocalProductCurrent n U q}
    (hS : IsPositive S) (hT : IsPositive T) {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) :
    coeffMeasure (hS.add hT) γ = coeffMeasure hS γ + coeffMeasure hT γ := by
  apply eq_of_forall_testFunction_integral_eq (coeffMeasure_compl (hS.add hT) γ)
    (by simp only [Measure.add_apply, coeffMeasure_compl, zero_add])
    (coeffMeasure_lt_top (hS.add hT) γ)
    (fun K hK hKU => by
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.mpr ⟨coeffMeasure_lt_top hS γ K hK hKU,
        coeffMeasure_lt_top hT γ K hK hKU⟩)
  intro φ
  rw [integral_add_measure
    (integrable_coefficient_weight hS γ (isTestWeight_testFunction φ))
    (integrable_coefficient_weight hT γ (isTestWeight_testFunction φ)),
    integral_coeffMeasure (hS.add hT) hγ,
    integral_coeffMeasure hS hγ, integral_coeffMeasure hT hγ]
  rfl

private theorem integral_weighted_coefficient {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {γ : formSpan n q} (hγ : γ ∈ posCone n q)
    {f : ComplexModel n → ℝ} (hf : Measurable f)
    (hfb : IsLocallyBoundedOn f U) (φ : 𝓓(U, ℝ)) :
    ∫ x, φ x * f x ∂coeffMeasure hT γ = mulBorel T f γ φ := by
  rw [coeffMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_densityForm hT γ)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), mulBorel_apply hT hf hfb]
  apply integral_congr_ae
  filter_upwards [ae_densityForm_nonneg hT, densityForm_ae hT γ] with x hx heq
  rw [ENNReal.toReal_ofReal (hx γ hγ), smul_eq_mul, heq]
  ring

private theorem mulBorel_add_positive_form {S T : LocalProductCurrent n U q}
    (hS : IsPositive S) (hT : IsPositive T) {f : ComplexModel n → ℝ}
    (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (φ : 𝓓(U, ℝ)) :
    mulBorel (S + T) f γ φ = mulBorel S f γ φ + mulBorel T f γ φ := by
  rw [← integral_weighted_coefficient (hS.add hT) hγ hf hfb,
    coefficient_measure_add hS hT hγ,
    integral_add_measure
      (integrable_coefficient_weight hS γ (isTestWeight_mul φ hf hfb))
      (integrable_coefficient_weight hT γ (isTestWeight_mul φ hf hfb)),
    integral_weighted_coefficient hS hγ hf hfb,
    integral_weighted_coefficient hT hγ hf hfb]

/-- Actual multiplication by a locally bounded Borel function is additive
in positive current bases, on every constant form and compact test. -/
theorem mulBorel_add_current {S T : LocalProductCurrent n U q}
    (hS : IsPositive S) (hT : IsPositive T) {f : ComplexModel n → ℝ}
    (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel (S + T) f = mulBorel S f + mulBorel T f := by
  ext γ φ
  obtain ⟨C, hC, _, hpos⟩ := exists_orderUnit γ.2
  have hω : C • kahlerPower n q ∈ posCone n q :=
    smul_mem_spCone (formPower_mem_spCone isSemipositiveOneOne_kahlerForm q) hC
  have hγ : C • kahlerPower n q + γ ∈ posCone n q := hpos
  have h1 := mulBorel_add_positive_form hS hT hf hfb hγ φ
  have h0 := mulBorel_add_positive_form hS hT hf hfb hω φ
  simp only [map_add, _root_.add_apply] at h1
  change mulBorel (S + T) f γ φ = mulBorel S f γ φ + mulBorel T f γ φ
  linarith

/-- The bounded scalar `ddcMul` operation is additive in positive bases. -/
theorem ddcMul_add_current {r : ℕ} {S T : LocalProductCurrent n U (r + 1)}
    (hS : IsPositive S) (hT : IsPositive T) {u : ComplexModel n → ℝ}
    (hu : Measurable ((U : Set (ComplexModel n)).indicator u))
    (hub : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator u) U) :
    ddcMul (S + T) u = ddcMul S u + ddcMul T u := by
  rw [ddcMul, mulBorel_add_current hS hT hu hub, ddc_add]
  rfl

/-- The actual bounded Bedford--Taylor product is additive in positive
closed base currents. Every recursively generated base remains positive. -/
theorem btProduct_add_current : ∀ (p r : ℕ)
    (S T : LocalProductCurrent n U (r + p)),
    IsPositive S → IsPositive T →
    IsClosedAny (r + p) S → IsClosedAny (r + p) T →
    ∀ (u : Fin p → ComplexModel n → ℝ),
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    btProduct p r u (S + T) = btProduct p r u S + btProduct p r u T
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | p + 1, r, S, T, hS, hT, hSc, hTc, u, hu => by
    rw [btProduct_succ, btProduct_succ, btProduct_succ,
      ddcMul_add_current hS hT
        (measurable_indicator_of_isLocallyBoundedPshOn (hu (Fin.last p)))
        (isLocallyBoundedOn_indicator (hu (Fin.last p)))]
    obtain ⟨hS', hSc'⟩ := isPositive_ddcMul hS hSc (hu (Fin.last p))
    obtain ⟨hT', hTc'⟩ := isPositive_ddcMul hT hTc (hu (Fin.last p))
    exact btProduct_add_current p r _ _ hS' hT' hSc' hTc' (Fin.init u) (fun i => hu _)

/-- Wedging with a fixed arbitrary smooth form is additive in all currents,
including signed and nonclosed currents. -/
theorem wedgeForm_add_current {r k m : ℕ} (h : r + k = m)
    (S T : LocalProductCurrent n U m)
    {σ : ComplexModel n → RealForm n (2 * k)} (hσ : ContDiffOn ℝ ∞ σ U) :
    wedgeForm h (S + T) hσ = wedgeForm h S hσ + wedgeForm h T hσ := by
  classical
  ext γ φ
  simp only [wedgeForm_apply, LinearMap.add_apply, _root_.add_apply,
    Finset.sum_add_distrib]

private theorem castLPC_add {a b : ℕ} (h : a = b)
    (S T : LocalProductCurrent n U a) :
    castLPC h (S + T) = castLPC h S + castLPC h T := by
  subst h
  rfl

/-- Each literal subset term of the nonclosed-background expansion is
additive in positive closed bases. -/
theorem backgroundExpansionTerm_add_current (p r : ℕ)
    (S T : LocalProductCurrent n U (r + p)) (hS : IsPositive S) (hT : IsPositive T)
    (hSc : IsClosedAny (r + p) S) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    backgroundExpansionTerm p r u hσ (S + T) s =
      backgroundExpansionTerm p r u hσ S s + backgroundExpansionTerm p r u hσ T s := by
  classical
  dsimp only [backgroundExpansionTerm]
  rw [castLPC_add,
    btProduct_add_current s.card (r + (p - s.card)) _ _
      (isPositive_castLPC _ hS) (isPositive_castLPC _ hT)
      (isClosedAny_castLPC _ hSc) (isClosedAny_castLPC _ hTc)
      (fun i => u (s.orderEmbOfFin rfl i)) (fun i => hu _),
    wedgeForm_add_current]

/-- The actual finite expansion used for Hermitian products is additive in
positive closed base currents. No signed-current Borel recursion is assumed. -/
theorem backgroundExpansion_add_current (p r : ℕ)
    (S T : LocalProductCurrent n U (r + p)) (hS : IsPositive S) (hT : IsPositive T)
    (hSc : IsClosedAny (r + p) S) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    backgroundExpansion p r u hσ (S + T) =
      backgroundExpansion p r u hσ S + backgroundExpansion p r u hσ T := by
  classical
  unfold backgroundExpansion
  simp_rw [backgroundExpansionTerm_add_current p r S T hS hT hSc hTc u hu hσ]
  exact Finset.sum_add_distrib

end SGPT.PSH.HermitianProducts
