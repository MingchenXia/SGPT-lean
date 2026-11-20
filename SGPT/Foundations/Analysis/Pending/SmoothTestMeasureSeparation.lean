import SGPT.Foundations.Analysis.Pending.PositiveDistributionMeasure
import SGPT.Foundations.Analysis.RegularDistribution

/-!
# Separation and positivity of locally signed measures by smooth tests

Let `E` be a finite-dimensional real normed space and `Ω ⊆ E` open.  A locally signed Radon
measure on `Ω` whose total variation is finite on compact sets is the difference `σ = μ - ν` of two
locally finite positive measures (its Jordan decomposition), and `σ ≥ 0` means `ν ≤ μ`.  In that
encoding:

* `Measure.le_of_testFunction_integral_le` — **positivity by smooth tests**: if
  `∫ φ dν ≤ ∫ φ dμ` for every nonnegative `φ ∈ C_c^∞(Ω)`, then `ν ≤ μ`;
* `Measure.add_eq_add_of_testFunction_integral_sub_eq` — **separation**: if
  `μ₁ - ν₁` and `μ₂ - ν₂` have the same smooth test integrals then `μ₁ + ν₂ = μ₂ + ν₁`, i.e.
  `μ₁ - ν₁ = μ₂ - ν₂`.

No regularity of the measures is assumed.  *Proof.*  With `ξ = μ + ν` and the Radon--Nikodym
densities `f = dμ/dξ`, `g = dν/dξ`, the hypothesis says that the regular distribution of
`f - g` with respect to `ξ` is positive; positive regular distributions have nonnegative densities
(`Pending.ae_nonneg_of_positiveDistribution_integral`, through the Riesz representation), so
`g ≤ f` `ξ`-almost everywhere and `ν = g ξ ≤ f ξ = μ`.

Blueprint: `dist:smooth-test-measure-separation` (Demailly, *Complex analytic and differential
geometry*, III.1.B).  Sorry-free.
-/

noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped CompactlySupported Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E}

open Classical in
/-- Extension by zero of a function on `Ω`. -/
def extendZero (h : Ω → ℝ) : E → ℝ :=
  fun y => if hy : y ∈ Ω then h ⟨y, hy⟩ else 0

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem extendZero_val (h : Ω → ℝ) (x : Ω) : extendZero h (x : E) = h x := by
  unfold extendZero
  rw [dif_pos x.2]

omit [NormedSpace ℝ E] in
theorem measurableEmbedding_val : MeasurableEmbedding (Subtype.val : Ω → E) :=
  MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet

omit [NormedSpace ℝ E] in
/-- A locally integrable function on `Ω`, extended by zero, is locally integrable on `Ω` for the
pushed-forward measure. -/
theorem locallyIntegrableOn_extendZero {ξ : Measure Ω} {h : Ω → ℝ}
    (hh : LocallyIntegrable h ξ) :
    LocallyIntegrableOn (extendZero h) (Ω : Set E) (ξ.map Subtype.val) := by
  intro y hy
  obtain ⟨U, hU, hint⟩ := hh ⟨y, hy⟩
  refine ⟨Subtype.val '' U, ?_, ?_⟩
  · rw [mem_nhdsWithin]
    obtain ⟨V, hVU, hVo, hyV⟩ := mem_nhds_iff.mp hU
    refine ⟨Subtype.val '' V, Ω.isOpen.isOpenMap_subtype_val V hVo, ⟨⟨y, hy⟩, hyV, rfl⟩, ?_⟩
    rintro z ⟨⟨w, hwV, rfl⟩, -⟩
    exact ⟨w, hVU hwV, rfl⟩
  · rw [IntegrableOn, measurableEmbedding_val.restrict_map,
      measurableEmbedding_val.integrable_map_iff]
    have hpre : Subtype.val ⁻¹' (Subtype.val '' U) = U :=
      Subtype.val_injective.preimage_image U
    rw [hpre]
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    simp

/-- The regular distribution of a locally integrable density with respect to a measure on `Ω`. -/
def subtypeRegularDistribution (ξ : Measure Ω) (h : Ω → ℝ) (hh : LocallyIntegrable h ξ) :
    𝓓'(Ω, ℝ) :=
  regularDistribution (ξ.map Subtype.val) (extendZero h) (locallyIntegrableOn_extendZero hh)

theorem subtypeRegularDistribution_apply (ξ : Measure Ω) (h : Ω → ℝ)
    (hh : LocallyIntegrable h ξ) (φ : 𝓓(Ω, ℝ)) :
    subtypeRegularDistribution ξ h hh φ = ∫ x : Ω, φ x * h x ∂ξ := by
  rw [subtypeRegularDistribution, regularDistribution_apply,
    measurableEmbedding_val.integral_map]
  simp

variable [FiniteDimensional ℝ E]

/-- **Positivity by smooth tests** (`dist:smooth-test-measure-separation`).  For locally finite
measures `μ, ν` on an open subset of a finite-dimensional real space, if every nonnegative smooth
test function has `∫ φ dν ≤ ∫ φ dμ`, then `ν ≤ μ`: the locally signed measure `μ - ν` is
positive. -/
theorem Measure.le_of_testFunction_integral_le (μ ν : Measure Ω)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hle : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → (∫ x : Ω, φ x ∂ν) ≤ ∫ x : Ω, φ x ∂μ) :
    ν ≤ μ := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  set ξ : Measure Ω := μ + ν with hξ
  have : IsLocallyFiniteMeasure ξ := Measure.isLocallyFiniteMeasure_add μ ν
  have hμξ : μ ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνξ : ν ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hfμ : LocallyIntegrable (fun x : Ω => (μ.rnDeriv ξ x).toReal) ξ := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top
  have hfν : LocallyIntegrable (fun x : Ω => (ν.rnDeriv ξ x).toReal) ξ := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top
  set f : Ω → ℝ := fun x => (μ.rnDeriv ξ x).toReal - (ν.rnDeriv ξ x).toReal with hfdef
  have hf : LocallyIntegrable f ξ := hfμ.sub hfν
  have hfmeas : Measurable f :=
    (Measure.measurable_rnDeriv μ ξ).ennreal_toReal.sub
      (Measure.measurable_rnDeriv ν ξ).ennreal_toReal
  -- integrals against the densities are the integrals against the measures
  have hdens : ∀ (ρ : Measure Ω) [IsLocallyFiniteMeasure ρ], ρ ≪ ξ →
      ∀ φ : 𝓓(Ω, ℝ), ∫ x : Ω, φ x * (ρ.rnDeriv ξ x).toReal ∂ξ = ∫ x : Ω, φ x ∂ρ := by
    intro ρ _ hρ φ
    rw [← integral_rnDeriv_smul hρ]
    congr 1
    funext x
    rw [smul_eq_mul, mul_comm]
  have hrep : ∀ φ : 𝓓(Ω, ℝ),
      subtypeRegularDistribution ξ f hf φ = ∫ x : Ω, φ x * f x ∂ξ :=
    subtypeRegularDistribution_apply ξ f hf
  have hint : ∀ (ρ : Measure Ω) [IsLocallyFiniteMeasure ρ], ρ ≪ ξ →
      ∀ φ : 𝓓(Ω, ℝ), Integrable (fun x : Ω => φ x * (ρ.rnDeriv ξ x).toReal) ξ := by
    intro ρ _ hρ φ
    have hloc : LocallyIntegrable (fun x : Ω => (ρ.rnDeriv ξ x).toReal) ξ := by
      rw [locallyIntegrable_iff]
      intro K hK
      exact Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top
    have hcont : Continuous fun x : Ω => φ x := φ.continuous.comp continuous_subtype_val
    have hsupp : HasCompactSupport fun x : Ω => φ x := by
      let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
      have : (fun x : Ω => φ x) = g₀ := by funext x; simp [g₀]
      rw [this]
      exact g₀.hasCompactSupport
    simpa [smul_eq_mul, mul_comm] using hloc.integrable_smul_right_of_hasCompactSupport hcont hsupp
  have hpos : PositiveDistribution (subtypeRegularDistribution ξ f hf) := by
    intro φ hφ
    rw [hrep]
    have hsplit : ∫ x : Ω, φ x * f x ∂ξ =
        (∫ x : Ω, φ x * (μ.rnDeriv ξ x).toReal ∂ξ) -
          ∫ x : Ω, φ x * (ν.rnDeriv ξ x).toReal ∂ξ := by
      rw [← integral_sub (hint μ hμξ φ) (hint ν hνξ φ)]
      congr 1
      funext x
      simp only [hfdef]
      ring
    rw [hsplit, hdens μ hμξ φ, hdens ν hνξ φ, sub_nonneg]
    exact hle φ hφ
  have hae : ∀ᵐ x ∂ξ, 0 ≤ f x :=
    ae_nonneg_of_positiveDistribution_integral hpos ξ hfmeas hf hrep
  -- compare the densities
  have hle_dens : ∀ᵐ x ∂ξ, ν.rnDeriv ξ x ≤ μ.rnDeriv ξ x := by
    filter_upwards [hae, Measure.rnDeriv_lt_top μ ξ, Measure.rnDeriv_lt_top ν ξ]
      with x hx hμx hνx
    have hx' : (ν.rnDeriv ξ x).toReal ≤ (μ.rnDeriv ξ x).toReal := by
      simpa [hfdef, sub_nonneg] using hx
    exact (ENNReal.toReal_le_toReal hνx.ne hμx.ne).mp hx'
  calc ν = ξ.withDensity (ν.rnDeriv ξ) := (Measure.withDensity_rnDeriv_eq ν ξ hνξ).symm
    _ ≤ ξ.withDensity (μ.rnDeriv ξ) := withDensity_mono hle_dens
    _ = μ := Measure.withDensity_rnDeriv_eq μ ξ hμξ

/-- **Smooth test integrals determine a locally signed measure**
(`dist:smooth-test-measure-separation`, second assertion).  If `μ₁ - ν₁` and `μ₂ - ν₂` (all four
locally finite) have the same smooth test integrals, they are equal: `μ₁ + ν₂ = μ₂ + ν₁`. -/
theorem Measure.add_eq_add_of_testFunction_integral_sub_eq (μ₁ ν₁ μ₂ ν₂ : Measure Ω)
    [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure ν₁]
    [IsLocallyFiniteMeasure μ₂] [IsLocallyFiniteMeasure ν₂]
    (heq : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x : Ω, φ x ∂μ₁) - (∫ x : Ω, φ x ∂ν₁) = (∫ x : Ω, φ x ∂μ₂) - ∫ x : Ω, φ x ∂ν₂) :
    μ₁ + ν₂ = μ₂ + ν₁ := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hint : ∀ (ρ : Measure Ω) [IsLocallyFiniteMeasure ρ] (φ : 𝓓(Ω, ℝ)),
      Integrable (fun x : Ω => φ x) ρ := by
    intro ρ _ φ
    let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    have : (fun x : Ω => φ x) = g₀ := by funext x; simp [g₀]
    rw [this]
    exact g₀.continuous.integrable_of_hasCompactSupport g₀.hasCompactSupport
  have hadd : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x : Ω, φ x ∂(μ₁ + ν₂)) = ∫ x : Ω, φ x ∂(μ₂ + ν₁) := by
    intro φ
    rw [integral_add_measure (hint μ₁ φ) (hint ν₂ φ),
      integral_add_measure (hint μ₂ φ) (hint ν₁ φ)]
    linarith [heq φ]
  have : IsLocallyFiniteMeasure (μ₁ + ν₂) := Measure.isLocallyFiniteMeasure_add μ₁ ν₂
  have : IsLocallyFiniteMeasure (μ₂ + ν₁) := Measure.isLocallyFiniteMeasure_add μ₂ ν₁
  exact le_antisymm
    (Measure.le_of_testFunction_integral_le (μ₂ + ν₁) (μ₁ + ν₂) fun φ _ => (hadd φ).le)
    (Measure.le_of_testFunction_integral_le (μ₁ + ν₂) (μ₂ + ν₁) fun φ _ => (hadd φ).ge)

/-- The vanishing form: a locally signed measure all of whose smooth test integrals vanish is
zero (`μ = ν`). -/
theorem Measure.eq_of_testFunction_integral_sub_eq_zero (μ ν : Measure Ω)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (h0 : ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μ) - ∫ x : Ω, φ x ∂ν = 0) : μ = ν :=
  le_antisymm
    (Measure.le_of_testFunction_integral_le ν μ fun φ _ => by linarith [h0 φ])
    (Measure.le_of_testFunction_integral_le μ ν fun φ _ => by linarith [h0 φ])

end SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation
