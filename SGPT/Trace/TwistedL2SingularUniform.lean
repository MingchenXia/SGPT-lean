import SGPT.Trace.TwistedL2SingularLocalL2

/-!
# Uniform local `L²` bounds along an exhaustion

The actual weighted bound on an increasing family of open sets gives one
uniform unweighted bound on every compact set eventually contained off the
pole set. The section is patched by the fixed datum outside each open set;
this makes the weighted error identically zero there and lets the compact
estimate use one fixed constant for the whole sequence.

-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- One constant bounds the actual unweighted norms on a fixed compact set,
for all sufficiently late members of the original increasing exhaustion. -/
theorem exists_eventually_uniform_local_sq_bound
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {U : ℕ → Set X} (hUo : ∀ j, IsOpen (U j)) (hUm : Monotone U)
    {K : Set X} (hK : IsCompact K)
    (hKU : ∃ j₀, K \ {x | ψ x = ⊥} ⊆ U j₀)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hbound : ∀ j, (∫⁻ x in U j, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ j in atTop,
      (∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) ≤ B := by
  classical
  obtain ⟨B, hB, hcontrol⟩ := exists_uniform_local_sq_bound_of_weighted_difference
    hμ L hqpsh htop hcl ha0 hb0 hM hG hK (subset_univ _) hI
  obtain ⟨j₀, hj₀⟩ := hKU
  refine ⟨B, hB, eventually_atTop.mpr ⟨j₀, fun j hj => ?_⟩⟩
  let T' : (x : X) → L.Fiber x := fun x => if x ∈ U j then T j x else G x
  have hpatched : (∫⁻ x, ENNReal.ofReal
      (‖G x - T' x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I := by
    have heq : (fun x => ENNReal.ofReal
        (‖G x - T' x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x))) =
        (U j).indicator (fun x => ENNReal.ofReal
          (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x))) := by
      funext x
      by_cases hx : x ∈ U j
      · simp [T', hx]
      · simp [T', hx]
    rw [heq, lintegral_indicator (hUo j).measurableSet]
    exact hbound j
  have hKA : MeasurableSet (K \ {x | ψ x = ⊥}) :=
    hK.isClosed.measurableSet.diff hcl.measurableSet
  have heq : (∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) =
      ∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖T' x‖ ^ 2) ∂μ := by
    refine setLIntegral_congr_fun hKA fun x hx => ?_
    have hmem : x ∈ U j := hUm hj (hj₀ hx)
    simp [T', hmem]
  rw [heq]
  exact hcontrol T' (by simpa only [Measure.restrict_univ] using hpatched)


/-- The same uniform estimate holds on the entire compact set: the actual
analytic pole set is null for the original smooth positive volume. -/
theorem exists_eventually_uniform_local_sq_bound_including_poles
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    (hAn : IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {U : ℕ → Set X} (hUo : ∀ j, IsOpen (U j)) (hUm : Monotone U)
    {K : Set X} (hK : IsCompact K)
    (hKU : ∃ j₀, K \ {x | ψ x = ⊥} ⊆ U j₀)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hbound : ∀ j, (∫⁻ x in U j, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ j in atTop,
      (∫⁻ x in K, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) ≤ B := by
  obtain ⟨B, hB, hboundK⟩ := exists_eventually_uniform_local_sq_bound
    hμ L hqpsh htop hcl ha0 hb0 hM hG hUo hUm hK hKU hI T hbound
  have hA0 : μ {x | ψ x = ⊥} = 0 := measure_eq_zero_of_isLocallyAnalyticNull hμ hAn
  have hae : ∀ᵐ x ∂μ, x ∉ {x | ψ x = ⊥} := measure_eq_zero_iff_ae_notMem.mp hA0
  have hsets : K =ᵐ[μ] K \ {x | ψ x = ⊥} := by
    filter_upwards [hae] with x hx
    apply propext
    change x ∈ K ↔ x ∈ K \ {x | ψ x = ⊥}
    exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  have hrestrict : μ.restrict K = μ.restrict (K \ {x | ψ x = ⊥}) :=
    Measure.restrict_congr_set hsets
  refine ⟨B, hB, hboundK.mono fun j hj => ?_⟩
  rw [hrestrict]
  exact hj

end SGPT.Trace.TwistedL2
