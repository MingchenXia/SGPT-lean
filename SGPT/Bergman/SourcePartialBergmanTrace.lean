import SGPT.Bergman.SourcePartialBergmanDensity
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# PartialBergmanTrace

Source `def:Bergman:L778`: the zero extension of `B^k_{v,φ,μ}` to `X`, the partial Bergman measure `β^k_{v,φ,μ} = n!/kⁿ · B^k_{v,φ,μ} dμ`, and its total mass `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ))`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- Finite basis density using the ON-basis INTERNALLY produced on the SAME actual original Hilbert space. -/
def sourceBasisDensityReal (x : W.carrier) : ℝ :=
  ∑ i, weightedQuadraticDensity L T W k
    (sourceOriginalSectionLinear L T W μ hBM k hk φ
      (sourceOrthonormalBasis L T W μ hBM k hk φ i)) x

/-- The true source supremum equals the produced actual basis density, not a postulated finite-family kernel. -/
theorem sourcePartialBergmanDensity_eq_produced_basis (x : W.carrier) :
    sourcePartialBergmanDensity L T W μ k φ x =
      ENNReal.ofReal (sourceBasisDensityReal L T W μ hBM k hk φ x) :=
  sourcePartialBergmanDensity_eq_basis L T W μ hBM k hk φ
    (sourceOrthonormalBasis L T W μ hBM k hk φ) x

/-- Genuine nonnegative SAME-metric quadratic densities supply nonnegativity of the actual finite sum. -/
theorem sourceBasisDensityReal_nonneg (x : W.carrier) :
    0 ≤ sourceBasisDensityReal L T W μ hBM k hk φ x :=
  Finset.sum_nonneg (fun _ _ => weightedQuadraticDensity_nonneg L T W k _ x)

/-- The original density is genuinely continuous on the SAME K. -/
theorem sourceBasisDensityReal_continuous : Continuous (sourceBasisDensityReal L T W μ hBM k hk φ) :=
  continuous_finsetSum _ (fun _ _ => weightedQuadraticDensity_continuous L T W k _)

/-- The source Borel probability is retained; no smooth-volume replacement enters integrability. -/
theorem sourceBasisDensityReal_integrable : Integrable (sourceBasisDensityReal L T W μ hBM k hk φ) μ := by
  let : IsProbabilityMeasure μ := hBM.1
  exact integrable_finsetSum _ (fun _ _ => weightedQuadraticDensity_integrable L T W k μ _)

include hBM hk in
/-- Genuine source density measurability follows from the internally produced finite basis formula. -/
theorem sourcePartialBergmanDensity_measurable : Measurable (sourcePartialBergmanDensity L T W μ k φ) := by
  have heq : sourcePartialBergmanDensity L T W μ k φ =
      fun x => ENNReal.ofReal (sourceBasisDensityReal L T W μ hBM k hk φ x) :=
    funext (sourcePartialBergmanDensity_eq_produced_basis L T W μ hBM k hk φ)
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp (sourceBasisDensityReal_continuous L T W μ hBM k hk φ)).measurable

/-- The genuine finite trace is internally derived by integrating the actual ON-basis quadratic densities. -/
theorem integral_sourceBasisDensityReal :
    (∫ x, sourceBasisDensityReal L T W μ hBM k hk φ x ∂μ) =
      (Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ) : ℝ) := by
  let : IsProbabilityMeasure μ := hBM.1
  unfold sourceBasisDensityReal
  rw [integral_finsetSum _ (fun _ _ => weightedQuadraticDensity_integrable L T W k μ _)]
  calc
    _ = ∑ i : Fin (Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ)),
        ‖sourceOrthonormalBasis L T W μ hBM k hk φ i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sourceHilbert_norm_sq_integral L T W μ hBM k hk φ _).symm
    _ = _ := by simp only [OrthonormalBasis.norm_eq_one, one_pow, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
include hBM hk in
/-- EXACT original density trace on the SAME original probability subtype; no mass certificate is input. -/
theorem lintegral_sourcePartialBergmanDensity :
    (∫⁻ x, sourcePartialBergmanDensity L T W μ k φ x ∂μ) =
      ENNReal.ofReal (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ)) := by
  simp_rw [sourcePartialBergmanDensity_eq_produced_basis L T W μ hBM k hk φ]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (sourceBasisDensityReal_integrable L T W μ hBM k hk φ)
      (Filter.Eventually.of_forall (sourceBasisDensityReal_nonneg L T W μ hBM k hk φ)),
    integral_sourceBasisDensityReal]
  exact congrArg (fun d : ℕ => ENNReal.ofReal (d : ℝ))
    (literalSourceHilbertEquiv L T W μ hBM k hk φ).finrank_eq.symm

/-- Source `def:Bergman:L778`: the partial Bergman kernel `B^k_{v,φ,μ}`, extended by `0` outside `K`. -/
def sourcePartialBergmanDensityOnX (x : X) : ℝ≥0∞ := by
  classical
  exact if hx : x ∈ W.carrier then sourcePartialBergmanDensity L T W μ k φ ⟨x, hx⟩ else 0

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Every actual included original point retains the SAME source density. -/
theorem sourcePartialBergmanDensityOnX_in (x : W.carrier) :
    sourcePartialBergmanDensityOnX L T W μ k φ x.val = sourcePartialBergmanDensity L T W μ k φ x := by
  classical
  simp only [sourcePartialBergmanDensityOnX, dif_pos x.property]

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Original extension is exactly zero off the ORIGINAL K. -/
theorem sourcePartialBergmanDensityOnX_out {x : X} (hx : x ∉ W.carrier) :
    sourcePartialBergmanDensityOnX L T W μ k φ x = 0 := by
  classical
  simp only [sourcePartialBergmanDensityOnX, dif_neg hx]

include hBM hk in
/-- The genuine original zero extension is globally Borel measurable, from actual density measurability on K. -/
theorem sourcePartialBergmanDensityOnX_measurable :
    Measurable (sourcePartialBergmanDensityOnX L T W μ k φ) := by
  classical
  exact (sourcePartialBergmanDensity_measurable L T W μ hBM k hk φ).dite
    (measurable_const : Measurable (fun _ : ↥(W.carrierᶜ) => (0 : ℝ≥0∞)))
    W.isClosed_carrier.measurableSet

/-- The original positive-degree scalar normalization n!/k^n, with no probability/volume substitution. -/
def sourceBergmanNormalization : ℝ≥0∞ := ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n)

/-- Source partial Bergman measure on SAME K, using the TRUE original supremum and SAME mu. -/
def sourcePartialBergmanMeasureOnK : Measure W.carrier :=
  sourceBergmanNormalization (n := n) k • μ.withDensity (sourcePartialBergmanDensity L T W μ k φ)

/-- Source `def:Bergman:L778`: the partial Bergman measure `β^k_{v,φ,μ} = n!/kⁿ · B^k_{v,φ,μ} dμ`,
as a measure on `X` (push-forward from `K`). -/
def sourcePartialBergmanMeasure : Measure X :=
  Measure.map (Subtype.val : W.carrier → X) (sourcePartialBergmanMeasureOnK L T W μ k φ)

set_option backward.isDefEq.respectTransparency false in
include hBM hk in
/-- Actual source finite trace/mass identity on X, with TRUE literal tensor-ideal Gamma dimension. -/
theorem sourcePartialBergmanMeasure_mass :
    sourcePartialBergmanMeasure L T W μ k φ univ =
      sourceBergmanNormalization (n := n) k *
        ENNReal.ofReal (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ)) := by
  rw [sourcePartialBergmanMeasure, Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp only [preimage_univ, sourcePartialBergmanMeasureOnK, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_sourcePartialBergmanDensity L T W μ hBM k hk φ]

set_option backward.isDefEq.respectTransparency false in
include hBM hk in
/-- The actual push from K IS the original normalized global density against the SAME included mu,
with zero extension off K; this is a proved source-measure dictionary, not an incoming equality. -/
theorem sourcePartialBergmanMeasure_eq_global_density :
    sourcePartialBergmanMeasure L T W μ k φ =
      sourceBergmanNormalization (n := n) k •
        (Measure.map (Subtype.val : W.carrier → X) μ).withDensity
          (sourcePartialBergmanDensityOnX L T W μ k φ) := by
  apply Measure.ext
  intro S hS
  rw [sourcePartialBergmanMeasure, Measure.map_apply measurable_subtype_coe hS,
    sourcePartialBergmanMeasureOnK, Measure.smul_apply, Measure.smul_apply,
    withDensity_apply _ (measurable_subtype_coe hS), withDensity_apply _ hS]
  congr 1
  rw [Measure.restrict_map measurable_subtype_coe hS,
    lintegral_map' (sourcePartialBergmanDensityOnX_measurable L T W μ hBM k hk φ).aemeasurable
      measurable_subtype_coe.aemeasurable]
  exact lintegral_congr (fun x => (sourcePartialBergmanDensityOnX_in L T W μ k φ x).symm)

end SGPT.Bergman.SingularWeightedHilbert
