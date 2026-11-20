import SGPT.Bergman.SourceWeightedEvaluation
import SGPT.Bergman.SourceWeightedHermitianIntegral

/-!
# PartialBergmanDensity

Source `def:Bergman:L778`: the partial Bergman kernel `B^k_{v,φ,μ}(x) = sup{|s(x)|² e^{-kv(x)} : s ∈ H⁰(X, L^k ⊗ T ⊗ I(kφ)), N^k_{v,μ}(s) ≤ 1}` on `K`, and its expression through an orthonormal basis.

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

/-- The genuine continuous evaluation retains the exact same actual point-norm formula. -/
theorem sourceWeightedEvaluation_continuous_norm (x : W.carrier)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ =
      weightedPointNorm (twistedPower L T k).Fiber W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) x := by
  change ‖sourceWeightedEvaluationLinear L T W μ hBM k hk φ x s‖ = _
  exact sourceWeightedEvaluation_norm L T W μ hBM k hk φ x s

/-- BOTH genuine maps from LITERAL original sheaf-tensor Gamma to the ACTUAL same-vector source Hilbert space. -/
def literalSourceHilbertEquiv :
    LiteralTwistedMultiplierSections L T k φ ≃ₗ[ℂ] SourceHilbertSections L T W μ hBM k hk φ :=
  (literalTwistedMultiplierSectionEquiv L T k φ).trans
    (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).symm

/-- Source `def:Bergman:L778`: the partial Bergman kernel
`B^k_{v,φ,μ}(x) = sup {|s(x)|² e^{-k v(x)} : s ∈ H⁰(X, L^k ⊗ T ⊗ I(kφ)), N^k_{v,μ}(s) ≤ 1}`
for `x ∈ K`, the supremum running over all global sections of the sheaf tensor product. -/
def sourcePartialBergmanDensity (x : W.carrier) : ℝ≥0∞ :=
  ⨆ s : LiteralTwistedMultiplierSections L T k φ,
    ⨆ (_ : weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
      (literalTwistedMultiplierSectionEquiv L T k φ s).val ≤ 1),
      weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k φ s).val x

set_option backward.isDefEq.respectTransparency false in
/-- The genuine literal Gamma/Hilbert maps retain BOTH the original admissible norm condition and original point density. -/
theorem sourcePartialBergmanDensity_eq_unitball (x : W.carrier) :
    sourcePartialBergmanDensity L T W μ k φ x =
      ⨆ s : SourceHilbertSections L T W μ hBM k hk φ, ⨆ (_ : ‖s‖ ≤ 1),
        ENNReal.ofReal (‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ ^ 2) := by
  apply (literalSourceHilbertEquiv L T W μ hBM k hk φ).toEquiv.iSup_congr
  intro s
  have hN : ENNReal.ofReal ‖literalSourceHilbertEquiv L T W μ hBM k hk φ s‖ =
      weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
        (literalTwistedMultiplierSectionEquiv L T k φ s).val :=
    sourceHilbert_ofReal_norm L T W μ hBM k hk φ _
  have hD : ENNReal.ofReal (‖sourceWeightedEvaluation L T W μ hBM k hk φ x
      (literalSourceHilbertEquiv L T W μ hBM k hk φ s)‖ ^ 2) =
      weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight
        (literalTwistedMultiplierSectionEquiv L T k φ s).val x := by
    rw [sourceWeightedEvaluation_continuous_norm]
    exact (weightedSectionDensity_eq_pointNorm_sq (twistedPower L T k).Fiber W k _ x).symm
  rw [← hD, ← hN, ENNReal.ofReal_le_one]
  rfl

/-- An actual original unit section attaining the produced evaluation norm, including the zero-space case. -/
theorem exists_source_unit_evaluation_max (x : W.carrier) :
    ∃ s : SourceHilbertSections L T W μ hBM k hk φ, ‖s‖ ≤ 1 ∧
      ‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ ^ 2 =
        ‖sourceEvaluationRiesz L T W μ hBM k hk φ x‖ ^ 2 := by
  let r := sourceEvaluationRiesz L T W μ hBM k hk φ x
  change ∃ s : SourceHilbertSections L T W μ hBM k hk φ, ‖s‖ ≤ 1 ∧
    ‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ ^ 2 = ‖r‖ ^ 2
  by_cases hr : r = 0
  · refine ⟨0, by simp, ?_⟩
    rw [map_zero, norm_zero, hr, norm_zero]
  · have hp : 0 < ‖r‖ := norm_pos_iff.mpr hr
    let c : ℂ := Complex.ofReal ‖r‖⁻¹
    let s := c • r
    have hc : ‖c‖ = ‖r‖⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    have hs : ‖s‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hp.ne']
    refine ⟨s, hs.le, ?_⟩
    have hself : sourceWeightedEvaluation L T W μ hBM k hk φ x r =
        Complex.ofReal (‖r‖ ^ 2) := by
      rw [← sourceEvaluationRiesz_inner]
      change inner ℂ r r = Complex.ofReal (‖r‖ ^ 2)
      calc
        _ = (RCLike.ofReal ‖r‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K r
        _ = _ := by norm_cast
    have hv : ‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ = ‖r‖ := by
      rw [map_smul, norm_smul, hc, hself, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
        pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    rw [hv]

/-- Genuine upper/lower source unit-ball comparison, hence the ORIGINAL supremum is finite and exact. -/
theorem sourcePartialBergmanDensity_eq_riesz (x : W.carrier) :
    sourcePartialBergmanDensity L T W μ k φ x =
      ENNReal.ofReal (‖sourceEvaluationRiesz L T W μ hBM k hk φ x‖ ^ 2) := by
  rw [sourcePartialBergmanDensity_eq_unitball L T W μ hBM k hk φ x]
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    apply ENNReal.ofReal_le_ofReal
    have hb : ‖sourceWeightedEvaluation L T W μ hBM k hk φ x s‖ ≤
        ‖sourceEvaluationRiesz L T W μ hBM k hk φ x‖ := by
      calc
        _ ≤ ‖sourceWeightedEvaluation L T W μ hBM k hk φ x‖ * ‖s‖ :=
          (sourceWeightedEvaluation L T W μ hBM k hk φ x).le_opNorm s
        _ ≤ ‖sourceWeightedEvaluation L T W μ hBM k hk φ x‖ * 1 :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
        _ = _ := by rw [mul_one, sourceEvaluationRiesz_norm]
    gcongr
  · obtain ⟨s, hs, heq⟩ := exists_source_unit_evaluation_max L T W μ hBM k hk φ x
    rw [← heq]
    exact le_iSup_of_le s (le_iSup_of_le hs le_rfl)

/-- Arbitrary actual ON-basis formula is PROVED by actual Riesz+Parseval; basis existence was already produced. -/
theorem sourcePartialBergmanDensity_eq_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (SourceHilbertSections L T W μ hBM k hk φ)) (x : W.carrier) :
    sourcePartialBergmanDensity L T W μ k φ x =
      ENNReal.ofReal (∑ i, weightedQuadraticDensity L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ (b i)) x) := by
  rw [sourcePartialBergmanDensity_eq_riesz L T W μ hBM k hk φ x]
  congr 1
  calc
    _ = ∑ i, ‖inner ℂ (sourceEvaluationRiesz L T W μ hBM k hk φ x) (b i)‖ ^ 2 :=
      (b.sum_sq_norm_inner_left _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sourceEvaluationRiesz_inner, sourceWeightedEvaluation_continuous_norm]
      rfl

end SGPT.Bergman.SingularWeightedHilbert
