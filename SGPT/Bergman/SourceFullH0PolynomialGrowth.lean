import SGPT.Bergman.SourcePolynomialSectionDimension
import SGPT.Bergman.SourceAuxiliaryProbabilityVolume

/-!
# FullH0PolynomialGrowth

Polynomial growth `dim H⁰(X, L^k ⊗ T ⊗ I(kφ)) ≤ C kⁿ` and `dim H⁰(X, L^k ⊗ T) ≤ C kⁿ` for smooth Hermitian metrics on a compact Kähler manifold (used in source `lma:BML` in place of `thm:DXmain1`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- All degrees at zero POTENTIAL give the true unit ideal, by the existing
actual positive-exponent zero-potential integrability producer. This is not
the earlier degree-zero theorem. -/
theorem sourceDegreeMultiplierIdeal_zeroPotential (k : ℕ) :
    sourceDegreeMultiplierIdeal (n := n) k (fun _ : X => (0 : EReal)) =
      originalUnitGermIdeal (n := n) (X := X) := by
  unfold sourceDegreeMultiplierIdeal
  simp only [mul_zero]
  exact zeroPotentialMultiplier_eq_unit (n := n) one_pos

/-- Actual original whole-stalk membership at zero potential is ALL full H0,
proved through the existing genuine preferred-coefficient criterion. -/
theorem fullHolomorphicZeroPotentialSections_eq_top
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) :
    fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k (fun _ : X => (0 : EReal))) = ⊤ := by
  rw [sourceDegreeMultiplierIdeal_zeroPotential]
  apply Submodule.eq_top_iff'.mpr
  intro s
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L T k).Fiber
    _ originalUnitGermIdeal_isCoherent s]
  intro x
  exact originalSectionCoefficient_holomorphicAt (n := n) (twistedPower L T k).Fiber
    (preferredOriginalFrame (twistedPower L T k).Fiber x) s
    (mem_baseSet_trivializationAt ℂ (twistedPower L T k).Fiber x)

/-- The actual literal Γ isomorphism gives the genuine full-H0 dimension
identity at zero potential, including zero-dimensional and zero spaces. -/
theorem literalZeroPotential_finrank_eq_fullH0
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k (fun _ : X => (0 : EReal))) =
      Module.finrank ℂ (twistedSections L T k) := by
  have h := (literalTwistedMultiplierSectionEquiv L T k (fun _ : X => (0 : EReal))).finrank_eq
  rw [fullHolomorphicZeroPotentialSections_eq_top, finrank_top] at h
  exact h

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Actual source Kähler geometry manufactures the auxiliary probability
internally; literal multiplier-section growth has NO auxiliary measure input. -/
theorem exists_source_literal_multiplier_dimension_bound
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ φ : X → EReal,
      (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ) ≤ C * (k : ℝ) ^ n :=
  exists_literal_multiplier_dimension_bound L T hL hT (sourceAuxiliaryProbabilityVolume omega)
    (sourceAuxiliaryProbabilityVolume_smoothPositive omega)

/-- Genuine full original H0 polynomial upper growth, obtained from the
actual zero-potential unit-ideal readback and the internally produced trace
bound; no finiteness, growth or positive-mass premise is supplied. -/
theorem exists_full_twisted_section_dimension_bound
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      (Module.finrank ℂ (twistedSections L T k) : ℝ) ≤ C * (k : ℝ) ^ n := by
  obtain ⟨C, hC, hd⟩ := exists_source_literal_multiplier_dimension_bound L T hL hT omega
  refine ⟨C, hC, fun k hk => ?_⟩
  have h := hd k hk (fun _ : X => (0 : EReal))
  rwa [literalZeroPotential_finrank_eq_fullH0] at h

end SGPT.Bergman.PolynomialH0Growth
