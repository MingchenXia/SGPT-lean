import SGPT.Trace.TwistedL2MainLocalEnergy

/-!
# Euclidean test families as actual local test pieces

This is the finite-dimensional test-field conversion needed to apply the
existing Euclidean adjoint-pairing-to-weak-equation theorem. The integral
change-of-variables step is separate and remains to be proved.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The finite tuple of scalar test functions as a complex Euclidean vector. -/
def vectorTest (α : Fin n → ComplexModel n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun j => α j z)

@[simp] theorem vectorTest_apply (α : Fin n → ComplexModel n → ℂ)
    (z : ComplexModel n) (j : Fin n) : vectorTest α z j = α j z := rfl

namespace TwistedDatum

variable (T : TwistedDatum n X)

omit [BorelSpace X] in
/-- A finite family of Euclidean tests on the actual chart piece defines a
local test vector field with the same support control. -/
theorem isLocalTestField_vectorTest (c : ComplexChart n X) (e : AtlasFrame T.L)
    (α : Fin n → ComplexModel n → ℂ)
    (hα : ∀ j, IsTestFunctionOn (T.pieceDomain c e) (α j)) :
    IsLocalTestField T.L T.U c e (vectorTest α) := by
  have hK : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j => (hα j).2.1
  have hsupp : tsupport (vectorTest α) ⊆ ⋃ j, tsupport (α j) := by
    refine closure_minimal ?_ hK.isClosed
    intro z hz
    by_contra hzK
    have hz0 : ∀ j, α j z = 0 := fun j =>
      image_eq_zero_of_notMem_tsupport (fun hj => hzK (mem_iUnion.mpr ⟨j, hj⟩))
    have : vectorTest α z = 0 := by
      ext j
      simp only [vectorTest_apply, PiLp.zero_apply]
      exact hz0 j
    exact hz this
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hsupp, ?_⟩
  · exact (contDiff_piLp 2).2 fun j => by simpa using (hα j).1
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hsupp hz)
    exact (hα j).2.2 hj

/-- `ψ₀` for the chart expression of the genuine weighted adjoint. -/
def localTwist (c : ComplexChart n X) (z : ComplexModel n) : ℝ :=
  -Real.log (T.a (c.val.symm z) + T.b (c.val.symm z))

omit [BorelSpace X] in
/-- On the local piece the two weights satisfy the Euclidean relation
`w₂ = w₁ + ψ₀`. -/
theorem localWeight_eq_H1_add_twist (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (z : ComplexModel n) :
    localWeight T.L c e ρ T.φ z = T.localH1Weight c e ρ z + T.localTwist c z := by
  simp only [localH1Weight, localTwist]
  ring

/-- The Euclidean weighted adjoint agrees pointwise with the genuine local
adjoint coefficient on the piece. -/
theorem tstarForm_vectorTest_eq_pieceTheta (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (α : Fin n → ComplexModel n → ℂ)
    {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) :
    tstarForm (localWeight T.L c e ρ T.φ) (T.localTwist c) α z =
      T.pieceTheta c e ρ (vectorTest α) z := by
  have hab := T.ab_pos hz.2
  simp only [tstarForm, localTwist, neg_neg, Real.exp_log hab, pieceTheta, chartTheta,
    vectorTest_apply]
  ring

/-- The book's `∂̄G` pairing is the usual sum of coordinate test pairings. -/
theorem dbarPairing_vectorTest (a : ComplexModel n → ℂ)
    (α : Fin n → ComplexModel n → ℂ) (z : ComplexModel n) :
    dbarPairing a z (vectorTest α z) =
      ∑ j, conj (α j z) * dbarDir (coordVec j) a z := by
  simp only [dbarPairing, vectorTest_apply]

end TwistedDatum
end SGPT.Trace.TwistedL2
