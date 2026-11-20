import SGPT.Unibranch.HironakaG10ArtinianBanachMatrix

/-! Actual finite coefficient vectors reconstruct Q-valued holomorphic
functions on the interior of the original compact window. -/
set_option autoImplicit false
open Set
namespace SGPT.Unibranch.HironakaG10CoefficientHolomorphicReconstruction
open SGPT.Foundations.Analysis.Pending.HironakaG10FlatPolydiscAlgebra
  SGPT.Unibranch.HironakaG10ArtinianTensorCoefficients
  SGPT.Unibranch.HironakaG10ArtinianBanachMatrix
noncomputable section
variable {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι]

def coefficientFunction (b : Module.Basis ι ℂ Q) (K : Set X) {r : Type*}
    (v : ι → r → holSubalgebra K) (j : r) (x : X) : Q :=
  ∑ l, extendZero K ((v l j : holSubalgebra K) : C(K,ℂ)) x • b l

theorem coefficientFunction_holomorphic (b : Module.Basis ι ℂ Q) (K : Set X) {r : Type*}
    (v : ι → r → holSubalgebra K) (j : r) :
    DifferentiableOn ℂ (coefficientFunction b K v j) (interior K) := by
  apply DifferentiableOn.fun_sum
  intro l hl
  exact (v l j).property.smul_const (b l)

theorem coefficientFunction_on_window (b : Module.Basis ι ℂ Q) (K : Set X) {r : Type*}
    (v : ι → r → holSubalgebra K) (j : r) (z : K) :
    coefficientFunction b K v j z = coefficientEvaluation b z v j := by
  rw [coefficientEvaluation_apply]
  simp [coefficientFunction, extendZero_of_mem K _ z.property]

theorem coefficientFunction_residue_on_window (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (K : Set X) {r : Type*} (v : ι → r → holSubalgebra K) (j : r) (z : K) :
    ε (coefficientFunction b K v j z) = (coefficientResidue b ε v j : C(K,ℂ)) z := by
  rw [coefficientFunction_on_window, coefficientResidue_evaluation]
end
end SGPT.Unibranch.HironakaG10CoefficientHolomorphicReconstruction
