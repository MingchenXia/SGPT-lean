import SGPT.Foundations.Analysis.Pending.NaturalVolumeContractionStokes
import SGPT.Foundations.Analysis.Pending.CompactDifferentialTests

/-! # The genuine full scalar-test contraction Stokes identity

The complete four mathematical statements and proofs precede this source.
All contractions use the same original normalized ordered basis volume.
-/

noncomputable section

open Function
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalConstantTestStokes

open _root_.SGPT.Foundations.Analysis.LocalCurrents NaturalVolumeContractionStokes
  CompactDifferentialTests FirstPass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance tensorNormedAddCommGroup (j : ℕ) :
    NormedAddCommGroup (E [⋀^Fin j]→L[ℝ] ℝ) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance tensorNormedSpace (j : ℕ) :
    NormedSpace ℝ (E [⋀^Fin j]→L[ℝ] ℝ) :=
  ContinuousAlternatingMap.instNormedSpace

/-- The actual first block contraction with no change of volume normalization. -/
def nextBlockContraction [FiniteDimensional ℝ E] {r s : ℕ}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (v : Fin (r + 1) → E) :
    E [⋀^Fin s]→L[ℝ] ℝ :=
  contractVolume (basisVolume (b.reindex finSumFinEquiv.symm)) v

/-- The first block contraction evaluates the original ordered full volume. -/
theorem nextBlockContraction_apply [FiniteDimensional ℝ E] {r s : ℕ}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (v : Fin (r + 1) → E)
    (w : Fin s → E) :
    nextBlockContraction b v w =
      basisVolume b (Fin.append (m := r + 1) (n := s) v w) := by
  classical
  rw [nextBlockContraction, contractVolume_apply, basisVolume_apply,
    Module.Basis.det_reindex, basisVolume_apply]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective z
  rcases x with i | j <;> simp

/-- The actual preceding block contraction of this same ordered full volume. -/
def precedingBlockContraction [FiniteDimensional ℝ E] {r s : ℕ}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (u : Fin r → E) :
    E [⋀^Fin (s + 1)]→L[ℝ] ℝ :=
  contractVolume (basisVolume (b.reindex
    (finSumFinEquiv.trans (finCongr (show r + (s + 1) = (r + 1) + s by omega))).symm)) u

/-- The preceding block contraction has the precise increasing index identification. -/
theorem precedingBlockContraction_apply [FiniteDimensional ℝ E] {r s : ℕ}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (u : Fin r → E)
    (w : Fin (s + 1) → E) :
    precedingBlockContraction b u w = basisVolume b
      (Fin.append (m := r) (n := s + 1) u w ∘ Fin.cast (by omega)) := by
  classical
  rw [precedingBlockContraction, contractVolume_apply, basisVolume_apply,
    Module.Basis.det_reindex, basisVolume_apply]
  congr 1
  funext z
  let e : (Fin r ⊕ Fin (s + 1)) ≃ Fin ((r + 1) + s) :=
    finSumFinEquiv.trans (finCongr (by omega))
  obtain ⟨x, rfl⟩ := e.surjective z
  rcases x with i | j <;> simp [e]

/-- The ordinary exterior derivative of a scalar times an actual constant form. -/
theorem exterior_constForm_apply {q : ℕ} (f : E → ℝ)
    (β : E [⋀^Fin q]→L[ℝ] ℝ) (x : E) (hf : DifferentiableAt ℝ f x)
    (w : Fin (q + 1) → E) :
    extDeriv (fun y => f y • β) x w =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (j : ℕ) •
        ((fderiv ℝ f x) (w j) * β (j.removeNth w)) := by
  rw [extDeriv, fderiv_smul_const hf]
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- The entire actual derivative form satisfies the full original signed contraction identity. -/
theorem signed_contracted_exterior [FiniteDimensional ℝ E] {r s : ℕ}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (v : Fin (r + 1) → E)
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    (-1 : ℤ) ^ (r + 1) • extDeriv (fun y => f y • nextBlockContraction b v) x =
      -(∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
        ((fderiv ℝ f x) (v i) • precedingBlockContraction b (i.removeNth v))) := by
  ext w
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.sum_apply, smul_eq_mul]
  rw [exterior_constForm_apply f _ x hf]
  simp only [nextBlockContraction_apply, precedingBlockContraction_apply]
  exact signed_block_contraction_identity r s b (fderiv ℝ f x) v w

/-- The genuine infinite-order LF test identity holds on all ambient coefficient functions. -/
theorem constantTest_signed_exterior {n r s : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ (ComplexModel n))
    (v : Fin (r + 1) → ComplexModel n) (φ : 𝓓(U, ℝ)) :
    (-1 : ℤ) ^ (r + 1) • exteriorTestCLM (constantTestFormCLM (nextBlockContraction b v) φ) =
      -(∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
        constantTestFormCLM (precedingBlockContraction b (i.removeNth v))
          (TestFunction.lineDerivCLM ℝ (v i) φ)) := by
  apply DFunLike.ext
  intro x
  simp only [smul_apply, neg_apply, sum_apply, constantTestFormCLM_apply]
  change (-1 : ℤ) ^ (r + 1) •
      (exteriorTestCLM (constantTestFormCLM (nextBlockContraction b v) φ)) x =
    -(∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
      ((TestFunction.lineDerivCLM ℝ (v i) φ) x •
        precedingBlockContraction b (i.removeNth v)))
  rw [exteriorTestCLM_apply]
  change (-1 : ℤ) ^ (r + 1) •
    extDeriv (fun y => φ y • nextBlockContraction b v) x = _
  rw [signed_contracted_exterior b v φ x (φ.contDiff.differentiable (by simp)).differentiableAt]
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM,
    congrFun (TestFunction.fderivCLM_apply_of_le φ (by simp)) x]

end SGPT.Foundations.Analysis.Pending.NaturalConstantTestStokes
