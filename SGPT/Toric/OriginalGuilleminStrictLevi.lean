import SGPT.Toric.OriginalGuilleminSmoothCornerInverse
import SGPT.Toric.NativeOriginalEdgeAnalyticCharts
import SGPT.Foundations.Analysis.Pending.YauSmoothOpenness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The actual complex Hessian of the original Guillemin weight

The exact finite-coordinate canonical weight is transported through the existing
complex model equivalence. Its genuine remainder matrix is positive semidefinite
by its original inactive-facet Gram sum. The source Jacobian and the Woodbury
identity give a positive inverse at every coordinate-zero pattern.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set Filter Matrix SGPT.Convex SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open scoped BigOperators Topology Classical ContDiff ComplexOrder ComplexConjugate

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The literal original weight in the genuine native Euclidean complex model. -/
def originalGuilleminNativeCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) : ℝ :=
  originalGuilleminComplexCornerWeight γ hsmooth v (originalPolytopeNativeModelEquiv n z)

/-- The actual model equivalence transports whole-chart smoothness. -/
theorem contDiff_originalGuilleminNativeCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiff ℝ ∞ (originalGuilleminNativeCornerWeight γ hsmooth v) :=
  (contDiff_originalGuilleminComplexCornerWeight γ hsmooth v).comp
    ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.restrictScalars ℝ).contDiff

/-- The entrywise complex embedding of the genuine original remainder Hessian. -/
def originalCornerRemainderComplexMatrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (originalCornerRemainderMatrix γ hsmooth v x).map Complex.ofRealHom

/-- The actual positive inactive-slack rank-one sum proves complex PSD directly. -/
theorem originalCornerRemainderComplexMatrix_posSemidef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    (originalCornerRemainderComplexMatrix γ hsmooth v x).PosSemidef := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  let a : originalVertexInactiveFacets γ v → Fin n → ℂ := fun F j =>
    (originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j) : ℂ)
  have hsum : originalCornerRemainderComplexMatrix γ hsmooth v x =
      ∑ F : originalVertexInactiveFacets γ v,
        (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F.val x)⁻¹ •
            Matrix.vecMulVec (a F) (star (a F)) := by
    ext j k
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j k)
      (originalCornerRemainderMatrix_eq_sum γ hsmooth v x)
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] at h
    change (originalCornerRemainderMatrix γ hsmooth v x j k : ℂ) = _
    rw [h]
    simp [a, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  rw [hsum]
  apply Matrix.posSemidef_sum
  intro F _
  exact (Matrix.posSemidef_vecMulVec_self_star (a F)).smul (inv_nonneg.mpr (hx F).le)

private def leviPoint (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) : Fin n → ℝ :=
  originalGuilleminCornerInverse γ hsmooth v
    ⟨fun j => Complex.normSq (w j), fun j => Complex.normSq_nonneg (w j)⟩

private def leviSlopes (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.exp (-1 - originalCornerRemainderPartial γ hsmooth v j x)

private def leviDiagonalB (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (leviSlopes γ hsmooth v x j : ℂ)

private def leviDiagonalX (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (x j : ℂ)

private theorem leviSlopes_mul_exp (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) (j : Fin n) :
    leviSlopes γ hsmooth v x j *
      Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) = 1 := by
  unfold leviSlopes
  rw [← Real.exp_add, show -1 - originalCornerRemainderPartial γ hsmooth v j x +
    (1 + originalCornerRemainderPartial γ hsmooth v j x) = 0 by ring, Real.exp_zero]

private theorem leviDiagonalB_posDef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (leviDiagonalB γ hsmooth v x).PosDef := by
  apply Matrix.PosDef.diagonal
  intro j
  exact Complex.zero_lt_real.mpr (Real.exp_pos _)

private theorem leviRealJacobian_factor (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) :
    Matrix.diagonal (leviSlopes γ hsmooth v x) *
        originalCornerJacobianMatrix γ hsmooth v x =
      1 + Matrix.diagonal x * originalCornerRemainderMatrix γ hsmooth v x := by
  ext j k
  simp only [Matrix.diagonal_mul, Matrix.add_apply, Matrix.one_apply,
    originalCornerJacobianMatrix_apply]
  rw [← mul_assoc, leviSlopes_mul_exp, one_mul]

private theorem leviT_isUnit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    IsUnit (1 + leviDiagonalX x * originalCornerRemainderComplexMatrix γ hsmooth v x) := by
  have hrealB : IsUnit (Matrix.diagonal (leviSlopes γ hsmooth v x)) :=
    (Matrix.PosDef.diagonal (fun _ => Real.exp_pos _)).isUnit
  have hrealT : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.diagonal x * originalCornerRemainderMatrix γ hsmooth v x) := by
    rw [← leviRealJacobian_factor]
    exact hrealB.mul (originalCornerJacobianMatrix_isUnit γ hsmooth v hx)
  have h := hrealT.map Complex.ofRealHom.mapMatrix
  change IsUnit (((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.diagonal x * originalCornerRemainderMatrix γ hsmooth v x).map Complex.ofRealHom) at h
  convert h using 1
  ext j k
  by_cases hjk : j = k <;> simp [leviDiagonalX, originalCornerRemainderComplexMatrix,
    Matrix.map_apply, Matrix.diagonal_mul, Matrix.add_apply, hjk]

private theorem leviPoint_eq_normSq_mul_slopes (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) (j : Fin n) :
    leviPoint γ hsmooth v w j =
      Complex.normSq (w j) * leviSlopes γ hsmooth v (leviPoint γ hsmooth v w) j := by
  let x := leviPoint γ hsmooth v w
  have hs : x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) =
      Complex.normSq (w j) := congrFun (originalGuilleminCornerMap_inverse γ hsmooth v
        ⟨fun k => Complex.normSq (w k), fun k => Complex.normSq_nonneg (w k)⟩) j
  have hb : Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) *
      leviSlopes γ hsmooth v x j = 1 := by
    rw [mul_comm, leviSlopes_mul_exp]
  calc
    x j = (x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x)) *
        leviSlopes γ hsmooth v x j := by rw [mul_assoc, hb, mul_one]
    _ = _ := by rw [hs]

private theorem leviDiagonal_normSq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) :
    Matrix.diagonal w * leviDiagonalB γ hsmooth v (leviPoint γ hsmooth v w) *
        (Matrix.diagonal w)ᴴ = leviDiagonalX (leviPoint γ hsmooth v w) := by
  unfold leviDiagonalB leviDiagonalX
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [leviPoint_eq_normSq_mul_slopes, Complex.ofReal_mul]
  change (w j * (leviSlopes γ hsmooth v (leviPoint γ hsmooth v w) j : ℂ)) *
    star (w j) = _
  rw [mul_right_comm]
  simpa only [Complex.star_def] using congrArg
    (fun a : ℂ => a * (leviSlopes γ hsmooth v (leviPoint γ hsmooth v w) j : ℂ))
      (Complex.mul_conj (w j))

/-- The explicit matrix produced by the actual inverse and original Hessian. -/
def originalGuilleminCornerLeviMatrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let x := leviPoint γ hsmooth v w
  let B := leviDiagonalB γ hsmooth v x
  let D := Matrix.diagonal w
  let H := originalCornerRemainderComplexMatrix γ hsmooth v x
  B - Dᴴ * B * H * (1 + leviDiagonalX x * H)⁻¹ * B * D

/-- Woodbury gives the inverse of an actual positive matrix without assuming
that the original remainder Hessian is invertible or dividing by a coordinate. -/
theorem originalGuilleminCornerLeviMatrix_eq_positiveInverse (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) :
    let x := originalGuilleminCornerInverse γ hsmooth v
      ⟨fun j => Complex.normSq (w j), fun j => Complex.normSq_nonneg (w j)⟩
    let B := Matrix.diagonal fun j =>
      (Real.exp (-1 - originalCornerRemainderPartial γ hsmooth v j x) : ℂ)
    originalGuilleminCornerLeviMatrix γ hsmooth v w =
      (B⁻¹ + (Matrix.diagonal w)ᴴ * originalCornerRemainderComplexMatrix γ hsmooth v x *
        Matrix.diagonal w)⁻¹ := by
  let x := leviPoint γ hsmooth v w
  let B := leviDiagonalB γ hsmooth v x
  let D := Matrix.diagonal w
  let H := originalCornerRemainderComplexMatrix γ hsmooth v x
  have hx : x ∈ originalVertexCornerDomain γ hsmooth v :=
    originalGuilleminCornerInverse_mem_domain γ hsmooth v _
  have hB : IsUnit B := (leviDiagonalB_posDef γ hsmooth v x).isUnit
  let := hB.invertible
  have hDBD : D * B * Dᴴ = leviDiagonalX x := leviDiagonal_normSq γ hsmooth v w
  have hT : IsUnit (1 + D * B * Dᴴ * H) := by
    rw [hDBD]
    exact leviT_isUnit γ hsmooth v hx
  have hT' : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ +
      D * (B⁻¹)⁻¹ * (Dᴴ * H)) := by
    simpa only [inv_one, Matrix.inv_inv_of_invertible, Matrix.mul_assoc] using hT
  have hwood := Matrix.add_mul_mul_inv_eq_sub B⁻¹ (Dᴴ * H) 1 D
    (Matrix.isUnit_nonsing_inv_iff.mpr hB) isUnit_one hT'
  simp only [Matrix.mul_one, inv_one,
    Matrix.inv_inv_of_invertible] at hwood
  have hBD : B * D = D * B := by
    dsimp only [B, D, leviDiagonalB]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact mul_comm _ _
  have hBDH : B * Dᴴ = Dᴴ * B := by
    dsimp only [B, D, leviDiagonalB]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact mul_comm _ _
  change B - Dᴴ * B * H * (1 + leviDiagonalX x * H)⁻¹ * B * D =
    (B⁻¹ + Dᴴ * H * D)⁻¹
  rw [hwood, ← hDBD, ← hBDH]
  simp only [Matrix.mul_assoc, hBD]

private theorem leviMatrix_posDef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) : (originalGuilleminCornerLeviMatrix γ hsmooth v w).PosDef := by
  rw [originalGuilleminCornerLeviMatrix_eq_positiveInverse]
  apply Matrix.PosDef.inv
  exact (leviDiagonalB_posDef γ hsmooth v (leviPoint γ hsmooth v w)).inv.add_posSemidef
    ((originalCornerRemainderComplexMatrix_posSemidef γ hsmooth v
      (originalGuilleminCornerInverse_mem_domain γ hsmooth v _).1).conjTranspose_mul_mul_same
        (Matrix.diagonal w))


private theorem hasFDerivAt_leviLegendreValue (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    HasFDerivAt (originalCornerLegendreValue γ hsmooth v)
      ((∑ j, leviSlopes γ hsmooth v x j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).comp
          (originalCornerJacobian γ hsmooth v x)) x := by
  have hsum : HasFDerivAt
      (fun y : Fin n → ℝ => ∑ j, y j * (1 + originalCornerRemainderPartial γ hsmooth v j y))
      (∑ j, ((1 + originalCornerRemainderPartial γ hsmooth v j x) •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) +
          x j • originalCornerPartialDerivative γ hsmooth v j x)) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    convert! (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul
      ((hasFDerivAt_originalCornerRemainderPartial γ hsmooth v j hx).const_add 1) using 1
    simp [add_comm]
  have hR := hsum.sub (hasFDerivAt_originalVertexCornerRemainder γ hsmooth v hx)
  apply hR.congr_fderiv
  apply ContinuousLinearMap.ext
  intro η
  rw [← (Pi.basisFun ℝ (Fin n)).sum_repr η]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change (∑ j, ((1 + originalCornerRemainderPartial γ hsmooth v j x) •
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) +
        x j • originalCornerPartialDerivative γ hsmooth v j x))
      (Pi.basisFun ℝ (Fin n) k) -
        originalCornerRemainderDerivative γ hsmooth v x (Pi.basisFun ℝ (Fin n) k) = _
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, originalCornerJacobian_apply]
  simp_rw [← mul_assoc, leviSlopes_mul_exp, one_mul]
  simp only [add_mul, Finset.sum_add_distrib, originalCornerRemainderPartial,
    originalCornerPartialDerivative, ContinuousLinearMap.flip_apply,
    Pi.basisFun_apply, Pi.single_apply]
  simp
  ring

private theorem hasFDerivAt_leviLegendre_composition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {s : Fin n → ℝ} (hf : HasFDerivAt f f' s)
    (hx : f s ∈ originalVertexCornerOpen γ hsmooth v)
    (heq : (fun t => originalGuilleminCornerMap γ hsmooth v (f t)) =ᶠ[𝓝 s] id) :
    HasFDerivAt (fun t => originalCornerLegendreValue γ hsmooth v (f t))
      (∑ j, leviSlopes γ hsmooth v (f s) j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) s := by
  have hS := (hasFDerivAt_originalGuilleminCornerMap γ hsmooth v hx).comp s hf
  have hJ : (originalCornerJacobian γ hsmooth v (f s)).comp f' =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [← hS.fderiv]
    change fderiv ℝ (fun t => originalGuilleminCornerMap γ hsmooth v (f t)) s = _
    rw [heq.fderiv_eq, fderiv_id]
  have hR := (hasFDerivAt_leviLegendreValue γ hsmooth v hx).comp s hf
  convert! hR using 1
  simp only [ContinuousLinearMap.comp_assoc, hJ, ContinuousLinearMap.comp_id]

private theorem exists_leviLegendre_germ (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s₀ : Ici (0 : Fin n → ℝ)) :
    ∃ (f : (Fin n → ℝ) → (Fin n → ℝ)) (V : Set (Fin n → ℝ)),
      ContDiffAt ℝ ∞ f s₀.val ∧
      f s₀.val = originalGuilleminCornerInverse γ hsmooth v s₀ ∧
      IsOpen V ∧ s₀.val ∈ V ∧
      ∀ s ∈ V, f s ∈ originalVertexCornerOpen γ hsmooth v ∧
        originalGuilleminCornerMap γ hsmooth v (f s) = s ∧
        (∀ hs : s ∈ Ici (0 : Fin n → ℝ),
          f s = originalGuilleminCornerInverse γ hsmooth v ⟨s, hs⟩) ∧
        HasFDerivAt (fun t => originalCornerLegendreValue γ hsmooth v (f t))
          (∑ j, leviSlopes γ hsmooth v (f s) j •
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) s := by
  obtain ⟨f, hf, hf₀, heq⟩ :=
    exists_originalGuilleminCornerInverse_smoothExtension γ hsmooth v s₀
  obtain ⟨t, ht, hft⟩ := hf.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) (by norm_num)
  obtain ⟨V, hVsub, hVopen, hV₀⟩ := mem_nhds_iff.mp (inter_mem ht heq)
  have hVdiff : ContDiffOn ℝ 2 f V := hft.mono (fun s hs => (hVsub hs).1)
  refine ⟨f, V, hf, hf₀, hVopen, hV₀, ?_⟩
  intro s hs
  have hprops := (hVsub hs).2
  refine ⟨hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  apply hasFDerivAt_leviLegendre_composition γ hsmooth v
    ((hVdiff.contDiffAt (hVopen.mem_nhds hs)).differentiableAt (by norm_num)).hasFDerivAt
    hprops.1
  filter_upwards [hVopen.mem_nhds hs] with t ht
  exact (hVsub ht).2.2.1

private theorem levi_realHessian_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : F → ℝ} {q : E → F} {z : E}
    (hr : ContDiffAt ℝ 2 r (q z)) (hq : ContDiffAt ℝ 2 q z) (η ξ : E) :
    realHessian (fun u => r (q u)) z η ξ =
      fderiv ℝ r (q z) (fderiv ℝ (fderiv ℝ q) z η ξ) +
        realHessian r (q z) (fderiv ℝ q z η) (fderiv ℝ q z ξ) := by
  have hDq : ∀ᶠ u in 𝓝 z, DifferentiableAt ℝ q u :=
    (hq.eventually (by norm_num)).mono (fun u hu => hu.differentiableAt (by norm_num))
  have hDr : ∀ᶠ u in 𝓝 (q z), DifferentiableAt ℝ r u :=
    (hr.eventually (by norm_num)).mono (fun u hu => hu.differentiableAt (by norm_num))
  have heq : fderiv ℝ (fun u => r (q u)) =ᶠ[𝓝 z]
      fun u => (fderiv ℝ r (q u)).comp (fderiv ℝ q u) := by
    filter_upwards [hDq, hq.continuousAt.tendsto.eventually hDr] with u hqu hru
    exact (hru.hasFDerivAt.comp u hqu.hasFDerivAt).fderiv
  have hDDr : DifferentiableAt ℝ (fderiv ℝ r) (q z) :=
    (hr.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDDq : DifferentiableAt ℝ (fderiv ℝ q) z :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomp := (hDDr.hasFDerivAt.comp z
    (hq.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hDDq.hasFDerivAt
  change HasFDerivAt (fun u => (fderiv ℝ r (q u)).comp (fderiv ℝ q u)) _ z at hcomp
  rw [realHessian_eq_fderiv, heq.fderiv_eq, hcomp.fderiv, realHessian_eq_fderiv]
  rfl

private def leviNativeCoordinate (j : Fin n) : ComplexModel n →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
    (originalPolytopeNativeModelEquiv n).toContinuousLinearMap).restrictScalars ℝ

private def leviNativeNormSq (z : ComplexModel n) : Fin n → ℝ :=
  fun j => Complex.normSq (leviNativeCoordinate j z)

private def leviNativeNormSqDerivative (z : ComplexModel n) :
    ComplexModel n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    2 • (innerSL ℝ (leviNativeCoordinate j z)).comp (leviNativeCoordinate j)

private theorem contDiff_leviNativeNormSq : ContDiff ℝ ∞ (leviNativeNormSq (n := n)) := by
  apply contDiff_pi.mpr
  intro j
  simp only [leviNativeNormSq, ← Complex.sq_norm]
  exact (contDiff_norm_sq ℝ).comp (leviNativeCoordinate j).contDiff

private theorem hasFDerivAt_leviNativeNormSq (z : ComplexModel n) :
    HasFDerivAt leviNativeNormSq (leviNativeNormSqDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  intro j
  simpa only [leviNativeNormSq, ← Complex.sq_norm, leviNativeNormSqDerivative,
    ContinuousLinearMap.proj_pi] using (leviNativeCoordinate j).hasFDerivAt.norm_sq

private theorem levi_realHessian_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → (Fin n → ℝ)} {z : E} (hq : ContDiffAt ℝ 2 q z)
    (η ξ : E) (j : Fin n) :
    realHessian (fun u => q u j) z η ξ =
      fderiv ℝ (fderiv ℝ q) z η ξ j := by
  have hDq : ∀ᶠ u in 𝓝 z, DifferentiableAt ℝ q u :=
    (hq.eventually (by norm_num)).mono (fun u hu => hu.differentiableAt (by norm_num))
  have heq : fderiv ℝ (fun u => q u j) =ᶠ[𝓝 z]
      fun u => (ContinuousLinearMap.proj j).comp (fderiv ℝ q u) := by
    filter_upwards [hDq] with u hu
    exact fderiv_apply hu j
  have hDDq : DifferentiableAt ℝ (fderiv ℝ q) z :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomp := (hasFDerivAt_const (ContinuousLinearMap.proj j :
      (Fin n → ℝ) →L[ℝ] ℝ) z).clm_comp hDDq.hasFDerivAt
  rw [realHessian_eq_fderiv, heq.fderiv_eq, hcomp.fderiv]
  simp

private theorem levi_realHessian_normSqCoordinate (z η ξ : ComplexModel n) (j : Fin n) :
    realHessian (fun u => leviNativeNormSq u j) z η ξ =
      2 * inner ℝ (leviNativeCoordinate j η) (leviNativeCoordinate j ξ) := by
  simpa only [leviNativeNormSq, ← Complex.sq_norm, zero_add] using
    (realHessian_comp_affine (contDiff_norm_sq ℝ) (leviNativeCoordinate j) 0 z η ξ).trans
      (realHessian_norm_sq _ _ _)

private theorem leviNativeNormSqDerivative_coordinate (z : ComplexModel n)
    (a : ℂ) (j : Fin n) :
    leviNativeNormSqDerivative z (a • coordinateVector j) =
      (2 * (a * conj (z j)).re) • Pi.basisFun ℝ (Fin n) j := by
  ext k
  by_cases h : k = j
  · subst k
    simp [leviNativeNormSqDerivative, leviNativeCoordinate, originalPolytopeNativeModelEquiv,
      coordinateVector, Pi.basisFun_apply]
    ring
  · simp [leviNativeNormSqDerivative, leviNativeCoordinate, originalPolytopeNativeModelEquiv,
      coordinateVector, Pi.basisFun_apply, h]

private theorem leviNativeNormSqSecond_coordinate (z : ComplexModel n)
    (a b : ℂ) (j k : Fin n) :
    fderiv ℝ (fderiv ℝ leviNativeNormSq) z (a • coordinateVector j)
        (b • coordinateVector k) =
      if j = k then (2 * (b * conj a).re) • Pi.basisFun ℝ (Fin n) j else 0 := by
  have hq : ContDiffAt ℝ 2 leviNativeNormSq z :=
    contDiff_leviNativeNormSq.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  ext l
  rw [← levi_realHessian_coordinate hq, levi_realHessian_normSqCoordinate]
  by_cases hjk : j = k
  · subst k
    by_cases hlj : l = j
    · subst l
      simp [leviNativeCoordinate, originalPolytopeNativeModelEquiv, coordinateVector,
        Pi.basisFun_apply]
    · simp [leviNativeCoordinate, originalPolytopeNativeModelEquiv, coordinateVector,
        Pi.basisFun_apply, hlj]
  · by_cases hlj : l = j
    · subst l
      simp [leviNativeCoordinate, originalPolytopeNativeModelEquiv, coordinateVector,
        hjk]
    · simp [leviNativeCoordinate, originalPolytopeNativeModelEquiv, coordinateVector,
        hjk, hlj]

private theorem leviLegendre_germ_hessian (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {s : Fin n → ℝ} (hf : HasFDerivAt f f' s)
    (hx : f s ∈ originalVertexCornerOpen γ hsmooth v)
    (hg : ∀ᶠ t in 𝓝 s,
      HasFDerivAt (fun u => originalCornerLegendreValue γ hsmooth v (f u))
        (∑ j, leviSlopes γ hsmooth v (f t) j •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) t)
    (η ξ : Fin n → ℝ) :
    realHessian (fun u => originalCornerLegendreValue γ hsmooth v (f u)) s η ξ =
      ∑ j, -(leviSlopes γ hsmooth v (f s) j) *
        originalCornerPartialDerivative γ hsmooth v j (f s) (f' η) * ξ j := by
  have hb (j : Fin n) : HasFDerivAt (fun t => leviSlopes γ hsmooth v (f t) j)
      (-(leviSlopes γ hsmooth v (f s) j) •
        (originalCornerPartialDerivative γ hsmooth v j (f s)).comp f') s := by
    convert! (((hasFDerivAt_originalCornerRemainderPartial γ hsmooth v j hx).comp s hf).neg.const_add
      (-1)).exp using 1
    ext θ
    simp [leviSlopes, sub_eq_add_neg]
  have hgrad : HasFDerivAt
      (fun t => ∑ j, leviSlopes γ hsmooth v (f t) j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))
      (∑ j, (-(leviSlopes γ hsmooth v (f s) j) •
        (originalCornerPartialDerivative γ hsmooth v j (f s)).comp f').smulRight
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) s := by
    apply HasFDerivAt.fun_sum
    intro j _
    convert! (hb j).smul_const (ContinuousLinearMap.proj j :
      (Fin n → ℝ) →L[ℝ] ℝ) using 1
  have heq : fderiv ℝ (fun u => originalCornerLegendreValue γ hsmooth v (f u)) =ᶠ[𝓝 s]
      fun t => ∑ j, leviSlopes γ hsmooth v (f t) j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := hg.mono fun t ht => ht.fderiv
  rw [realHessian_eq_fderiv, heq.fderiv_eq, hgrad.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

private theorem levi_complexHessian_normSq_pullback
    {r : (Fin n → ℝ) → ℝ} (z : ComplexModel n)
    (hr : ContDiffAt ℝ 2 r (leviNativeNormSq z)) (j k : Fin n) :
    complexHessian (fun u => r (leviNativeNormSq u)) z j k =
      (if j = k then (fderiv ℝ r (leviNativeNormSq z)
        (Pi.basisFun ℝ (Fin n) j) : ℂ) else 0) +
      conj (z j) * z k * (realHessian r (leviNativeNormSq z)
        (Pi.basisFun ℝ (Fin n) k) (Pi.basisFun ℝ (Fin n) j) : ℂ) := by
  have hq : ContDiffAt ℝ 2 leviNativeNormSq z :=
    contDiff_leviNativeNormSq.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hchain (a b : ℂ) :
      realHessian (fun u => r (leviNativeNormSq u)) z
          (a • coordinateVector j) (b • coordinateVector k) =
        (if j = k then 2 * (b * conj a).re *
          fderiv ℝ r (leviNativeNormSq z) (Pi.basisFun ℝ (Fin n) j) else 0) +
        (2 * (a * conj (z j)).re) * (2 * (b * conj (z k)).re) *
          realHessian r (leviNativeNormSq z)
            (Pi.basisFun ℝ (Fin n) j) (Pi.basisFun ℝ (Fin n) k) := by
    rw [levi_realHessian_comp hr hq, (hasFDerivAt_leviNativeNormSq z).fderiv,
      leviNativeNormSqDerivative_coordinate, leviNativeNormSqDerivative_coordinate,
      leviNativeNormSqSecond_coordinate]
    by_cases hjk : j = k <;>
      simp [hjk, realHessian_smul_left, realHessian_smul_right] <;> ring
  have h11 := hchain 1 1
  have hII := hchain Complex.I Complex.I
  have h1I := hchain 1 Complex.I
  have hI1 := hchain Complex.I 1
  simp only [one_smul] at h11 h1I hI1
  rw [complexHessian, h11, hII, h1I, hI1]
  have hsym : realHessian r (leviNativeNormSq z) (Pi.basisFun ℝ (Fin n) j)
      (Pi.basisFun ℝ (Fin n) k) =
      realHessian r (leviNativeNormSq z) (Pi.basisFun ℝ (Fin n) k)
        (Pi.basisFun ℝ (Fin n) j) := by
    simpa only [realHessian_eq_fderiv] using hr.isSymmSndFDerivAt (by norm_num)
      (Pi.basisFun ℝ (Fin n) j) (Pi.basisFun ℝ (Fin n) k)
  simp only [hsym]
  by_cases hjk : j = k <;> apply Complex.ext <;>
    simp [hjk, Complex.mul_re, Complex.mul_im] <;> ring

private theorem leviHessian_mulVec (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η : Fin n → ℝ) :
    originalCornerRemainderMatrix γ hsmooth v x *ᵥ η =
      fun j => originalCornerPartialDerivative γ hsmooth v j x η := by
  have hm : originalCornerRemainderMatrix γ hsmooth v x =
      LinearMap.toMatrix' (ContinuousLinearMap.pi
        (fun j => originalCornerPartialDerivative γ hsmooth v j x)).toLinearMap := by
    ext j k
    simp [LinearMap.toMatrix'_apply, originalCornerRemainderMatrix,
      originalCornerPartialDerivative, Pi.basisFun_apply]
  rw [hm]
  exact LinearMap.toMatrix'_mulVec
    (ContinuousLinearMap.pi (fun j => originalCornerPartialDerivative γ hsmooth v j x)).toLinearMap η

private theorem leviRealT_isUnit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.diagonal x * originalCornerRemainderMatrix γ hsmooth v x) := by
  rw [← leviRealJacobian_factor]
  exact (Matrix.PosDef.diagonal (fun _ => Real.exp_pos _)).isUnit.mul
    (originalCornerJacobianMatrix_isUnit γ hsmooth v hx)

private theorem leviInverse_fderiv (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {s : Fin n → ℝ} (hf : HasFDerivAt f f' s)
    (hx : f s ∈ originalVertexCornerDomain γ hsmooth v)
    (heq : (fun t => originalGuilleminCornerMap γ hsmooth v (f t)) =ᶠ[𝓝 s] id)
    (η : Fin n → ℝ) :
    f' η = (((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.diagonal (f s) * originalCornerRemainderMatrix γ hsmooth v (f s))⁻¹ *
        Matrix.diagonal (leviSlopes γ hsmooth v (f s))) *ᵥ η := by
  have hS := (hasFDerivAt_originalGuilleminCornerMap γ hsmooth v hx.1).comp s hf
  have hJ : (originalCornerJacobian γ hsmooth v (f s)).comp f' =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [← hS.fderiv]
    change fderiv ℝ (fun t => originalGuilleminCornerMap γ hsmooth v (f t)) s = _
    rw [heq.fderiv_eq, fderiv_id]
  have hJη : originalCornerJacobianMatrix γ hsmooth v (f s) *ᵥ f' η = η := by
    rw [originalCornerJacobianMatrix_mulVec]
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L η) hJ
  let T : Matrix (Fin n) (Fin n) ℝ :=
    1 + Matrix.diagonal (f s) * originalCornerRemainderMatrix γ hsmooth v (f s)
  let B := Matrix.diagonal (leviSlopes γ hsmooth v (f s))
  have hT : IsUnit T := leviRealT_isUnit γ hsmooth v hx
  have hTη : T *ᵥ f' η = B *ᵥ η := by
    dsimp only [T, B]
    rw [← leviRealJacobian_factor, ← Matrix.mulVec_mulVec, hJη]
  let := hT.invertible
  calc
    f' η = (T⁻¹ * T) *ᵥ f' η := by simp
    _ = T⁻¹ *ᵥ (T *ᵥ f' η) := (Matrix.mulVec_mulVec (f' η) T⁻¹ T).symm
    _ = T⁻¹ *ᵥ (B *ᵥ η) := by rw [hTη]
    _ = _ := Matrix.mulVec_mulVec η T⁻¹ B

private theorem leviLegendre_germ_hessian_matrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {s : Fin n → ℝ} (hf : HasFDerivAt f f' s)
    (hx : f s ∈ originalVertexCornerDomain γ hsmooth v)
    (heq : (fun t => originalGuilleminCornerMap γ hsmooth v (f t)) =ᶠ[𝓝 s] id)
    (hg : ∀ᶠ t in 𝓝 s,
      HasFDerivAt (fun u => originalCornerLegendreValue γ hsmooth v (f u))
        (∑ j, leviSlopes γ hsmooth v (f t) j •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) t)
    (j k : Fin n) :
    realHessian (fun u => originalCornerLegendreValue γ hsmooth v (f u)) s
      (Pi.basisFun ℝ (Fin n) k) (Pi.basisFun ℝ (Fin n) j) =
        -((Matrix.diagonal (leviSlopes γ hsmooth v (f s)) *
          originalCornerRemainderMatrix γ hsmooth v (f s) *
          ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal (f s) *
            originalCornerRemainderMatrix γ hsmooth v (f s))⁻¹ *
              Matrix.diagonal (leviSlopes γ hsmooth v (f s))) j k) := by
  rw [leviLegendre_germ_hessian γ hsmooth v hf hx.1 hg]
  simp only [Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change -(leviSlopes γ hsmooth v (f s) j) *
    originalCornerPartialDerivative γ hsmooth v j (f s)
      (f' (Pi.single k 1)) = _
  rw [← congrFun (leviHessian_mulVec γ hsmooth v (f s)
    (f' (Pi.single k 1))) j, leviInverse_fderiv γ hsmooth v hf hx heq,
    Matrix.mulVec_mulVec]
  simp [Matrix.diagonal_mul, Matrix.mul_assoc, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
  ring

private theorem leviRealMatrix_inverse_map (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsUnit T) :
    (T⁻¹).map Complex.ofRealHom = (T.map Complex.ofRealHom)⁻¹ := by
  let := hT.invertible
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  change Complex.ofRealHom.mapMatrix T⁻¹ * Complex.ofRealHom.mapMatrix T = 1
  rw [← map_mul, Matrix.inv_mul_of_invertible, map_one]

private theorem leviRealCorrection_map (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    (Matrix.diagonal (leviSlopes γ hsmooth v x) * originalCornerRemainderMatrix γ hsmooth v x *
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal x *
        originalCornerRemainderMatrix γ hsmooth v x)⁻¹ *
          Matrix.diagonal (leviSlopes γ hsmooth v x)).map Complex.ofRealHom =
    leviDiagonalB γ hsmooth v x * originalCornerRemainderComplexMatrix γ hsmooth v x *
      (1 + leviDiagonalX x * originalCornerRemainderComplexMatrix γ hsmooth v x)⁻¹ *
        leviDiagonalB γ hsmooth v x := by
  let B := Matrix.diagonal (leviSlopes γ hsmooth v x)
  let T : Matrix (Fin n) (Fin n) ℝ :=
    1 + Matrix.diagonal x * originalCornerRemainderMatrix γ hsmooth v x
  have hB : B.map Complex.ofRealHom = leviDiagonalB γ hsmooth v x := by
    ext j k
    by_cases hjk : j = k <;> simp [B, Matrix.map_apply, leviDiagonalB, hjk]
  have hT : T.map Complex.ofRealHom =
      1 + leviDiagonalX x * originalCornerRemainderComplexMatrix γ hsmooth v x := by
    ext j k
    by_cases hjk : j = k <;>
      simp [T, Matrix.map_apply, leviDiagonalX, originalCornerRemainderComplexMatrix,
        Matrix.diagonal_mul, Matrix.add_apply, hjk]
  change Complex.ofRealHom.mapMatrix
    (B * originalCornerRemainderMatrix γ hsmooth v x * T⁻¹ * B) = _
  rw [map_mul, map_mul, map_mul]
  change B.map Complex.ofRealHom * originalCornerRemainderComplexMatrix γ hsmooth v x *
    (T⁻¹).map Complex.ofRealHom * B.map Complex.ofRealHom = _
  rw [leviRealMatrix_inverse_map T (leviRealT_isUnit γ hsmooth v hx), hT, hB]

private theorem levi_complexHessian_germ {u v : ComplexModel n → ℝ} {z : ComplexModel n}
    (heq : u =ᶠ[𝓝 z] v) : complexHessian u z = complexHessian v z := by
  have hD : fderiv ℝ u =ᶠ[𝓝 z] fderiv ℝ v := heq.fderiv
  have hDD : fderiv ℝ (fderiv ℝ u) z = fderiv ℝ (fderiv ℝ v) z := hD.fderiv_eq
  ext j k
  simp only [complexHessian, realHessian_eq_fderiv, hDD]

private theorem leviCornerLeviMatrix_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) (j k : Fin n) :
    originalGuilleminCornerLeviMatrix γ hsmooth v w j k =
      (if j = k then (leviSlopes γ hsmooth v (leviPoint γ hsmooth v w) j : ℂ) else 0) -
      conj (w j) * w k *
        (leviDiagonalB γ hsmooth v (leviPoint γ hsmooth v w) *
          originalCornerRemainderComplexMatrix γ hsmooth v (leviPoint γ hsmooth v w) *
          (1 + leviDiagonalX (leviPoint γ hsmooth v w) *
            originalCornerRemainderComplexMatrix γ hsmooth v (leviPoint γ hsmooth v w))⁻¹ *
              leviDiagonalB γ hsmooth v (leviPoint γ hsmooth v w)) j k := by
  let B := leviDiagonalB γ hsmooth v (leviPoint γ hsmooth v w)
  let H := originalCornerRemainderComplexMatrix γ hsmooth v (leviPoint γ hsmooth v w)
  let T : Matrix (Fin n) (Fin n) ℂ := 1 + leviDiagonalX (leviPoint γ hsmooth v w) * H
  let D := Matrix.diagonal w
  have heq : Dᴴ * B * H * T⁻¹ * B * D = Dᴴ * (B * H * T⁻¹ * B) * D := by
    simp only [Matrix.mul_assoc]
  change (B - Dᴴ * B * H * T⁻¹ * B * D) j k = _
  rw [heq]
  simp only [Matrix.sub_apply, D, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  change (if j = k then (leviSlopes γ hsmooth v (leviPoint γ hsmooth v w) j : ℂ) else 0) -
    star (w j) * (B * H * T⁻¹ * B) j k * w k = _
  rw [Complex.star_def]
  ring

/-- The genuine native complex Hessian is the produced all-strata matrix of
this exact original weight. Every inverse germ is supplied by original geometry. -/
theorem complexHessian_originalGuilleminNativeCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    complexHessian (originalGuilleminNativeCornerWeight γ hsmooth v) z =
      originalGuilleminCornerLeviMatrix γ hsmooth v (originalPolytopeNativeModelEquiv n z) := by
  let s₀ : Ici (0 : Fin n → ℝ) :=
    ⟨leviNativeNormSq z, fun j => Complex.normSq_nonneg (leviNativeCoordinate j z)⟩
  obtain ⟨f, V, hf, hf₀, hVopen, hV₀, hprops⟩ := exists_leviLegendre_germ γ hsmooth v s₀
  let r : (Fin n → ℝ) → ℝ := fun s => originalCornerLegendreValue γ hsmooth v (f s)
  have hx : f s₀.val ∈ originalVertexCornerDomain γ hsmooth v := by
    rw [hf₀]
    exact originalGuilleminCornerInverse_mem_domain γ hsmooth v s₀
  have hR : ContDiffAt ℝ ∞ (originalCornerLegendreValue γ hsmooth v) (f s₀.val) :=
    (contDiffOn_originalCornerLegendreValue γ hsmooth v).contDiffAt
      ((isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds hx.1)
  have hr : ContDiffAt ℝ 2 r (leviNativeNormSq z) :=
    (ContDiffAt.comp (f := f) (g := originalCornerLegendreValue γ hsmooth v)
      s₀.val hR hf).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hS : (fun s => originalGuilleminCornerMap γ hsmooth v (f s)) =ᶠ[𝓝 s₀.val] id := by
    filter_upwards [hVopen.mem_nhds hV₀] with s hs
    exact (hprops s hs).2.1
  have hg : ∀ᶠ s in 𝓝 s₀.val, HasFDerivAt r
      (∑ j, leviSlopes γ hsmooth v (f s) j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) s := by
    filter_upwards [hVopen.mem_nhds hV₀] with s hs
    exact (hprops s hs).2.2.2
  have heq : originalGuilleminNativeCornerWeight γ hsmooth v =ᶠ[𝓝 z]
      fun u => r (leviNativeNormSq u) := by
    filter_upwards [contDiff_leviNativeNormSq.continuous.continuousAt.tendsto.eventually
      (hVopen.mem_nhds hV₀)] with u hu
    have hnonneg : leviNativeNormSq u ∈ Ici (0 : Fin n → ℝ) :=
      fun j => Complex.normSq_nonneg (leviNativeCoordinate j u)
    change originalCornerLegendreValue γ hsmooth v
      (originalGuilleminCornerInverse γ hsmooth v ⟨leviNativeNormSq u, hnonneg⟩) = _
    exact congrArg (originalCornerLegendreValue γ hsmooth v)
      ((hprops (leviNativeNormSq u) hu).2.2.1 hnonneg).symm
  rw [levi_complexHessian_germ heq]
  ext j k
  rw [levi_complexHessian_normSq_pullback z hr]
  have hder : fderiv ℝ r (leviNativeNormSq z) (Pi.basisFun ℝ (Fin n) j) =
      leviSlopes γ hsmooth v (f s₀.val) j := by
    rw [(hprops s₀.val hV₀).2.2.2.fderiv]
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [hder, leviLegendre_germ_hessian_matrix γ hsmooth v
    (hf.differentiableAt (by simp)).hasFDerivAt hx hS hg, Complex.ofReal_neg]
  have hcorrection := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k)
    (leviRealCorrection_map γ hsmooth v hx)
  change ((Matrix.diagonal (leviSlopes γ hsmooth v (f s₀.val)) *
      originalCornerRemainderMatrix γ hsmooth v (f s₀.val) *
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal (f s₀.val) *
        originalCornerRemainderMatrix γ hsmooth v (f s₀.val))⁻¹ *
          Matrix.diagonal (leviSlopes γ hsmooth v (f s₀.val))) j k : ℂ) = _ at hcorrection
  rw [hcorrection, leviCornerLeviMatrix_apply]
  have hfX : f s₀.val = leviPoint γ hsmooth v (originalPolytopeNativeModelEquiv n z) := hf₀
  rw [← hfX]
  change (if j = k then (leviSlopes γ hsmooth v (f s₀.val) j : ℂ) else 0) +
    conj (z j) * z k * -(leviDiagonalB γ hsmooth v (f s₀.val) *
      originalCornerRemainderComplexMatrix γ hsmooth v (f s₀.val) *
      (1 + leviDiagonalX (f s₀.val) *
        originalCornerRemainderComplexMatrix γ hsmooth v (f s₀.val))⁻¹ *
          leviDiagonalB γ hsmooth v (f s₀.val)) j k = _
  simp [originalPolytopeNativeModelEquiv]
  ring

/-- The genuine Hessian is positive definite at every coordinate-zero pattern. -/
theorem complexHessian_originalGuilleminNativeCornerWeight_posDef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    (complexHessian (originalGuilleminNativeCornerWeight γ hsmooth v) z).PosDef := by
  rw [complexHessian_originalGuilleminNativeCornerWeight]
  exact leviMatrix_posDef γ hsmooth v (originalPolytopeNativeModelEquiv n z)

/-- Strict positivity concerns the actual native normalized ddC of the literal
weight, with the existing normalization and no supplied comparison form. -/
theorem isStrictlyPositive_smoothDDC_originalGuilleminNativeCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    IsStrictlyPositive (smoothDDC (originalGuilleminNativeCornerWeight γ hsmooth v) z) := by
  have hu : ContDiffAt ℝ 2 (originalGuilleminNativeCornerWeight γ hsmooth v) z :=
    (contDiff_originalGuilleminNativeCornerWeight γ hsmooth v).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply SGPT.Foundations.Analysis.Pending.YauSmoothOpenness.isStrictlyPositive_of_posDef
    (smoothDDC_isOneOne hu)
  rw [normalizedHermitianMatrix_smoothDDC hu]
  exact complexHessian_originalGuilleminNativeCornerWeight_posDef γ hsmooth v z

end SGPT.Toric
