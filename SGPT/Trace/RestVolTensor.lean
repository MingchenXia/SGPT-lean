import SGPT.Trace.RestVolFrames
import SGPT.Bergman.SourceNativeTensorSmoothMetric
import SGPT.Bergman.SourceNativeDegreeChern

/-!
# The bundle `L^{k₀} ⊗ A` of Step 2 of `thm:rest_volume`

Source: `chapter_trace.tex`, proof of `thm:rest_volume`, Step 2: multiplication by `ϕ^q`,
`ϕ ∈ H⁰(X, A)`, maps `H⁰(Y, T|_Y ⊗ L|_Y^{qk₀+r} ⊗ ·)` into
`H⁰(Y, (T ⊗ L^r)|_Y ⊗ (L^{k₀} ⊗ A)|_Y^q ⊗ ·)`.

* `perturbedBundle L A K = L^{⊗(K+1)} ⊗ A` with its smooth tensor metric and Chern form
  `(K+1) c₁(L) + c₁(A)` (`perturbedBundle_chern_coeff`);
* `stepIndex K r q = r + (K+1) q` (defined recursively, `stepIndex_eq`);
* `mulAFiber σ q : (L^{stepIndex q} ⊗ T)_x → ((L^{K+1} ⊗ A)^q ⊗ (L^r ⊗ T))_x`, `w ↦ w ⊗ σ^{⊗q}`
  reassociated; in product frames it multiplies coordinates by `(coordinate of σ)^q`
  (`frameCoord_mulAFiber`);
* `castTwistedFiber`: the identification of `(L^a ⊗ T)_x` and `(L^b ⊗ T)_x` for `a = b`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter Bundle
open scoped Topology ContDiff Manifold TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth
open SGPT.IGood.DXLow2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The bundle and its curvature -/

/-- `L^{⊗(K+1)} ⊗ A`. -/
abbrev perturbedBundle (L A : HermitianHolomorphicLineBundle.{0, 0} n X) (K : ℕ) :
    HermitianHolomorphicLineBundle.{0, 0} n X :=
  tensor (positivePower L K) A

theorem perturbedBundle_smooth {L A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hA : IsSourceSmoothHermitianMetric A) (K : ℕ) :
    IsSourceSmoothHermitianMetric (perturbedBundle L A K) :=
  sourceNativeTensor_smooth _ _ (sourceNativePositivePower_smooth L hL K) hA

/-- `c₁(L^{K+1} ⊗ A) = (K+1) c₁(L) + c₁(A)` (geometrically). -/
theorem perturbedBundle_chern_geometricallyEq {L A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hA : IsSourceSmoothHermitianMetric A) (K : ℕ) :
    (sourceNativeFirstChernForm (perturbedBundle L A K) (perturbedBundle_smooth hL hA K)).val.GeometricallyEq
      (((K + 1 : ℕ) : ℝ) • sourceNativeFirstChernForm L hL + sourceNativeFirstChernForm A hA).val := by
  intro c z hz
  rw [sourceNativeTensor_chern_coeff (positivePower L K) A (sourceNativePositivePower_smooth L hL K)
    hA c hz, sourceNativePositivePower_chern_coeff L hL c hz K]
  rfl

/-! ### Indices -/

/-- `stepIndex K r q = r + (K+1) q`, by recursion on `q`. -/
def stepIndex (K r : ℕ) : ℕ → ℕ
  | 0 => r
  | q + 1 => stepIndex K r q + K + 1

theorem stepIndex_eq (K r : ℕ) : ∀ q, stepIndex K r q = r + (K + 1) * q
  | 0 => by simp [stepIndex]
  | q + 1 => by rw [stepIndex, stepIndex_eq K r q]; ring

/-- The fibres of `L^a ⊗ T` and `L^b ⊗ T` for `a = b`. -/
def castTwistedFiber (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (x : X) {a b : ℕ}
    (h : a = b) : (twistedPower L T a).Fiber x ≃ₗ[ℂ] (twistedPower L T b).Fiber x := by
  subst h
  exact LinearEquiv.refl ℂ _

theorem frameCoord_castTwistedFiber {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (e : AtlasFrame L) (f : AtlasFrame T) (x : X) {a b : ℕ} (h : a = b)
    (w : (twistedPower L T a).Fiber x) :
    frameCoord (twistedPowerAtlasFrame e f b) x (castTwistedFiber L T x h w) =
      frameCoord (twistedPowerAtlasFrame e f a) x w := by
  subst h
  rfl

/-! ### Multiplication by `σ^{⊗q}` -/

section Mul

variable (L A T : HermitianHolomorphicLineBundle.{0, 0} n X) (K r : ℕ) {x : X}

/-- **`w ↦ w ⊗ σ^{⊗q}`**, `(L^{r+(K+1)q} ⊗ T)_x → ((L^{K+1} ⊗ A)^q ⊗ (L^r ⊗ T))_x`. -/
def mulAFiber (σ : A.Fiber x) : ∀ q : ℕ, (twistedPower L T (stepIndex K r q)).Fiber x →ₗ[ℂ]
    (twistedPower (perturbedBundle L A K) (twistedPower L T r) q).Fiber x
  | 0 => TensorProduct.mk ℂ ℂ ((twistedPower L T r).Fiber x) 1
  | q + 1 =>
    TensorProduct.lift (mulOneFiber (perturbedBundle L A K) (twistedPower L T r) x q) ∘ₗ
      TensorProduct.map ((TensorProduct.mk ℂ ((positivePower L K).Fiber x) (A.Fiber x)).flip σ)
        (mulAFiber σ q) ∘ₗ
      (shiftFiber (L := L) (T := T) (stepIndex K r q) K x).toLinearMap

variable {L A T K r}

/-- **In product frames `mulAFiber σ q` multiplies coordinates by `(coordinate of σ)^q`.** -/
theorem frameCoord_mulAFiber (eL : AtlasFrame L) (eA : AtlasFrame A) (eT : AtlasFrame T)
    (hL : x ∈ eL.val.baseSet) (hA : x ∈ eA.val.baseSet) (hT : x ∈ eT.val.baseSet)
    (σ : A.Fiber x) :
    ∀ (q : ℕ) (w : (twistedPower L T (stepIndex K r q)).Fiber x),
      frameCoord (twistedPowerAtlasFrame (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA)
          (twistedPowerAtlasFrame eL eT r) q) x (mulAFiber L A T K r σ q w) =
        frameCoord eA x σ ^ q * frameCoord (twistedPowerAtlasFrame eL eT (stepIndex K r q)) x w
  | 0, w => by
    have hr := twistedPowerAtlasFrame_mem eL eT hL hT r
    have h := frameCoord_tensor_tmul (unitAtlasFrame (n := n) (M := X))
      (twistedPowerAtlasFrame eL eT r) (Set.mem_univ x) hr (1 : ℂ) w
    change frameCoord (tensorAtlasFrame unitAtlasFrame (twistedPowerAtlasFrame eL eT r)) x
      ((1 : ℂ) ⊗ₜ[ℂ] w) = _
    rw [h, frameCoord_unit, pow_zero]
    rfl
  | q + 1, w => by
    have hK := positivePowerAtlasFrame_mem eL hL K
    have hL' : x ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA).val.baseSet := ⟨hK, hA⟩
    have hr : x ∈ (twistedPowerAtlasFrame eL eT r).val.baseSet :=
      twistedPowerAtlasFrame_mem eL eT hL hT r
    have hq := twistedPowerAtlasFrame_mem eL eT hL hT (stepIndex K r q)
    have key : (frameCoord (twistedPowerAtlasFrame (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA)
          (twistedPowerAtlasFrame eL eT r) (q + 1)) x).comp
        (TensorProduct.lift (mulOneFiber (perturbedBundle L A K) (twistedPower L T r) x q) ∘ₗ
          TensorProduct.map ((TensorProduct.mk ℂ ((positivePower L K).Fiber x) (A.Fiber x)).flip σ)
            (mulAFiber L A T K r σ q)) =
        (frameCoord eA x σ ^ (q + 1)) •
          frameCoord (tensorAtlasFrame (positivePowerAtlasFrame eL K)
            (twistedPowerAtlasFrame eL eT (stepIndex K r q))) x := by
      apply TensorProduct.ext'
      intro l v
      change frameCoord (twistedPowerAtlasFrame (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA)
          (twistedPowerAtlasFrame eL eT r) (q + 1)) x
          (mulOneFiber (perturbedBundle L A K) (twistedPower L T r) x q (l ⊗ₜ[ℂ] σ)
            (mulAFiber L A T K r σ q v)) =
        frameCoord eA x σ ^ (q + 1) * frameCoord (tensorAtlasFrame (positivePowerAtlasFrame eL K)
          (twistedPowerAtlasFrame eL eT (stepIndex K r q))) x (l ⊗ₜ[ℂ] v)
      rw [frameCoord_mulOneFiber _ _ hL' hr q, frameCoord_mulAFiber eL eA eT hL hA hT σ q v,
        frameCoord_tensor_tmul _ _ hK hA, frameCoord_tensor_tmul _ _ hK hq]
      ring
    have h2 := LinearMap.congr_fun key (shiftFiber (L := L) (T := T) (stepIndex K r q) K x w)
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h2
    change frameCoord (twistedPowerAtlasFrame (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA)
        (twistedPowerAtlasFrame eL eT r) (q + 1)) x
      ((TensorProduct.lift (mulOneFiber (perturbedBundle L A K) (twistedPower L T r) x q) ∘ₗ
        TensorProduct.map ((TensorProduct.mk ℂ ((positivePower L K).Fiber x) (A.Fiber x)).flip σ)
          (mulAFiber L A T K r σ q))
        (shiftFiber (L := L) (T := T) (stepIndex K r q) K x w)) = _
    rw [h2]
    have h3 := frameCoord_shiftFiber eL eT hL hT (stepIndex K r q) K w
    exact congrArg (frameCoord eA x σ ^ (q + 1) * ·) h3

end Mul

end SGPT.Trace.RestVol
