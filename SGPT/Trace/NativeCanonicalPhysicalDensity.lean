import SGPT.Trace.BertiniCanonicalPreferredFrameCoordinates
import SGPT.Trace.BertiniFixedNativeChartDerivative

/-! Intrinsic actual native canonical coefficients valued in the SAME physical L.
The only norm used is the original physical L norm. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

private def actualCanonicalTupleEvaluation {n : ℕ} {C V : Type*}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup V] [Module ℂ V]
    (F : C ≃ₗ[ℂ] (V [⋀^Fin n]→ₗ[ℂ] ℂ)) (v : Fin n → V) : C →ₗ[ℂ] ℂ where
  toFun α := F α v
  map_add' α β := by rw [map_add, AlternatingMap.add_apply]
  map_smul' a α := by rw [map_smul, AlternatingMap.smul_apply]; rfl

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (L : HermitianHolomorphicLineBundle n X)

def nativeCanonicalPhysicalValue (x : X) (v : Fin n → TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x →ₗ[ℂ] L.Fiber x :=
  (TensorProduct.lid ℂ (L.Fiber x)).toLinearMap.comp (TensorProduct.map
    (actualCanonicalTupleEvaluation (nativeCanonicalFiberEquiv (n := n) x) v) LinearMap.id)

theorem nativeCanonicalPhysicalValue_tmul (x : X)
    (v : Fin n → TangentSpace 𝓘(ℂ, ComplexModel n) x)
    (α : (nativeCanonicalBundle (n := n) (X := X)).Fiber x) (l : L.Fiber x) :
    nativeCanonicalPhysicalValue L x v (α ⊗ₜ[ℂ] l) = nativeCanonicalFiberEquiv (n := n) x α v • l := rfl

def nativeCanonicalPhysicalChartValue (e : ComplexChart n X) (x : X) (hx : x ∈ e.val.source) :
    (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x →ₗ[ℂ] L.Fiber x :=
  nativeCanonicalPhysicalValue L x (fun k => (nativeOriginalChartTangentEquiv e x hx).symm
    ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis k))

def nativeCanonicalPhysicalChartDensity (e : ComplexChart n X) (x : X) (hx : x ∈ e.val.source)
    (T : (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (‖nativeCanonicalPhysicalChartValue L e x hx T‖ ^ 2) * w

theorem nativeCanonicalPhysicalChartValue_change (e f : ComplexChart n X) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source)
    (T : (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) :
    nativeCanonicalPhysicalChartValue L f x hf T =
      LinearMap.det ((nativeOriginalChartTangentEquiv e x he).toLinearMap.comp
        (nativeOriginalChartTangentEquiv f x hf).symm.toLinearMap) •
        nativeCanonicalPhysicalChartValue L e x he T := by
  let A := nativeOriginalChartTangentEquiv e x he
  let B := nativeOriginalChartTangentEquiv f x hf
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let M := A.toLinearMap.comp B.symm.toLinearMap
  let F := nativeCanonicalPhysicalChartValue L f x hf
  let G := (LinearMap.det M) • nativeCanonicalPhysicalChartValue L e x he
  have hFG : F = G := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro l
    change nativeCanonicalFiberEquiv (n := n) x α (fun k => B.symm (b k)) • l =
      LinearMap.det M • (nativeCanonicalFiberEquiv (n := n) x α (fun k => A.symm (b k)) • l)
    let β := nativeCanonicalFiberInChart e x he α
    have htuple : (fun k => A.symm (M (b k))) = fun k => B.symm (b k) := by
      funext k
      exact A.symm_apply_apply (B.symm (b k))
    have hβ := congrArg (fun (a : (ComplexModel n) [⋀^Fin n]→ₗ[ℂ] ℂ) => a (M ∘ b))
      (β.eq_smul_basis_det b)
    change nativeCanonicalFiberEquiv (n := n) x α (fun k => A.symm (M (b k))) =
      β b * b.det (M ∘ b) at hβ
    rw [htuple, Module.Basis.det_comp, Module.Basis.det_self, mul_one] at hβ
    rw [hβ]
    change (β b * LinearMap.det M) • l = LinearMap.det M • ((β b) • l)
    rw [smul_smul, mul_comm]
  exact LinearMap.congr_fun hFG T

theorem nativeCanonicalPhysicalChartDensity_change (e f : ComplexChart n X) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source)
    (T : (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : ℝ≥0∞) :
    nativeCanonicalPhysicalChartDensity L f x hf T w =
      ENNReal.ofReal (‖LinearMap.det ((nativeOriginalChartTangentEquiv e x he).toLinearMap.comp
        (nativeOriginalChartTangentEquiv f x hf).symm.toLinearMap)‖ ^ 2) *
        nativeCanonicalPhysicalChartDensity L e x he T w := by
  unfold nativeCanonicalPhysicalChartDensity
  rw [nativeCanonicalPhysicalChartValue_change, norm_smul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

end SGPT.Trace.Bertini
