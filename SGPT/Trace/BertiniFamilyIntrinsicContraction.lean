import SGPT.Trace.BertiniFamilyCanonicalFibres
import SGPT.Trace.BertiniGlobalOriginalAdjunctionOverlap
import SGPT.Trace.BertiniCanonicalPreferredFrameCoordinates
import SGPT.Trace.BertiniLocalOriginalChartNormal

/-! Actual intrinsic family canonical contraction read in the original native X tangent. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem familyNativeCanonicalFiberEquiv_intrinsic (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber q.val.2)
      (w : (nativeBertiniHyperplaneBundle p).Fiber q.val.2)
      (nu : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q)
      (_hnu : nativeScalarDifferential (scalarParameter p i a v U) q nu = (1 : ℂ))
      (u : Fin d → TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q)
      (_hu : ∀ k, nativeScalarDifferential (scalarParameter p i a v U) q (u k) = 0)
      (nuX : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q.val.2)
      (_hnuX : nativeBertiniIntrinsicConormal p i (a - q.val.1.val 0 • v) q.val.2 q.property nuX = w),
      familyNativeCanonicalFiberEquiv p i a v U hsm q (α ⊗ₜ[ℂ] w) (Matrix.vecCons nu u) =
        nativeCanonicalFiberEquiv (n := d + 1) q.val.2 α
          (Matrix.vecCons nuX (fun k => mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
            (familyNativeXMap p i a v U hsm) q (u k))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  intro α w nu hnu u hu nuX hnuX
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2, q.property⟩
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  let uk (k : Fin d) : LinearMap.ker
      (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q).toLinearMap :=
    ⟨u k, hu k⟩
  let z : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y := fun k => K.symm (uk k)
  have hD (k : Fin d) : familyMemberTangent p i a v U hsm q.val.1 y (z k) = u k := by
    have h := congrArg Subtype.val (K.apply_symm_apply (uk k))
    exact h
  have htuple : (fun k => familyMemberTangent p i a v U hsm q.val.1 y (z k)) = u := funext hD
  have hF := familyNativeCanonicalFiberEquiv_any_normal p i a v U hsm q (α ⊗ₜ[ℂ] w) nu hnu z
  rw [htuple] at hF
  rw [hF, nativeBertiniAdjunctionFiberEquiv_any_normal p i (a - q.val.1.val 0 • v)
    (hsm q.val.1) y α w nuX hnuX z]
  have hX (k : Fin d) :
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
        (Subtype.val : member p (affinePoint i (a - q.val.1.val 0 • v)) → X) y (z k) =
      mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
        (familyNativeXMap p i a v U hsm) q (u k) := by
    have h := congrArg (fun D => D (z k)) (familyMemberTangent_X p i a v U hsm q.val.1 y)
    change mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
        (familyNativeXMap p i a v U hsm) q
        (familyMemberTangent p i a v U hsm q.val.1 y (z k)) = _ at h
    rw [hD k] at h
    exact h.symm
  exact congrArg (fun b => nativeCanonicalFiberEquiv (n := d + 1) q.val.2 α (Matrix.vecCons nuX b)) (funext hX)

theorem familyNativeCanonicalFiberEquiv_X_coordinates (q : familyIncidence p i a v U)
    (x₀ : X) (j : Fin (N + 1)) (m : Fin (d + 1))
    (hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
    (hpj : p q.val.2 ∈ (affineChart j).source)
    (hm : chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
      (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2 ≠ 0) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber q.val.2)
      (w : (nativeBertiniHyperplaneBundle p).Fiber q.val.2)
      (nu : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q)
      (_hnu : nativeScalarDifferential (scalarParameter p i a v U) q nu = (1 : ℂ))
      (u : Fin d → TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q)
      (_hu : ∀ k, nativeScalarDifferential (scalarParameter p i a v U) q (u k) = 0)
      , familyNativeCanonicalFiberEquiv p i a v U hsm q (α ⊗ₜ[ℂ] w) (Matrix.vecCons nu u) =
      ((nativeCanonicalFrame (n := d + 1) x₀).val ⟨q.val.2, α⟩).2 *
        nativeBertiniCoordinateFiberEquiv p j q.val.2 hpj w *
        (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
          (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2)⁻¹ *
        (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
          (Matrix.vecCons (EuclideanSpace.single m 1)
            (fun k => nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) x₀) q.val.2 hx
              (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
                (familyNativeXMap p i a v U hsm) q (u k)))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro α w nu hnu u hu
  let eX := complexChartAt (n := d + 1) x₀
  let A := nativeOriginalChartTangentEquiv eX q.val.2 hx
  let C := nativeBertiniCoordinateFiberEquiv p j q.val.2 hpj
  let gm := chartDeriv eX (EuclideanSpace.single m 1)
    (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2
  let nuX := nativeBertiniLocalChartNormal p i (a - q.val.1.val 0 • v) j eX m q.val.2 hx
  have hnuX : nativeBertiniIntrinsicConormal p i (a - q.val.1.val 0 • v) q.val.2 q.property
      (C w • nuX) = w := by
    rw [map_smul, nativeBertiniLocalChartNormal_spec p i (a - q.val.1.val 0 • v) j eX m
      q.val.2 hx hpj q.property hm]
    apply C.injective
    rw [map_smul, nativeBertiniCoordinateFiberEquiv_coordinate, smul_eq_mul, mul_one]
  rw [familyNativeCanonicalFiberEquiv_intrinsic p i a v U hsm q α w nu hnu u hu (C w • nuX) hnuX]
  let V := Matrix.vecCons (C w • nuX) (fun k =>
    mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
      (familyNativeXMap p i a v U hsm) q (u k))
  have hX := nativeCanonicalFiberInPreferredChart_coordinates (n := d + 1) x₀ q.val.2 hx α
    (fun k => A (V k))
  change nativeCanonicalFiberEquiv (n := d + 1) q.val.2 α
    (fun k => A.symm (A (V k))) = _ at hX
  have hround : (fun k => A.symm (A (V k))) = V := by
    funext k
    exact A.symm_apply_apply (V k)
  rw [hround] at hX
  change nativeCanonicalFiberEquiv (n := d + 1) q.val.2 α V = _
  rw [hX]
  have hV : (fun k => A (V k)) = Matrix.vecCons (C w • (gm⁻¹ • EuclideanSpace.single m 1))
      (fun k => A (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
        (familyNativeXMap p i a v U hsm) q (u k))) := by
    funext k
    cases k using Fin.cases with
    | zero =>
      change A (C w • A.symm (gm⁻¹ • EuclideanSpace.single m 1)) = _
      rw [map_smul, LinearEquiv.apply_symm_apply]
      rfl
    | succ k => rfl
  rw [hV, AlternatingMap.map_vecCons_smul, AlternatingMap.map_vecCons_smul]
  change _ * (C w * (gm⁻¹ * _)) = _
  ring

end SGPT.Trace.BertiniFamilyCanonical
