import SGPT.Trace.BertiniFamilyIntrinsicContraction
import SGPT.Trace.BertiniFamilyCoefficientRegularity
import SGPT.Trace.BertiniCoordinateKernelBasis
import SGPT.Trace.BertiniFixedNativeChartDerivative

/-! Literal actual native full-family canonical rational cofactor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyParameterKernelVector :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → Fin (d + 1) → Fin d →
      familyIncidence p i a v U → ComplexModel (d + 1) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e k j q => EuclideanSpace.single (k.succAbove j) 1 -
    ((chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q)⁻¹ *
      chartDeriv e (EuclideanSpace.single (k.succAbove j) 1) (scalarParameter p i a v U) q) •
        EuclideanSpace.single k 1

def familyParameterKernelVolume :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → Fin (d + 1) →
      familyIncidence p i a v U → ℂ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e k q => (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
    (Matrix.vecCons ((chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q)⁻¹ •
      EuclideanSpace.single k 1) (fun j => familyParameterKernelVector p i a v U hsm e k j q))

def familyProjectedKernelVolume :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → ComplexChart (d + 1) X →
      Fin (d + 1) → Fin (d + 1) → familyIncidence p i a v U → ℂ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e eX k m q => (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
    (Matrix.vecCons (EuclideanSpace.single m 1) (fun j =>
      fderiv ℂ (coordinateMap (familyNativeXMap p i a v U hsm) e eX) (e.val q)
        (familyParameterKernelVector p i a v U hsm e k j q)))

variable [CompactSpace X]

def familyCanonicalCoordinateValue :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source), (familyNativeCanonicalModel p i a v U hsm).Fiber q →ₗ[ℂ] ℂ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  let A := nativeOriginalChartTangentEquiv e q hq
  exact {
    toFun := fun s => familyNativeCanonicalFiberEquiv p i a v U hsm q s
      (fun j => A.symm ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j))
    map_add' s t := by rw [map_add, AlternatingMap.add_apply]
    map_smul' c s := by rw [map_smul, AlternatingMap.smul_apply]; rfl }

private theorem actualInsert_basis_single (k : Fin (d + 1)) (j : Fin d) :
    tangentCoordinateInsert k ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j) =
      EuclideanSpace.single (k.succAbove j) 1 := by
  ext r
  rcases Fin.eq_self_or_eq_succAbove k r with rfl | ⟨r, rfl⟩
  · simp [tangentCoordinateInsert]
  · simp [tangentCoordinateInsert, EuclideanSpace.basisFun_apply]

omit [CompactSpace X] in
theorem familyParameterKernelVolume_ne_zero :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (k : Fin (d + 1))
      (q : familyIncidence p i a v U)
      (_hk : chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q ≠ 0),
      familyParameterKernelVolume p i a v U hsm e k q ≠ 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e k q hk
  let ell := (fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)).toLinearMap
  have hR (j : Fin d) : (coordinateConormalKernelEquiv ell k hk
      ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)).val =
      familyParameterKernelVector p i a v U hsm e k j q := by
    rw [coordinateConormalKernelEquiv_apply, actualInsert_basis_single]
    rfl
  have h := coordinateConormalTuple_volume_ne_zero ell k hk
  have ht := funext hR
  rw [ht] at h
  exact h

theorem familyCanonicalCoordinateValue_tmul :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (k : Fin (d + 1))
      (q : familyIncidence p i a v U) (hq : q ∈ e.val.source)
      (_hk : chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q ≠ 0)
      (x₀ : X) (j : Fin (N + 1)) (m : Fin (d + 1))
      (_hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (hpj : p q.val.2 ∈ (affineChart j).source)
      (_hm : chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2 ≠ 0)
      (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber q.val.2)
      (w : (nativeBertiniHyperplaneBundle p).Fiber q.val.2),
      familyCanonicalCoordinateValue p i a v U hsm e q hq (α ⊗ₜ[ℂ] w) =
        (((nativeCanonicalFrame (n := d + 1) x₀).val ⟨q.val.2, α⟩).2 *
          nativeBertiniCoordinateFiberEquiv p j q.val.2 hpj w *
          (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
            (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2)⁻¹ *
          familyProjectedKernelVolume p i a v U hsm e (complexChartAt (n := d + 1) x₀) k m q) /
          familyParameterKernelVolume p i a v U hsm e k q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e k q hq hk x₀ j m hx hpj hm α w
  let A := nativeOriginalChartTangentEquiv e q hq
  let eX := complexChartAt (n := d + 1) x₀
  let AX := nativeOriginalChartTangentEquiv eX q.val.2 hx
  let ell := (fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)).toLinearMap
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let W := fun j => familyParameterKernelVector p i a v U hsm e k j q
  let nu0 : ComplexModel (d + 1) := (ell (EuclideanSpace.single k 1))⁻¹ • EuclideanSpace.single k 1
  let nu := A.symm nu0
  let u := fun j => A.symm (W j)
  have hnorm : nativeScalarDifferential (scalarParameter p i a v U) q nu = 1 := by
    rw [familyScalarDifferential_in_chart p i a v U hsm e q hq nu]
    change ell (A (A.symm nu0)) = 1
    rw [LinearEquiv.apply_symm_apply]
    change ell ((ell (EuclideanSpace.single k 1))⁻¹ • EuclideanSpace.single k 1) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (show ell (EuclideanSpace.single k 1) ≠ 0 from hk)
  have hW (j : Fin d) : W j ∈ LinearMap.ker ell := by
    have h := (coordinateConormalKernelEquiv ell k hk
      ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)).property
    have hR : (coordinateConormalKernelEquiv ell k hk
        ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)).val = W j := by
      rw [coordinateConormalKernelEquiv_apply, actualInsert_basis_single]
      rfl
    rw [hR] at h
    exact h
  have hu (j : Fin d) : nativeScalarDifferential (scalarParameter p i a v U) q (u j) = 0 := by
    rw [familyScalarDifferential_in_chart p i a v U hsm e q hq (u j)]
    change ell (A (A.symm (W j))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hW j
  have hF := familyNativeCanonicalFiberEquiv_X_coordinates p i a v U hsm q x₀ j m hx hpj hm α w nu hnorm u hu
  have hX (r : Fin d) : AX (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
      (familyNativeXMap p i a v U hsm) q (u r)) =
      fderiv ℂ (coordinateMap (familyNativeXMap p i a v U hsm) e eX) (e.val q) (W r) := by
    exact (coordinateMap_fderiv_fixed_native_charts_apply (familyNativeXMap p i a v U hsm)
      e eX q hq hx (W r)).symm
  have htX := funext hX
  rw [htX] at hF
  let beta := (familyNativeCanonicalFiberEquiv p i a v U hsm q (α ⊗ₜ[ℂ] w)).compLinearMap A.symm.toLinearMap
  let V := Matrix.vecCons nu0 W
  have hbeta := congrArg (fun F : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ => F V)
    (beta.eq_smul_basis_det b)
  have htuple : (fun r => A.symm (V r)) = Matrix.vecCons nu u := by
    funext r
    cases r using Fin.cases with
    | zero => rfl
    | succ r => rfl
  change familyNativeCanonicalFiberEquiv p i a v U hsm q (α ⊗ₜ[ℂ] w)
      (fun r => A.symm (V r)) =
    familyCanonicalCoordinateValue p i a v U hsm e q hq (α ⊗ₜ[ℂ] w) *
      familyParameterKernelVolume p i a v U hsm e k q at hbeta
  rw [htuple] at hbeta
  apply (eq_div_iff (familyParameterKernelVolume_ne_zero p i a v U hsm e k q hk)).mpr
  exact hbeta.symm.trans hF

end SGPT.Trace.BertiniFamilyCanonical
