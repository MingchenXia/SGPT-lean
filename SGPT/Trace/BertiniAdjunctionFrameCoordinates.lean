import SGPT.Trace.BertiniGlobalOriginalAdjunctionOverlap
import SGPT.Trace.BertiniCanonicalPreferredFrameCoordinates
import SGPT.Trace.BertiniLocalOriginalChartNormal
import SGPT.Trace.BertiniNativeChartCofactor

/-! Exact actual native-frame cofactor formula for original global adjunction.
All normals, derivative columns and canonical-frame interpretations are
produced from original geometry. Full incidence retains base O_Lambda(1). -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

def nativeBertiniMemberInclusionMap
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
      (member p (affinePoint i ζ)) X ∞ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  exact ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d)
    (nativeBertiniMemberRegularity p i ζ hsm)⟩

variable [CompactSpace X]

theorem nativeBertiniAdjunctionFrameCoefficient_tmul
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y₀ : member p (affinePoint i ζ)) (x₀ : X) (j : Fin (N + 1)) (m : Fin (d + 1))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (_hy : y ∈ (complexChartAt (n := d) y₀).val.source)
      (_hx : y.val ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (hpj : p y.val ∈ (affineChart j).source)
      (_hm : chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i ζ j) y.val ≠ 0)
      (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      (w : (nativeBertiniHyperplaneBundle p).Fiber y.val),
      ((nativeCanonicalFrame (n := d) y₀).val
        ⟨y, nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)⟩).2 =
      ((nativeCanonicalFrame (n := d + 1) x₀).val ⟨y.val, α⟩).2 *
        nativeBertiniCoordinateFiberEquiv p j y.val hpj w *
        (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
          (nativeBertiniLocalEquation p i ζ j) y.val)⁻¹ *
        nativeChartCofactor (nativeBertiniMemberInclusionMap p i ζ hsm)
          (complexChartAt (n := d) y₀) (complexChartAt (n := d + 1) x₀) m
          ((complexChartAt (n := d) y₀).val y) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hy hx hpj hm α w
  let eH := complexChartAt (n := d) y₀
  let eX := complexChartAt (n := d + 1) x₀
  let A := nativeOriginalChartTangentEquiv eX y.val hx
  let B := nativeOriginalChartTangentEquiv eH y hy
  let b := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
  let bX := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let C := nativeBertiniCoordinateFiberEquiv p j y.val hpj
  let gm := chartDeriv eX (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j) y.val
  let ν := nativeBertiniLocalChartNormal p i ζ j eX m y.val hx
  let inc := nativeBertiniMemberInclusionMap p i ζ hsm
  let D := mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
    (Subtype.val : member p (affinePoint i ζ) → X) y
  let v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y := fun k => B.symm (b k)
  have hν : nativeBertiniIntrinsicConormal p i ζ y.val y.property (C w • ν) = w := by
    rw [map_smul, nativeBertiniLocalChartNormal_spec p i ζ j eX m y.val hx hpj y.property hm]
    apply C.injective
    rw [map_smul]
    have hs : C (nativeBertiniCoordinateSection p j y.val) = 1 :=
      nativeBertiniCoordinateFiberEquiv_coordinate p j y.val hpj
    rw [hs, smul_eq_mul, mul_one]
  have hH := nativeCanonicalFiberInPreferredChart_coordinates (n := d) y₀ y hy
    (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)) b
  rw [Module.Basis.det_self, mul_one] at hH
  change nativeCanonicalFiberEquiv (n := d) y
    (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)) v = _ at hH
  rw [← hH, nativeBertiniAdjunctionFiberEquiv_any_normal p i ζ hsm y α w (C w • ν) hν v]
  let V := Matrix.vecCons (C w • ν) (fun k => D (v k))
  have hX := nativeCanonicalFiberInPreferredChart_coordinates (n := d + 1) x₀ y.val hx α
    (fun k => A (V k))
  change nativeCanonicalFiberEquiv (n := d + 1) y.val α
    (fun k => A.symm (A (V k))) = _ at hX
  simp only [LinearEquiv.symm_apply_apply] at hX
  change nativeCanonicalFiberEquiv (n := d + 1) y.val α V = _
  rw [hX]
  have hD (k : Fin d) : fderiv ℂ (coordinateMap inc eH eX) (eH.val y) (b k) =
      A (D (B.symm (b k))) := by
    have h := coordinateMap_fderiv_fixed_native_charts_apply inc eH eX y hy hx (b k)
    exact h
  have hV : (fun k => A (V k)) = Matrix.vecCons (C w • (gm⁻¹ • EuclideanSpace.single m 1))
      (fun k => fderiv ℂ (coordinateMap inc eH eX) (eH.val y) (b k)) := by
    funext k
    cases k using Fin.cases with
    | zero =>
      change A (C w • A.symm (gm⁻¹ • EuclideanSpace.single m 1)) = _
      rw [map_smul, LinearEquiv.apply_symm_apply]
      rfl
    | succ k => exact (hD k).symm
  rw [hV, AlternatingMap.map_vecCons_smul, AlternatingMap.map_vecCons_smul]
  have hb (k : Fin d) : b k = EuclideanSpace.single k 1 := by
    change (EuclideanSpace.basisFun (Fin d) ℂ) k = _
    rw [EuclideanSpace.basisFun_apply]
  have hvol : bX.det (Matrix.vecCons (EuclideanSpace.single m 1)
      (fun k => fderiv ℂ (coordinateMap inc eH eX) (eH.val y) (b k))) =
      nativeChartCofactor inc eH eX m (eH.val y) := by
    simp_rw [hb]
    exact (nativeChartCofactor_eq_volume inc eH eX m (eH.val y)).symm
  rw [hvol]
  change _ * (C w * (gm⁻¹ * nativeChartCofactor inc eH eX m (eH.val y))) = _
  ring


theorem nativeBertiniAdjunctionFrameCoefficient
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y₀ : member p (affinePoint i ζ)) (x₀ : X) (j : Fin (N + 1)) (m : Fin (d + 1))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (_hy : y ∈ (complexChartAt (n := d) y₀).val.source)
      (_hx : y.val ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hpj : p y.val ∈ (affineChart j).source)
      (_hm : chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i ζ j) y.val ≠ 0)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (_hP : y.val ∈ eP.val.baseSet)
      (T : (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)).Fiber y.val),
      ((nativeCanonicalFrame (n := d) y₀).val
        ⟨y, nativeBertiniAdjunctionFiberEquiv p i ζ hsm y T⟩).2 =
      ((tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP).val ⟨y.val, T⟩).2 *
        ((eP.val ⟨y.val, nativeBertiniCoordinateSection p j y.val⟩).2)⁻¹ *
        (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
          (nativeBertiniLocalEquation p i ζ j) y.val)⁻¹ *
        nativeChartCofactor (nativeBertiniMemberInclusionMap p i ζ hsm)
          (complexChartAt (n := d) y₀) (complexChartAt (n := d + 1) x₀) m
          ((complexChartAt (n := d) y₀).val y) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hy hx hpj hm eP hP T
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  let eH := nativeCanonicalFrame (n := d) y₀
  let q := tensorAtlasFrame eK eP
  let := eK.property
  let := eH.property
  let := eP.property
  let := q.property
  have hK : y.val ∈ eK.val.baseSet := hx
  have hH : y ∈ eH.val.baseSet := hy
  have hq : y.val ∈ q.val.baseSet := ⟨hK, hP⟩
  let c := ((eP.val ⟨y.val, nativeBertiniCoordinateSection p j y.val⟩).2)⁻¹ *
    (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
      (nativeBertiniLocalEquation p i ζ j) y.val)⁻¹ *
    nativeChartCofactor (nativeBertiniMemberInclusionMap p i ζ hsm)
      (complexChartAt (n := d) y₀) (complexChartAt (n := d + 1) x₀) m
      ((complexChartAt (n := d) y₀).val y)
  let F := (eH.val.linearEquivAt ℂ y hH).toLinearMap.comp
    (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y).toLinearMap
  let G := c • (q.val.linearEquivAt ℂ y.val hq).toLinearMap
  have hFG : F = G := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro w
    change (eH.val ⟨y, nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)⟩).2 =
      c * (q.val ⟨y.val, α ⊗ₜ[ℂ] w⟩).2
    rw [nativeBertiniAdjunctionFrameCoefficient_tmul p i ζ hsm y₀ x₀ j m y hy hx hpj hm]
    have hcoord : (q.val ⟨y.val, α ⊗ₜ[ℂ] w⟩).2 =
        (eK.val ⟨y.val, α⟩).2 * (eP.val ⟨y.val, w⟩).2 := by
      change tensorCoordinate _ _ eK.val eP.val y.val (α ⊗ₜ[ℂ] w) = _
      rw [tensorCoordinate_tmul, Trivialization.coe_linearMapAt_of_mem eK.val hK,
        Trivialization.coe_linearMapAt_of_mem eP.val hP]
    rw [hcoord]
    have hratio := nativeNonzeroFiberScalarEquiv_in_frame (nativeBertiniHyperplaneBundle p)
      y.val (nativeBertiniCoordinateSection p j y.val)
      (nativeBertiniCoordinateSection_ne_zero p j y.val hpj) eP hP w
    change nativeBertiniCoordinateFiberEquiv p j y.val hpj w = _ at hratio
    rw [hratio]
    dsimp only [c, eK]
    ring
  have h := LinearMap.congr_fun hFG T
  change (eH.val ⟨y, nativeBertiniAdjunctionFiberEquiv p i ζ hsm y T⟩).2 =
    c * (q.val ⟨y.val, T⟩).2 at h
  rw [h]
  dsimp only [c, q, eK]
  ring

end SGPT.Trace.Bertini
