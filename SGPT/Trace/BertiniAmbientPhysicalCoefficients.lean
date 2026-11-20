import SGPT.Trace.BertiniPreferredSliceSource
import SGPT.Trace.BertiniCanonicalPreferredFrameCoordinates

/-! Actual physical ambient residue numerator in SAME original tensor frames. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

private theorem actualAmbientTensorFrame {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {E F : HermitianHolomorphicLineBundle.{0,0} n Y}
    (e : AtlasFrame E) (f : AtlasFrame F) (x : Y) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet)
    (u : E.Fiber x) (v : F.Fiber x) :
    ((tensorAtlasFrame e f).val ⟨x,u ⊗ₜ[ℂ] v⟩).2 = (e.val ⟨x,u⟩).2 * (f.val ⟨x,v⟩).2 := by
  change tensorCoordinate _ _ e.val f.val x (u ⊗ₜ[ℂ] v) = _
  rw [tensorCoordinate_tmul,Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem f.val hf]

private theorem actualAmbientFiberNorm {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (E : HermitianHolomorphicLineBundle.{0,0} n Y) (e : AtlasFrame E) (x : Y)
    (he : x ∈ e.val.baseSet) (u : E.Fiber x) :
    ‖u‖ = ‖(e.val ⟨x,u⟩).2‖ * frameNorm E.Fiber e.val x := by
  let A := e.val.linearEquivAt ℂ x he
  have hu : u = (e.val ⟨x,u⟩).2 • e.val.symm x 1 := by
    apply A.injective
    rw [map_smul]
    have hone : A (e.val.symm x 1) = 1 := congrArg Prod.snd (e.val.apply_mk_symm he (1 : ℂ))
    rw [hone,smul_eq_mul,mul_one]
    rfl
  calc
    ‖u‖ = ‖(e.val ⟨x,u⟩).2 • e.val.symm x 1‖ := congrArg norm hu
    _ = _ := by rw [norm_smul]; rfl

namespace SliceChart
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalAmbientLValue_frameCoefficient (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (eL : AtlasFrame L)
    (hP : c.tangentPoint q ∈ eP.val.baseSet) (hL : c.tangentPoint q ∈ eL.val.baseSet)
    (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber
      (c.tangentPoint q)) :
    (eL.val ⟨c.tangentPoint q,c.originalAmbientLValue p.contMDiff q L T⟩).2 =
      ((tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) a) eP) eL).val ⟨c.tangentPoint q,T⟩).2 *
      ((eP.val ⟨c.tangentPoint q,nativeBertiniCoordinateSection p c.j (c.tangentPoint q)⟩).2)⁻¹ *
      (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
        (Matrix.vecCons (EuclideanSpace.single c.m 1) (fun j => EuclideanSpace.single (c.m.succAbove j) 1)) := by
  let x := c.tangentPoint q
  let eK := nativeCanonicalFrame (n := d + 1) a
  let eKP := tensorAtlasFrame eK eP
  let eT := tensorAtlasFrame eKP eL
  let := eK.property
  let := eP.property
  let := eL.property
  let := eKP.property
  let := eT.property
  have hx := (c.tangentPoint_chart_coordinates q).1
  have hK : x ∈ eK.val.baseSet := by
    change x ∈ (complexChartAt (n := d + 1) a).val.source
    rw [← ha]
    exact hx
  have hKP : x ∈ eKP.val.baseSet := ⟨hK,hP⟩
  have hT : x ∈ eT.val.baseSet := ⟨hKP,hL⟩
  have hpj : p x ∈ (affineChart c.j).source :=
    (mem_chartLiftDomain_iff p hx).mp (c.tangentPoint_chart_coordinates q).2.2
  let v : Fin (d + 1) → ComplexModel (d + 1) :=
    Matrix.vecCons (EuclideanSpace.single c.m (1 : ℂ)) (fun j => EuclideanSpace.single (c.m.succAbove j) (1 : ℂ))
  let δ := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det v
  let cs := (eP.val ⟨x,nativeBertiniCoordinateSection p c.j x⟩).2
  let F := (eL.val.linearEquivAt ℂ x hL).toLinearMap.comp (c.originalAmbientLValue p.contMDiff q L)
  let G := (cs⁻¹ * δ) • (eT.val.linearEquivAt ℂ x hT).toLinearMap
  have hFG : F = G := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro α
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro l
    change (eL.val.linearEquivAt ℂ x hL)
      ((c.originalAmbientCanonicalNormalCoefficient p.contMDiff q (α ⊗ₜ[ℂ] w)) • l) =
      (cs⁻¹ * δ) * (eT.val ⟨x,(α ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] l⟩).2
    rw [map_smul,smul_eq_mul,c.originalAmbientCanonicalNormalCoefficient_tmul p.contMDiff q,
      actualAmbientTensorFrame eKP eL x hKP hL,actualAmbientTensorFrame eK eP x hK hP]
    have hcan : nativeCanonicalFiberInChart c.e x hx α v = (eK.val ⟨x,α⟩).2 * δ := by
      simpa only [ha] using nativeCanonicalFiberInPreferredChart_coordinates a x hK α v
    have hr := nativeNonzeroFiberScalarEquiv_in_frame (nativeBertiniHyperplaneBundle p) x
      (nativeBertiniCoordinateSection p c.j x) (nativeBertiniCoordinateSection_ne_zero p c.j x hpj) eP hP w
    change nativeBertiniCoordinateFiberEquiv p c.j x hpj w = _ at hr
    rw [hcan]
    let ca : ℂ := (eK.val ⟨x,α⟩).2
    let cp : ℂ := (eP.val ⟨x,w⟩).2
    let cl : ℂ := (eL.val ⟨x,l⟩).2
    let pp : ℂ := nativeBertiniCoordinateFiberEquiv p c.j x hpj w
    change ca * δ * pp * cl = (cs⁻¹ * δ) * (ca * cp * cl)
    have hpp : pp = cp * cs⁻¹ := hr.trans (div_eq_mul_inv _ _)
    rw [hpp]
    ring
  have h := LinearMap.congr_fun hFG T
  change (eL.val ⟨x,c.originalAmbientLValue p.contMDiff q L T⟩).2 = (cs⁻¹ * δ) * (eT.val ⟨x,T⟩).2 at h
  change (eL.val ⟨x,c.originalAmbientLValue p.contMDiff q L T⟩).2 = (eT.val ⟨x,T⟩).2 * cs⁻¹ * δ
  rw [h]
  ring

theorem originalAmbientLValue_frameNorm (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (eL : AtlasFrame L)
    (hP : c.tangentPoint q ∈ eP.val.baseSet) (hL : c.tangentPoint q ∈ eL.val.baseSet)
    (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber
      (c.tangentPoint q)) :
    ‖c.originalAmbientLValue p.contMDiff q L T‖ =
      ‖((tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) a) eP) eL).val ⟨c.tangentPoint q,T⟩).2 *
        ((eP.val ⟨c.tangentPoint q,nativeBertiniCoordinateSection p c.j (c.tangentPoint q)⟩).2)⁻¹ *
        (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
          (Matrix.vecCons (EuclideanSpace.single c.m 1) (fun j => EuclideanSpace.single (c.m.succAbove j) 1))‖ *
      frameNorm L.Fiber eL.val (c.tangentPoint q) := by
  have hn := actualAmbientFiberNorm L eL (c.tangentPoint q) hL (c.originalAmbientLValue p.contMDiff q L T)
  exact hn.trans (congrArg (fun z : ℂ => ‖z‖ * frameNorm L.Fiber eL.val (c.tangentPoint q))
    (c.originalAmbientLValue_frameCoefficient a ha q L eP eL hP hL T))

end SliceChart
end SGPT.Trace.Bertini
