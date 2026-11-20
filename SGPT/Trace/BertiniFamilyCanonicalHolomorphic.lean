import SGPT.Trace.BertiniFamilyCanonicalCofactor
import SGPT.Bergman.SourceTensorDictionary

/-! Actual holomorphic nonzero native family canonical frame coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

private theorem actualDeterminant_contMDiffAt {m n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (M : Y → Matrix (Fin n) (Fin n) ℂ) (q : Y)
    (hM : ∀ r s, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) ∞ (fun y => M y r s) q) :
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) ∞ (fun y => (M y).det) q := by
  classical
  simp only [Matrix.det_apply]
  apply ContMDiffAt.sum
  intro σ _
  have hp : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) ∞
      (fun y => ∏ r : Fin n, M y (σ r) r) q := by
    apply ContMDiffAt.prod
    intro r _
    exact hM (σ r) r
  have hc := (contMDiffAt_const (c := (((Equiv.Perm.sign σ : ℤ) : ℂ)))).mul hp
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with y
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Pi.mul_apply]

private theorem actualStandardVolume_eq_det {n : ℕ} (v : Fin n → ComplexModel n) :
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det v =
      Matrix.det (fun r k => v k r) := by
  rw [Module.Basis.det_apply]
  apply congrArg Matrix.det
  funext r k
  rfl

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem contMDiffAt_familyParameterKernelVolume :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (k : Fin (d + 1))
      (q : familyIncidence p i a v U) (_hq : q ∈ e.val.source)
      (_hk : chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q ≠ 0),
      ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (familyParameterKernelVolume p i a v U hsm e k) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e k q hq hk
  let l := fun r => chartDeriv e (EuclideanSpace.single r 1) (scalarParameter p i a v U)
  have hl (r : Fin (d + 1)) := contMDiffAt_familyParameterPartial p i a v U hsm e r q hq
  have hinv := (hl k).inv₀ hk
  have hentry (r s : Fin (d + 1)) :
      ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (fun y => Matrix.vecCons ((l k y)⁻¹ • EuclideanSpace.single k 1)
          (fun j => familyParameterKernelVector p i a v U hsm e k j y) s r) q := by
    cases s using Fin.cases with
    | zero =>
      change ContMDiffAt _ _ ∞ (fun y => (l k y)⁻¹ * (EuclideanSpace.single k (1 : ℂ)) r) q
      exact hinv.mul contMDiffAt_const
    | succ j =>
      change ContMDiffAt _ _ ∞ (fun y => (EuclideanSpace.single (k.succAbove j) (1 : ℂ)) r -
        ((l k y)⁻¹ * l (k.succAbove j) y) * (EuclideanSpace.single k (1 : ℂ)) r) q
      exact contMDiffAt_const.sub ((hinv.mul (hl (k.succAbove j))).mul contMDiffAt_const)
  have h := actualDeterminant_contMDiffAt
    (fun y r s => Matrix.vecCons ((l k y)⁻¹ • EuclideanSpace.single k 1)
      (fun j => familyParameterKernelVector p i a v U hsm e k j y) s r) q hentry
  apply h.congr_of_eventuallyEq
  filter_upwards [] with y
  exact actualStandardVolume_eq_det _

theorem contMDiffAt_familyProjectedKernelVolume :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (eX : ComplexChart (d + 1) X)
      (k m : Fin (d + 1)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source) (_hx : q.val.2 ∈ eX.val.source)
      (_hk : chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q ≠ 0),
      ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (familyProjectedKernelVolume p i a v U hsm e eX k m) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e eX k m q hq hx hk
  let l := fun r => chartDeriv e (EuclideanSpace.single r 1) (scalarParameter p i a v U)
  let J := fun y => fderiv ℂ (coordinateMap (familyNativeXMap p i a v U hsm) e eX) (e.val y)
  have hl (r : Fin (d + 1)) := contMDiffAt_familyParameterPartial p i a v U hsm e r q hq
  have hinv := (hl k).inv₀ hk
  have hJ (c r : Fin (d + 1)) := contMDiffAt_familyXJacobianEntry p i a v U hsm e eX c r q hq hx
  have hentry (r s : Fin (d + 1)) : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
      (fun y => Matrix.vecCons (EuclideanSpace.single m 1)
        (fun j => J y (familyParameterKernelVector p i a v U hsm e k j y)) s r) q := by
    cases s using Fin.cases with
    | zero => exact contMDiffAt_const
    | succ j =>
      apply ((hJ (k.succAbove j) r).sub ((hinv.mul (hl (k.succAbove j))).mul (hJ k r))).congr_of_eventuallyEq
      filter_upwards [] with y
      change (J y (EuclideanSpace.single (k.succAbove j) 1 -
        ((l k y)⁻¹ * l (k.succAbove j) y) • EuclideanSpace.single k 1)) r = _
      rw [map_sub, map_smul]
      rfl
  have h := actualDeterminant_contMDiffAt
    (fun y r s => Matrix.vecCons (EuclideanSpace.single m 1)
      (fun j => J y (familyParameterKernelVector p i a v U hsm e k j y)) s r) q hentry
  apply h.congr_of_eventuallyEq
  filter_upwards [] with y
  exact actualStandardVolume_eq_det _

variable [CompactSpace X]

def familyCanonicalModelFrame (x₀ : X) (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    AtlasFrame (familyNativeCanonicalModel p i a v U hsm) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let e := tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP
  exact ⟨e.val.pullback (familyNativeXMap p i a v U hsm), by
    constructor
    exact ⟨e.val, e.property, rfl⟩⟩

theorem familyCanonicalModelFrame_symm (x₀ : X) (eP : AtlasFrame (nativeBertiniHyperplaneBundle p))
    (q : familyIncidence p i a v U)
    (_hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source) (_hP : q.val.2 ∈ eP.val.baseSet) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (familyCanonicalModelFrame p i a v U hsm x₀ eP).val.symm q 1 =
      (nativeCanonicalFrame (n := d + 1) x₀).val.symm q.val.2 1 ⊗ₜ[ℂ] eP.val.symm q.val.2 1 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  change ((tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP).val.pullback
    (familyNativeXMap p i a v U hsm)).symm q 1 = _
  rw [nativeHolomorphicPullbackFrame_symm _ _ _ (show q.val.2 ∈
    (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP).val.baseSet from ⟨_hx, _hP⟩)]
  change (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP).val.symm q.val.2 1 = _
  exact (tensorAtlasFrame_symm (nativeCanonicalFrame (n := d + 1) x₀) eP ⟨_hx, _hP⟩ (1 : ℂ)).trans (one_smul _ _)

def familyModelCanonicalFrameCoefficient :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) → X →
      AtlasFrame (nativeBertiniHyperplaneBundle p) → familyIncidence p i a v U → ℂ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e x₀ eP q => if hq : q ∈ e.val.source then
    familyCanonicalCoordinateValue p i a v U hsm e q hq
      ((familyCanonicalModelFrame p i a v U hsm x₀ eP).val.symm q 1) else 0

theorem familyModelCanonicalFrameCoefficient_ne_zero :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (x₀ : X)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source) (_hx : q.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hP : q.val.2 ∈ eP.val.baseSet), familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q ≠ 0 := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e x₀ eP q hq hx hP
  let f := familyCanonicalModelFrame p i a v U hsm x₀ eP
  let := f.property
  have hf : q ∈ f.val.baseSet := ⟨hx, hP⟩
  have hs : f.val.symm q 1 ≠ 0 := by
    intro hz
    have h := congrArg Prod.snd (f.val.apply_mk_symm hf (1 : ℂ))
    change f.val.linearEquivAt ℂ q hf (f.val.symm q 1) = 1 at h
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have ht : familyNativeCanonicalFiberEquiv p i a v U hsm q (f.val.symm q 1) ≠ 0 := by
    intro hz
    apply hs
    apply (familyNativeCanonicalFiberEquiv p i a v U hsm q).injective
    rw [hz, map_zero]
  let A := nativeOriginalChartTangentEquiv e q hq
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.map A.symm
  have hval := (familyNativeCanonicalFiberEquiv p i a v U hsm q (f.val.symm q 1)).map_basis_ne_zero_iff b |>.mpr ht
  change familyCanonicalCoordinateValue p i a v U hsm e q hq (f.val.symm q 1) ≠ 0 at hval
  unfold familyModelCanonicalFrameCoefficient
  rw [dif_pos hq]
  exact hval


theorem contMDiffAt_familyModelCanonicalFrameCoefficient :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (x₀ : X)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (q₀ : familyIncidence p i a v U)
      (_hq : q₀ ∈ e.val.source) (_hx : q₀.val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hP : q₀.val.2 ∈ eP.val.baseSet),
      ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP) q₀ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e x₀ eP q₀ hq₀ hx₀ hP₀
  let := eP.property
  let eX := complexChartAt (n := d + 1) x₀
  let eT := complexChartAt (n := 1) q₀.val.1
  let j := chartIndex (p q₀.val.2)
  have hpj₀ : p q₀.val.2 ∈ (affineChart j).source := mem_affineChart_chartIndex _
  obtain ⟨k, hk₀⟩ := exists_familyParameterChartPartial_ne_zero p i a v U hsm e q₀ hq₀
  obtain ⟨m, hm₀⟩ := exists_nativeBertiniChartPartial_ne_zero p i (a - q₀.val.1.val 0 • v)
    j eX q₀.val.2 hx₀ hpj₀ q₀.property (hsm q₀.val.1)
  let cs : familyIncidence p i a v U → ℂ :=
    fun q => (eP.val ⟨q.val.2, nativeBertiniCoordinateSection p j q.val.2⟩).2
  let gm : familyIncidence p i a v U → ℂ := fun q => chartDeriv eX (EuclideanSpace.single m 1)
    (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2
  have hcsX : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
      (fun x => (eP.val ⟨x, nativeBertiniCoordinateSection p j x⟩).2) q₀.val.2 :=
    (eP.val.contMDiffAt_section_iff hP₀).mp ((nativeBertiniCoordinateSection p j).contMDiff q₀.val.2)
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞ cs q₀ := by
    have h := hcsX.comp q₀ (show ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1))
      𝓘(ℂ, ComplexModel (d + 1)) ∞ (fun q : familyIncidence p i a v U => q.val.2) q₀ from
      (familyNativeXMap p i a v U hsm).contMDiff.contMDiffAt)
    exact h
  have hcsne : cs q₀ ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p j q₀.val.2 hpj₀
    apply (eP.val.linearEquivAt ℂ q₀.val.2 hP₀).injective
    exact hz.trans (map_zero _).symm
  have hgm : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞ gm q₀ :=
    contMDiffAt_familyVerticalPartial p i a v U hsm eT eX j m q₀
      (mem_complexChartAt_source _) hx₀ hpj₀
  have hl := contMDiffAt_familyParameterPartial p i a v U hsm e k q₀ hq₀
  have hN := contMDiffAt_familyProjectedKernelVolume p i a v U hsm e eX k m q₀ hq₀ hx₀ hk₀
  have hD := contMDiffAt_familyParameterKernelVolume p i a v U hsm e k q₀ hq₀ hk₀
  have hDne := familyParameterKernelVolume_ne_zero p i a v U hsm e k q₀ hk₀
  have hR := (((hcs.inv₀ hcsne).mul (hgm.inv₀ hm₀)).mul hN).div₀ hD hDne
  apply hR.congr_of_eventuallyEq
  have hnearX := (familyNativeXMap p i a v U hsm).contMDiff.continuous.continuousAt.eventually
    (eX.val.open_source.mem_nhds hx₀)
  have hnearP := (familyNativeXMap p i a v U hsm).contMDiff.continuous.continuousAt.eventually
    (eP.val.open_baseSet.mem_nhds hP₀)
  have hnearj := (p.contMDiff.continuous.comp (familyNativeXMap p i a v U hsm).contMDiff.continuous).continuousAt.eventually
    ((affineChart j).open_source.mem_nhds hpj₀)
  have hlcont : ContinuousAt (chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U)) q₀ := hl.continuousAt
  have hgmcont : ContinuousAt gm q₀ := hgm.continuousAt
  filter_upwards [e.val.open_source.mem_nhds hq₀, hnearX, hnearP, hnearj,
    hlcont.eventually_ne hk₀, hgmcont.eventually_ne hm₀] with q hq hx hP hpj hk hm
  unfold familyModelCanonicalFrameCoefficient
  rw [dif_pos hq, familyCanonicalModelFrame_symm p i a v U hsm x₀ eP q hx hP,
    familyCanonicalCoordinateValue_tmul p i a v U hsm e k q hq hk x₀ j m hx hpj hm]
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  have hK1 : (eK.val ⟨q.val.2, eK.val.symm q.val.2 1⟩).2 = 1 :=
    congrArg Prod.snd (eK.val.apply_mk_symm hx (1 : ℂ))
  have hP1 : (eP.val ⟨q.val.2, eP.val.symm q.val.2 1⟩).2 = 1 :=
    congrArg Prod.snd (eP.val.apply_mk_symm hP (1 : ℂ))
  have hratio := nativeNonzeroFiberScalarEquiv_in_frame (nativeBertiniHyperplaneBundle p)
    q.val.2 (nativeBertiniCoordinateSection p j q.val.2)
    (nativeBertiniCoordinateSection_ne_zero p j q.val.2 hpj) eP hP (eP.val.symm q.val.2 1)
  change nativeBertiniCoordinateFiberEquiv p j q.val.2 hpj (eP.val.symm q.val.2 1) = _ at hratio
  rw [hP1, one_div] at hratio
  rw [hK1, one_mul, hratio]
  rfl

end SGPT.Trace.BertiniFamilyCanonical
