import SGPT.Trace.BertiniFamilyNormalTangent
import SGPT.Trace.BertiniFamilyNormalPhysical
import SGPT.Trace.BertiniGlobalPhysicalAdjunction
import SGPT.Trace.NativeCanonicalPhysicalDensity
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Actual original member tangent values behind the normal physical density. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyNormalMemberTangent :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      let q := finv F z
      letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      Fin d → TangentSpace 𝓘(ℂ, ComplexModel d)
        (⟨q.val.2,q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  dsimp only
  let q := finv F z
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  intro j
  let u := familyNormalChartTangentEquiv p i a v U hsm F z hz
    ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j.castSucc)
  have hu : u ∈ LinearMap.ker
      (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q).toLinearMap := by
    change mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q u = 0
    rw [familyParameter_flatInverse_derivative p i a v U hsm F hF z hz]
    simp [EuclideanSpace.basisFun_apply]
  exact K.symm ⟨u,hu⟩

theorem familyNormalMemberTangent_lift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target),
      let q := finv F z
      letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      ∀ j : Fin d, familyMemberTangent p i a v U hsm q.val.1
        (⟨q.val.2,q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))
        (familyNormalMemberTangent p i a v U hsm F hF z hz j) =
      familyNormalChartTangentEquiv p i a v U hsm F z hz
        ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j.castSucc) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  dsimp only
  let q := finv F z
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  intro j
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  change (K (K.symm _)).val = _
  rw [K.apply_symm_apply]

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle (d + 1) X)

def familyNormalMemberValue :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      (familyNativePhysicalModel p i a v U hsm L).Fiber (finv F z) →ₗ[ℂ] L.Fiber (finv F z).val.2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  let q := finv F z
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous
    (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  let LH := nativeHolomorphicPullbackBundle L
    (nativeBertiniMemberInclusionMap p i (a - q.val.1.val 0 • v) (hsm q.val.1))
  let J := nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1) L y
  exact (nativeCanonicalPhysicalValue LH y (familyNormalMemberTangent p i a v U hsm F hF z hz)).comp J.toLinearMap

theorem familyNormalMemberValue_tmul :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target),
      let q := finv F z
      letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
      letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous
        (affinePoint i (a - q.val.1.val 0 • v))).isCompact
      ∀ (A : (familyNativeCanonicalModel p i a v U hsm).Fiber q) (l : L.Fiber q.val.2),
      familyNormalMemberValue p i a v U hsm L F hF z hz (A ⊗ₜ[ℂ] l) =
        nativeCanonicalFiberEquiv (n := d) (⟨q.val.2,q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))
          (nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1)
            (⟨q.val.2,q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) A)
          (familyNormalMemberTangent p i a v U hsm F hF z hz) • l := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  dsimp only
  intros
  rfl

theorem familyNormalPhysicalValue_member_sign :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target),
      familyNormalPhysicalValue p i a v U hsm L F z hz =
        Equiv.Perm.sign (finRotate (d + 1)) • familyNormalMemberValue p i a v U hsm L F hF z hz := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  let q := finv F z
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous
    (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let tuple := fun r => familyNormalChartTangentEquiv p i a v U hsm F z hz (b r)
  let nu := tuple (Fin.last d)
  let tang := fun j : Fin d => tuple j.castSucc
  let u := familyNormalMemberTangent p i a v U hsm F hF z hz
  have hnu : mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q nu = (1 : ℂ) := by
    change mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q
      (familyNormalChartTangentEquiv p i a v U hsm F z hz (b (Fin.last d))) = (1 : ℂ)
    rw [familyParameter_flatInverse_derivative p i a v U hsm F hF z hz]
    simp [b, EuclideanSpace.basisFun_apply]
  have htang : (fun j => familyMemberTangent p i a v U hsm q.val.1 y (u j)) = tang := by
    funext j
    exact familyNormalMemberTangent_lift p i a v U hsm F hF z hz j
  have hfirst (A : (familyNativeCanonicalModel p i a v U hsm).Fiber q) :
      familyNativeCanonicalFiberEquiv p i a v U hsm q A (Matrix.vecCons nu tang) =
        nativeCanonicalFiberEquiv (n := d) y
          (nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1) y A) u := by
    have h := familyNativeCanonicalFiberEquiv_any_normal p i a v U hsm q A nu hnu u
    rw [htang] at h
    exact h
  have hsnoc : Fin.snoc tang nu = tuple := by
    funext r
    refine Fin.lastCases ?_ (fun j => ?_) r
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
  have hrot : (Matrix.vecCons nu tang) ∘ finRotate (d + 1) = tuple :=
    (Fin.snoc_eq_cons_rotate tang nu).symm.trans hsnoc
  apply TensorProduct.ext
  apply LinearMap.ext
  intro A
  apply LinearMap.ext
  intro l
  change familyNormalPhysicalValue p i a v U hsm L F z hz (A ⊗ₜ[ℂ] l) =
    Equiv.Perm.sign (finRotate (d + 1)) • familyNormalMemberValue p i a v U hsm L F hF z hz (A ⊗ₜ[ℂ] l)
  rw [familyNormalPhysicalValue_tmul, familyNormalMemberValue_tmul]
  let beta := (familyNativeCanonicalFiberEquiv p i a v U hsm q A).smulRight l
  have h := beta.map_perm (Matrix.vecCons nu tang) (finRotate (d + 1))
  rw [hrot] at h
  have hc := congrArg (fun c : ℂ => c • l) (hfirst A)
  exact h.trans (congrArg (fun l' : L.Fiber q.val.2 => Equiv.Perm.sign (finRotate (d + 1)) • l') hc)

theorem familyNormalPhysicalValue_norm_member :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target)
      (s : (familyNativePhysicalModel p i a v U hsm L).Fiber (finv F z)),
      ‖familyNormalPhysicalValue p i a v U hsm L F z hz s‖ ^ 2 =
        ‖familyNormalMemberValue p i a v U hsm L F hF z hz s‖ ^ 2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz s
  rw [familyNormalPhysicalValue_member_sign p i a v U hsm L F hF z hz, LinearMap.smul_apply,
    norm_units_zsmul]

theorem familyNormalPhysicalDensity_eq_member :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (w : familyIncidence p i a v U → ℝ≥0∞) (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target),
      familyNormalPhysicalDensity p i a v U hsm L F S w z =
        ENNReal.ofReal (‖familyNormalMemberValue p i a v U hsm L F hF z hz (S (finv F z))‖ ^ 2) * w (finv F z) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S w z hz
  rw [familyNormalPhysicalDensity_eq_value p i a v U hsm L F S w z hz,
    familyNormalPhysicalValue_norm_member p i a v U hsm L F hF z hz]

end SGPT.Trace.BertiniFamilyCanonical
