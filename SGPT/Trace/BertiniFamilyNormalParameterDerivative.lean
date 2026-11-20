import SGPT.Trace.BertiniFamilyNormalParameter

/-! Actual native derivatives of the genuine fixed-tau original member maps. -/
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
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel

theorem mfderiv_openComplexModel_val {m : ℕ} (D : TopologicalSpace.Opens (ComplexModel m)) (u : D) :
    mfderiv 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) (Subtype.val : D → ComplexModel m) u =
      ContinuousLinearMap.id ℂ (ComplexModel m) := by
  have heq : (extChartAt 𝓘(ℂ, ComplexModel m) u : D → ComplexModel m) = Subtype.val := by
    funext z
    rfl
  rw [← heq]
  exact mfderiv_extChartAt_self

theorem normalProductEquiv_castSucc (d : ℕ) (q : ComplexModel d × ℂ) (j : Fin d) :
    normalProductEquiv d q j.castSucc = q.1 j := by
  change prodModelEquiv d 1 (q.1,modelOneScalarEquiv.symm q.2) j.castSucc = q.1 j
  simp [prodModelEquiv]

theorem normalProductEquiv_basis (d : ℕ) (j : Fin d) :
    normalProductEquiv d ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j,0) =
      (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis j.castSucc := by
  ext r
  refine Fin.lastCases ?_ (fun r => ?_) r
  · rw [normalProductEquiv_last]
    simp [EuclideanSpace.basisFun_apply]
  · rw [normalProductEquiv_castSucc]
    simp [EuclideanSpace.basisFun_apply]

theorem fderiv_normalProduct_tangent (d : ℕ) (τ : ℂ) (u w : ComplexModel d) :
    fderiv ℂ (fun z : ComplexModel d => normalProductEquiv d (z,τ)) u w = normalProductEquiv d (w,0) := by
  have h := (normalProductEquiv d).hasFDerivAt.comp u
    ((hasFDerivAt_id u).prodMk (hasFDerivAt_const τ u))
  exact congrArg (fun A : ComplexModel d →L[ℂ] ComplexModel (d + 1) => A w) h.fderiv

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem mfderiv_familyNormalSliceLift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (t : U) (u : familyNormalSliceDomain p i a v U hsm F t) (w : ComplexModel d),
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) (familyNormalSliceLift p i a v U hsm F t) u w =
      familyNormalChartTangentEquiv p i a v U hsm F (normalProductEquiv d (u.val,t.val 0)) u.property
        (normalProductEquiv d (w,0)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F t u w
  let η₀ : ComplexModel d → ComplexModel (d + 1) := fun z => normalProductEquiv d (z,t.val 0)
  let η : familyNormalSliceDomain p i a v U hsm F t → ComplexModel (d + 1) := fun z => η₀ z.val
  have hη₀ : ContDiff ℂ ∞ η₀ := (normalProductEquiv d).contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hη : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) ∞ η :=
    hη₀.contMDiff.comp contMDiff_subtype_val
  have hval : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
      (Subtype.val : familyNormalSliceDomain p i a v U hsm F t → ComplexModel d) u :=
    (contMDiff_subtype_val (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
  have hηc := mfderiv_comp u (hη₀.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hval
  rw [mfderiv_eq_fderiv, mfderiv_openComplexModel_val] at hηc
  have hηw : mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) η u w =
      normalProductEquiv d (w,0) := by
    have h := DFunLike.congr_fun hηc w
    change mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) η u w = fderiv ℂ η₀ u.val w at h
    exact h.trans (fderiv_normalProduct_tangent d (t.val 0) u.val w)
  have hcomp := mfderiv_comp u (mdifferentiableAt_finv F u.property) (hη.contMDiffAt.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) (finv F ∘ η) u w = _
  rw [hcomp]
  change mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) (finv F) (η u)
    (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) η u w) = _
  rw [hηw]
  rfl

theorem mfderiv_familyNormalMemberParameter_lift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ (u : familyNormalSliceDomain p i a v U hsm F t) (w : ComplexModel d),
      familyMemberTangent p i a v U hsm t (familyNormalMemberParameter p i a v U hsm F hF t u)
        (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (familyNormalMemberParameter p i a v U hsm F hF t) u w) =
      familyNormalChartTangentEquiv p i a v U hsm F (normalProductEquiv d (u.val,t.val 0)) u.property
        (normalProductEquiv d (w,0)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  dsimp only
  intro u w
  let g := familyNormalMemberParameter p i a v U hsm F hF t
  let l := familyMemberLift p i a v U hsm t
  have hg : l ∘ g = familyNormalSliceLift p i a v U hsm F t := by
    funext x
    exact familyNormalMemberParameter_familyLift p i a v U hsm F hF t x
  have h := DFunLike.congr_fun (mfderiv_comp u (l.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (g.contMDiff.contMDiffAt.mdifferentiableAt (by simp))) w
  rw [hg] at h
  exact h.symm.trans (mfderiv_familyNormalSliceLift p i a v U hsm F t u w)

end SGPT.Trace.BertiniFamilyCanonical
