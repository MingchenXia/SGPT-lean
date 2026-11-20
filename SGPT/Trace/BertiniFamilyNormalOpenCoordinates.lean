import SGPT.Trace.BertiniFamilyNormalParameterDerivative

/-! Produced genuine original open member normal coordinates and both inverses. -/
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

theorem normalProductEquiv_symm_snd (d : ℕ) (z : ComplexModel (d + 1)) :
    ((normalProductEquiv d).symm z).2 = z (Fin.last d) := by
  have h := normalProductEquiv_last d ((normalProductEquiv d).symm z)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

private theorem actualNormalReconstruct (d : ℕ) (z : ComplexModel (d + 1)) (τ : ℂ)
    (h : z (Fin.last d) = τ) :
    normalProductEquiv d (((normalProductEquiv d).symm z).1,τ) = z := by
  have hs := (normalProductEquiv_symm_snd d z).trans h
  rw [← hs]
  exact (normalProductEquiv d).apply_symm_apply z

private def actualModelCodRestrict {n m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (O : TopologicalSpace.Opens (ComplexModel m))
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) Y (ComplexModel m) ∞)
    (h : ∀ y, f y ∈ O) : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) Y O ∞ := by
  refine ⟨fun y => ⟨f y,h y⟩,?_⟩
  apply (ContMDiff.subtypeVal_comp_iff O _).mp
  exact f.contMDiff

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

def familyNormalMemberSource :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (_F : FlatData (d + 1) d (familyIncidence p i a v U) W) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      TopologicalSpace.Opens (member p (affinePoint i (a - t.val 0 • v))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  exact ⟨(familyMemberLift p i a v U hsm t) ⁻¹' F.ambSource,
    F.isOpen_ambSource.preimage (familyMemberLift p i a v U hsm t).contMDiff.continuous⟩

def familyNormalMemberCoordinates :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        (familyNormalMemberSource p i a v U hsm F t) (familyNormalSliceDomain p i a v U hsm F t) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let l := familyMemberLift p i a v U hsm t
  let P : ComplexModel (d + 1) →L[ℂ] ComplexModel d :=
    (ContinuousLinearMap.fst ℂ (ComplexModel d) ℂ).comp (normalProductEquiv d).symm.toContinuousLinearMap
  let raw : ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
      (familyNormalMemberSource p i a v U hsm F t) (ComplexModel d) ∞ := by
    refine ⟨fun y => P (fcoord F (l y.val)),?_⟩
    intro y
    have hsrc : l y.val ∈ F.ambSource := y.property
    have hA : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) ∞ F.amb.val (l y.val) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property) hsrc.1
    have hB : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) ∞ F.flat (F.amb.val (l y.val)) :=
      (contDiffAt_of_differentiableOn_complex F.differentiableOn_flat F.flat.open_source hsrc.2).contMDiffAt
    have hcoord : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) ∞
        (fcoord F) (l y.val) := hB.comp (l y.val) hA
    have hl : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) ∞
        (fun y : familyNormalMemberSource p i a v U hsm F t => l y.val) :=
      l.contMDiff.comp contMDiff_subtype_val
    have hfull : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) ∞
        (fun y : familyNormalMemberSource p i a v U hsm F t => fcoord F (l y.val)) y :=
      ContMDiffAt.comp (f := fun y : familyNormalMemberSource p i a v U hsm F t => l y.val) (g := fcoord F) y hcoord (show ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) ∞
        (fun y : familyNormalMemberSource p i a v U hsm F t => l y.val) y from hl.contMDiffAt)
    have hP : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel d) ∞ P (fcoord F (l y.val)) :=
      (show ContDiff ℂ ∞ P from P.contDiff).contMDiff.contMDiffAt
    exact hP.comp y hfull
  apply actualModelCodRestrict (familyNormalSliceDomain p i a v U hsm F t) raw
  intro y
  have hsrc : l y.val ∈ F.ambSource := y.property
  have hlast : fcoord F (l y.val) (Fin.last d) = t.val 0 := (hF (l y.val) hsrc).trans rfl
  have hprod := actualNormalReconstruct d (fcoord F (l y.val)) (t.val 0) hlast
  change normalProductEquiv d (((normalProductEquiv d).symm (fcoord F (l y.val))).1,t.val 0) ∈ F.flat.target
  exact hprod.symm ▸ fcoord_mem F hsrc

theorem familyNormalMemberCoordinates_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ y : familyNormalMemberSource p i a v U hsm F t,
      (familyNormalMemberCoordinates p i a v U hsm F hF t y).val =
        ((normalProductEquiv d).symm (fcoord F (familyMemberLift p i a v U hsm t y.val))).1 := by
  intros
  rfl

def familyNormalMemberOpenParameter :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        (familyNormalSliceDomain p i a v U hsm F t) (familyNormalMemberSource p i a v U hsm F t) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let g := familyNormalMemberParameter p i a v U hsm F hF t
  let f : familyNormalSliceDomain p i a v U hsm F t → familyNormalMemberSource p i a v U hsm F t :=
    fun u => ⟨g u, by
      change familyMemberLift p i a v U hsm t (g u) ∈ F.ambSource
      rw [familyNormalMemberParameter_familyLift p i a v U hsm F hF t u]
      exact finv_mem F u.property⟩
  refine ⟨f,?_⟩
  apply (ContMDiff.subtypeVal_comp_iff (familyNormalMemberSource p i a v U hsm F t) f).mp
  exact g.contMDiff

theorem familyNormalMemberCoordinates_familyLift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ y : familyNormalMemberSource p i a v U hsm F t,
      familyNormalSliceLift p i a v U hsm F t (familyNormalMemberCoordinates p i a v U hsm F hF t y) =
        familyMemberLift p i a v U hsm t y.val := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  intro y
  rw [familyNormalSliceLift_apply, familyNormalMemberCoordinates_apply]
  have hsrc : familyMemberLift p i a v U hsm t y.val ∈ F.ambSource := y.property
  have hlast : fcoord F (familyMemberLift p i a v U hsm t y.val) (Fin.last d) = t.val 0 :=
    (hF _ hsrc).trans rfl
  rw [actualNormalReconstruct d _ _ hlast]
  exact finv_fcoord F hsrc

theorem familyNormalMemberCoordinates_openParameter :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ u : familyNormalSliceDomain p i a v U hsm F t,
      familyNormalMemberCoordinates p i a v U hsm F hF t (familyNormalMemberOpenParameter p i a v U hsm F hF t u) = u := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  intro u
  apply Subtype.ext
  rw [familyNormalMemberCoordinates_apply]
  change ((normalProductEquiv d).symm
    (fcoord F (familyMemberLift p i a v U hsm t (familyNormalMemberParameter p i a v U hsm F hF t u)))).1 = u.val
  rw [familyNormalMemberParameter_familyLift p i a v U hsm F hF t u, familyNormalSliceLift_apply,
    fcoord_finv F u.property, ContinuousLinearEquiv.symm_apply_apply]

theorem familyNormalMemberOpenParameter_coordinates :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ y : familyNormalMemberSource p i a v U hsm F t,
      familyNormalMemberOpenParameter p i a v U hsm F hF t (familyNormalMemberCoordinates p i a v U hsm F hF t y) = y := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  intro y
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun q : familyIncidence p i a v U => q.val.2)
    (familyNormalMemberCoordinates_familyLift p i a v U hsm F hF t y)
  exact h

def familyNormalMemberHomeomorph :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      familyNormalMemberSource p i a v U hsm F t ≃ₜ familyNormalSliceDomain p i a v U hsm F t := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  exact {
    toFun := familyNormalMemberCoordinates p i a v U hsm F hF t
    invFun := familyNormalMemberOpenParameter p i a v U hsm F hF t
    left_inv := familyNormalMemberOpenParameter_coordinates p i a v U hsm F hF t
    right_inv := familyNormalMemberCoordinates_openParameter p i a v U hsm F hF t
    continuous_toFun := (familyNormalMemberCoordinates p i a v U hsm F hF t).contMDiff.continuous
    continuous_invFun := (familyNormalMemberOpenParameter p i a v U hsm F hF t).contMDiff.continuous }

end SGPT.Trace.BertiniFamilyCanonical
