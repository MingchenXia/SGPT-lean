import SGPT.Trace.BertiniFamilyNormalMember
import SGPT.Trace.BertiniNativeNormalKernel

/-! Genuine original member parametrizations from actual fixed-tau normal slices. -/
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
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1))

theorem contMDiffAt_nativeBertiniMember_of_val {m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (ζ : ComplexModel N) (hs : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (f : Y → member p (affinePoint i ζ)) (z : Y)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (d + 1)) ∞ (fun y => (f y).val) z) :
    letI := nativeBertiniMemberChartedSpace p i ζ hs
    letI := nativeBertiniMemberComplex p i ζ hs
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ f z := by
  let := nativeBertiniMemberChartedSpace p i ζ hs
  let := nativeBertiniMemberComplex p i ζ hs
  let G := FlatData.ofRegularAtDim (nativeBertiniMemberRegularity p i ζ hs (f z).val (f z).property)
  have hgy : (f z).val ∈ G.ambSource := FlatData.mem_ambSource_ofRegularAtDim _
  have hchart : f z ∈ (chartAt (ComplexModel d) (f z)).source := mem_chart_source _ _
  rw [contMDiffAt_iff_target_of_mem_source hchart]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞
    (fun y => coordinateProjection (d + 1) d (G.flat (G.amb.val (f y).val))) z
  have hfa := (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas G.amb.property) hgy.1).comp z hf
  have hfb := (contDiffAt_of_differentiableOn_complex G.differentiableOn_flat
    G.flat.open_source hgy.2).contMDiffAt
  exact (coordinateProjection (d + 1) d).contDiff.contMDiff.contMDiffAt.comp z (hfb.comp z hfa)

variable (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyNormalSliceDomain :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)}, FlatData (d + 1) d (familyIncidence p i a v U) W →
      U → TopologicalSpace.Opens (ComplexModel d) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F t
  let η : ComplexModel d → ComplexModel (d + 1) := fun u => normalProductEquiv d (u,t.val 0)
  have hη : Continuous η := (normalProductEquiv d).continuous.comp (continuous_id.prodMk continuous_const)
  exact ⟨η ⁻¹' F.flat.target,F.flat.open_target.preimage hη⟩

def familyNormalSliceLift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W) (t : U),
      ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
        (familyNormalSliceDomain p i a v U hsm F t) (familyIncidence p i a v U) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F t
  let η : ComplexModel d → ComplexModel (d + 1) := fun u => normalProductEquiv d (u,t.val 0)
  have hη : ContDiff ℂ ∞ η := (normalProductEquiv d).contDiff.comp (contDiff_id.prodMk contDiff_const)
  refine ⟨fun u => finv F (η u.val), ?_⟩
  intro u
  have hz : η u.val ∈ F.flat.target := u.property
  have hflat : ContDiffAt ℂ ∞ F.flat.symm (η u.val) :=
    contDiffAt_of_differentiableOn_complex F.differentiableOn_flat_symm F.flat.open_target hz
  have hamb : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) ∞
      F.amb.val.symm (F.flat.symm (η u.val)) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property)
      (F.flat_source_subset (F.flat.map_target hz))
  exact hamb.comp u (hflat.contMDiffAt.comp u (hη.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

theorem familyNormalSliceLift_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (t : U) (u : familyNormalSliceDomain p i a v U hsm F t),
      familyNormalSliceLift p i a v U hsm F t u = finv F (normalProductEquiv d (u.val,t.val 0)) := by
  intros
  rfl

theorem familyNormalSliceLift_parameter :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (t : U) (u : familyNormalSliceDomain p i a v U hsm F t),
      (familyNormalSliceLift p i a v U hsm F t u).val.1 = t := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t u
  apply Subtype.ext
  ext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  change scalarParameter p i a v U (finv F (normalProductEquiv d (u.val,t.val 0))) = t.val 0
  rw [SGPT.Trace.BertiniExactNormalCoordinates.exact_normal_inverse hF u.property,normalProductEquiv_last]

def familyNormalMemberParameter :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        (familyNormalSliceDomain p i a v U hsm F t) (member p (affinePoint i (a - t.val 0 • v))) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let g := familyNormalSliceLift p i a v U hsm F t
  let f : familyNormalSliceDomain p i a v U hsm F t → member p (affinePoint i (a - t.val 0 • v)) :=
    fun u => ⟨(g u).val.2, by
      have h := (g u).property
      have ht := familyNormalSliceLift_parameter p i a v U hsm F hF t u
      change (g u).val.2 ∈ member p (affinePoint i (a - (g u).val.1.val 0 • v)) at h
      rwa [ht] at h⟩
  refine ⟨f, ?_⟩
  intro u
  apply contMDiffAt_nativeBertiniMember_of_val p i (a - t.val 0 • v) (hsm t) f u
  exact ((familyNativeXMap p i a v U hsm).contMDiff.comp g.contMDiff).contMDiffAt

theorem familyNormalMemberParameter_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ u : familyNormalSliceDomain p i a v U hsm F t,
      (familyNormalMemberParameter p i a v U hsm F hF t u).val =
        (finv F (normalProductEquiv d (u.val,t.val 0))).val.2 := by
  intros
  rfl

theorem familyNormalMemberParameter_familyLift :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ u : familyNormalSliceDomain p i a v U hsm F t,
      familyMemberLift p i a v U hsm t (familyNormalMemberParameter p i a v U hsm F hF t u) =
        familyNormalSliceLift p i a v U hsm F t u := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  intro u
  apply Subtype.ext
  change (t, (familyNormalMemberParameter p i a v U hsm F hF t u).val) =
    (familyNormalSliceLift p i a v U hsm F t u).val
  apply Prod.ext
  · exact (familyNormalSliceLift_parameter p i a v U hsm F hF t u).symm
  · rfl

end SGPT.Trace.BertiniFamilyCanonical
