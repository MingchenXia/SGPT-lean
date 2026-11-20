import SGPT.BDivisor.StrictVolume.PencilGlobalWeight
import SGPT.BDivisor.StrictVolume.PencilPullbackNef
import SGPT.Toric.OriginalGuilleminInvariance
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-! Identify the SAME physical pencil metric curvature with the actual q*FS. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open Set Filter
open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalPencilFsMetric_form_eq_pullback :
    (originalPencilFsMetric hs).form = originalPencilPullbackForm hs := by
  let := originalPolytopeNativeChartedSpace blowupGenerator hs
  let := originalPolytopeNativeIsComplexManifold blowupGenerator hs
  apply Subtype.ext
  symm
  apply originalNativeSmoothForm_ext_of_torus blowupGenerator hs
  intro v z _
  let D := blowupDirectionDivisor hs
  let m := blowupDirectionLatticePoint hs
  let F : ComplexModel 2 → Fin 2 → ℂ := originalMonomialVector D m v
  obtain ⟨j, hj⟩ := blowupDirectionDatum_occurs hs v
  have hFj (u : ComplexModel 2) : F u j = 1 := by
    change toricMonomial D v (m j).val u = 1
    rw [show (m j).val = toricCartierDatum D v from hj]
    simp [toricMonomial]
  have hFjne (u : ComplexModel 2) : F u j ≠ 0 := by
    rw [hFj]
    exact one_ne_zero
  have hFzero (u : ComplexModel 2) : F u ≠ 0 :=
    originalMonomialVector_ne_zero D m (blowupDirectionDatum_occurs hs) v u
  have hF : ContDiff ℂ ∞ F := by
    apply contDiffOn_univ.mp
    apply contDiffOn_of_differentiableOn_complex _ isOpen_univ
    apply Differentiable.differentiableOn
    exact differentiable_pi.mpr fun i => differentiable_toricMonomial D v (m i).val
  let c : ComplexModel 2 → ComplexModel 1 :=
    fun u => ComplexProjectiveSpace.affineRatio j (F u)
  have hc : ContDiff ℂ ∞ c := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    exact (ComplexProjectiveSpace.contDiffAt_affineRatio j (hFjne u)).comp u hF.contDiffAt
  let e := polytopeToricVertexChart blowupGenerator hs v
  let d : ComplexChart 1 (ComplexProjectiveSpace 1) :=
    ⟨ComplexProjectiveSpace.affineChart j, ComplexProjectiveSpace.affineChart_mem_atlas j⟩
  have hpoint (u : ComplexModel 2) :
      originalBlowupDirection hs ((originalPolytopeNativeModelChart blowupGenerator hs v).symm u) =
        ComplexProjectiveSpace.affinePoint j (c u) := by
    have hu : u ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).target := by
      rw [originalPolytopeNativeModelChart_target]
      exact mem_univ _
    have hmem := (originalPolytopeNativeModelChart blowupGenerator hs v).map_target hu
    change originalMonomialProjectiveMap D m (blowupDirectionDatum_occurs hs) _ = _
    rw [originalMonomialProjectiveMap_eq_chart D m (blowupDirectionDatum_occurs hs) v hmem,
      (originalPolytopeNativeModelChart blowupGenerator hs v).right_inv hu]
    exact ComplexProjectiveSpace.mk_eq_affinePoint j (hFzero u) (hFjne u)
  have hz : z ∈ HolomorphicMaps.coordinateDomain (originalBlowupDirection hs) e d := by
    refine ⟨?_, ?_⟩
    · change z ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).target
      rw [originalPolytopeNativeModelChart_target]
      exact mem_univ _
    · change originalBlowupDirection hs
        ((originalPolytopeNativeModelChart blowupGenerator hs v).symm z) ∈
          (ComplexProjectiveSpace.affineChart j).source
      rw [hpoint]
      exact ComplexProjectiveSpace.affinePoint_mem_source _ _
  have hcoord : HolomorphicMaps.coordinateMap (originalBlowupDirection hs) e d = c := by
    funext u
    change ComplexProjectiveSpace.affineChart j (originalBlowupDirection hs
      ((originalPolytopeNativeModelChart blowupGenerator hs v).symm u)) = c u
    rw [hpoint, ComplexProjectiveSpace.affineChart_affinePoint]
  have hweight : (originalPencilFsMetric hs).weight v =
      fun u => Real.log 2 + ComplexProjectiveSpace.fsPotential (c u) := by
    funext u
    rw [originalPencilFsMetric_weight_homNormSq hs v u]
    change Real.log 2 + Real.log (ComplexProjectiveSpace.homNormSq (F u)) =
      Real.log 2 + Real.log (1 + ‖c u‖ ^ 2)
    apply congrArg (fun t : ℝ => Real.log 2 + Real.log t)
    have hratio := ComplexProjectiveSpace.one_add_norm_sq_affineRatio j (hFjne u)
    rw [hFj u, norm_one, one_pow, div_one] at hratio
    exact hratio.symm
  change (ClosedRealOneOneForm.pullback (contMDiff_originalBlowupDirection hs)
    (ComplexProjectiveSpace.fsClosedForm (N := 1))).val.coeff e z = _
  rw [ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff (contMDiff_originalBlowupDirection hs)
      (ComplexProjectiveSpace.fsClosedForm (N := 1)).val e d hz, hcoord]
  change (smoothDDC ComplexProjectiveSpace.fsPotential (c z)).compContinuousLinearMap
    (fderiv ℝ c z) = (originalPencilFsMetric hs).form.val.coeff e z
  rw [(originalPencilFsMetric hs).coeff v z, hweight]
  have hreal : ContDiff ℝ ∞ (fun u => ComplexProjectiveSpace.fsPotential (c u)) :=
    ComplexProjectiveSpace.contDiff_fsPotential.comp (hc.restrict_scalars ℝ)
  rw [smoothDDC_add isOpen_univ contDiff_const.contDiffOn hreal.contDiffOn (mem_univ z),
    GlobalPotentialTransforms.smoothDDC_const, zero_add]
  exact (HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ hc.contDiffOn
    ComplexProjectiveSpace.contDiff_fsPotential.contDiffOn (mapsTo_univ _ _) (mem_univ z)).symm

theorem originalPencilFsMetric_isSemipositive :
    (originalPencilFsMetric hs).form.val.IsSemipositive := by
  rw [originalPencilFsMetric_form_eq_pullback]
  exact originalPencilPullbackForm_isSemipositive hs

end SGPT.BDivisor.StrictPencilNext
