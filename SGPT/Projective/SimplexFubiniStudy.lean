import SGPT.Toric.StrictPhysicalBergman
import SGPT.Toric.Toric4Projective
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import Lean.Elab.Command

section FsBlowdownCanonicalFragmentSimplexOriginalFsWeightsDraft
/- BEGIN SimplexOriginalFsWeightsDraft; original frozen source SHA256 8954ae54fb44d40abf8bcf544b24422eec22545ef7221efc7b3ed550672b8806 -/
/-! The SAME actual original simplex full-lattice metric, homogeneous points
and projective FS potentials. These are geometric readbacks, not mass labels. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext

open Set Filter
open SGPT.Toric
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Manifold ContDiff

variable {N : ℕ} (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- The actual original homogeneous monomial vector in standard projective order. -/
def simplexFsChartLift (v : latticePolytopeVertices (simplexGenerator N))
    (z : ComplexModel N) : Fin (N + 1) → ℂ :=
  simplexCoordLinear (originalPolytopeNativeVector _ hs v (originalPolytopeNativeModelEquiv N z))

/-- The original vertex homogeneous coordinate, through the SAME genuine permutation. -/
def simplexFsChartIndex (v : latticePolytopeVertices (simplexGenerator N)) : Fin (N + 1) :=
  simplexHomogeneousIndex.symm (originalPolytopeNativeVertexIndex (simplexGenerator N) v)

/-- Every original full-chart lift is normalized at its actual original vertex. -/
theorem simplexFsChartLift_vertex (v : latticePolytopeVertices (simplexGenerator N))
    (z : ComplexModel N) :
    simplexFsChartLift hs v z (simplexFsChartIndex v) = 1 := by
  simp only [simplexFsChartLift, simplexFsChartIndex, simplexCoordLinear_apply,
    Equiv.apply_symm_apply]
  exact monomialVertexVector_vertex _ _ _ _

/-- The SAME actual full-lattice weight is the original reordered homogeneous norm. -/
theorem simplexFsChartWeight_eq_log_homNormSq
    (v : latticePolytopeVertices (simplexGenerator N)) (z : ComplexModel N) :
    toricFullLatticeFsWeight (hs := hs) v z =
      Real.log (ComplexProjectiveSpace.homNormSq (simplexFsChartLift hs v z)) := by
  rw [toricFullLatticeFsWeight_eq_log_sum]
  apply congrArg Real.log
  unfold ComplexProjectiveSpace.homNormSq simplexFsChartLift
  simp only [simplexCoordLinear_apply]
  exact (Equiv.sum_comp simplexHomogeneousIndex
    (fun i => ‖originalPolytopeNativeVector (simplexGenerator N) hs v
      (originalPolytopeNativeModelEquiv N z) i‖ ^ 2)).symm

/-- Literal equality with the SAME original affine FS potential, on the entire chart. -/
theorem simplexFsChartWeight_eq_fsPotential
    (v : latticePolytopeVertices (simplexGenerator N)) (z : ComplexModel N) :
    toricFullLatticeFsWeight (hs := hs) v z =
      ComplexProjectiveSpace.fsPotential
        (ComplexProjectiveSpace.affineRatio (simplexFsChartIndex v) (simplexFsChartLift hs v z)) := by
  rw [simplexFsChartWeight_eq_log_homNormSq,
    ComplexProjectiveSpace.fsPotential_eq_log_homNormSq (simplexFsChartIndex v)]
  rw [ComplexProjectiveSpace.affineLift_affineRatio (simplexFsChartIndex v)
    (by rw [simplexFsChartLift_vertex hs v z]; exact one_ne_zero),
    simplexFsChartLift_vertex, inv_one, one_smul]

/-- The SAME actual native vertex-chart point is the SAME original projective affine point. -/
theorem simplexFsChartPoint_readback
    (v : latticePolytopeVertices (simplexGenerator N)) (z : ComplexModel N) :
    simplexProjectiveHomeomorph hs ((originalPolytopeNativeModelChart _ hs v).symm z) =
      ComplexProjectiveSpace.affinePoint (simplexFsChartIndex v)
        (ComplexProjectiveSpace.affineRatio (simplexFsChartIndex v) (simplexFsChartLift hs v z)) := by
  have hG : simplexFsChartLift hs v z ≠ 0 := by
    intro h
    have hcoord := congrFun h (simplexFsChartIndex v)
    rw [simplexFsChartLift_vertex] at hcoord
    exact one_ne_zero hcoord
  have hpoint : simplexProjectiveHomeomorph hs
      ((originalPolytopeNativeModelChart _ hs v).symm z) =
      ComplexProjectiveSpace.mk (simplexFsChartLift hs v z) hG := by
    change simplexProjectiveMap
      (((originalPolytopeNativePiChart _ hs v).symm (originalPolytopeNativeModelEquiv N z)).val) = _
    rw [originalPolytopeNativePiChart_symm_val,
      simplexProjectiveMap, Projectivization.map_mk]
    rfl
  rw [hpoint]
  exact ComplexProjectiveSpace.mk_eq_affinePoint _ hG
    (by rw [simplexFsChartLift_vertex]; exact one_ne_zero)

end SGPT.Projective.FsNormalizationNext

end
/- END SimplexOriginalFsWeightsDraft -/
end FsBlowdownCanonicalFragmentSimplexOriginalFsWeightsDraft

section FsBlowdownCanonicalFragmentSimplexOriginalFsFormDraft
/- BEGIN SimplexOriginalFsFormDraft; original frozen source SHA256 91afb820fbff5c1a637449e11b52166ecdac5e1eb9c416adf170919e25c6efca -/
/-! Equality of the SAME actual original simplex full-lattice curvature
with the genuine pullback of the original projective Fubini--Study form. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext

open Set Filter
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Manifold ContDiff Topology

variable {N : ℕ} (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- The actual original projective affine coordinate of a whole original vertex chart. -/
def simplexFsChartCoordinate (v : latticePolytopeVertices (simplexGenerator N)) :
    ComplexModel N → ComplexModel N :=
  fun z => ComplexProjectiveSpace.affineRatio (simplexFsChartIndex v) (simplexFsChartLift hs v z)

/-- Genuine whole-chart holomorphicity is supplied by the SAME lift with coordinate one. -/
theorem simplexFsChartCoordinate_contDiff (v : latticePolytopeVertices (simplexGenerator N)) :
    ContDiff ℂ ∞ (simplexFsChartCoordinate hs v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hnonzero : simplexFsChartLift hs v z (simplexFsChartIndex v) ≠ 0 := by
    rw [simplexFsChartLift_vertex]; exact one_ne_zero
  exact (ComplexProjectiveSpace.contDiffAt_affineRatio (simplexFsChartIndex v) hnonzero).comp z
    (contDiff_simplexChartLift hs v).contDiffAt

/-- Actual equality of closed forms, in all dimensions including zero; no comparison input. -/
theorem simplexFullLatticeMetric_form_eq_original_fs_pullback :
    (toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)).form =
      ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph hs)
        (ComplexProjectiveSpace.fsClosedForm (N := N)) := by
  let := originalPolytopeNativeChartedSpace (simplexGenerator N) hs
  let := originalPolytopeNativeIsComplexManifold (simplexGenerator N) hs
  apply Subtype.ext
  symm
  apply originalNativeSmoothForm_ext_of_torus (simplexGenerator N) hs
  intro v z _
  let e := polytopeToricVertexChart (simplexGenerator N) hs v
  let j := simplexFsChartIndex v
  let d : ComplexChart N (ComplexProjectiveSpace N) :=
    ⟨ComplexProjectiveSpace.affineChart j, ComplexProjectiveSpace.affineChart_mem_atlas j⟩
  have hz : z ∈ HolomorphicMaps.coordinateDomain (simplexProjectiveHomeomorph hs) e d := by
    refine ⟨?_, ?_⟩
    · change z ∈ (originalPolytopeNativeModelChart (simplexGenerator N) hs v).target
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ _
    · change simplexProjectiveHomeomorph hs
        ((originalPolytopeNativeModelChart _ hs v).symm z) ∈
          (ComplexProjectiveSpace.affineChart j).source
      rw [simplexFsChartPoint_readback]
      exact ComplexProjectiveSpace.affinePoint_mem_source _ _
  have hcoord : HolomorphicMaps.coordinateMap (simplexProjectiveHomeomorph hs) e d =
      simplexFsChartCoordinate hs v := by
    funext u
    change ComplexProjectiveSpace.affineChart j (simplexProjectiveHomeomorph hs
      ((originalPolytopeNativeModelChart _ hs v).symm u)) = _
    rw [simplexFsChartPoint_readback, ComplexProjectiveSpace.affineChart_affinePoint]
    rfl
  change (ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph hs)
    (ComplexProjectiveSpace.fsClosedForm (N := N))).val.coeff e z = _
  rw [ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff (contMDiff_simplexProjectiveHomeomorph hs)
      (ComplexProjectiveSpace.fsClosedForm (N := N)).val e d hz, hcoord]
  change (smoothDDC ComplexProjectiveSpace.fsPotential (simplexFsChartCoordinate hs v z)).compContinuousLinearMap
    (fderiv ℝ (simplexFsChartCoordinate hs v) z) =
      (toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)).form.val.coeff e z
  rw [(toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)).coeff v z]
  change _ = smoothDDC (toricFullLatticeFsWeight (hs := hs) v) z
  have hweight : toricFullLatticeFsWeight (hs := hs) v =
      fun u => ComplexProjectiveSpace.fsPotential (simplexFsChartCoordinate hs v u) :=
    funext (simplexFsChartWeight_eq_fsPotential hs v)
  rw [hweight]
  exact (HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ
    (simplexFsChartCoordinate_contDiff hs v).contDiffOn
    ComplexProjectiveSpace.contDiff_fsPotential.contDiffOn (mapsTo_univ _ _) (mem_univ z)).symm

end SGPT.Projective.FsNormalizationNext

end
/- END SimplexOriginalFsFormDraft -/
end FsBlowdownCanonicalFragmentSimplexOriginalFsFormDraft


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden original private module in actual proper FS/blowdown provider: {m}"
