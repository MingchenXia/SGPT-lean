import SGPT.Trace.BertiniFixedNativeChartDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.Determinant

/-! Actual original native chart cofactor and its holomorphic field,
produced from the LITERAL derivative of the original coordinate map. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {d : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] [IsComplexManifold d X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  (f : ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) X Y ∞)
  (e : ComplexChart d X) (a : ComplexChart (d + 1) Y) (m : Fin (d + 1))

def nativeChartCofactor (z : ComplexModel d) : ℂ :=
  Matrix.det (fun r k : Fin (d + 1) =>
    Matrix.vecCons (EuclideanSpace.single m 1)
      (fun j => fderiv ℂ (coordinateMap f e a) z (EuclideanSpace.single j 1)) k r)

omit [IsComplexManifold d X] [IsComplexManifold (d + 1) Y] in
theorem nativeChartCofactor_eq_volume (z : ComplexModel d) :
    nativeChartCofactor f e a m z =
      (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
        (Matrix.vecCons (EuclideanSpace.single m 1)
          (fun j => fderiv ℂ (coordinateMap f e a) z (EuclideanSpace.single j 1))) := by
  rw [Module.Basis.det_apply]
  apply congrArg Matrix.det
  funext r k
  rfl

theorem contDiffAt_nativeChartCofactor {z : ComplexModel d}
    (hz : z ∈ coordinateDomain f e a) :
    ContDiffAt ℂ ∞ (nativeChartCofactor f e a m) z := by
  classical
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ (coordinateMap f e a)) z :=
    (coordinateMap_contDiffAt f.contMDiff e a hz).fderiv_right (by simp)
  have hentry (r k : Fin (d + 1)) : ContDiffAt ℂ ∞
      (fun z => Matrix.vecCons (EuclideanSpace.single m 1)
        (fun j => fderiv ℂ (coordinateMap f e a) z (EuclideanSpace.single j 1)) k r) z := by
    cases k using Fin.cases with
    | zero => exact contDiffAt_const
    | succ k =>
      exact (EuclideanSpace.proj (𝕜 := ℂ) r).contDiff.contDiffAt.comp z
        (hD.clm_apply contDiffAt_const)
  unfold nativeChartCofactor
  simp only [Matrix.det_apply]
  apply ContDiffAt.sum
  intro σ _
  have hp : ContDiffAt ℂ ∞ (fun z => ∏ k : Fin (d + 1),
      Matrix.vecCons (EuclideanSpace.single m 1)
        (fun j => fderiv ℂ (coordinateMap f e a) z (EuclideanSpace.single j 1)) k (σ k)) z := by
    apply contDiffAt_prod
    intro k _
    exact hentry (σ k) k
  have hprod := (contDiffAt_const (c := (((Equiv.Perm.sign σ : ℤ) : ℂ)))).mul hp
  simpa only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hprod

theorem contMDiffAt_nativeChartCofactor (x : X)
    (hex : x ∈ e.val.source) (hax : f x ∈ a.val.source) :
    ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y => nativeChartCofactor f e a m (e.val y)) x := by
  have hco := contDiffAt_nativeChartCofactor f e a m (mem_coordinateDomain hex hax)
  exact hco.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hex)

end SGPT.Trace.Bertini
