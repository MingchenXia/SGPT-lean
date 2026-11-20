import SGPT.Trace.BertiniConormalResidueAdjunction
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-! The actual original native submanifold tangent as its conormal kernel.

The final geometric constructor proves injectivity from original flattening
data and surjectivity from the actual differentiated local equation. No
tangent/kernel isomorphism or inclusion-derivative certificate is an input.
Specializing the local equation and normal to the original incidence slice
is a separate producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

/-- The actual inclusion's complex derivative is injective in every native
submanifold/ambient chart; actual regular flattening proves it internally. -/
theorem injective_nativeSubmanifoldCoordinateDerivative :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    ∀ (e : ComplexChart k W) (a : ComplexChart n X) (z : ComplexModel k),
      z ∈ coordinateDomain (Subtype.val : W → X) e a →
        Function.Injective (fderiv ℂ (coordinateMap (Subtype.val : W → X) e a) z) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  intro e a z hz
  have hinc := SubmanifoldChartedSpace.contMDiff_val hk hW
  have hd := (coordinateMap_contDiffAt hinc e a hz).differentiableAt (by simp)
  have hi := SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val hk hW e a z hz
  intro u v huv
  apply hi
  rw [hd.fderiv_restrictScalars ℝ]
  exact huv

private def conormalKernelEquivOfDerivative {d : ℕ}
    (D : ComplexModel d →L[ℂ] ComplexModel (d + 1)) (hD : Function.Injective D)
    (ℓ : ComplexModel (d + 1) →L[ℂ] ℂ) (ν : ComplexModel (d + 1)) (hν : ℓ ν = 1)
    (hzero : ℓ.comp D = 0) : ComplexModel d ≃ₗ[ℂ] LinearMap.ker ℓ.toLinearMap := by
  let R : ComplexModel d →ₗ[ℂ] LinearMap.ker ℓ.toLinearMap :=
    D.toLinearMap.codRestrict (LinearMap.ker ℓ.toLinearMap) (by
      intro v
      have hz := congrArg (fun A : ComplexModel d →L[ℂ] ℂ => A v) hzero
      exact hz)
  have hi : Function.Injective R := by
    intro u v huv
    exact hD (congrArg Subtype.val huv)
  have hs : Function.Surjective ℓ.toLinearMap := by
    intro a
    refine ⟨a • ν, ?_⟩
    simp [hν]
  have hdim := ℓ.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at hdim
  have hdim' : Module.finrank ℂ (ComplexModel d) =
      Module.finrank ℂ (LinearMap.ker ℓ.toLinearMap) := by
    simp at hdim ⊢
    exact (Nat.add_left_cancel (hdim.trans (Nat.add_comm d 1))).symm
  exact LinearEquiv.ofBijective R
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hi⟩

section Hypersurface

variable {d : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {Z : Set Y} (hZ : ∀ y ∈ Z, RegularAtDim (n := d + 1) Z y d)

/-- The actual original coordinate inclusion is an isomorphism onto the
literal kernel of its actual local equation. Its normal and local zero
equation are geometric data; no derivative injection or kernel map is assumed. -/
def nativeSubmanifoldCoordinateConormalEquiv :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hZ
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hZ
    ∀ (e : ComplexChart d Z) (a : ComplexChart (d + 1) Y) (z : ComplexModel d)
      (_hz : z ∈ coordinateDomain (Subtype.val : Z → Y) e a)
      (g : ComplexModel (d + 1) → ℂ)
      (_hg : DifferentiableAt ℂ g (coordinateMap (Subtype.val : Z → Y) e a z))
      (ν : ComplexModel (d + 1))
      (_hν : fderiv ℂ g (coordinateMap (Subtype.val : Z → Y) e a z) ν = 1)
      (_hzero : (g ∘ coordinateMap (Subtype.val : Z → Y) e a) =ᶠ[𝓝 z] fun _ => 0),
      ComplexModel d ≃ₗ[ℂ]
        LinearMap.ker (fderiv ℂ g (coordinateMap (Subtype.val : Z → Y) e a z)).toLinearMap := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hZ
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hZ
  intro e a z hz g hg ν hν hzero
  have hinc := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d) hZ
  have hd := (coordinateMap_contDiffAt hinc e a hz).differentiableAt (by simp)
  have hcomp : (fderiv ℂ g (coordinateMap (Subtype.val : Z → Y) e a z)).comp
      (fderiv ℂ (coordinateMap (Subtype.val : Z → Y) e a) z) = 0 := by
    rw [← fderiv_comp z hg hd, hzero.fderiv_eq]
    exact fderiv_const_apply (0 : ℂ)
  exact conormalKernelEquivOfDerivative
    (fderiv ℂ (coordinateMap (Subtype.val : Z → Y) e a) z)
    (injective_nativeSubmanifoldCoordinateDerivative (Nat.le_succ d) hZ e a z hz)
    (fderiv ℂ g (coordinateMap (Subtype.val : Z → Y) e a z)) ν hν hcomp

theorem nativeSubmanifoldCoordinateConormalEquiv_apply :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hZ
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hZ
    ∀ (e : ComplexChart d Z) (a : ComplexChart (d + 1) Y) (z : ComplexModel d)
      (hz : z ∈ coordinateDomain (Subtype.val : Z → Y) e a)
      (g : ComplexModel (d + 1) → ℂ)
      (hg : DifferentiableAt ℂ g (coordinateMap (Subtype.val : Z → Y) e a z))
      (ν : ComplexModel (d + 1))
      (hν : fderiv ℂ g (coordinateMap (Subtype.val : Z → Y) e a z) ν = 1)
      (hzero : (g ∘ coordinateMap (Subtype.val : Z → Y) e a) =ᶠ[𝓝 z] fun _ => 0)
      (v : ComplexModel d),
      (nativeSubmanifoldCoordinateConormalEquiv hZ e a z hz g hg ν hν hzero v).val =
        fderiv ℂ (coordinateMap (Subtype.val : Z → Y) e a) z v := by
  intros
  rfl

end Hypersurface

end SGPT.Trace.Bertini
