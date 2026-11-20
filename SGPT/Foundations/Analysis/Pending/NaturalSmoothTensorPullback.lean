module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

/-!
# Smooth pullback of actual alternating coefficient tensors

A continuous left inverse of the actual alternating inclusion is constructed internally
in finite dimensions. The polynomial multilinear pullback operation then gives genuine
all-order smoothness of variable tensor pullback and actual atlas-change coefficients.
No global form topology, overlap certificate, or Green operator is assumed.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback

variable {X E F G : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {q : ℕ} {r : WithTop ℕ∞}

/-- An internally chosen continuous retraction of the actual alternating inclusion. -/
def alternatingRetraction :
    (ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) →L[ℝ]
      E [⋀^Fin q]→L[ℝ] G := by
  letI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  exact (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ)).leftInverse
    |>.toContinuousLinearMap

/-- The constructed retraction is literally the identity on original alternating tensors. -/
theorem alternatingRetraction_apply (A : E [⋀^Fin q]→L[ℝ] G) :
    alternatingRetraction A.toContinuousMultilinearMap = A := by
  change (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ)).leftInverse
    (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ) A) = A
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr ContinuousAlternatingMap.toContinuousMultilinearMap_injective

/-- Variable linear pullback is smooth in the full actual alternating-tensor norm. -/
theorem contDiffOn_compContinuousLinearMap {s : Set X}
    {A : X → F [⋀^Fin q]→L[ℝ] G} {L : X → E →L[ℝ] F}
    (hA : ContDiffOn ℝ r A s) (hL : ContDiffOn ℝ r L s) :
    ContDiffOn ℝ r (fun x => (A x).compContinuousLinearMap (L x)) s := by
  let B := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin q => E) (fun _ : Fin q => F) G
  have hpi : ContDiffOn ℝ r (fun x => fun _ : Fin q => L x) s :=
    contDiffOn_pi.mpr fun _ => hL
  have hc := B.contDiff.comp_contDiffOn hpi
  have ha : ContDiffOn ℝ r (fun x => (A x).toContinuousMultilinearMap) s :=
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
      (F [⋀^Fin q]→L[ℝ] G) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => F) G).contDiff.comp_contDiffOn hA
  have h := hc.clm_apply ha
  have hr := (alternatingRetraction (E := E) (G := G) (q := q)).contDiff.comp_contDiffOn h
  convert hr using 1
  funext x
  exact (alternatingRetraction_apply ((A x).compContinuousLinearMap (L x))).symm

/-- Smooth nonlinear pullback uses the internally derived smooth full derivative. -/
theorem contDiffOn_pullback {s : Set E} {t : Set F} {f : E → F}
    {A : F → F [⋀^Fin q]→L[ℝ] G}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (hA : ContDiffOn ℝ ∞ A t) (hmap : MapsTo f s t) :
    ContDiffOn ℝ ∞
      (fun x => (A (f x)).compContinuousLinearMap (fderiv ℝ f x)) s := by
  exact contDiffOn_compContinuousLinearMap (hA.comp hf hmap)
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hf).2

open FirstPass

/-- Actual smooth atlas-change transport of arbitrary full tensor coefficients. -/
theorem contDiffOn_chart_pullback {n q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (e f : ComplexChart n M)
    {A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ}
    (hA : ContDiffOn ℝ ∞ A f.val.target) :
    ContDiffOn ℝ ∞
      (fun z => (A (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z)) (chartTransition e f).source := by
  apply contDiffOn_pullback (chartTransition e f).open_source
    (fun z hz => (HolomorphicMaps.chartTransition_contDiffAt_real e f hz).contDiffWithinAt)
    hA
  intro z hz
  exact f.val.map_source hz.2

end SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback
