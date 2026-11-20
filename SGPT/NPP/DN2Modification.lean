import SGPT.NPP.DN2Core
import SGPT.NPP.DN2Pullback

/-!
# FPT `thm:big-metric-laplacian-rooftop` on a modification of `X`

Lane DN2, `thm:DNT23_C11bar`.  Assembly of the theorem on the resolution
(`hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing`) with the envelope pullback
(`envelope_pullback_data`) and the pulled-back obstacle (`neg_comp_isThetaPshPotential_of_hasBoundedComplexHessian`):
for a big class `{θ}` on a compact Kähler manifold `X` of positive dimension, an obstacle `g` with
bounded complex Hessian and `0 ≤ g ≤ B`, and an analytic modification `π : Y → X` from a compact
Kähler manifold `(Y, ω_Y)` carrying a joint smoothing and a `π^*θ`-psh potential `φ ≤ 0` with
`π^*θ + ddᶜφ ≥ ω_Y`, finite, smooth and with `i∂∂̄φ ≤ C_φ ω_Y` off an analytic set `Z ⊂ Y` with
empty interior, the function `P_θ(g) ∘ π` lies in `C^{1,1̄}_{ω_Y}(Y \ Z)`.

What is not formalized here (the rest of FPT's modification package): the existence of such a `π`
and `φ` with `π(Z) = nK({θ})` and `π` biholomorphic over `X \ nK({θ})` (gentle Kähler current with
analytic singularities and poles `nK`, log resolution, Kähler current `≥ ω_Y`), and the transfer of
the Laplacian bound from `Y \ Z` to `X \ nK({θ})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Envelopes.LapClass

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **FPT `thm:big-metric-laplacian-rooftop` on a modification** (from the joint smoothing of
`(Y, ω_Y)`): `P_θ(g) ∘ π ∈ C^{1,1̄}_{ω_Y}(Y \ Z)`. -/
theorem hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing
    [CompactSpace X] [Nonempty X] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (hn : 0 < n) (A : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {g : X → ℝ}
    (hg : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := n) g) (hg0 : ∀ x, 0 ≤ g x)
    {B : ℝ} (hB0 : 0 ≤ B) (hgB : ∀ x, g x ≤ B)
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {wY : KahlerBackground n Y} {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    (hJ : IsJointSmoothing wY r₀ Ψ)
    {φ : Y → EReal}
    (hφ : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hπ.1 θ - wY.form).val φ)
    (hφθ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val φ)
    (hφ0 : ∀ y, φ y ≤ 0)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hZi : interior Z = ∅)
    (hφZ : ∀ y ∉ Z, φ y ≠ ⊥) (hφc : ContinuousOn (fun y => (φ y).toReal) Zᶜ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφs : ∀ e : ComplexChart n Y, ContDiffOn ℝ ∞ (fun z => (φ (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' Zᶜ))
    (hφL : ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ Zᶜ → ∀ v : ComplexModel n,
        leviForm (fun z => (φ (e.val.symm z)).toReal) z v ≤
          Cφ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v])) :
    HasBoundedMetricLaplacianOn wY Zᶜ
      (fun y => (rooftopEnvelope θ.val (fun x => (g x : EReal)) (π y)).toReal) := by
  obtain ⟨hu, hudef, hule⟩ := envelope_pullback_data hn hπ θ hbig hg.1
  obtain ⟨S, -, hfneg⟩ := neg_comp_isThetaPshPotential_of_hasBoundedComplexHessian hπ A hg
  exact hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing hJ (hg.1.comp hπ.1.continuous)
    (fun y => hg0 (π y)) hB0 (fun y => hgB (π y)) hfneg hu hudef hule hφ hφθ hφ0 hZ hZi hφZ hφc
    hCφ hφs hφL

end SGPT.NPP.DN2
