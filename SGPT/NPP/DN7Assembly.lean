import SGPT.NPP.DN7Main
import SGPT.NPP.DN2Modification

/-!
# FPT `thm:big-metric-laplacian-rooftop` on the constructed modification

Lane DN7, `thm:DNT23_C11bar`.  Assembly of the existence of the modification data
(`SGPT.NPP.DN7.exists_modificationData`) with the theorem on a modification
(`SGPT.NPP.DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing`), relative to the joint
smoothing statement `SGPT.NPP.DN2.JointSmoothingStatement` (FPT `lem:chern-joint-smoothing`, lanes
DN3–DN6): for a big class `{θ}` on a compact complex manifold `X` of positive dimension and an
obstacle `g` with bounded complex Hessian and `0 ≤ g ≤ B`, there is a finite sequence of blowups
`π : Y → X`, an isomorphism over `X \ nK({θ})` with a holomorphic section there, and a Kähler form
`ω_Y` on `Y`, such that `P_θ(g) ∘ π ∈ C^{1,1̄}_{ω_Y}(Y \ π⁻¹ nK({θ}))`.

What remains for `thm:DNT23_C11bar` at the level of `X`: the transfer of the bounded
Laplacian through the section `σ` to `X \ nK({θ})`, the reduction of a `C^{1,1̄}_ω` obstacle to
one with bounded complex Hessian and `0 ≤ g ≤ B`, and the source wrappers; and the joint smoothing
statement itself.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Manifold

universe u

namespace SGPT.NPP.DN7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Envelopes.LapClass

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **FPT `thm:big-metric-laplacian-rooftop` on the constructed modification**, relative to the
joint smoothing statement: `P_θ(g) ∘ π ∈ C^{1,1̄}_{ω_Y}(Y \ π⁻¹ nK({θ}))`, for a modification
`π : Y → X` which is an isomorphism over `X \ nK({θ})` with a holomorphic section there. -/
theorem exists_modification_envelope_hasBoundedMetricLaplacianOn [CompactSpace X] [Nonempty X]
    (hn : 0 < n) (A : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {g : X → ℝ}
    (hg : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := n) g) (hg0 : ∀ x, 0 ≤ g x)
    {B : ℝ} (hB0 : 0 ≤ B) (hgB : ∀ x, g x ≤ B)
    (hJ : SGPT.NPP.DN2.JointSmoothingStatement.{u}) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : MeasurableSpace Y) (_ : BorelSpace Y)
      (π : Y → X) (wY : KahlerBackground n Y),
      IsAnalyticModification (n := n) π ∧ IsBlowupSequence n X Y π ∧
      IsIsomorphismOver n π (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
      (∃ σ : X → Y, ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ
          (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
        (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ), π (σ x) = x) ∧
        ∀ y, π y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) → σ (π y) = y) ∧
      HasBoundedMetricLaplacianOn wY (π ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
        (fun y => (rooftopEnvelope θ.val (fun x => (g x : EReal)) (π y)).toReal) := by
  obtain ⟨Y, tY, chY, mY, π, hπ, wY, φ, Cφ, hcpt, hblow, hiso, hsec, hφ, hφθ, hφ0, hZa, hZi,
    hφZ, hφc, hCφ, hφs, hφL⟩ := exists_modificationData hn θ hbig
  let := tY
  let := chY
  let := mY
  let := hcpt
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  obtain ⟨r₀, Ψ, hΨ⟩ := hJ n Y wY
  exact ⟨Y, tY, chY, mY, hcpt, borel Y, ⟨rfl⟩, π, wY, hπ, hblow, hiso, hsec,
    SGPT.NPP.DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing hn A θ hbig hg hg0
      hB0 hgB hπ hΨ hφ hφθ hφ0 hZa hZi hφZ hφc hCφ hφs hφL⟩

end SGPT.NPP.DN7
