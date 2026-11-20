import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.Pending.AnalyticGluingProof

set_option autoImplicit false

/-!
# Gluing a global and a local positive branch

Source: Copy-4, `prop:gluing` (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:gluing`.

Let `Y` be a connected compact Kähler manifold, `θ_Y` a smooth closed real
`(1,1)`-form, `U₁ ⋐ U₂` open subsets and `p ∈ U₁`.  Let `φ_G` be quasi-psh on `Y`
and `φ_U` quasi-psh near `closure U₂`, with

1. `θ_Y + ddᶜ φ_G` a Kähler current and `φ_G(p) = -∞`;
2. `θ_Y + ddᶜ φ_U` dominating a Kähler form near `closure U₂`, `φ_U` smooth near `p`;
3. `φ_U ≤ φ_G + C` on `closure U₂ \ U₁`.

Then `{θ_Y}` contains a Kähler current smooth near `p`; in particular
`p ∉ E_nK({θ_Y})`.

The quasi-psh hypotheses are contained in (1) and (2) (`GluingHypotheses`).  A
Kähler current smooth near `p` is a `KahlerCurrent` whose potential is smooth near
`p`, its representative being smooth.

Proved in `Pending.AnalyticGluingProof`.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.AnalyticGluing

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.AnalyticGluingData

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Gluing a global and a local positive branch** (Copy-4, `prop:gluing`). -/
theorem exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses
    [CompactSpace Y] [ConnectedSpace Y] (hKahler : Nonempty (KahlerBackground n Y))
    (θY : ClosedRealOneOneForm n Y) (U₁ U₂ : Set Y) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hU₁₂ : RelCompactSubset U₁ U₂) (p : Y) (hp : p ∈ U₁) (φG φU : Y → EReal)
    (hglue : GluingHypotheses θY U₁ U₂ p φG φU) :
    (∃ T : KahlerCurrent (RealBottChern.ofRepresentative θY),
        IsSmoothNear (n := n) T.potential p) ∧
      p ∉ nonKahlerLocus (RealBottChern.ofRepresentative θY) :=
  AnalyticGluingProof.exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses hKahler θY U₁ U₂
    hU₁ hU₂ hU₁₂ p hp φG φU hglue

end

end SGPT.Foundations.Analysis.Pending.AnalyticGluing
