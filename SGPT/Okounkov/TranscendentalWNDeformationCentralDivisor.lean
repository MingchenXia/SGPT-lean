import SGPT.Okounkov.TranscendentalWNDeformationDivisorClass
import SGPT.Foundations.Analysis.Pending.BlowupStrictIdeal
import SGPT.Foundations.Analysis.Pending.MemberTraceIdealAlong

/-!
# `X₀ = X' + ℰ` as divisors

Blueprint `tok-wn-def:central-divisor` (`claude-tok-wn-def`); WN21 §1.1.

For a deformation to the normal cone `μ : 𝒳 → X × ℙ¹`, the ideal of the central fibre
`X × {0}` pulls back to the product of the ideals of the strict transform `X'` and of the
exceptional divisor `ℰ` (`centralFibreDivisor`, i.e. `CentralFibreDivisorStatement`):

* TN's `BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul`: `μ^*𝓘_N = 𝒪(-ℰ) · 𝓘_{N'}` for a closed
  submanifold `N ⊇ C` (here `N = X × {0}`), proved in monomial charts;
* TN's `MemberTraceIdealAlong.exceptionalDivisor_mem_iff_vanishingIdeal`: the exceptional divisor
  is reduced, `𝒪(-ℰ) = 𝓘_ℰ` at the points of `ℰ` (off `ℰ` both are the unit ideal).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **The exceptional divisor is reduced**: its ideal is the vanishing ideal of `ℰ`. -/
theorem exceptionalDivisor_mem_iff_vanishingIdeal_exceptionalSet
    (hμ : IsNormalConeDeformation F μ) (z : 𝒳) (g : 𝒳 → ℂ) :
    (BlowupExceptionalDivisor.exceptionalDivisor hμ).ideal.mem z g ↔
      (vanishingIdeal (n := m + 1 + 1) (exceptionalSet F μ)).mem z g := by
  by_cases hz : μ z ∈ deformationCentre F
  · exact MemberTraceIdealAlong.exceptionalDivisor_mem_iff_vanishingIdeal hμ hz g
  · show (GermIdeal.pullback (m := m + 1 + 1) μ
        (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).mem z g ↔ _
    rw [pullback_vanishingIdeal_mem_iff_of_notMem hμ hz g]
    constructor
    · intro hg
      refine ⟨hg.1, ?_⟩
      filter_upwards [(isClosed_exceptionalSet F hμ).isOpen_compl.mem_nhds hz] with y hy hyE
      exact absurd hyE hy
    · intro hg
      exact isInSpanAt_of_eq_mul rfl hg.1 hg.1 (Eventually.of_forall fun _ => by simp)

/-- **`X₀ = X' + ℰ` as divisors** (`tok-wn:deformation`): `μ^*𝓘_{X × 0} = 𝓘_{X'} · 𝓘_ℰ`. -/
theorem pullback_vanishingIdeal_centralBase_mem_iff (hμ : IsNormalConeDeformation F μ)
    (z : 𝒳) (f : 𝒳 → ℂ) :
    (GermIdeal.pullback (m := m + 1 + 1) μ
        (vanishingIdeal (n := m + 1 + 1) (centralBase F))).mem z f ↔
      ((vanishingIdeal (n := m + 1 + 1) (strictCentralFibre F μ)).mul
        (vanishingIdeal (n := m + 1 + 1) (exceptionalSet F μ))).mem z f := by
  rw [BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hμ (isClosedSubmanifold_centralBase F)
    (deformationCentre_subset_centralBase F)]
  unfold GermIdeal.mul
  dsimp only
  refine MeteredDivisorGlobalIdeal.isInSpanAt_congr_pred (n := m + 1 + 1) (fun s => ?_) z f
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨b, a, hb, (exceptionalDivisor_mem_iff_vanishingIdeal_exceptionalSet F hμ z a).mp ha,
      mul_comm a b⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨b, a, (exceptionalDivisor_mem_iff_vanishingIdeal_exceptionalSet F hμ z b).mpr hb, ha,
      mul_comm a b⟩

end Deformation

/-- **`tok-wn:deformation`, `X₀ = X' + ℰ` as divisors** (`CentralFibreDivisorStatement`). -/
theorem centralFibreDivisor : CentralFibreDivisorStatement F := by
  intro 𝒳 _ _ _ μ hμ z f
  exact pullback_vanishingIdeal_centralBase_mem_iff F hμ z f

end SGPT.Okounkov.TranscendentalWN
