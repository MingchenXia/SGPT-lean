import SGPT.Bergman.SourcePartialBergmanTrace
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

/-!
# IdealOrderSectionInclusion

If `φ ⪯_I ψ` then `H⁰(X, L^k ⊗ T ⊗ I(kφ)) ⊆ H⁰(X, L^k ⊗ T ⊗ I(kψ))` (used in source `rmk:Bergman:L797`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.IdealOrderMonotonicity
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The existing genuine source theta/native dictionary supplies the ORIGINAL QPSH domain.
This is an imported domain readback, not a new ideal-equivalence/order operation. -/
theorem nativeQpsh_of_sourceDomain {u : X → EReal} (hu : (ofFixedModel n X).IsQPSH u) :
    IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- EXISTING all-positive-coefficient original order gives SAME original positive degree ideal inclusion. -/
theorem sourceDegreeIdeal_le_of_sourceIOrder {φ ψ : X → EReal}
    (hI : sourceIOrder (ofFixedModel n X) φ ψ) (k : ℕ) (hk : 0 < k) :
    (sourceDegreeMultiplierIdeal (n := n) k φ).Le (sourceDegreeMultiplierIdeal (n := n) k ψ) := by
  rw [sourceDegreeMultiplierIdeal_pos k hk φ, sourceDegreeMultiplierIdeal_pos k hk ψ]
  exact SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    ((sourceIOrder_iff_native hI.1 hI.2.1).mp hI) (Nat.cast_pos.mpr hk)

/-- Genuine entire same-tensor H0 inclusion, produced at ALL original coefficients with BOTH coherences internal. -/
theorem fullIdealSections_le_of_sourceIOrder
    (L T : HermitianHolomorphicLineBundle n X) {φ ψ : X → EReal}
    (hI : sourceIOrder (ofFixedModel n X) φ ψ) (k : ℕ) (hk : 0 < k) :
    fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ) ≤
      fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k ψ) := by
  intro s hs
  have hφ := sourceDegreeMultiplierIdeal_isCoherent k (nativeQpsh_of_sourceDomain hI.1)
  have hψ := sourceDegreeMultiplierIdeal_isCoherent k (nativeQpsh_of_sourceDomain hI.2.1)
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L T k).Fiber _ hφ s] at hs
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L T k).Fiber _ hψ s]
  intro x
  exact sourceDegreeIdeal_le_of_sourceIOrder hI k hk x _ (hs x)

end SGPT.Bergman.IdealOrderMonotonicity
