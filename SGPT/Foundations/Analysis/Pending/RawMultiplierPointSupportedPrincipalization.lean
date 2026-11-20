import SGPT.Foundations.Analysis.Pending.PointSupportedIdealPrincipalization
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence

set_option autoImplicit false

/-! # Actual raw multiplier point truncations principalized over the same whole manifold -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierPointSupportedPrincipalization

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  GermIdealOrder IdealWeightPowers RestrictedIdealExtension
  HironakaAdmissibleSequence NormalCrossings

noncomputable section

/-- Raw Nadel coherence and genuine point powers supply same-whole-space principalization. -/
theorem exists_principalization_point_truncation
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {v : X → EReal} (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (x : X) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) c v)
      (idealPow (pointIdeal (m + 1) x) N)
    𝔟.zeroLocus ⊆ ({x} : Set X) ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
        (_ : IsComplexManifold (m + 1) Y) (π : Y → X)
        (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y)),
        IsAdmissibleBlowupSequence (m + 1) X [] 𝔟.zeroLocus Y π E ∧
        GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal ∧
        IsSNCDivisor (m + 1) E ∧ D.support = ⋃ H ∈ E, H ∧
        D.support = π ⁻¹' 𝔟.zeroLocus ∧ IsIsomorphismOver (m + 1) π 𝔟.zeroLocusᶜ := by
  dsimp only
  have hcoh := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.zero_lt_succ m) hv hc
  exact ⟨(PointSupportedIdealPrincipalization.truncation_properties x hcoh N).2.1,
    PointSupportedIdealPrincipalization.exists_principalization_truncation x hcoh N⟩

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierPointSupportedPrincipalization
