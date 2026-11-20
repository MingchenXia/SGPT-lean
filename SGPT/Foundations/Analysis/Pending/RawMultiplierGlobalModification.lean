import SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalPrimeReaders
import SGPT.Foundations.Analysis.Pending.AdmissiblePrincipalizationAnalyticModification

set_option autoImplicit false

/-! # Original raw point truncations internally supply genuine whole-source modifications -/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalModification

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences GermIdealOrder IdealWeightPowers RestrictedIdealExtension
  HironakaAdmissibleSequence NormalCrossings

noncomputable section

/-- Natural original raw data internally supply the full same-source modification
and all original whole prime and germ-reader outputs. -/
theorem exists_principalization_with_global_modification
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
        AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π ∧
        ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π ∧
        IsProperMap π ∧ Function.Surjective π ∧
        GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal ∧
        IsSNCDivisor (m + 1) E ∧ D.support = ⋃ H ∈ E, H ∧
        D.support = π ⁻¹' 𝔟.zeroLocus ∧ IsIsomorphismOver (m + 1) π 𝔟.zeroLocusᶜ ∧
        ∀ (i : Fin E.length) (y : Y), y ∈ E.get i →
          ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
            V.dim = m ∧ V.carrier = connectedComponentIn (E.get i) y ∧ y ∈ V.carrier ∧
            V.carrier ⊆ E.get i ∧ IsConnected V.carrier ∧
            (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
            (∀ z ∈ V.carrier, ∃ W : Set Y, IsOpen W ∧ z ∈ W ∧
              E.get i ∩ W = V.carrier ∩ W) ∧
            (∀ z ∈ V.carrier, π z = x) ∧
            ∀ F G : X → ℂ, F =ᶠ[𝓝 x] G →
              (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
                (fun w => ENNReal.log (ENNReal.ofReal ‖F (π w)‖)) z) =
              ⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
                (fun w => ENNReal.log (ENNReal.ofReal ‖G (π w)‖)) z := by
  dsimp only
  obtain ⟨hz, Y, tY, cY, mY, π, D, E, hseq, hhol, hproper, hsurj,
      hpull, hE, hs, hpre, hiso, hreaders⟩ :=
    RawMultiplierGlobalPrimeReaders.exists_principalization_with_global_prime_readers
      (m := m) (X := X) hv x hc N
  let _ := tY
  let _ := cY
  let _ := mY
  have hcoh := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.zero_lt_succ m) hv hc
  have hcohB := (PointSupportedIdealPrincipalization.truncation_properties x hcoh N).1
  have hmod := AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    hcohB hseq D hpre
  exact ⟨hz, Y, tY, cY, mY, π, D, E, hseq, hmod, hhol, hproper, hsurj,
    hpull, hE, hs, hpre, hiso, hreaders⟩

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalModification
