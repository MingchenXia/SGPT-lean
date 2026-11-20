import SGPT.Foundations.Analysis.Pending.RawMultiplierPointSupportedPrincipalization
import SGPT.Foundations.Analysis.Pending.PointCenteredPrimeGermReaders
import SGPT.Foundations.Analysis.Pending.HironakaAdmissibleCalculus

set_option autoImplicit false

/-! # Actual raw point truncations internally supply same-source global prime readers -/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalPrimeReaders

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences GermIdealOrder IdealWeightPowers RestrictedIdealExtension
  HironakaAdmissibleSequence NormalCrossings

noncomputable section

/-- Genuine raw data supply the same whole-source principalization and every whole point-centered prime reader. -/
theorem exists_principalization_with_global_prime_readers
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
  obtain ⟨hz, Y, tY, cY, mY, π, D, E, hseq, hpull, hE, hs, hpre, hiso⟩ :=
    RawMultiplierPointSupportedPrincipalization.exists_principalization_point_truncation
      (m := m) (X := X) hv x hc N
  let _ := tY
  let _ := cY
  let _ := mY
  have hbl := hseq.isBlowupSequence
  refine ⟨hz, Y, tY, cY, mY, π, D, E, hseq, hbl.contMDiff,
    HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hbl,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective hbl,
    hpull, hE, hs, hpre, hiso, ?_⟩
  have hpoint : D.support ⊆ π ⁻¹' ({x} : Set X) := by
    rw [hpre]
    exact preimage_mono hz
  intro i y hy
  exact PointCenteredPrimeGermReaders.exists_global_prime_germ_reader
    (m := m) (X := X) (Y := Y) hbl.contMDiff.continuous D hE hs hpoint i hy

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalPrimeReaders
