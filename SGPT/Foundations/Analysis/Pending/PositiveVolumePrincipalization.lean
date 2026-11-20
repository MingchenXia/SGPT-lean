import SGPT.Foundations.Analysis.Pending.RelativePrincipalization

set_option autoImplicit false

/-!
# Relative principalization from positive restricted volume

A positive numerical restricted volume supplies the existing coherent-ideal
bridge nontrivial on the subvariety.  Combining it with the relative
principalization interface produces the adapted modification and divisor
factorization used in the paper.  No new interface is introduced here.
-/

open Set Filter

universe u

namespace SGPT.Foundations.Analysis.Pending.PositiveVolumePrincipalization

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.NumericalRestrictedVolume
  RelativePrincipalization

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- A positive restricted volume yields an ideal and an adapted relative
principalization of it along the selected smooth subvariety. -/
theorem exists_relativePrincipalization_of_numericalRestrictedVolume_pos
    [CompactSpace Y] [ConnectedSpace Y]
    (hn : 0 < n) (omega : KahlerBackground n Y)
    (alpha : RealBottChern n Y) (hbig : IsBigClass alpha)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : IsClosedConnectedSubmanifold n W.carrier W.dim) (hWY : W.carrier ≠ univ)
    (hvolume : 0 < numericalRestrictedVolume omega alpha W) :
    ∃ 𝔞 : GermIdeal n Y, 𝔞.IsCoherent ∧
      ¬ 𝔞.Le (vanishingIdeal (n := n) W.carrier) ∧
      ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
        (_ : IsComplexManifold n Y') (f : Y' → Y),
        IsAdaptedBlowupSequence n Y W.carrier Y' f ∧ CompactSpace Y' ∧ ConnectedSpace Y' ∧
        IsClosedConnectedSubmanifold n (strictTransform n f W.carrier) W.dim ∧
        (∃ U : Set Y, IsOpen U ∧ (U ∩ W.carrier).Nonempty ∧ IsIsomorphismOver n f U) ∧
        ∃ H H' : EffectiveDivisor n Y',
          H.support ⊆ exceptionalLocus n f ∧
          Disjoint H'.support (strictTransform n f W.carrier) ∧
          ¬ strictTransform n f W.carrier ⊆ H.support ∧
          GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W.carrier) =
            H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W.carrier)) ∧
          GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal ∧
          ∀ y ∈ strictTransform n f W.carrier, ∀ g : Y' → ℂ, HolomorphicAt n g y →
            (IsInSpanOnAt (n := n) (strictTransform n f W.carrier)
                (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g ↔
              IsInSpanOnAt (n := n) (strictTransform n f W.carrier) (H.ideal.mem y) y g) := by
  obtain ⟨𝔞, h𝔞, hres⟩ :=
    exists_coherentIdeal_not_le_vanishingIdeal_of_numericalRestrictedVolume_pos
      hn omega alpha hbig W hvolume
  exact ⟨𝔞, h𝔞, hres,
    exists_relativePrincipalization W.carrier W.dim hW hWY 𝔞 h𝔞 hres⟩

end

end SGPT.Foundations.Analysis.Pending.PositiveVolumePrincipalization
