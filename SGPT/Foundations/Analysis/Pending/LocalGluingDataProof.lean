import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback

set_option autoImplicit false

/-!
# Proof of the compact-collar lemma

Source: Copy-4, `prop:principalization` and `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:local-gluing-data`.

This module proves, sorry-free, the statement of
`Pending.LocalGluingData.exists_collars_gluingHypotheses_of_principalizationGluingConclusions`
(same hypotheses, same conclusion).  It is a separate module only because that
file belongs to a different write set; the open statement there can be closed by
a one-line appeal to the theorem below.

## Proof

The strict transform `W` is closed in the compact Hausdorff manifold `Y`, hence
compact, and lies in the open set `U`.  Two applications of
`exists_open_between_and_isCompact_closure` give open `U₁, U₂` with
`W ⊆ U₁`, `closure U₁ ⊆ U₂`, `closure U₂ ⊆ U`.  The first two gluing hypotheses
are the first two principalization conclusions (with `Ω = U`, and `φ_G(y) = -∞`
because `y ∈ W`).  The collar `closure U₂ \ U₁` is compact and contained in
`U \ W`, so the third principalization conclusion supplies the collar constant.
Only the principalization data are used; the remaining hypotheses are carried
to keep the statement identical.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.LocalGluingDataProof

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  FirstPass.AnalyticGluingData

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A compact subset `W` of an open subset `U` of a compact Hausdorff space admits
open neighbourhoods `W ⋐ U₁ ⋐ U₂ ⋐ U`. -/
theorem exists_relCompactSubset_chain {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] {W U : Set Y} (hWc : IsClosed W) (hU : IsOpen U) (hWU : W ⊆ U) :
    ∃ U₁ U₂ : Set Y, IsOpen U₁ ∧ IsOpen U₂ ∧ W ⊆ U₁ ∧
      RelCompactSubset W U₁ ∧ RelCompactSubset U₁ U₂ ∧ RelCompactSubset U₂ U := by
  obtain ⟨U₂, hU₂, hWU₂, hU₂U, hU₂c⟩ :=
    exists_open_between_and_isCompact_closure hWc.isCompact hU hWU
  obtain ⟨U₁, hU₁, hWU₁, hU₁U₂, hU₁c⟩ :=
    exists_open_between_and_isCompact_closure hWc.isCompact hU₂ hWU₂
  refine ⟨U₁, U₂, hU₁, hU₂, hWU₁, ⟨?_, ?_⟩, ⟨hU₁c, hU₁U₂⟩,
    ⟨hU₂c, hU₂U⟩⟩
  · rw [hWc.closure_eq]
    exact hWc.isCompact
  · rw [hWc.closure_eq]
    exact hWU₁

/-- **Compact collars from principalization gluing data**
(Copy-4, `sec:gluing`). -/
theorem exists_collars_gluingHypotheses_of_principalizationGluingConclusions
    [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (_hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (_hdim_pos : 0 < V.dim) (_hdim_lt : V.dim < n)
    (_hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (_hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (_hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
    (_hKahlerY : Nonempty (KahlerBackground n Y)) (π : Y → X)
    (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim)
    (y : Y) (hy : y ∈ strictTransform n π V.carrier) (U : Set Y) (hU : IsOpen U)
    (hWU : strictTransform n π V.carrier ⊆ U) (φG φU : Y → EReal)
    (hdata : PrincipalizationGluingConclusions
      (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
      (strictTransform n π V.carrier) y U φG φU) :
    ∃ U₁ U₂ : Set Y, IsOpen U₁ ∧ IsOpen U₂ ∧ y ∈ U₁ ∧
      RelCompactSubset (strictTransform n π V.carrier) U₁ ∧
      RelCompactSubset U₁ U₂ ∧ RelCompactSubset U₂ U ∧
      GluingHypotheses (ClosedRealOneOneForm.pullback hπ.contMDiff θ) U₁ U₂ y φG φU := by
  obtain ⟨⟨hGK, hGbot⟩, ⟨hUdom, hUsmooth⟩, hcollar⟩ := hdata
  obtain ⟨U₁, U₂, hU₁, hU₂, hWU₁, hW₁, h₁₂, h₂U⟩ :=
    exists_relCompactSubset_chain hW.1 hU hWU
  refine ⟨U₁, U₂, hU₁, hU₂, hWU₁ hy, hW₁, h₁₂, h₂U,
    ⟨hGK, hGbot y hy⟩, ⟨⟨U, hU, h₂U.2, hUdom⟩, hUsmooth⟩, ?_⟩
  obtain ⟨C, hC⟩ := hcollar (closure U₂ \ U₁) (h₂U.1.diff hU₁)
    fun z hz => ⟨h₂U.2 hz.1, fun hzW => hz.2 (hWU₁ hzW)⟩
  exact ⟨C, hC⟩

end

end SGPT.Foundations.Analysis.Pending.LocalGluingDataProof
