import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.Pending.LocalGluingDataProof

set_option autoImplicit false

/-!
# Compact collars from principalization gluing data

Source: Copy-4, `prop:principalization` and `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:local-gluing-data`.

Assume the hypotheses, data and conclusions of `ana:principalization-data`
(`Pending.PrincipalizationData`), and put `θ_Y = π^* θ`.  Then there are open
neighbourhoods `W ⋐ U₁ ⋐ U₂ ⋐ U` such that `y`, `φ_G` and `φ_U` satisfy the three
hypotheses of `ana:gluing` for `Y, θ_Y, U₁, U₂, y`.  The conclusion also records
`y ∈ U₁` (from `y ∈ W ⋐ U₁`), which `ana:gluing` assumes.

The hypothesis list repeats that of the principalization proposition verbatim,
followed by its data `(Y, π, W, y, U, φ_G, φ_U)` and its conclusions.

Proved in `Pending.LocalGluingDataProof`.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.LocalGluingData

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  FirstPass.AnalyticGluingData

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Compact collars from principalization gluing data**
(Copy-4, `sec:gluing`). -/
theorem exists_collars_gluingHypotheses_of_principalizationGluingConclusions
    [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
    (hKahlerY : Nonempty (KahlerBackground n Y)) (π : Y → X)
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
      GluingHypotheses (ClosedRealOneOneForm.pullback hπ.contMDiff θ) U₁ U₂ y φG φU :=
  LocalGluingDataProof.exists_collars_gluingHypotheses_of_principalizationGluingConclusions
    omega θ hbig V hVsmooth hdim_pos hdim_lt hcomponent hnonNef hvolume hKahlerY π hπ hW y hy U hU
    hWU φG φU hdata

end

end SGPT.Foundations.Analysis.Pending.LocalGluingData
