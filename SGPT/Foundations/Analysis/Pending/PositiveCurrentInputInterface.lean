import SGPT.Foundations.Analysis.Pending.Copy4TraceInputReduction
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMassAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `sec:positive-current` for `V_θ` (formerly a named input; PROVED along route F)

Source: Copy-4, `sec:positive-current` (the quasi-equisingular approximation `φ_{K,ℓ}` of the
minimal-singularity potential `V_θ`, the ideals `𝔅_q = 𝓘(q V_θ)`, and the Kähler current `φ_K` on
`V` with the singularities of `ψ_𝔅 / (m r)`)
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex`, `sec:positive-current`);
blueprint `ana:copy4-trace-input-positive-current`.

Human decision I-0739 item 5 (answering I-0735 (A)): `ct22Copy4_exists_stepOneData` is proved from
two named inputs in their own modules; this is input (ii).  Its content is the quasi-equisingular
approximation (QEA), which waits (item 7 of the same decision opens it for scoping by
TN23-ENVELOPES).

PROVED (positive-current programme, human decision I-0752; route F, I-0796 D0): the `sorry` is
discharged in place by
`RestrictedApproximantMassAssembly.positiveCurrentInput_of_numericalRestrictedVolume_pos`
(`TraceUPart` from the restricted approximant mass bound `F-b`, `lem:domination` from bigness of
`{θ|_V}`).  The statement is unchanged.  The proof does not use `hcomponent`.  It reaches one named
input, the Boucksom bigness criterion
`UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`, which is already a root
of the main theorem.

The hypotheses are exactly the standing hypotheses of `ct22Copy4_exists_stepOneData` (Copy-4,
`prop:principalization`): every one of them is available to the source at that point, and keeping
all of them makes the input as weak as possible.  The conclusion is
`Copy4TraceInputReduction.PositiveCurrentInput` (27befb48), unchanged.  Reverse test: it does not
follow from the conclusion of `ct22Copy4_exists_stepOneData` (that conclusion lives on a
modification `Y` and says nothing about `V_θ`'s multiplier ideals on `X`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentInputInterface

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.NonKahlerLocus FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.BlowupSequences Copy4TraceInputReduction

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

-- The hypothesis `hcomponent` turns out to be redundant: route F does not use that `V` is a
-- component of `E_nK(α)`.  It is part of an existing statement, so it is kept and the
-- unused-binder linter is switched off here rather than the signature being changed.
set_option linter.unusedVariables false in
/-- **Copy-4 `sec:positive-current` for `φ = V_θ`** (proved along route F).  Under the standing
hypotheses of `prop:principalization`: for every `C ≥ 2` there are `m ≥ 1` and `δ₀ > 0` such that for
arbitrarily large `r` there are a coherent ideal `𝔅` with `V ⊄ Z(𝔅)` and a weight `ψ_𝔅` with
analytic singularities of type `𝔅`, with `𝔅 · 𝓘(m V_θ)^{(C-1) r} ⊆ 𝓘(C m r V_θ)` along `V`, and a
level potential `φ_K` on `V` (constant `δ₀`) with the singularities of `ψ_𝔅 / (m r)`. -/
theorem ct22Copy4_positiveCurrentInput [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    PositiveCurrentInput omega θ V hVsmooth := by
  exact RestrictedApproximantMassAssembly.positiveCurrentInput_of_numericalRestrictedVolume_pos omega θ
    hbig V hVsmooth hdim_pos hdim_lt hnonNef hvolume

end SGPT.Foundations.Analysis.Pending.PositiveCurrentInputInterface
