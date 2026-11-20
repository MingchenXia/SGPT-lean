import SGPT.Foundations.Analysis.Pending.PrincipalizationStepOneData
import SGPT.Foundations.Analysis.Pending.PrincipalizationPolarBranchStepFive
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.RelativePrincipalization
import SGPT.Foundations.Analysis.Pending.CartanCoherenceInterface
import SGPT.Foundations.Analysis.Pending.PositiveCurrentInputInterface

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `prop:principalization` on the modification that Step 1 builds

Source: Copy-4, `prop:principalization`, Steps 1--6, `sec:fixed-data` and
`sec:positive-current`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1395-1992`);
blueprint `ana:principalization-data`.  Human decision I-0661, point 3 (answering I-0608),
following I-0484 item 6.

## What changes

`PrincipalizationPolarBranchStepFive.ct22Copy4_exists_polarBranch_copy4StepFiveExceptionalWeightData`
asserted Copy-4 Steps 1--5 for **every** adapted sequence of blowups `π` with smooth strict
transform.  Copy-4 proves them for the modification it **builds** in Step 1 (three relative
principalizations making `𝔅_m`, `𝔅_M` and the QEA ideal `𝔅` invertible along `W`), and its
Step 4 needs exactly that.  This module states Copy-4 in that form:

* `Copy4StepOneData` — the data Copy-4 has in hand once Steps 1--4 are done on a given
  modification `π`: the exceptional metric of Step 3, the fixed data of `sec:fixed-data`
  (`R = θ + ddᶜΦ_R ≥ δ_R ω`, `eq:PhiR-lower`, the ideal function `Ψ` of `𝔧 𝔅_m` with a point
  `x₀ ∈ V` near which it is smooth), the regularization `U_M` of `eq:def-TM` with
  `V ⊄ Z(𝔅_M)` (`sec:positive-current`), the constants of `eq:constants`, Step 1's
  effective divisors `G̃_M, H^fix, P^mov, P^F` with their ideal identities (`P^mov`, `P^F`
  exceptional), smooth metrics on them, and Step 4's Kähler current `φ'` on `W` with
  logarithmic singularities along `D|_W`.  These are exactly the hypotheses of the proved
  assembly `StepFourNoComponentContainsW.exists_polarBranch_stepFiveData_of_effectiveDivisors_of_exceptional`.
* `ct22Copy4_exists_stepOneData` — formerly **the named input**, now proved (see its docstring): under the standing hypotheses of
  `prop:principalization`, SOME adapted sequence of blowups with smooth strict transform
  carries such data.  This is Copy-4 Step 1 (built with relative principalization) together
  with the quasi-equisingular approximation of `sec:positive-current` (I-0484; since proved,
  `QuasiEquisingularApproximationInterface.xiaTheorem162_exists_quasiEquisingularApproximation`)
  and `lem:regularization` at level `M` (proved since 2980657b; the field `U_M` still needs
  Nadel coherence of `𝔅_M`, see `AmbientUMWeightLowerBound`); it is existential in `π`, as in
  the source.
* `Copy4StepOneData.exists_polarBranch_stepFiveData` — **the proved half**: Steps 3--6
  (the polar branch `φ_G = φ_{Q_M} ∘ π + τψ_{E_rel}` and its Step-5 data), by the assembly.
* `exists_adaptedBlowup_principalizationGluingConclusions` — the conclusion of
  `PrincipalizationData.exists_principalizationGluingData`, now obtained through the
  modification of Step 1 instead of through an arbitrary relative principalization.

The universally quantified interface is no longer consumed by the main route.

`Copy4StepOneData`, its proved half and `RelativePrincipalizationHolds` (with
`relativePrincipalizationHolds`) are declared, under these same names, in the base module
`PrincipalizationStepOneData` (moved there in run 0110, statements unchanged), so that the
producers of the fields can be imported here without an import cycle.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.PrincipalizationStepOneInterface

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.AnalyticGluingData
  FirstPass.NonKahlerLocus FirstPass.BlowupSequences FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction
  ManifoldTubePositivity TubePositivityOneFlattening DivisorMetric
  PrincipalizationSourceDataReduction

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Copy-4 `prop:principalization`, Step 1 with the data of `sec:fixed-data`,
`sec:positive-current` and Step 4.**  Under the standing hypotheses of
`prop:principalization`, some sequence of blowups adapted to `V`, with closed connected
smooth strict transform `W` of dimension `dim V`, carries `Copy4StepOneData`.

Copy-4 builds this `π` in three stages (`π_fix` principalizing `𝔅_m`, then the moving part of
`𝔅_M`, then an ideal realizing the excess divisor `F_B`), each an application of
`lem:relative-principalization`; the ideals `𝔅_q = 𝓘(qV_θ)`, the regularization `U_M` and the
current `φ'` come from `sec:positive-current` (the quasi-equisingular approximation `φ_{K,ℓ}`
of `V_θ`, since proved).  Existential in `π`, as in the source.

The relative principalizations are not part of this statement: it takes
`lem:relative-principalization` as the hypothesis `hRP`, which the route discharges with the
Hironaka statement `RelativePrincipalization.exists_factorizationData` (proved in place from the canonical resolution invariant), so
the Hironaka content stays in that one statement.

**Proved** (human decision I-0739 item 5, statement unchanged) by
`CartanComponentIdeal.exists_copy4StepOneData_of_cartanCoherence` from `hRP` and two inputs in
their own modules, both since proved: `CartanCoherenceInterface.cartanCoherence` (Cartan 1950; Oka/Cartan
programme of TN-CLASSICAL) and `PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput`
(`sec:positive-current` for `V_θ`, QEA). -/
theorem ct22Copy4_exists_stepOneData [CompactSpace X] [ConnectedSpace X]
    (hRP : RelativePrincipalizationHolds.{u} n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) := by
  exact CartanComponentIdeal.exists_copy4StepOneData_of_cartanCoherence hRP
    CartanCoherenceInterface.cartanCoherence omega θ hbig V hVsmooth hdim_pos hdim_lt hcomponent
    hnonNef (PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput omega θ hbig V hVsmooth
      hdim_pos hdim_lt hcomponent hnonNef hvolume)

/-- **Copy-4 Steps 1--5 on the modification of Step 1**: some adapted sequence of blowups,
with compact connected Kähler total space and smooth strict transform, carries a polar
branch with Step-5 data. -/
theorem exists_adaptedBlowup_polarBranch_stepFiveData [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π),
      CompactSpace Y ∧ ConnectedSpace Y ∧ Nonempty (KahlerBackground n Y) ∧
      IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim ∧
      ∃ φG : Y → EReal,
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
        Nonempty (Copy4StepFiveExceptionalWeightData
          (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
          (strictTransform n π V.carrier) φG) := by
  obtain ⟨Y, _instY, _chartY, _manifoldY, π, hπ, hW, ⟨D⟩⟩ :=
    ct22Copy4_exists_stepOneData (relativePrincipalizationHolds n) omega θ hbig V hVsmooth
      hdim_pos hdim_lt hcomponent hnonNef hvolume
  obtain ⟨hcompact, hKahlerY⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omega⟩ π hπ.isBlowupSequence
  have hconnected : ConnectedSpace Y :=
    BlowupConnected.connectedSpace_of_isBlowupSequence π hπ.isBlowupSequence
  have := hcompact
  have := hconnected
  obtain ⟨φG, hφG, hdata⟩ := D.exists_polarBranch_stepFiveData
  exact ⟨Y, _instY, _chartY, _manifoldY, π, hπ, hcompact, hconnected, hKahlerY, hW, φG, hφG,
    hdata⟩

/-- **The conclusion of `PrincipalizationData.exists_principalizationGluingData`, through the
modification of Copy-4 Step 1.**  The polar branch and its Step-5 data come from
`exists_adaptedBlowup_polarBranch_stepFiveData`; the pole clause from bigness
(`PrincipalizationPolarBranchStepFive.eq_bot_on_strictTransform_of_isKahlerCurrentPotential`);
the local branch with its collar comparison from the already-proved Step-5 → Step-6
reduction. -/
theorem exists_adaptedBlowup_principalizationGluingConclusions [CompactSpace X]
    [ConnectedSpace X] (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hvolume : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π),
      CompactSpace Y ∧ ConnectedSpace Y ∧ Nonempty (KahlerBackground n Y) ∧
      IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim ∧
      ∃ y ∈ strictTransform n π V.carrier, ∃ U : Set Y, IsOpen U ∧
        strictTransform n π V.carrier ⊆ U ∧
        ∃ φG φU : Y → EReal,
          PrincipalizationGluingConclusions
            (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
            (strictTransform n π V.carrier) y U φG φU := by
  obtain ⟨Y, _instY, _chartY, _manifoldY, π, hπ, hcompact, hconnected, hKahlerY, hW, φG, hφG,
    hdata⟩ :=
    exists_adaptedBlowup_polarBranch_stepFiveData omega θ hbig V hVsmooth hdim_pos hdim_lt
      hcomponent hnonNef hvolume
  have := hcompact
  have hφGpole : ∀ w ∈ strictTransform n π V.carrier, φG w = ⊥ :=
    PrincipalizationPolarBranchStepFive.eq_bot_on_strictTransform_of_isKahlerCurrentPotential
      omega hbig hdim_pos hcomponent π hπ hφG
  obtain ⟨d⟩ := nonempty_anchoredData_of_nonempty_copy4StepFiveExceptionalWeightData hdata
  obtain ⟨y, hy, U, hU, hWU, φU, hφU, hcomparison⟩ := d.exists_localBranch hφG hφGpole
  exact ⟨Y, _instY, _chartY, _manifoldY, π, hπ, hcompact, hconnected, hKahlerY,
    hW, y, hy, U, hU, hWU, φG, φU, ⟨⟨hφG, hφGpole⟩, hφU, hcomparison⟩⟩

end

end SGPT.Foundations.Analysis.Pending.PrincipalizationStepOneInterface
