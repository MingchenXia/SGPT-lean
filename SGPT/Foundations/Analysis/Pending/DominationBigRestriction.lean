import SGPT.Foundations.Analysis.Pending.DivisorialDomination
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationSmoothOffPole
import SGPT.Foundations.Analysis.Pending.UniformAmbientVolumeBignessInterface
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bigness of `α|_V` from a positive-mass potential, and `PositiveCurrentInput` from `TraceUPart`

Source: Copy-4, `sec:setup`, "The trace of `V_θ`"
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1398-1416`):

> Since `PSH(V, γ)_{>0} ≠ ∅`, the class `{γ} = α|_V` is big by `sec:npp` `it:bigness`; this is the
> bigness hypothesis needed in `lem:domination` for `(Z, ω_Z, γ) = (V, ω_V, γ)`.

`it:bigness` is Boucksom's criterion (a pseudoeffective class of positive volume is big,
`bou02-volume:4.8`).  In the tree it is the named published input
`UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound` (I-0739 item 8,
already a root of the main theorem's cone), stated for an arbitrary compact Kähler manifold with
the volume read through admissible presentations.

* `hasUniformAmbientMassLowerBound_of_lt_diagonalPotentialMass` (sorry-free): a `θ`-psh `u` of
  mass `m` gives, at EVERY error `ε > 0`, an admissible presentation of `{θ}` (Demailly's
  approximant of `u`, analytic singularities smooth off the poles,
  `DemaillyApproximationSmoothOffPole.exists_algebraicApproximation`) of mass `≥ m`
  (`eq:dom-mass`, `DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul`).
* `isBigClass_of_diagonalPotentialMass_pos`: hence `{θ}` is big (the named input).
* `positiveCurrentInput_of_traceUPart'`: with `lem:domination` for big classes
  (`DivisorialDomination.dominationLemma_of_isBigClass`) the positive-current root needs only
  `TraceUPart`: `HasDominationLemma` is DISCHARGED, through the existing Boucksom root.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.DominationBigRestriction

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold DiagonalMass

/-! ### Positive mass gives a uniform ambient mass lower bound -/

section Mass

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- The whole of a connected nonempty complex manifold, as a closed irreducible analytic
subvariety of full dimension. -/
def univSubvariety [ConnectedSpace Z] [Nonempty Z] : ClosedIrreducibleAnalyticSubvariety k Z where
  carrier := univ
  isClosed_carrier := isClosed_univ
  irreducible_carrier := AnalyticIrreducibleComponents.isComplexAnalyticallyIrreducible_univ
  dim := k
  dim_le := le_rfl
  regularLocus_nonempty := by
    obtain ⟨x⟩ := ‹Nonempty Z›
    exact ⟨x, AnalyticIrreducibleComponents.regularAtDim_univ x⟩

/-- **A `θ`-psh potential of mass `m` bounds the perturbed ambient volumes of `{θ}` below by `m`,
at every error.**  For `ε > 0` take Demailly's approximant `ψ_j ≥ u` of `u` with error
`δ_j < ε`: it is `(θ + εω)`-psh, has analytic singularities smooth off its poles and is not
identically `-∞`, so it is an admissible presentation of `{θ}` at error `ε` (on the full space),
and `∫(θ + εω)_{ψ_j}^k ≥ ∫θ_u^k` (`eq:dom-mass`). -/
theorem hasUniformAmbientMassLowerBound_of_lt_diagonalPotentialMass [Nonempty Z]
    (omega : KahlerBackground k Z) (θ : ClosedRealOneOneForm k Z) {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) {η : ℝ≥0∞} (hη : η < diagonalPotentialMass θ u hu)
    (V : ClosedIrreducibleAnalyticSubvariety k Z) (hV : V.carrier = univ) :
    PerturbedAmbientEnvelopeMonotone.HasUniformAmbientMassLowerBound omega
      (RealBottChern.ofRepresentative θ) V η := by
  obtain ⟨ψs, δ, -, hsop, -, hinf, -, hδ, hψs⟩ :=
    DemaillyApproximationSmoothOffPole.exists_algebraicApproximation omega θ u hu
  intro ε
  obtain ⟨j, hj⟩ : ∃ j, δ j < (ε : ℝ) := (hδ.eventually (gt_mem_nhds ε.2)).exists
  have hle : u ≤ ψs j := fun x => by
    rw [← hinf x]
    exact iInf_le (fun i => ψs i x) j
  have hpsh : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val (ψs j) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hψs j)
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.2 hj.le))
    rwa [show θ + δ j • omega.form + ((ε : ℝ) - δ j) • omega.form =
      θ + (ε : ℝ) • omega.form by module] at h
  let p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) V ε :=
    { representative := θ
      represents := rfl
      potential := ψs j
      potential_psh := hpsh
      smoothAnalyticSingularities := hsop j
      not_carrier_subset_poleSet := by
        rw [hV]
        intro hsub
        obtain ⟨x⟩ := ‹Nonempty Z›
        obtain ⟨y, -, hy⟩ := (hψs j).2 x univ isOpen_univ (mem_univ x)
        exact hy (hsub (mem_univ y)) }
  refine lt_of_lt_of_le ?_
    (le_iSup (fun q : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative θ) V ε => FullSpaceAmbientMass.perturbedDiagonalPotentialMass q) p)
  exact hη.trans_le
    (DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul omega ε.2 hu hpsh hle)

/-- **Copy-4 `sec:npp` `it:bigness`**: on a compact connected Kähler manifold of positive
dimension, a class admitting a potential of positive non-pluripolar mass is big.  This is the
named published input `UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`
(Boucksom 4.8 with the volume sandwich, already a root of the main cone) at `η = m/2`. -/
theorem isBigClass_of_diagonalPotentialMass_pos (hk : 0 < k) [ConnectedSpace Z] [Nonempty Z]
    (omega : KahlerBackground k Z) (θ : ClosedRealOneOneForm k Z) {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) (hpos : 0 < diagonalPotentialMass θ u hu) :
    IsBigClass (RealBottChern.ofRepresentative θ) := by
  have htop : diagonalPotentialMass θ u hu ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega _ univ).ne
  exact UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound hk omega _
    univSubvariety rfl ⟨u, hu⟩ _ (ENNReal.half_pos hpos.ne')
    (hasUniformAmbientMassLowerBound_of_lt_diagonalPotentialMass omega θ hu
      (ENNReal.half_lt_self hpos.ne' htop) univSubvariety rfl)

end Mass

/-! ### `PositiveCurrentInput` from `TraceUPart` -/

section Assembly

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

open FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.BlowupSequences FirstPass.QuasiEquisingularApproximation FirstPass.IEnvelope
  SubmanifoldChartedSpace SubmanifoldIdealRestriction SubmanifoldMassCalculus
  Copy4TraceInputReduction PositiveCurrentAssembly

/-- **`lem:domination` on `V` from the bigness of `{θ|_V}`** (`DivisorialDomination.dominationLemma_of_isBigClass`
with `V`'s flattening complex structure). -/
theorem hasDominationLemma_of_isBigClass [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hbigV : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      IsBigClass (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback
        (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ))) :
    HasDominationLemma omega θ V hV := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier := connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  exact DivisorialDomination.dominationLemma_of_isBigClass _ _ hbigV

/-- **The positive-current root needs only `TraceUPart`.**  Under the standing hypotheses of
`PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput` (`{θ}` big, `0 < dim V < n`,
`V ⊄ E_nn(α)`), `TraceUPart` gives `PositiveCurrentInput`: the `γ`-psh `u` of positive mass of
(T1) makes `{γ} = α|_V` big (`isBigClass_of_diagonalPotentialMass_pos`, Copy-4 `it:bigness`,
through the existing Boucksom root), so `lem:domination` holds on `V`
(`hasDominationLemma_of_isBigClass`), and `PositiveCurrentAssembly.positiveCurrentInput_of_traceUPart`
applies. -/
theorem positiveCurrentInput_of_traceUPart' [CompactSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hU : TraceUPart omega θ V hV) :
    PositiveCurrentInput omega θ V hV := by
  refine positiveCurrentInput_of_traceUPart omega θ hbig V hV hdim_pos hdim_lt hnonNef hU
    (hasDominationLemma_of_isBigClass omega θ V hV ?_)
  have hpkg := hasTracePackage_of_traceUPart (hdim_pos.trans hdim_lt) omega θ hbig V hV hnonNef hU
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier := connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  obtain ⟨-, -, -, -, -, u, hu, -, hpos, -⟩ := hpkg
  exact isBigClass_of_diagonalPotentialMass_pos hdim_pos
    (SubmanifoldKahlerRestriction.kahlerBackground hk hV.2.2 omega) _ hu hpos

end Assembly

end

end SGPT.Foundations.Analysis.Pending.DominationBigRestriction
