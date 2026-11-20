import SGPT.Foundations.Analysis.Pending.UniformAmbientVolumeBignessInterface
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationSmoothOffPole
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A potential of positive non-pluripolar mass makes the class big (Boucksom 4.8)

Source: Boucksom, *On the volume of a line bundle*, Theorem 4.8 (`bou02-volume:4.8`); Copy-4
`sec:npp` `it:bigness`.  This is `DominationBigRestriction.hasUniformAmbientMassLowerBound_of_lt_diagonalPotentialMass`
and `DominationBigRestriction.isBigClass_of_diagonalPotentialMass_pos` restated on a layer that does
not import the rooftop / envelope modules (TN-CLASSICAL run 0159 r2): their proofs use only Demailly's
approximation smooth off the poles, the one-term mass comparison
(`PotentialMassComparison.diagonalPotentialMass_le_of_le_add_smul`) and Boucksom 4.8
(`UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`, proved in place modulo
Hironaka's `exists_factorizationData` and Yau's theorem).  Its consumer is the non-big branch
`BoucksomNonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`, which
sits below the rooftop modules and so cannot import `DominationBigRestriction`.

* `hasUniformAmbientMassLowerBound_of_lt_diagonalPotentialMass` — a `θ`-psh potential of mass `> η`
  bounds the perturbed ambient volumes of `{θ}` below by `η` at every error;
* `isBigClass_of_diagonalPotentialMass_pos` — positive mass ⇒ big;
* `diagonalPotentialMass_eq_zero_of_not_isBigClass` — the contrapositive: in a non-big class every
  potential has zero non-pluripolar mass.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold DiagonalMass

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
at every error** (Demailly's approximants `ψ_j ≥ u` are admissible presentations at error `ε`, and
`∫(θ + εω)_{ψ_j}^k ≥ ∫θ_u^k`). -/
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
    (PotentialMassComparison.diagonalPotentialMass_le_of_le_add_smul omega ε.2 hu hpsh hle)

/-- **Positive mass makes the class big** (Copy-4 `sec:npp` `it:bigness`; Boucksom 4.8 at
`η = m/2`): on a compact connected Kähler manifold of positive dimension, a class admitting a
potential of positive non-pluripolar mass is big. -/
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

/-- **In a non-big class every potential has zero non-pluripolar mass** (the contrapositive). -/
theorem diagonalPotentialMass_eq_zero_of_not_isBigClass (hk : 0 < k) [ConnectedSpace Z]
    [Nonempty Z] (omega : KahlerBackground k Z) (θ : ClosedRealOneOneForm k Z) {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) (hnb : ¬ IsBigClass (RealBottChern.ofRepresentative θ)) :
    diagonalPotentialMass θ u hu = 0 := by
  by_contra h
  exact hnb (isBigClass_of_diagonalPotentialMass_pos hk omega θ hu (pos_iff_ne_zero.mpr h))

end

end SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
