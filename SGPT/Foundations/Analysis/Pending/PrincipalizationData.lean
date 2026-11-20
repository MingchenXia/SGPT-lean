import SGPT.Foundations.Analysis.FirstPass.BlowupSequences
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.Pending.BlowupBigPullback
import SGPT.Foundations.Analysis.Pending.PositiveVolumePrincipalization
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.PrincipalizationPolarBranchStepFive
import SGPT.Foundations.Analysis.Pending.PrincipalizationStepOneInterface

set_option autoImplicit false

/-!
# Principalization data for gluing

Source: Copy-4, `prop:principalization`, in the standing situation fixed in
`sec:setup` after `lem:resolution` (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:principalization-data`.

Let `X` be a connected compact Kähler manifold, `α = {θ}` big, and `V` a closed
connected complex submanifold of dimension `0 < k < n` which is an irreducible
component of `E_nK(α)`, is not contained in `E_nn(α)`, and has
`h = ⟨α^k⟩_{X|V} > 0`.  Then there are a sequence of blowups `π : Y → X` adapted
to `V`, its closed connected smooth strict transform `W`, a point `y ∈ W`, an
open neighbourhood `U` of `W`, and functions `φ_G` on `Y` and `φ_U` on `U` such
that, with `θ_Y = π^* θ`,

1. `θ_Y + ddᶜ φ_G` is a Kähler current and `φ_G = -∞` on `W`;
2. `θ_Y + ddᶜ φ_U` dominates a Kähler form on `U`, and `φ_U` is smooth near `y`;
3. for every compact `Λ ⊆ U \ W` there is `C_Λ` with `φ_U ≤ φ_G + C_Λ` on `Λ`.

The quasi-psh property of `φ_G` and `φ_U` is part of (1) and (2).  See
`AnalyticGluingData` for the encoding of "dominates a Kähler form on `U`"; since
`W` is compact, `U` can be shrunk, so the existential statement is unchanged.
`W` is nonempty because it is connected.  The conclusion also records that `Y`
is a connected compact Kähler manifold (blowups of compact Kähler manifolds along
smooth centers are compact Kähler, and adapted centers are proper), which the
gluing proposition requires.

The modification, the polar branch `φ_G` and the local analytic branch come from
`PrincipalizationStepOneInterface` (I-0661, answering I-0608): Copy-4 *builds* the
modification `π` in Step 1 and the polar branch `φ_{Q,π} + τψ_E` in Steps 1--5 on that `π`,
so `π`, its Step-1 data, `φ_G` and the Step-5 data are produced together, existentially in
`π`; Steps 3--6 are proved there, from
`PrincipalizationStepOneInterface.ct22Copy4_exists_stepOneData` (formerly a named input, proved since).  This file has no direct
classical or resolution placeholder.

`exists_adaptedBlowup_globalPolarBranch_of_numericalRestrictedVolume_pos` below (an
arbitrary relative principalization with *some* polar branch, from
`exists_kahlerCurrentPotential_eq_bot_on_subset_nonKahlerLocus`) is no longer on the route
of `exists_principalizationGluingData`; it is kept as a statement about arbitrary adapted
principalizations.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.PrincipalizationData

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.BlowupSequences FirstPass.AnalyticGluingData
  PositiveVolumePrincipalization LocusProperties PrincipalizationPolarBranchStepFive

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The global branch required by principalization already comes from any
Kähler current in the class: after changing to the chosen representative, its
potential has a pole at every point of a non-Kähler-locus component.

The remaining principalization problem is therefore the construction of the
local strictly positive branch after an adapted modification. -/
theorem exists_kahlerCurrentPotential_eq_bot_on_component [CompactSpace X]
    (hn : 0 < n) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ))) :
    ∃ φG : X → EReal,
      IsKahlerCurrentPotential θ φG ∧ ∀ w ∈ V.carrier, φG w = ⊥ := by
  obtain ⟨T⟩ := hbig
  obtain ⟨h, hh, hrel⟩ :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  refine ⟨fun x => T.potential x - (h x : EReal), ⟨T.lowerBound, ?_⟩, ?_⟩
  · refine thetaPshPotential_sub_smooth
      (θ := (T.representative - T.lowerBound.form).val)
      (η := (θ - T.lowerBound.form).val) hh (fun e z hz => ?_) T.strictlyPsh
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, hrel e z hz]
    abel
  · intro w hw
    change T.potential w - (h w : EReal) = ⊥
    rw [eq_bot_of_lelongNumber_pos hn T.strictlyPsh.1 (hcomponent.1 hw T)]
    simp

/-- A Kähler current with poles along the entire non-Kähler locus yields a
global Kähler-current potential with a pole along any selected subset. -/
theorem exists_kahlerCurrentPotential_eq_bot_on_subset_nonKahlerLocus [CompactSpace X]
    (hn : 0 < n) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (W : Set X)
    (hW : W ⊆ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ∃ φG : X → EReal,
      IsKahlerCurrentPotential θ φG ∧ ∀ w ∈ W, φG w = ⊥ := by
  obtain ⟨T, -, -, hpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbig
  obtain ⟨h, hh, hrel⟩ :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  refine ⟨fun x => T.potential x - (h x : EReal), ⟨T.lowerBound, ?_⟩, ?_⟩
  · refine thetaPshPotential_sub_smooth
      (θ := (T.representative - T.lowerBound.form).val)
      (η := (θ - T.lowerBound.form).val) hh (fun e z hz => ?_) T.strictlyPsh
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, hrel e z hz]
    abel
  · intro w hw
    have hbot : T.potential w = ⊥ := by
      change w ∈ poleSet T.potential
      rw [hpole]
      exact hW hw
    change T.potential w - (h w : EReal) = ⊥
    rw [hbot]
    simp

/-- Positive restricted volume supplies an adapted principalization whose
strict transform carries a global Kähler-current branch singular along that
transform.  This isolates the global part of the principalization proposition;
the local strictly positive branch and the comparison away from the transform
remain separate analytic inputs. -/
theorem exists_adaptedBlowup_globalPolarBranch_of_numericalRestrictedVolume_pos
    [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hVsmooth : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hdim_pos : 0 < V.dim) (hdim_lt : V.dim < n)
    (hcomponent : IsIrreducibleComponent V
      (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hvolume : 0 < numericalRestrictedVolume omega
      (RealBottChern.ofRepresentative θ) V) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π),
      CompactSpace Y ∧ ConnectedSpace Y ∧ Nonempty (KahlerBackground n Y) ∧
      IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim ∧
      ∃ φG : Y → EReal,
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
        ∀ y ∈ strictTransform n π V.carrier, φG y = ⊥ := by
  have hn : 0 < n := lt_trans hdim_pos hdim_lt
  have hVne : V.carrier ≠ univ := by
    intro hV
    have hdim : V.dim = n :=
      AnalyticIrreducibleComponents.dim_eq_of_carrier_eq_univ V hV
    exact (ne_of_lt hdim_lt) hdim
  obtain ⟨a, ha, haV, Y, _instY, _chartY, _manifoldY, π, hπ, hcompact, hconnected,
    hW, _hiso, H, H', hHexc, hH'disj, hHnot, hvanish, hideal, hspan⟩ :=
    exists_relativePrincipalization_of_numericalRestrictedVolume_pos
      hn omega (RealBottChern.ofRepresentative θ) hbig V hVsmooth hVne hvolume
  have := hcompact
  have := hconnected
  obtain ⟨_, hKahlerY⟩ := compactSpace_and_kahler_of_isBlowupSequence
    ⟨omega⟩ π hπ.isBlowupSequence
  have hbigY : IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hπ.contMDiff θ)) :=
    isBigClass_pullback ⟨omega⟩ θ hbig π hπ.isBlowupSequence
  have hstrict : strictTransform n π V.carrier ⊆ π ⁻¹' V.carrier := by
    rw [strictTransform]
    exact closure_minimal sdiff_subset (V.isClosed_carrier.preimage hπ.contMDiff.continuous)
  have hsubset : strictTransform n π V.carrier ⊆
      nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hπ.contMDiff θ)) := by
    rw [nonKahlerLocus_pullback ⟨omega⟩ θ hbig π hπ.isBlowupSequence]
    exact fun y hy => Or.inl (hcomponent.1 (hstrict hy))
  obtain ⟨φG, hφG, hφGpole⟩ :=
    exists_kahlerCurrentPotential_eq_bot_on_subset_nonKahlerLocus hn
      (ClosedRealOneOneForm.pullback hπ.contMDiff θ) hbigY
      (strictTransform n π V.carrier) hsubset
  exact ⟨Y, _instY, _chartY, _manifoldY, π, hπ, hcompact, hconnected, hKahlerY,
    hW, φG, hφG, hφGpole⟩

/-- **Principalization data for gluing** (Copy-4, `prop:principalization`). -/
theorem exists_principalizationGluingData [CompactSpace X] [ConnectedSpace X]
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
      ∃ y ∈ strictTransform n π V.carrier, ∃ U : Set Y, IsOpen U ∧
        strictTransform n π V.carrier ⊆ U ∧
        ∃ φG φU : Y → EReal,
          PrincipalizationGluingConclusions
            (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
            (strictTransform n π V.carrier) y U φG φU :=
  PrincipalizationStepOneInterface.exists_adaptedBlowup_principalizationGluingConclusions
    omega θ hbig V hVsmooth hdim_pos hdim_lt hcomponent hnonNef hvolume

end

end SGPT.Foundations.Analysis.Pending.PrincipalizationData
