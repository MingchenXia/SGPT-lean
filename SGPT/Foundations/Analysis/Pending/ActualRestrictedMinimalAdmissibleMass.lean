import SGPT.Foundations.Analysis.Pending.NonKahlerMinimalRestrictionTraceMass
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationSmoothOffPole
import SGPT.Foundations.Analysis.Pending.RestrictedMassEquality
import SGPT.Foundations.Analysis.Pending.RestrictedVolumeModelMass

set_option autoImplicit false

/-! # Actual admissible regularization of the smaller minimal restriction -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualRestrictedMinimalAdmissibleMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  SubmanifoldChartedSpace SubmanifoldMassCalculus SubmanifoldRestrictedPresentation
  RestrictedVolumeModelMass DiagonalMass

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Original non-nef avoidance internally supplies the genuine smaller
minimal restriction and an actual larger-error admissible competitor. -/
theorem exists_admissible_mass_ge_smaller_minimal_restriction
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hnn : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (δ ε : PositiveError) (hδε : (δ : ℝ) < ε) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
    let γ := ClosedRealOneOneForm.pullback
      (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ
    let omegaV := SubmanifoldKahlerRestriction.kahlerBackground
      (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega
    ∃ hmin : IsThetaPshPotential (γ + (δ : ℝ) • omegaV.form).val
        (restrictedModel θ omega.form δ (W := V.carrier)),
      ∃ p : AdmissibleRestrictedCurrentPresentation omega
          (RealBottChern.ofRepresentative θ) V ε,
        p.representative = θ ∧
        thetaPshSupremum (θ + (δ : ℝ) • omega.form).val ≤ p.potential ∧
        diagonalPotentialMass (γ + (δ : ℝ) • omegaV.form)
          (restrictedModel θ omega.form δ (W := V.carrier)) hmin ≤ acTopMass p := by
  classical
  let hk := le_of_isClosedConnectedSubmanifold hV
  let hW := hV.2.2
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier := connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  let hι := contMDiff_val hk hW
  let γ := ClosedRealOneOneForm.pullback hι θ
  let omegaV := SubmanifoldKahlerRestriction.kahlerBackground hk hW omega
  let σ := θ + (δ : ℝ) • omega.form
  obtain ⟨x, hxV, hx⟩ := Set.not_subset.mp hnn
  have : Nonempty X := ⟨x⟩
  have hxnK : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative σ) := by
    intro h
    apply hx
    apply mem_nonNefLocus.mpr
    refine ⟨δ, ?_⟩
    simpa only [σ, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul] using h
  have hbig : IsBigClass (RealBottChern.ofRepresentative σ) := by
    have h := hxnK
    rw [mem_nonKahlerLocus] at h
    obtain ⟨T, _⟩ := not_forall.mp h
    exact ⟨T⟩
  have hu := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum σ hbig
  obtain ⟨_, hmin0, _⟩ :=
    NonKahlerMinimalRestrictionTraceMass.exists_positive_ordinary_restriction_mass_eq_normalizedTraceMass_of_not_mem_nonKahlerLocus
      omega omegaV hι omegaV.isKahler σ ⟨⟨x, hxV⟩, hxnK⟩
  have hmin : IsThetaPshPotential (γ + (δ : ℝ) • omegaV.form).val
      (restrictedModel θ omega.form δ (W := V.carrier)) := by
    have hRform : ClosedRealOneOneForm.pullback hι σ =
        γ + (δ : ℝ) • omegaV.form := by
      dsimp only [σ]
      rw [NefCoreKahlerCurrent.pullback_add_smul]
      rfl
    rw [hRform] at hmin0
    exact hmin0
  obtain ⟨ψ, a, _, hsop, _, hinf, _, ha, hψ⟩ :=
    DemaillyApproximationSmoothOffPole.exists_algebraicApproximation omega σ
      (thetaPshSupremum σ.val) hu
  obtain ⟨j, hj⟩ : ∃ j, a j < (ε : ℝ) - δ :=
    (ha.eventually (gt_mem_nhds (sub_pos.mpr hδε))).exists
  have hle : thetaPshSupremum σ.val ≤ ψ j := fun y => by
    rw [← hinf y]
    exact iInf_le (fun i => ψ i y) j
  have hform : σ + a j • omega.form + ((ε : ℝ) - δ - a j) • omega.form =
      θ + (ε : ℝ) • omega.form := by dsimp only [σ]; module
  have hp : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val (ψ j) := by
    simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hψ j) (KahlerDomination.isSemipositive_smul omega.isSemipositive
        (sub_nonneg.mpr hj.le))
  have hnopole : ¬ V.carrier ⊆ poleSet (ψ j) := by
    intro hsub
    let y0 : V.carrier := Classical.choice inferInstance
    obtain ⟨y, _, hy⟩ := hmin.2 y0 univ isOpen_univ (mem_univ y0)
    apply hy
    change thetaPshSupremum σ.val y.1 = ⊥
    exact le_bot_iff.mp ((hle y.1).trans_eq (hsub y.2))
  let p : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative θ) V ε :=
    { representative := θ
      represents := rfl
      potential := ψ j
      potential_psh := hp
      smoothAnalyticSingularities := hsop j
      not_carrier_subset_poleSet := hnopole }
  have hpR : IsThetaPshPotential (γ + (ε : ℝ) • omegaV.form).val
      (fun y : V.carrier => ψ j y.1) := (restrictPresentation hk hW p).potential_psh
  have hformV : γ + (δ : ℝ) • omegaV.form + ((ε : ℝ) - δ) • omegaV.form =
      γ + (ε : ℝ) • omegaV.form := by module
  have hpR' : IsThetaPshPotential
      (γ + (δ : ℝ) • omegaV.form + ((ε : ℝ) - δ) • omegaV.form).val
      (fun y : V.carrier => ψ j y.1) := by simpa only [hformV] using hpR
  have hmass := DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
    omegaV (sub_pos.mpr hδε) hmin hpR' (fun y => hle y.1)
  have hac := RestrictedMassEquality.acTopMass_eq_diagonalPotentialMass_restrict' hk hW p
  refine ⟨hmin, p, rfl, hle, ?_⟩
  rw [hac]
  simpa only [hformV] using hmass

end
end SGPT.Foundations.Analysis.Pending.ActualRestrictedMinimalAdmissibleMass
