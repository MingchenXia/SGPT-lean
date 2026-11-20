import SGPT.Foundations.Analysis.Pending.ActualRestrictedMinimalAdmissibleMass

set_option autoImplicit false

/-! # The actual infimum and right limit of ordinary minimal restricted masses -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMinimalRestrictedMassFormula

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume SubmanifoldChartedSpace
  SubmanifoldMassCalculus RestrictedVolumeModelMass DiagonalMass
  ActualRestrictedMinimalAdmissibleMass

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The entire genuine ordinary restriction family is produced before
all positive error paths; its actual finite masses tend to restricted volume,
including zero restricted volume and non-big original classes. -/
theorem exists_minimal_restriction_mass_inf_and_tendsto
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hnn : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
    let γ := ClosedRealOneOneForm.pullback
      (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ
    let omegaV := SubmanifoldKahlerRestriction.kahlerBackground
      (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega
    ∃ H : ∀ ε : PositiveError, IsThetaPshPotential (γ + (ε : ℝ) • omegaV.form).val
        (restrictedModel θ omega.form ε (W := V.carrier)),
      (∀ ε : PositiveError, diagonalPotentialMass (γ + (ε : ℝ) • omegaV.form)
        (restrictedModel θ omega.form ε (W := V.carrier)) (H ε) ≠ ⊤) ∧
      numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V =
        ⨅ ε : PositiveError, diagonalPotentialMass (γ + (ε : ℝ) • omegaV.form)
          (restrictedModel θ omega.form ε (W := V.carrier)) (H ε) ∧
      ∀ {I : Type*} (F : Filter I) (ε : I → PositiveError),
        Tendsto (fun i => (ε i : ℝ)) F (𝓝 0) →
        Tendsto (fun i => diagonalPotentialMass (γ + (ε i : ℝ) • omegaV.form)
          (restrictedModel θ omega.form (ε i) (W := V.carrier)) (H (ε i))) F
          (𝓝 (numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V)) := by
  classical
  let hk := le_of_isClosedConnectedSubmanifold hV
  let hW := hV.2.2
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : Nonempty X := ⟨hV.2.1.nonempty.choose⟩
  let hι := contMDiff_val hk hW
  let γ := ClosedRealOneOneForm.pullback hι θ
  let omegaV := SubmanifoldKahlerRestriction.kahlerBackground hk hW omega
  have H : ∀ ε : PositiveError, IsThetaPshPotential (γ + (ε : ℝ) • omegaV.form).val
      (restrictedModel θ omega.form ε (W := V.carrier)) := by
    intro ε
    let e2 : PositiveError := ⟨2 * (ε : ℝ), mul_pos (by norm_num) ε.2⟩
    obtain ⟨hmin, _⟩ := exists_admissible_mass_ge_smaller_minimal_restriction
      omega θ V hV hnn ε e2 (by dsimp only [e2]; linarith [ε.2])
    exact hmin
  let M : PositiveError → ℝ≥0∞ := fun ε => diagonalPotentialMass
    (γ + (ε : ℝ) • omegaV.form) (restrictedModel θ omega.form ε (W := V.carrier)) (H ε)
  have hfinite : ∀ ε, M ε ≠ ⊤ := by
    intro ε
    exact (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omegaV
      (fun _ : Fin V.dim => (H ε).1) univ).ne
  have hupper : ∀ ε, restrictedMassEnvelope (acTopMassData omega)
      (RealBottChern.ofRepresentative θ) V ε ≤ M ε := by
    intro ε
    apply iSup_le
    intro p
    exact acTopMass_le_restrictedModelMass omega θ V hV p (H ε)
  have hlower : ∀ ε : PositiveError, M ⟨(ε : ℝ) / 2, half_pos ε.2⟩ ≤
      restrictedMassEnvelope (acTopMassData omega) (RealBottChern.ofRepresentative θ) V ε := by
    intro ε
    let ehalf : PositiveError := ⟨(ε : ℝ) / 2, half_pos ε.2⟩
    obtain ⟨_, p, _, _, hmass⟩ := exists_admissible_mass_ge_smaller_minimal_restriction
      omega θ V hV hnn ehalf ε (by dsimp only [ehalf]; linarith [ε.2])
    exact hmass.trans (le_iSup (fun p : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative θ) V ε => acTopMass p) p)
  have hinf : numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V =
      ⨅ ε, M ε := by
    rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ V hnn]
    apply le_antisymm
    · exact iInf_mono hupper
    · apply le_iInf
      intro ε
      exact (iInf_le M ⟨(ε : ℝ) / 2, half_pos ε.2⟩).trans (hlower ε)
  have hmono : Monotone M := by
    intro δ ε hδε
    rcases hδε.eq_or_lt with heq | hlt
    · exact le_of_eq (congrArg M heq)
    have hδeps : (δ : ℝ) < ε := hlt
    have hambient := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
      (θ + (δ : ℝ) • omega.form) (by
        obtain ⟨x, hxV, hx⟩ := Set.not_subset.mp hnn
        have hnk : x ∉ nonKahlerLocus
            (RealBottChern.ofRepresentative (θ + (δ : ℝ) • omega.form)) := by
          intro h
          apply hx
          apply mem_nonNefLocus.mpr
          refine ⟨δ, ?_⟩
          simpa only [RealBottChern.ofRepresentative_add,
            RealBottChern.ofRepresentative_smul] using h
        rw [mem_nonKahlerLocus] at hnk
        obtain ⟨T, _⟩ := not_forall.mp hnk
        exact ⟨T⟩)
    have hformX : θ + (δ : ℝ) • omega.form + ((ε : ℝ) - δ) • omega.form =
        θ + (ε : ℝ) • omega.form := by module
    have hlarge : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val
        (thetaPshSupremum (θ + (δ : ℝ) • omega.form).val) := by
      simpa only [hformX] using LocalPotentials.isThetaPshPotential_add_of_semipositive
        hambient (KahlerDomination.isSemipositive_smul omega.isSemipositive
          (sub_pos.mpr hδeps).le)
    have hle := le_thetaPshSupremum hlarge
      (thetaPshSupremum_le_zero (θ + (δ : ℝ) • omega.form).val)
    have hformV : γ + (δ : ℝ) • omegaV.form + ((ε : ℝ) - δ) • omegaV.form =
        γ + (ε : ℝ) • omegaV.form := by module
    have hε : IsThetaPshPotential
        (γ + (δ : ℝ) • omegaV.form + ((ε : ℝ) - δ) • omegaV.form).val
        (restrictedModel θ omega.form ε (W := V.carrier)) := by
      simpa only [hformV] using H ε
    have hm := DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      omegaV (sub_pos.mpr hδeps) (H δ) hε (fun y => hle y.1)
    simpa only [hformV] using hm
  refine ⟨H, hfinite, hinf, ?_⟩
  intro I F ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le
      (hinf.trans_le (iInf_le M (ε i)))
  · intro b hb
    obtain ⟨e, he⟩ := iInf_lt_iff.mp (hinf.symm.trans_lt hb)
    filter_upwards [hε.eventually (gt_mem_nhds e.2)] with i hi
    exact (hmono hi.le).trans_lt he

end
end SGPT.Foundations.Analysis.Pending.ActualMinimalRestrictedMassFormula
