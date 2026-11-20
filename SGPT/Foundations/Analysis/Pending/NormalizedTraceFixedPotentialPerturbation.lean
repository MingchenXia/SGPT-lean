import SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
import SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain

set_option autoImplicit false

/-! # Actual fixed-potential numerical trace perturbation, including undefined zero -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialPerturbation

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  TraceRepresentativeConstruction DiagonalMass PositiveNormalizedTrace NumericalTraceMass
  NormalizedTraceBackgroundMonotonicity IEnvelopeVaryingBackgroundModelInfimum
  VaryingBackgroundIModelGlobalClass SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]


/-- Every positive perturbed domain is produced internally; the original
positive-infimum and actual undefined-zero branches give one true numerical limit. -/
theorem tendsto_numericalTraceMass_add_smul_of_antitone
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => numericalTraceMass omega omegaV hι (θ + ε j • omega.form) u)
      atTop (𝓝 (numericalTraceMass omega omegaV hι θ u)) := by
  classical
  let κ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let η : ClosedRealOneOneForm k V := ClosedRealOneOneForm.pullback hι θ
  have hdefined (j : ℕ) : HasPositiveTraceRepresentativeAlong
      omega omegaV hι (θ + ε j • omega.form) u := by
    apply PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin
      omega omegaV hι hpull (hεpos j)
    · simpa only [add_sub_cancel_right] using hu
    · exact hgeneric
  let v : ℕ → V → EReal := fun j =>
    normalizedTraceAlong omega omegaV hι (θ + ε j • omega.form) u (hdefined j)
  have hform (j : ℕ) : ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
      η + ε j • κ.form := NefCoreKahlerCurrent.pullback_add_smul hι θ omega.form (ε j)
  have hv (j : ℕ) : IsModelPotential (η + ε j • κ.form) (v j) := by
    simpa only [hform j] using
      (normalizedTraceAlong_models omega omegaV hι (θ + ε j • omega.form) u (hdefined j)).1
  have hI (j : ℕ) : IsIModelPotential (η + ε j • κ.form).val (v j) := by
    simpa only [hform j] using
      (normalizedTraceAlong_models omega omegaV hι (θ + ε j • omega.form) u (hdefined j)).2
  have hT (j : ℕ) : IsTraceRepresentativeAlong omega omegaV hι u (v j) :=
    isTraceRepresentativeAlong_normalizedTraceAlong omega omegaV hι
      (θ + ε j • omega.form) u (hdefined j)
  have heq (j : ℕ) : SourcePEquivalent (n := k) (v j) (v 0) :=
    TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      omegaV omegaV hι (hT j) (hT 0)
  have hanti : Antitone v := by
    intro i j hij
    have hd : 0 ≤ ε i - ε j := sub_nonneg.mpr (hεanti hij)
    have hdiff : θ + ε i • omega.form - (θ + ε j • omega.form) =
        (ε i - ε j) • omega.form := by module
    have hsemi : (θ + ε i • omega.form - (θ + ε j • omega.form)).val.IsSemipositive := by
      rw [hdiff]
      exact KahlerDomination.isSemipositive_smul omega.isSemipositive hd
    exact normalizedTraceAlong_le_of_semipositive_difference omega omega omegaV omegaV
      hι (θ + ε j • omega.form) (θ + ε i • omega.form) u hsemi (hdefined j) (hdefined i)
  let U : V → EReal := ⨅ j, v j
  have hU : IsThetaPshPotential η.val U :=
    isThetaPshPotential_iInf_varying_models κ η hεanti hεlim hv hanti
  let L : ENNReal := diagonalPotentialMass η U hU
  have hm : Tendsto (fun j => diagonalPotentialMass (η + ε j • κ.form)
      (v j) (hv j).plurisubharmonic) atTop (𝓝 L) :=
    tendsto_diagonalPotentialMass_iInf_varying_models κ η hεpos hεanti hεlim hv hanti
  have hnum (j : ℕ) : numericalTraceMass omega omegaV hι (θ + ε j • omega.form) u =
      diagonalPotentialMass (η + ε j • κ.form) (v j) (hv j).plurisubharmonic := by
    simp only [numericalTraceMass, dif_pos (hdefined j), hform j]
    rfl
  have horiginal : numericalTraceMass omega omegaV hι θ u = L := by
    by_cases hpos : 0 < L
    · have hclass : SourcePEquivalent (n := k) U (v 0) :=
        sourcePEquivalent_iInf_of_varying_iModels κ η hεpos hεanti hεlim hv hI hanti hpos heq
      have hTU : IsTraceRepresentativeAlong omega omegaV hι u U :=
        TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
          omegaV hι (hT 0) hclass.symm
      have hd : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := ⟨U, hTU, hU, hpos⟩
      exact numericalTraceMass_eq_of_positive_reader omegaV omegaV hι θ u hd hTU hU hpos
    · have hzero : L = 0 := le_antisymm (not_lt.mp hpos) zero_le
      have hundefined : ¬ HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
        intro hd
        let A := normalizedTraceAlong omega omegaV hι θ u hd
        have hA : IsModelPotential η A := (normalizedTraceAlong_models omega omegaV hι θ u hd).1
        have hAU : A ≤ U := by
          apply le_iInf
          intro j
          have hdiff : θ + ε j • omega.form - θ = ε j • omega.form := by module
          have hsemi : (θ + ε j • omega.form - θ).val.IsSemipositive := by
            rw [hdiff]
            exact KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos j).le
          exact normalizedTraceAlong_le_of_semipositive_difference omega omega omegaV omegaV
            hι θ (θ + ε j • omega.form) u hsemi hd (hdefined j)
        have hmass : diagonalPotentialMass η A hA.plurisubharmonic ≤ L :=
          diagonalPotentialMass_mono_of_kahler omegaV hA.plurisubharmonic hU
            (MoreSingularOn.of_le fun x _ => hAU x)
        exact (hA.positive_mass.trans_le hmass).ne' hzero
      exact (numericalTraceMass_eq_zero_of_undefined omega omegaV hι θ u hundefined).trans hzero.symm
  rw [horiginal]
  exact hm.congr (fun j => (hnum j).symm)

end
end SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialPerturbation
