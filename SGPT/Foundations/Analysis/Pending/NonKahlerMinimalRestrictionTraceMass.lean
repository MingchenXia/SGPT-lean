import SGPT.Foundations.Analysis.Pending.NonKahlerPointSmallGenericBackground
import SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryNormalizedTraceMass

set_option autoImplicit false

/-! # Actual ordinary-normalized minimal trace mass off the non-Kahler locus -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.NonKahlerMinimalRestrictionTraceMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass PositiveNormalizedTrace NumericalTraceMass MinimalPotentialPositiveTraceDomain
  MinimalPotentialOrdinaryNormalizedTraceMass NonKahlerPointSmallGenericBackground

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- A range point outside the actual corresponding non-Kahler locus
internally supplies the positive normalized reader and exact ordinary mass. -/
theorem exists_positive_ordinary_restriction_mass_eq_normalizedTraceMass_of_not_mem_nonKahlerLocus
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (σ : ClosedRealOneOneForm n M)
    (hx : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative σ)) :
    ∃ hd : HasPositiveTraceRepresentativeAlong omega omegaV hι σ (thetaPshSupremum σ.val),
      ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι σ).val
          (fun y => thetaPshSupremum σ.val (ι y)),
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι σ)
          (fun y => thetaPshSupremum σ.val (ι y)) hw =
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι σ)
          (normalizedTraceAlong omega omegaV hι σ (thetaPshSupremum σ.val) hd)
          (normalizedTraceAlong_models omega omegaV hι σ (thetaPshSupremum σ.val) hd).1.plurisubharmonic := by
  classical
  obtain ⟨δ, hδ, hbig, hgeneric⟩ :=
    exists_pos_big_sub_smul_generic_zero_of_not_mem_nonKahlerLocus omega σ ι hx
  let β := σ - δ • omega.form
  have hform : β + δ • omega.form = σ := by dsimp only [β]; abel
  have hd : HasPositiveTraceRepresentativeAlong omega omegaV hι σ (thetaPshSupremum σ.val) := by
    simpa only [hform] using hasPositiveTraceRepresentativeAlong_minimal_add_smul
      omega omegaV hι hpull β hbig hgeneric hδ
  have hmass : ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι σ).val
      (fun y => thetaPshSupremum σ.val (ι y)),
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι σ)
        (fun y => thetaPshSupremum σ.val (ι y)) hw =
        numericalTraceMass omega omegaV hι σ (thetaPshSupremum σ.val) := by
    simpa only [hform] using exists_ordinary_restriction_mass_eq_numericalTraceMass_minimal_add_smul
      omega omegaV hι hpull β hbig hgeneric hδ
  obtain ⟨hw, heq⟩ := hmass
  refine ⟨hd, hw, ?_⟩
  simpa only [numericalTraceMass, dif_pos hd] using heq

end
end SGPT.Foundations.Analysis.Pending.NonKahlerMinimalRestrictionTraceMass
