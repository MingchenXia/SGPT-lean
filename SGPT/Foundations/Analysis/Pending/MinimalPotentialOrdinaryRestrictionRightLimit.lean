import SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryNormalizedTraceMass
import SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceRightLimit
import SGPT.Foundations.Analysis.Pending.NonNefLocusLelong

set_option autoImplicit false

/-! # Actual ordinary minimal restriction mass tends to the original numerical trace -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionRightLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  NumericalTraceMass MinimalPotentialOrdinaryNormalizedTraceMass
  MinimalPotentialNumericalTraceRightLimit

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Natural non-nef-locus geometry supplies every ordinary restricted stage
and its actual mass limit, with the original undefined-trace zero convention. -/
theorem exists_tendsto_ordinary_minimal_restriction_mass_of_not_mem_nonNefLocus
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hx : ∃ y : V, ι y ∉ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    ∃ hW : ∀ (e : ℝ), 0 < e →
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      ∀ (I : Type*) (F : Filter I) (r : I → ℝ) (hr : ∀ i, 0 < r i),
        Tendsto r F (𝓝 0) →
          Tendsto (fun i => diagonalPotentialMass
            (ClosedRealOneOneForm.pullback hι (θ + r i • omega.form))
            (fun y => thetaPshSupremum (θ + r i • omega.form).val (ι y)) (hW (r i) (hr i))) F
            (𝓝 (numericalTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
  classical
  obtain ⟨y, hy⟩ := hx
  rw [NonNefLocusLelong.nonNefLocus_eq_setOf_lelongNumber_pos omega θ hbig] at hy
  simp only [mem_ofPred_eq] at hy
  have hpoint : lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hy)
  have hgeneric : (⨅ z : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι z)) = 0 :=
    le_antisymm (iInf_le_of_le y hpoint.le) zero_le
  have hex (e : ℝ) (he : 0 < e) :
      ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
          (fun z => thetaPshSupremum (θ + e • omega.form).val (ι z)),
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
          (fun z => thetaPshSupremum (θ + e • omega.form).val (ι z)) hw =
          numericalTraceMass omega omegaV hι (θ + e • omega.form)
            (thetaPshSupremum (θ + e • omega.form).val) :=
    exists_ordinary_restriction_mass_eq_numericalTraceMass_minimal_add_smul
      omega omegaV hι hpull θ hbig hgeneric he
  choose hW hmass using hex
  have hnum := tendsto_numericalTraceMass_minimal_add_smul_right
    omega omegaV hι hpull θ hbig hgeneric
  refine ⟨hW, fun I F r hr hrlim => ?_⟩
  have hpath : Tendsto r F (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim, Eventually.of_forall hr⟩
  exact (hnum.comp hpath).congr (fun i => (hmass (r i) (hr i)).symm)

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionRightLimit
