import SGPT.Foundations.Analysis.Pending.SingularMinimalGlobalPMassCriterion
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # Zero actual canonical distance and the source global P-equivalence -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  SingularMinimalCanonicalRay SingularMinimalGlobalPMassCriterion SingularGlobalPOrder
  SingularGlobalPMaximum SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison ActualMixedMassJoinGap

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual constant-sequence mixed-mass criterion and produced global
P-classification identify distance-zero inputs; the reverse direction
internally makes the actual maximum mass gap zero. -/
theorem singularityDistance_eq_zero_iff_sourcePEquivalent
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) :
    singularityDistance omega θ hbig u v = 0 ↔ SourcePEquivalent (n := n) u v := by
  let p := thetaPshSupremum θ.val
  have hp : IsThetaPshPotential θ.val p :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hw : IsThetaPshPotential θ.val (fun x => max (u x) (v x)) :=
    IsThetaPshPotential.max hu hv
  have hfinite {q : M → EReal} (hq : IsThetaPshPotential θ.val q)
      (j : Fin (n + 1)) : endpointMixedMass θ p q hp hq j ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ j q p hq hp)).ne
  constructor
  · intro hzero
    have hD : Tendsto (fun _ : ℕ => (singularityDistance omega θ hbig u v).toReal)
        atTop (𝓝 0) := by
      rw [hzero, EReal.toReal_zero]
      exact tendsto_const_nhds
    have hm := (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig
      (atTop : Filter ℕ) (fun _ => hu) hv).mp hD
    have hmu (j : Fin (n + 1)) : endpointMixedMass θ p u hp hu j =
        endpointMixedMass θ p v hp hv j :=
      (ENNReal.toReal_eq_toReal_iff' (hfinite hu j) (hfinite hv j)).mp
        (tendsto_nhds_unique tendsto_const_nhds (hm j).1)
    have hmw (j : Fin (n + 1)) :
        endpointMixedMass θ p (fun x => max (u x) (v x)) hp hw j =
          endpointMixedMass θ p v hp hv j :=
      (ENNReal.toReal_eq_toReal_iff' (hfinite hw j) (hfinite hv j)).mp
        (tendsto_nhds_unique tendsto_const_nhds (hm j).2)
    have hUW := sourcePOrder_of_moreSingularOn omega θ θ hu hw
      (MoreSingularOn.of_le fun x _ => le_max_left _ _)
    have hVW := sourcePOrder_of_moreSingularOn omega θ θ hv hw
      (MoreSingularOn.of_le fun x _ => le_max_right _ _)
    have hUeqW := (sourcePEquivalent_iff_minimal_endpointMixedMass_eq omega θ hbig
      hu hw hUW).mpr (fun j => (hmu j).trans (hmw j).symm)
    have hVeqW := (sourcePEquivalent_iff_minimal_endpointMixedMass_eq omega θ hbig
      hv hw hVW).mpr (fun j => (hmw j).symm)
    exact ⟨hUeqW.1.trans omega hVeqW.2, hVeqW.1.trans omega hUeqW.2⟩
  · intro hUV
    have hWV := (sourcePOrder_iff_sourcePEquivalent_max omega hu hv).mp hUV.1
    have hUmass := (sourcePEquivalent_iff_minimal_endpointMixedMass_eq omega θ hbig
      hu hv hUV.1).mp hUV
    have hWmass := (sourcePEquivalent_iff_minimal_endpointMixedMass_eq omega θ hbig
      hw hv hWV.1).mp hWV
    have hJ : mixedMassJoinGap hp hu hv = 0 := by
      unfold mixedMassJoinGap
      dsimp only [p] at hp ⊢
      simp_rw [hWmass, hUmass]
      have hterm (m : ℝ) : 2 * m - m - m = 0 := by ring
      simp only [hterm, Finset.sum_const_zero, zero_div]
    have hupper := (singularityDistance_le_mixedMassJoinGap_le omega θ hbig hu hv).1
    change singularityDistance omega θ hbig u v ≤ (mixedMassJoinGap hp hu hv : EReal)
      at hupper
    rw [hJ, EReal.coe_zero] at hupper
    obtain ⟨m, hm, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hbig hu hv
    exact le_antisymm hupper (he.symm ▸ EReal.coe_nonneg.mpr hm)

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
