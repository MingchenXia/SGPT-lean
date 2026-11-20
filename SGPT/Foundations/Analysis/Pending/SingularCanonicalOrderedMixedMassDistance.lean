import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrder
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayOrderedDistance

set_option autoImplicit false

/-! # Exact actual canonical distance under pointwise and global P-order -/

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays
  SingularMinimalCanonicalRay SingularGlobalPOrder SingularGlobalPMaximum
  SingularMinimalGlobalPMassCriterion SingularCanonicalSingularityDistance
  SingularCanonicalSingularityOrder SingularCanonicalDistanceZeroPEquivalence
  SingularModelGeodesicRayOrderedDistance ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem finiteEnergy_canonicalRay (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsFiniteEnergyRayFromModel θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) (canonicalRay θ u) := by
  have hR := isBoundedRayFromModel_canonicalRay omega θ hbig hu
  exact ⟨⟨hR.1.1, fun t ht =>
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (hR.1.2 t ht.le)⟩, hR.2⟩

/-- Actual canonical ray order and the genuine radial-energy formula give
an equality of the defining extended distance, not only a gap comparison. -/
theorem singularityDistance_eq_mixedMass_sub_of_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hle : u ≤ v) :
    singularityDistance omega θ hbig u v =
      (((∑ j : Fin (n + 1),
        ((endpointMixedMass θ (thetaPshSupremum θ.val) v
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv j).toReal -
        (endpointMixedMass θ (thetaPshSupremum θ.val) u
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu j).toReal)) /
        (n + 1 : ℝ) : ℝ) : EReal) := by
  have horder := canonicalRay_le_of_moreSingularOn omega θ hbig hu hv
    (MoreSingularOn.of_le fun x _ => hle x)
  unfold singularityDistance
  rw [rayD1_eq_radialEnergy_sub_of_model_origin omega
    (finiteEnergy_canonicalRay omega θ hbig hu)
    (finiteEnergy_canonicalRay omega θ hbig hv) (fun t _ => horder t),
    radialEnergy_canonicalRay_eq_mixed_mass_deficit omega θ hbig hv,
    radialEnergy_canonicalRay_eq_mixed_mass_deficit omega θ hbig hu, ← EReal.coe_sub]
  congr 1
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem singularityDistance_eq_of_right_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u v w : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hw : IsThetaPshPotential θ.val w)
    (hzero : singularityDistance omega θ hbig v w = 0) :
    singularityDistance omega θ hbig u v = singularityDistance omega θ hbig u w := by
  let := singularityPseudoMetricSpace omega θ hbig
  let U : ThetaPshL1 θ.val := ⟨u, hu⟩
  let V : ThetaPshL1 θ.val := ⟨v, hv⟩
  let W : ThetaPshL1 θ.val := ⟨w, hw⟩
  have hvw : dist V W = 0 := by
    rw [dist_eq_singularityDistance_toReal omega θ hbig]
    exact hzero ▸ EReal.toReal_zero
  have hwv : dist W V = 0 := by rw [dist_comm, hvw]
  have heq : dist U V = dist U W := by
    apply le_antisymm
    · have h := dist_triangle U W V
      rwa [hwv, add_zero] at h
    · have h := dist_triangle U V W
      rwa [hvw, add_zero] at h
  have hreal : (singularityDistance omega θ hbig u v).toReal =
      (singularityDistance omega θ hbig u w).toReal := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig] using heq
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig hu hv
  obtain ⟨k, _, _, _, hk⟩ := exists_tendsto_singularityDistance omega θ hbig hu hw
  have hmk : m = k := by simpa only [hm, hk, EReal.toReal_coe] using hreal
  exact hm.trans ((congrArg (fun x : ℝ => (x : EReal)) hmk).trans hk.symm)

/-- The actual global source order gives a maximum in the same P-class as
the right input. Produced zero distance, actual native triangle inequalities
and actual endpoint masses internally give the exact original formula. -/
theorem singularityDistance_eq_mixedMass_sub_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (huv : SourcePOrder (n := n) u v) :
    singularityDistance omega θ hbig u v =
      (((∑ j : Fin (n + 1),
        ((endpointMixedMass θ (thetaPshSupremum θ.val) v
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv j).toReal -
        (endpointMixedMass θ (thetaPshSupremum θ.val) u
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu j).toReal)) /
        (n + 1 : ℝ) : ℝ) : EReal) := by
  have hw := IsThetaPshPotential.max hu hv
  have hwv := (sourcePOrder_iff_sourcePEquivalent_max omega hu hv).mp huv
  have hzero := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig hv hw).mpr
    ⟨hwv.2, hwv.1⟩
  rw [singularityDistance_eq_of_right_zero omega θ hbig hu hv hw hzero,
    singularityDistance_eq_mixedMass_sub_of_le omega θ hbig hu hw (fun x => le_max_left _ _)]
  have hmass := (sourcePEquivalent_iff_minimal_endpointMixedMass_eq omega θ hbig
    hw hv hwv.1).mp hwv
  simp_rw [hmass]

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
