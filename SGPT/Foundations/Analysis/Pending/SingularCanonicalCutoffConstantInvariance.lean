import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRayEnergy
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

set_option autoImplicit false

/-! # Genuine cutoff-ray order and constant invariance from actual mass and separation -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffConstantInvariance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularModelNormalizedMixedCutoff
  SingularCanonicalCutoffStages SingularCanonicalCutoffSlices SingularCanonicalCutoffRay
  SingularCanonicalCutoffRayEnergy GlobalNonPluripolar FirstPass.GlobalPotentialTransforms

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem cutoffStage_mono_input {θ : ClosedRealOneOneForm n M}
    {φ u v : M → EReal} (huv : u ≤ v) {C s : ℝ}
    (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    cutoffStage θ φ u C s ≤ cutoffStage θ φ v C s := by
  by_cases h0 : s = 0
  · simp only [h0, cutoffStage_zero, le_refl]
  by_cases h1 : s = C
  · rw [h1, cutoffStage_terminal θ φ u hC, cutoffStage_terminal θ φ v hC]
    exact fun x => max_le_max (huv x) le_rfl
  have hr : s / C ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (lt_of_le_of_ne hs.1 (Ne.symm h0)) hC,
      (div_lt_one hC).mpr (lt_of_le_of_ne hs.2 h1)⟩
  rw [cutoffStage, cutoffStage, closedSubgeodesicSlice_eq_curve hr,
    closedSubgeodesicSlice_eq_curve hr]
  exact finiteGeodesic_mono le_rfl (fun x => max_le_max (huv x) le_rfl) (s / C)

/-- Genuine actual terminal maximum order, endpoint completion and Perron order internally give actual cutoff-slice order at every real time. -/
theorem cutoffSlice_mono_input {θ : ClosedRealOneOneForm n M}
    {φ u v : M → EReal} (huv : u ≤ v) (s : ℝ) :
    cutoffSlice θ φ u s ≤ cutoffSlice θ φ v s := by
  apply uscRegularization_mono
  apply iSup_mono
  intro C
  exact cutoffStage_mono_input huv (lt_of_le_of_lt (le_max_right s 0) C.property)
    ⟨le_max_right s 0, C.property.le⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}

omit [ConnectedSpace M] in
/-- Genuine slotwise canonical measure constant invariance internally identifies the actual endpoint mixed masses, including the empty tuple. -/
theorem endpointMixedMass_sub_const (hp : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (c : ℝ) (j : Fin (n + 1)) :
    endpointMixedMass θ φ (fun x => u x - (c : EReal)) hp (hu.sub_const c) j =
      endpointMixedMass θ φ u hp hu j := by
  classical
  let cs : Fin n → ℝ := fun i => if i.val < j.val then c else 0
  have htuple : endpointMixedPotential j (fun x => u x - (c : EReal)) φ =
      fun i x => endpointMixedPotential j u φ i x - (cs i : EReal) := by
    funext i x
    by_cases hi : i.val < j.val
    · simp only [endpointMixedPotential, hi, if_true, cs]
    · simp only [endpointMixedPotential, hi, if_false, cs, EReal.coe_zero, sub_zero]
  have hpots := endpointMixedPotential_thetaPlurisubharmonic θ j u φ hu hp
  have hshift := GlobalMeasureInvariance.globalMixedMeasure_sub_const hpots cs
  unfold endpointMixedMass endpointMixedMeasure
  calc
    _ = globalMixedMeasure (fun _ : Fin n => θ)
        (fun i x => endpointMixedPotential j u φ i x - (cs i : EReal))
        (fun i => thetaPlurisubharmonic_sub_const (hpots i) (cs i)) univ := by
      exact congrArg (fun μ => μ univ)
        (AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples rfl htuple _ _)
    _ = _ := congrArg (fun μ => μ univ) hshift

/-- Genuine canonical mixed-measure constant invariance gives equal produced radial energies; actual ray energy linearity, input order and true E1 Darvas separation then produce equality of the actual cutoff-ray functions. -/
theorem cutoffSlice_sub_const_eq (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    (c : ℝ) (hsubp : (fun x => u x - (c : EReal)) ≤ φ) :
    cutoffSlice θ φ (fun x => u x - (c : EReal)) = cutoffSlice θ φ u := by
  let v : M → EReal := fun x => u x - (c : EReal)
  have hv : IsThetaPshPotential θ.val v := hu.sub_const c
  have hmass : RelativeGeodesicRays.radialEnergy θ φ hφ (cutoffSlice θ φ v) =
      RelativeGeodesicRays.radialEnergy θ φ hφ (cutoffSlice θ φ u) := by
    rw [radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega hφ hv hsubp,
      radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega hφ hu hup]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    rw [endpointMixedMass_sub_const hφ.plurisubharmonic hu c j]
  have hRu := isBoundedRayFromModel_cutoffSlice omega hφ hu hup
  have hRv := isBoundedRayFromModel_cutoffSlice omega hφ hv hsubp
  have hfu : IsFiniteEnergyRayFromModel θ φ hφ (cutoffSlice θ φ u) :=
    ⟨⟨hRu.1.1, fun t ht =>
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hRu.1.2 t ht.le)⟩, hRu.2⟩
  have hfv : IsFiniteEnergyRayFromModel θ φ hφ (cutoffSlice θ φ v) :=
    ⟨⟨hRv.1.1, fun t ht =>
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hRv.1.2 t ht.le)⟩, hRv.2⟩
  funext s
  by_cases hs : 0 ≤ s
  · have he : (energy θ φ hφ (cutoffSlice θ φ v s)).toReal =
        (energy θ φ hφ (cutoffSlice θ φ u s)).toReal := by
      rw [SingularModelOriginRayEnergy.energy_ray_eq_mul_radialEnergy omega hfv hs,
        SingularModelOriginRayEnergy.energy_ray_eq_mul_radialEnergy omega hfu hs, hmass]
    have heu : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ u s) hφ :=
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hRu.1.2 s hs)
    have hev : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ v s) hφ :=
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hRv.1.2 s hs)
    by_cases hc : 0 ≤ c
    · have hle : v ≤ u := by
        intro x
        calc
          v x = u x + ((-c : ℝ) : EReal) := by
            change u x - (c : EReal) = _
            rw [sub_eq_add_neg, EReal.coe_neg]
          _ ≤ u x + 0 := add_le_add le_rfl (EReal.coe_nonpos.mpr (neg_nonpos.mpr hc))
          _ = u x := add_zero _
      apply SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq omega hev heu
      rw [relativeD1_eq_sub_of_le hev.1.plurisubharmonic (cutoffSlice_mono_input hle s),
        he, sub_self]
    · have hle : u ≤ v := by
        intro x
        calc
          u x = u x + 0 := (add_zero _).symm
          _ ≤ u x + ((-c : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_nonneg.mpr (by linarith))
          _ = v x := by
            change _ = u x - (c : EReal)
            rw [EReal.coe_neg, sub_eq_add_neg]
      symm
      apply SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq omega heu hev
      rw [relativeD1_eq_sub_of_le heu.1.plurisubharmonic (cutoffSlice_mono_input hle s),
        he, sub_self]
  · have hz : max s 0 = 0 := max_eq_right (le_of_not_ge hs)
    let : Nonempty {C : ℝ // max s 0 < C} := ⟨⟨max s 0 + 1, by linarith⟩⟩
    have hzero (w : M → EReal) : cutoffSlice θ φ w s = φ := by
      simp only [cutoffSlice, hz, cutoffStage_zero, iSup_const]
      exact uscRegularization_eq hφ.plurisubharmonic.quasiPshPotential.1.upperSemicontinuous
    change cutoffSlice θ φ v s = cutoffSlice θ φ u s
    exact (hzero v).trans (hzero u).symm


end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffConstantInvariance
