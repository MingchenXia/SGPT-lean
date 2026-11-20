import SGPT.PSH.SourceGeneralMixedIVolumePerturbation
import SGPT.PSH.SourceCurrentMixedIVolume
import SGPT.Okounkov.ThetaPotentialCurrentCombinations

/-!
# Class-uniform Kähler perturbation for the original full currents

The SAME constant is selected from the intrinsic current classes before all
currents and all genuine representations. Natural properties of the literal
perturbed currents are manufactured. The native degree-two current interface
has dimension m+1; the represented producer retains the genuine n=0 branch.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open scoped Topology ENNReal Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction CurrentBottChernClass GlobalCurrentPotentials
open LelongPoincareDivisor
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem zeroCurrent (σ : ClosedRealOneOneForm (m + 1) M)
    (hu : IsThetaPshPotential σ.val (fun _ => 0)) :
    thetaPotentialCurrent σ.val (fun _ => 0) hu =
      (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) σ).val := by
  have hz : globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) (fun _ => 0)
      hu.quasiPshPotential = 0 := by
    apply globalCurrent_ext (canonicalBasis (m + 1))
    intro e
    rw [globalDDC_coefficients, GlobalCurrent.coefficients_zero]
    have hreg : regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction (fun _ : M => (0 : EReal)) e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
          (Nat.succ_pos m) (fun _ => 0) hu.quasiPshPotential e) = 0 := by
      ext φ
      simp [regularDistribution_apply, chartFunction]
    change ddC _ = 0
    rw [hreg]
    ext v : 1
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, ddC_apply]
    simp
  rw [thetaPotentialCurrent, hz, add_zero]
  rfl

private theorem perturbedThetaCurrent (ω : KahlerBackground (m + 1) M)
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {t : ℝ} (ht : 0 ≤ t) :
    ∃ htu : IsThetaPshPotential (θ + t • ω.form).val u,
      thetaPotentialCurrent (θ + t • ω.form).val u htu =
        thetaPotentialCurrent θ.val u hu +
          (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) (t • ω.form)).val := by
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff (t • ω.form)).mpr
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ht)
  obtain ⟨hsum, hread⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hzero
  have hp : (fun x => u x + (0 : EReal)) = u := by funext x; simp
  have htu : IsThetaPshPotential (θ + t • ω.form).val u := by simpa only [hp] using hsum
  refine ⟨htu, ?_⟩
  simpa only [hp, zeroCurrent (t • ω.form) hzero] using hread

/-- The literal original current tuple Tᵢ plus the standard current induced
by the actual smooth form tω. This definition makes sense for every real t. -/
def sourceCurrentKahlerPerturbation (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (t : ℝ) :
    Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  fun i => T i + (smoothClosedCurrent (canonicalBasis (m + 1))
    (Nat.succ_pos m) (t • ω.form)).val

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem nativeToSource {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    (ofFixedModel (m + 1) M).IsThetaPSH (nativeClosedFormToAtlas θ) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hu

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- All natural current-domain properties are OUTPUTS from the original
currents and t≥0. No property of the desired sum is an incoming certificate. -/
theorem sourceCurrentKahlerPerturbation_closed_type_positive (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, (sourceCurrentKahlerPerturbation ω T t i).IsClosed (canonicalBasis (m + 1)) ∧
      (sourceCurrentKahlerPerturbation ω T t i).IsTypeOneOne
        (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
      IsFullPositive (sourceCurrentKahlerPerturbation ω T t i) := by
  intro i
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  obtain ⟨htu, htuRead⟩ := perturbedThetaCurrent ω hu ht
  have he : sourceCurrentKahlerPerturbation ω T t i =
      thetaPotentialCurrent (θ + t • ω.form).val u htu := by
    change T i + _ = _
    rw [hread]
    exact htuRead.symm
  rw [he]
  exact thetaPotentialCurrent_closed_type_positive _ u htu

/-- Actual mixed volume of the literal perturbed original currents; all
closed/type/full-positive domain proofs are internally manufactured. -/
def sourceCurrentMixedIVolumeKahlerPerturbed (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) (t : ℝ) (ht : 0 ≤ t) : ENNReal :=
  sourceCurrentMixedIVolume ω (sourceCurrentKahlerPerturbation ω T t)
    (fun i => (sourceCurrentKahlerPerturbation_closed_type_positive ω T hc h11 hp ht i).1)
    (fun i => (sourceCurrentKahlerPerturbation_closed_type_positive ω T hc h11 hp ht i).2.1)
    (fun i => (sourceCurrentKahlerPerturbation_closed_type_positive ω T hc h11 hp ht i).2.2)

/-- EVERY genuine original representation reads the independent original
perturbed-current value as the actual represented general perturbed value. -/
theorem sourceCurrentMixedIVolumeKahlerPerturbed_eq_representation
    (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i))
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hread : ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i))
    (t : ℝ) (ht : 0 ≤ t) :
    sourceCurrentMixedIVolumeKahlerPerturbed ω T hc h11 hp t ht =
      sourceGeneralMixedIVolumeKahlerPerturbed ω (fun i => nativeClosedFormToAtlas (θ i))
        u (fun i => nativeToSource (hu i)) t ht := by
  choose htu htuRead using fun i => perturbedThetaCurrent ω (hu i) ht
  have hreadS i : sourceCurrentKahlerPerturbation ω T t i =
      thetaPotentialCurrent (θ i + t • ω.form).val (u i) (htu i) := by
    change T i + _ = _
    rw [hread i]
    exact (htuRead i).symm
  unfold sourceCurrentMixedIVolumeKahlerPerturbed
  rw [sourceCurrentMixedIVolume_eq_representation ω _ _ _ _
    (fun i => θ i + t • ω.form) u htu hreadS]
  change sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (θ i + t • ω.form)) u _ =
    sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas
      (atlasClosedFormToNative (nativeClosedFormToAtlas (θ i)) + t • ω.form)) u _
  simp only [sourceNativeAtlasForm_roundTrip]

/-- Original lma:perturbvol for arbitrary original full positive currents.
The constant is selected using their ACTUAL intrinsic classes before all
currents, all produced representations and every real parameter in [0,1]. -/
theorem sourceCurrentMixedIVolume_class_uniform_perturbation_bound
    (ω : KahlerBackground (m + 1) M) (α : Fin (m + 1) → RealBottChern (m + 1) M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
        (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
        (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
        (hp : ∀ i, IsFullPositive (T i)),
        (∀ i, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (⟨T i, hc i, h11 i⟩ : ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)) = α i) →
        ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ 1 →
          0 ≤ (sourceCurrentMixedIVolumeKahlerPerturbed ω T hc h11 hp t ht).toReal -
            (sourceCurrentMixedIVolume ω T hc h11 hp).toReal ∧
          (sourceCurrentMixedIVolumeKahlerPerturbed ω T hc h11 hp t ht).toReal -
            (sourceCurrentMixedIVolume ω T hc h11 hp).toReal ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := sourceGeneralMixedIVolume_class_uniform_perturbation_bound ω α
  refine ⟨C, hC, ?_⟩
  intro T hc h11 hp hclass t ht ht1
  choose θ u hu hread hchart using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  have hθclass i : RealBottChern.ofRepresentative (θ i) = α i := by
    have hsub : (⟨T i, hc i, h11 i⟩ :
        ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
        ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (θ i) (u i) (hu i) :=
      Subtype.ext (hread i)
    have h := hclass i
    rw [hsub, ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent] at h
    exact h
  have h := hbound (fun i => nativeClosedFormToAtlas (θ i)) u
    (fun i => nativeToSource (hu i))
    (fun i => by simpa only [sourceNativeAtlasForm_roundTrip] using hθclass i) t ht ht1
  rw [sourceCurrentMixedIVolumeKahlerPerturbed_eq_representation ω T hc h11 hp θ u hu hread t ht,
    sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  exact h

end SGPT.PSH.VariableComplexAtlas
