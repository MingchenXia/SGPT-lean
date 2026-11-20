import SGPT.Foundations.Analysis.Pending.DivisorialDomination

set_option autoImplicit false

/-! # A genuine strict-current potential below an original positive-mass potential -/

namespace SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass DivisorialDomination ThetaPshConvexCombination ConvexCombEnvelopeMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual class current and the actual affine-obstacle barrier produce
a pointwise lower potential with a strictly positive Kahler margin. -/
theorem exists_strict_thetaPsh_potential_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s : M → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val s ∧ s ≤ u := by
  obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ :=
    exists_isThetaPshPotential_sub_smul_of_isBigClass omega θ hbig
  have hu₀θ : IsThetaPshPotential θ.val u₀ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ₀.le)
    rwa [sub_add_cancel] at h
  let v : M → EReal := fun x => max (u x) (u₀ x)
  have hv : IsThetaPshPotential θ.val v := IsThetaPshPotential.max hu hu₀θ
  have huv : u ≤ v := fun x => le_max_left _ _
  have hmuv := diagonalPotentialMass_mono_of_kahler omega hu hv
    (MoreSingularOn.of_le fun x _ => huv x)
  have hmvfinite : diagonalPotentialMass θ v hv ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hv.1)).ne
  obtain ⟨a, ha, hsmall⟩ := exists_one_lt_ofReal_pow_sub_one_mul_lt hmvfinite hpos n
  have hadm := isAdmissibleWeight_of_le ha hmvfinite le_rfl hmuv le_rfl hsmall
  obtain ⟨w, hw, hbar⟩ :=
    PositiveCurrentRooftop.exists_thetaPsh_convexCombBarrier_of_isBigClass
      omega θ hbig hu hv huv hpos hadm
  have ha0 : 0 < a⁻¹ := inv_pos.mpr (zero_lt_one.trans ha)
  have ha1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  refine ⟨(1 - a⁻¹) * δ₀, mul_pos (by linarith) hδ₀,
    convexComb a⁻¹ w u₀, ?_, ?_⟩
  · have hw0 : IsThetaPshPotential (θ - (0 : ℝ) • omega.form).val w := by
      simpa only [zero_smul, sub_zero] using hw
    have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul
      omega ha0 ha1 hw0 hu₀
    simpa only [mul_zero, zero_add] using h
  · exact (convexComb_mono ha0.le ha1.le le_rfl
      fun x => le_max_right (u x) (u₀ x)).trans hbar

end

end SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow
