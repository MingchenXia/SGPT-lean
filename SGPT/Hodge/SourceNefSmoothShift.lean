import SGPT.Hodge.SourceModifiedModelNef

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft
open scoped Topology ENNReal

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- Semipositive smooth addition preserves the original net-defined nef cone;
the output follows from genuine all-model modified-nef witnesses. -/
theorem isNef_add_root_semipositive (ω : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m)) (hD : D.IsNef)
    (σ : ClosedRealOneOneForm (m + 1) X) (hσ : σ.val.IsSemipositive) :
    (D + rootCartier (RealBottChern.ofRepresentative σ)).IsNef := by
  apply isNef_of_allModelModifiedNef ω _
  exact allModelModifiedNef_add_semipositive ω D
    (fun π κ => (WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ω⟩ hD π).2 κ) σ hσ

/-- The actual conditional-infimum volume increases under semipositive smooth
addition to a nef family. -/
theorem vol_le_add_root_semipositive (ω : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m)) (hD : D.IsNef)
    (σ : ClosedRealOneOneForm (m + 1) X) (hσ : σ.val.IsSemipositive) :
    D.vol ≤ (D + rootCartier (RealBottChern.ofRepresentative σ)).vol := by
  have hmn : ∀ (π : (ModelSystem.blowup (m + 1) X).Model)
      (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ (D.onModel π) :=
    fun π κ => (WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ω⟩ hD π).2 κ
  have hmn' := allModelModifiedNef_add_semipositive ω D hmn σ hσ
  have hp : D.IsPseudoeffective := by
    rw [WeilBDivisorOn.isPseudoeffective_iff]
    intro π
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    exact classPseudoeffective_of_modifiedNef κ (hmn π κ)
  have hp' : (D + rootCartier (RealBottChern.ofRepresentative σ)).IsPseudoeffective := by
    rw [WeilBDivisorOn.isPseudoeffective_iff]
    intro π
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    exact classPseudoeffective_of_modifiedNef κ (hmn' π κ)
  rw [WeilBDivisorOn.vol_of_isPseudoeffective hp,
    WeilBDivisorOn.vol_of_isPseudoeffective hp']
  apply iInf_mono
  intro π
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  have : BorelSpace π.1.carrier := ⟨rfl⟩
  obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
  rw [WeilBDivisorOn.add_onModel, rootCartier_onModel, classPullback_ofRepresentative]
  exact SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_le_add_semipositive κ _ _
    (ClosedRealOneOneForm.pullback_isSemipositive π.1.contMDiff_map hσ)

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft

open scoped ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

/-- Genuine all-dimensional nefness after arbitrary semipositive smooth addition. -/
theorem isNefAny_add_root_semipositive (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D)
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    IsNefAny (D + rootCartierAny (RealBottChern.ofRepresentative σ)) := by
  cases n with
  | zero => exact isNefAny_zero _
  | succ m =>
    rw [isNefAny_iff_existing (Nat.succ_pos m)]
    have hD' := (isNefAny_iff_existing (Nat.succ_pos m) D).mp hD
    have h := isNef_add_root_semipositive ω (toExisting _ (Nat.succ_pos m) D) hD' σ hσ
    exact h

/-- The original all-dimensional family volume is monotone under this actual shift. -/
theorem volumeAny_le_add_root_semipositive (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D)
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    volumeAny D ≤ volumeAny (D + rootCartierAny (RealBottChern.ofRepresentative σ)) := by
  cases n with
  | zero => simp only [volumeAny_eq_one_of_dim_zero, le_refl]
  | succ m =>
    rw [volumeAny_eq_existing (Nat.succ_pos m), volumeAny_eq_existing (Nat.succ_pos m)]
    exact vol_le_add_root_semipositive ω (toExisting _ (Nat.succ_pos m) D)
      ((isNefAny_iff_existing (Nat.succ_pos m) D).mp hD) σ hσ

/-- Every nef family becomes genuinely big after adding any actual Kähler root form. -/
theorem volumeAny_pos_add_rootKahler (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D)
    (κ : KahlerBackground n X) :
    0 < volumeAny (D + rootCartierAny (RealBottChern.ofRepresentative κ.form)) := by
  cases n with
  | zero => simpa only [volumeAny_eq_one_of_dim_zero] using (zero_lt_one : (0 : ℝ≥0∞) < 1)
  | succ m =>
    rw [volumeAny_eq_existing (Nat.succ_pos m)]
    exact isBig_add_rootKahler_of_allModelModifiedNef ω (toExisting _ (Nat.succ_pos m) D)
      (fun π κπ => (WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ω⟩
        ((isNefAny_iff_existing (Nat.succ_pos m) D).mp hD) π).2 κπ) κ

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
