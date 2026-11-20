import SGPT.Hodge.SourceRootCartier
import SGPT.Hodge.SourceModifiedNefShift

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
open scoped Topology ENNReal

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]

def rootCartier (α : RealBottChern (m + 1) X) :
    BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m) :=
  WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root α

omit [ConnectedSpace X] in
theorem rootCartier_onModel (α : RealBottChern (m + 1) X)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    (rootCartier α).onModel π = classPullback π.1.contMDiff_map α := by
  exact (WeilBDivisorOn.isRealization_cartierOf ModelSystem.Model.root α π
    (ModelSystem.Model.root_le π)).trans (Modification.classPullbackOfLE_root π.1 α)

omit [ConnectedSpace X] in
/-- Every model has the same original modified-nef epsilon witnesses after pulling
back a genuinely semipositive smooth root form. -/
theorem allModelModifiedNef_add_semipositive (_ω : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m))
    (hD : ∀ (π : (ModelSystem.blowup (m + 1) X).Model)
      (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ (D.onModel π))
    (σ : ClosedRealOneOneForm (m + 1) X) (hσ : σ.val.IsSemipositive) :
    ∀ (π : (ModelSystem.blowup (m + 1) X).Model)
      (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ
        ((D + rootCartier (RealBottChern.ofRepresentative σ)).onModel π) := by
  intro π κ
  rw [WeilBDivisorOn.add_onModel, rootCartier_onModel, classPullback_ofRepresentative]
  exact classModifiedNef_add_semipositive κ (hD π κ) _
    (ClosedRealOneOneForm.pullback_isSemipositive π.1.contMDiff_map hσ)

/-- Adding a Kähler root form gives a *uniform* positive lower bound on every
actual model volume, and hence on the actual conditional infimum. -/
theorem isBig_add_rootKahler_of_allModelModifiedNef (ω : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m))
    (hD : ∀ (π : (ModelSystem.blowup (m + 1) X).Model)
      (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ (D.onModel π))
    (κ : KahlerBackground (m + 1) X) :
    (D + rootCartier (RealBottChern.ofRepresentative κ.form)).IsBig := by
  let E := D + rootCartier (RealBottChern.ofRepresentative κ.form)
  have hmn := allModelModifiedNef_add_semipositive ω D hD κ.form κ.isSemipositive
  have hEp : E.IsPseudoeffective := by
    rw [WeilBDivisorOn.isPseudoeffective_iff]
    intro π
    obtain ⟨κπ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    exact classPseudoeffective_of_modifiedNef κπ (hmn π κπ)
  have h0 : IsThetaPshPotential κ.form.val (fun _ : X => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff _).mpr κ.isSemipositive
  have hlower : Modification.classVolume Modification.root
      (RealBottChern.ofRepresentative κ.form) ≤ E.vol := by
    rw [WeilBDivisorOn.vol_of_isPseudoeffective hEp]
    apply le_iInf
    intro π
    let : MeasurableSpace π.1.carrier := borel π.1.carrier
    have : BorelSpace π.1.carrier := ⟨rfl⟩
    obtain ⟨κπ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    have hDp := classPseudoeffective_of_modifiedNef κπ (hD π κπ)
    have hCp : ClassPseudoeffectiveViaPotentials
        (classPullback π.1.contMDiff_map (RealBottChern.ofRepresentative κ.form)) := by
      rw [classPullback_ofRepresentative]
      exact ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (ClosedRealOneOneForm.pullback_isSemipositive π.1.contMDiff_map κ.isSemipositive)⟩
    have hv := classVolume_classPullbackOfLE_blowup ⟨ω⟩
      (ModelSystem.Model.root_le π) κ.form h0
    change Modification.classVolume π.1
      (Modification.classPullbackOfLE (Modification.root_le π.1)
        (RealBottChern.ofRepresentative κ.form)) =
      Modification.classVolume Modification.root (RealBottChern.ofRepresentative κ.form) at hv
    have hv' : Modification.classVolume π.1
        (classPullback π.1.contMDiff_map (RealBottChern.ofRepresentative κ.form)) =
        Modification.classVolume Modification.root (RealBottChern.ofRepresentative κ.form) :=
      (congrArg (Modification.classVolume π.1)
        (Modification.classPullbackOfLE_root π.1 (RealBottChern.ofRepresentative κ.form))).symm.trans hv
    apply le_trans (le_of_eq hv'.symm)
    change sourceClassVolume (classPullback π.1.contMDiff_map
      (RealBottChern.ofRepresentative κ.form)) ≤
      sourceClassVolume (E.onModel π)
    dsimp only [E]
    rw [WeilBDivisorOn.add_onModel, rootCartier_onModel]
    exact (SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_le_add_of_pseudoeffective
      κπ hCp hDp).trans_eq (congrArg sourceClassVolume (add_comm _ _))
  have hpos : 0 < Modification.classVolume Modification.root
      (RealBottChern.ofRepresentative κ.form) := by
    let : MeasurableSpace X := borel X
    have : BorelSpace X := ⟨rfl⟩
    exact (SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass
      κ _).mpr (isBigClass_kahler κ)
  exact hpos.trans_le hlower

/-- Modified-nefness on every original book model forces nefness of the original
family, via actual positive realization of every epsilon Kähler shift and the
closed original net-defined nef cone. -/
theorem isNef_of_allModelModifiedNef (ω : KahlerBackground (m + 1) X)
    (D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m))
    (hD : ∀ (π : (ModelSystem.blowup (m + 1) X).Model)
      (κ : KahlerBackground (m + 1) π.1.carrier),
      SGPT.Siu.ClassModifiedNefWithRespectTo κ (D.onModel π)) : D.IsNef := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have hshift : ∀ κ : KahlerBackground (m + 1) X,
      (D + rootCartier (RealBottChern.ofRepresentative κ.form)).IsNef := by
    intro κ
    obtain ⟨θ, v, -, hreal, -⟩ := exists_iGood_currentBDivisor_eq ω _
      (allModelModifiedNef_add_semipositive ω D hD κ.form κ.isSemipositive)
      (isBig_add_rootKahler_of_allModelModifiedNef ω D hD κ)
    rw [← hreal]
    exact currentBDivisor_isNef ω _
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let κ : ℕ → KahlerBackground (m + 1) X := fun k =>
    KahlerBackground.smul (by dsimp [ε]; positivity : 0 < ε k) ω
  have hκ : ∀ k, rootCartier (RealBottChern.ofRepresentative (κ k).form) =
      ε k • rootCartier (RealBottChern.ofRepresentative ω.form) := by
    intro k
    change rootCartier (RealBottChern.ofRepresentative (ε k • ω.form)) = _
    rw [RealBottChern.ofRepresentative_smul]
    exact WeilBDivisorOn.cartierOf_smul ModelSystem.Model.root _ _
  apply WeilBDivisorOn.IsNef.of_converges (fun k => hshift (κ k))
  rw [WeilBDivisorOn.converges_iff_forall_dual]
  intro π f
  simp_rw [hκ, WeilBDivisorOn.add_onModel, WeilBDivisorOn.smul_onModel,
    map_add, map_smul, smul_eq_mul]
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.add
    (hε.mul_const (f ((rootCartier (RealBottChern.ofRepresentative ω.form)).onModel π)))

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
