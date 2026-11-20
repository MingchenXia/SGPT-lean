import SGPT.Hodge.SourceCartierKahlerRows

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem sourceRootClass_add (D E : WeilFamilyAny (ModelSystem.blowup (m+1) X)) :
    sourceRootClass (D+E) = sourceRootClass D + sourceRootClass E := rfl

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem sourceRootClass_cartier (α : RealBottChern (m+1) X) :
    sourceRootClass (rootCartierAny α) = α := rootCartierAny_root α

/-- Genuine original current order reads on EVERY actual native presentation. -/
theorem iOrder_of_representedCurrentIOrder (ω : KahlerBackground (m+1) X)
    (θ η : ClosedRealOneOneForm (m+1) X) (u v : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential η.val v)
    (hI : currentIOrderAny (representedCurrent θ u hu) (representedCurrent η v hv)) :
    IOrderOnManifold (n := m+1) u v := by
  have hp := (isPresentationAny_iff_book _ θ u).mp (representedCurrent_isPresentation θ u hu)
  have hq := (isPresentationAny_iff_book _ η v).mp (representedCurrent_isPresentation η v hv)
  exact (sourceCurrentIOrder_iff_of_representation ω hp.1 hq.1 hp.2 hq.2).mp
    ((currentIOrderAny_iff_existing _ _).mp hI)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Actual smooth addition for a GIVEN genuine presentation, retaining the
same full potential and proving the entire family identity internally. -/
theorem representedSmoothShift_bdivisor (θ : ClosedRealOneOneForm (m+1) X)
    (u : X → EReal) (hu : IsThetaPshPotential θ.val u)
    (σ : ClosedRealOneOneForm (m+1) X) (hσ : σ.val.IsSemipositive) :
    currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
      (representedCurrent (θ+σ) u (LocalPotentials.isThetaPshPotential_add_of_semipositive hu hσ)) =
      currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu) +
        rootCartierAny (RealBottChern.ofRepresentative σ) := by
  let T := representedCurrent θ u hu
  let U := representedCurrent (θ+σ) u (LocalPotentials.isThetaPshPotential_add_of_semipositive hu hσ)
  have hp := (isPresentationAny_iff_book T θ u).mp (representedCurrent_isPresentation θ u hu)
  have hq := (isPresentationAny_iff_book U (θ+σ) u).mp
    (representedCurrent_isPresentation _ _ _)
  have hz := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  obtain ⟨hsum,hcur⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hz
  have he : (fun x => u x + (0 : EReal)) = u := by funext x; simp
  have hsum' : IsThetaPshPotential (θ+σ).val u := by simpa only [he] using hsum
  have hcur' : thetaPotentialCurrent (θ+σ).val u hsum' =
      thetaPotentialCurrent θ.val u hu + thetaPotentialCurrent σ.val (fun _ => 0) hz := by
    simpa only [he] using hcur
  have hread : (toBookCurrent U).current =
      (toBookCurrent T).current + thetaPotentialCurrent σ.val (fun _ => 0) hz :=
    hq.2.trans (hcur'.trans (congrArg (fun A => A +
      thetaPotentialCurrent σ.val (fun _ => 0) hz) hp.2.symm))
  apply family_eq_of_toExisting_eq (Nat.succ_pos m)
  rw [currentBDivisorAnyOn_eq_existing]
  let S := ModelSystem.blowup (m+1) X
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)
  have hZ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hz
  have hsumT := hT.add hZ
  have hU := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent U)
  have hf := (currentBDivisorOn_congr S hread hU hsumT).trans
    (currentBDivisorOn_add S hT hZ hsumT)
  rw [currentBDivisorOn_smooth S σ hz] at hf
  have hTbridge := currentBDivisorAnyOn_eq_existing S T
  change currentBDivisorOn S _ hU = _
  exact hf.trans (congrArg (fun A => A +
    WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root
      (RealBottChern.ofRepresentative σ)) hTbridge.symm)

/-- Actual reciprocal realization families force exact original potential
I-equivalence; all regularity and class/root comparisons are produced here. -/
theorem realization_rows_IEquivalent (ω : KahlerBackground (m+1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m+1) X))
    (θ : ℕ → ClosedRealOneOneForm (m+1) X) (u : ℕ → X → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hclass : ∀ i, RealBottChern.ofRepresentative (θ i) =
      sourceRootClass D + reciprocalStep i • RealBottChern.ofRepresentative ω.form)
    (hfamily : ∀ i, currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
      (representedCurrent (θ i) (u i) (hu i)) =
        D + reciprocalStep i • rootCartierAny (RealBottChern.ofRepresentative ω.form)) :
    ∀ i, IEquivalentOnManifold (n := m+1) (u i) (u 0) := by
  intro i
  let σ : ClosedRealOneOneForm (m+1) X := (1-reciprocalStep i) • ω.form
  have hσ : σ.val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr (reciprocalStep_le_one i))
  have hψ := LocalPotentials.isThetaPshPotential_add_of_semipositive (hu i) hσ
  let A := representedCurrent (θ i+σ) (u i) hψ
  let B := representedCurrent (θ 0) (u 0) (hu 0)
  have hAf : currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) A =
      D + rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
    calc
      _ = currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
          (representedCurrent (θ i) (u i) (hu i)) +
          rootCartierAny (RealBottChern.ofRepresentative σ) :=
        representedSmoothShift_bdivisor (θ i) (u i) (hu i) σ hσ
      _ = (D + reciprocalStep i • rootCartierAny (RealBottChern.ofRepresentative ω.form)) +
          (1-reciprocalStep i) • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
        rw [hfamily, RealBottChern.ofRepresentative_smul, rootCartierAny_smul]
      _ = _ := by module
  have hBf : currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) B =
      D + rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
    simpa only [reciprocalStep, Nat.cast_zero, zero_add, div_one, one_smul] using hfamily 0
  have hAc : currentClassAny A = sourceRootClass D + RealBottChern.ofRepresentative ω.form := by
    calc
      _ = RealBottChern.ofRepresentative (θ i+σ) :=
        currentClassAny_eq_of_presentation _ _ _ (representedCurrent_isPresentation _ _ _)
      _ = RealBottChern.ofRepresentative (θ i) + RealBottChern.ofRepresentative σ :=
        RealBottChern.ofRepresentative_add _ _
      _ = (sourceRootClass D + reciprocalStep i • RealBottChern.ofRepresentative ω.form) +
          (1-reciprocalStep i) • RealBottChern.ofRepresentative ω.form := by
        rw [hclass, RealBottChern.ofRepresentative_smul]
      _ = _ := by module
  have hBc : currentClassAny B = sourceRootClass D + RealBottChern.ofRepresentative ω.form := by
    have he := currentClassAny_eq_of_presentation B _ _ (representedCurrent_isPresentation _ _ _)
    exact he.trans (by simpa only [reciprocalStep, Nat.cast_zero, zero_add, div_one, one_smul] using hclass 0)
  have hrootA : (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) A).val ModelSystem.Model.root =
      currentClassAny A := by
    change sourceRootClass (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) A) = _
    rw [hAf, sourceRootClass_add, sourceRootClass_cartier, hAc]
  have hrootB : (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) B).val ModelSystem.Model.root =
      currentClassAny B := by
    change sourceRootClass (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) B) = _
    rw [hBf, sourceRootClass_add, sourceRootClass_cartier, hBc]
  have hI := currentIEquivalent_of_currentBDivisorAnyOn_eq
    (current_eq_regular_of_root_eq_class A hrootA)
    (current_eq_regular_of_root_eq_class B hrootB)
    (hAc.trans hBc.symm) (hAf.trans hBf.symm)
  exact ⟨iOrder_of_representedCurrentIOrder ω _ _ _ _ hψ (hu 0) hI.1,
    iOrder_of_representedCurrentIOrder ω _ _ _ _ (hu 0) hψ hI.2⟩

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
