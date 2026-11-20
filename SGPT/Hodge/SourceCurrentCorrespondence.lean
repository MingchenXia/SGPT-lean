import SGPT.Hodge.SourceCurrentNaturalMap

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Equality is reflected by the exact same-trace positive-dimensional family comparison. -/
theorem family_eq_of_toExisting_eq {S : ModelSystem n X} (hn : 0 < n)
    {D E : WeilFamilyAny S} (h : toExisting S hn D = toExisting S hn E) : D = E := by
  apply Subtype.ext
  funext π
  exact congrArg (fun F : WeilBDivisorOn S hn => F.onModel π) h

/-- Actual realization produces a member of the WHOLE source G(alpha).
Nondivisoriality and positive volume are conclusions, not caller certificates. -/
theorem exists_gCurrent_realizing (ω : KahlerBackground n X) (α : RealBottChern n X)
    (D : BigNefRoot α) : ∃ T : GCurrent α, gCurrentToBigNefRoot ω α T = D := by
  have hex : ∃ T : ClosedPositive (n := n) (X := X),
      currentClassAny T = D.val.val ModelSystem.Model.root ∧
      currentBDivisorAnyOn (ModelSystem.blowup n X) T = D.val := by
    cases n with
    | zero =>
      obtain ⟨θ, u, hclass, hfamily, -⟩ :=
        exists_iGood_currentBDivisorAnyOn_eq_zero (ModelSystem.blowup 0 X) D.val
      exact ⟨sourcePotentialCurrentZero θ u, hclass, hfamily⟩
    | succ m =>
      have hbig : (toExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m) D.val).IsBig := by
        change 0 < (toExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m) D.val).vol
        rw [← volumeAny_eq_existing (Nat.succ_pos m) D.val]
        exact D.property.1
      have hnef := (isNefAny_iff_existing (Nat.succ_pos m) D.val).mp D.property.2.1
      obtain ⟨θ, u, hclass, hfamily, -⟩ := exists_iGood_currentBDivisor_eq_of_big_nef ω
        (toExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m) D.val) hbig hnef
      let T := ofBookCurrent (sourcePotentialCurrent θ u)
      have hcl : currentClassAny T = D.val.val ModelSystem.Model.root := by
        change SGPT.PSH.BookCurrent.currentClass
          (toBookCurrent (ofBookCurrent (sourcePotentialCurrent θ u))) = _
        rw [toBookCurrent_ofBookCurrent]
        change SGPT.PSH.BookCurrent.currentClass
          (SGPT.PSH.BookCurrent.thetaPositiveCurrent (atlasClosedFormToNative θ) u.val _) = _
        rw [SGPT.PSH.BookCurrent.currentClass_thetaPositiveCurrent]
        exact hclass
      have hbridge : toExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m)
          (currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X) T) =
            currentBDivisor (sourcePotentialCurrent θ u) := by
        simpa only [T, toBookCurrent_ofBookCurrent, currentBDivisor] using
          (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) T)
      exact ⟨T, hcl, family_eq_of_toExisting_eq (Nat.succ_pos m) (hbridge.trans hfamily)⟩
  obtain ⟨T, hclass, hfamily⟩ := hex
  have hregular : T = regularCurrentAny T :=
    current_eq_regular_of_root_eq_class T (by rw [hfamily]; exact hclass.symm)
  have hvolume : 0 < currentIVolumeAny T := by
    rw [currentIVolumeAny_eq_bdivisorVolume ω T, hfamily]
    exact D.property.1
  refine ⟨⟨T, hclass.trans D.property.2.2, hregular, hvolume⟩, ?_⟩
  apply Subtype.ext
  exact hfamily

/-- Genuine surjectivity of the actual quotient map onto all original big nef root-alpha families. -/
theorem quotientToBigNefRoot_surjective (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Surjective (quotientToBigNefRoot ω α) := by
  intro D
  obtain ⟨T, hT⟩ := exists_gCurrent_realizing ω α D
  exact ⟨Quotient.mk _ T, hT⟩

/-- WHOLE thm:bdiv_current_corr in every natural dimension, on the actual original quotient.
The statement is even valid for arbitrary alpha; no alpha-big or I-good input restriction is used. -/
theorem source_bdiv_current_corr (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Bijective (quotientToBigNefRoot ω α) :=
  ⟨quotientToBigNefRoot_injective ω α, quotientToBigNefRoot_surjective ω α⟩

/-- The natural actual-current map induces this genuine equivalence of the original sets. -/
def sourceCurrentBDivisorEquiv (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Quotient (gCurrentISetoid ω α) ≃ BigNefRoot α :=
  Equiv.ofBijective (quotientToBigNefRoot ω α) (source_bdiv_current_corr ω α)

/-- Exact forward readback: the full actual family of the same original current. -/
theorem sourceCurrentBDivisorEquiv_apply_mk (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : GCurrent α) :
    (sourceCurrentBDivisorEquiv ω α (Quotient.mk _ T)).val =
      currentBDivisorAnyOn (ModelSystem.blowup n X) T.val := rfl

/-- Both inverse laws hold on the original quotient and the entire target, including empty cases. -/
theorem sourceCurrentBDivisorEquiv_left_inverse (ω : KahlerBackground n X) (α : RealBottChern n X)
    (q : Quotient (gCurrentISetoid ω α)) :
    (sourceCurrentBDivisorEquiv ω α).symm ((sourceCurrentBDivisorEquiv ω α) q) = q :=
  (sourceCurrentBDivisorEquiv ω α).symm_apply_apply q

theorem sourceCurrentBDivisorEquiv_right_inverse (ω : KahlerBackground n X) (α : RealBottChern n X)
    (D : BigNefRoot α) :
    sourceCurrentBDivisorEquiv ω α ((sourceCurrentBDivisorEquiv ω α).symm D) = D :=
  (sourceCurrentBDivisorEquiv ω α).apply_symm_apply D

end SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
