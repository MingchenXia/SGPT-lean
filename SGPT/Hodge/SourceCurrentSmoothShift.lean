import SGPT.Hodge.SourceRootCartier

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The actual class of any genuine presentation, including dimension zero. -/
theorem currentClassAny_eq_of_presentation (T : ClosedPositive (n := n) (X := X))
    (θ : ClosedRealOneOneForm n X) (u : X → EReal) (hp : IsPresentationAny T θ u) :
    currentClassAny T = RealBottChern.ofRepresentative θ := by
  cases n with
  | zero =>
    exact (realBottChern_eq_zero_of_dim_zero (currentClassAny T)).trans
      (realBottChern_eq_zero_of_dim_zero (RealBottChern.ofRepresentative θ)).symm
  | succ m => exact ((isPresentationAny_iff_book T θ u).mp hp).currentClass_eq

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- The genuine current T+σ, constructed on the same original potential with
background shifted by the actual semipositive smooth form. -/
def semipositiveShiftCurrent (T : ClosedPositive (n := n) (X := X))
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    ClosedPositive (n := n) (X := X) :=
  let θ := atlasClosedFormToNative (currentPresentationBackground T)
  let u := currentPresentationPotential T
  let hu := LocalPotentials.isThetaPshPotential_add_of_semipositive
    (currentPresentation_isPresentation T).choose hσ
  SourceDSDraft.sourcePotentialCurrentAny (nativeClosedFormToAtlas (θ + σ))
    ⟨u, (isThetaPSH_iff_nativeThetaPotential _ _).mpr hu⟩

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- The same pointwise potential, with all original poles, presents T+σ. -/
theorem semipositiveShiftCurrent_isPresentation (T : ClosedPositive (n := n) (X := X))
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    IsPresentationAny (semipositiveShiftCurrent T σ hσ)
      (atlasClosedFormToNative (currentPresentationBackground T) + σ)
      (currentPresentationPotential T) := by
  exact SourceDSDraft.sourcePotentialCurrentAny_isPresentation _ _

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem semipositiveShiftCurrent_class (T : ClosedPositive (n := n) (X := X))
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    currentClassAny (semipositiveShiftCurrent T σ hσ) =
      currentClassAny T + RealBottChern.ofRepresentative σ := by
  rw [currentClassAny_eq_of_presentation _ _ _ (semipositiveShiftCurrent_isPresentation T σ hσ),
    RealBottChern.ofRepresentative_add,
    currentClassAny_eq_of_presentation T _ _ (currentPresentation_isPresentation T)]

/-- Literal positive-dimensional current readback, independent of quotient choices. -/
theorem semipositiveShiftCurrent_book_add {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (T : ClosedPositive (n := m + 1) (X := Y))
    (σ : ClosedRealOneOneForm (m + 1) Y) (hσ : σ.val.IsSemipositive) :
    (toBookCurrent (semipositiveShiftCurrent T σ hσ)).current =
      (toBookCurrent T).current +
        thetaPotentialCurrent σ.val (fun _ : Y => (0 : EReal))
          ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hσ) := by
  let θ := atlasClosedFormToNative (currentPresentationBackground T)
  let u := currentPresentationPotential T
  have hp := (isPresentationAny_iff_book T θ u).mp (currentPresentation_isPresentation T)
  have hp' := (isPresentationAny_iff_book _ (θ + σ) u).mp
    (semipositiveShiftCurrent_isPresentation T σ hσ)
  have hz := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  obtain ⟨hsum, hcur⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hp.1 hz
  have he : (fun x => u x + (0 : EReal)) = u := by funext x; simp
  have hu : IsThetaPshPotential (θ + σ).val u := by simpa only [he] using hsum
  have hr : thetaPotentialCurrent (θ + σ).val u hu =
      thetaPotentialCurrent θ.val u hp.1 + thetaPotentialCurrent σ.val (fun _ => 0) hz := by
    simpa only [he] using hcur
  exact hp'.2.trans (hr.trans (congrArg (fun A => A +
    thetaPotentialCurrent σ.val (fun _ => 0) hz) hp.2.symm))

/-- The full family shifts by the genuine smooth root Cartier family, on ALL
original book models and in every dimension. -/
theorem semipositiveShiftCurrent_bdivisor (T : ClosedPositive (n := n) (X := X))
    (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    currentBDivisorAnyOn (ModelSystem.blowup n X) (semipositiveShiftCurrent T σ hσ) =
      currentBDivisorAnyOn (ModelSystem.blowup n X) T +
        rootCartierAny (RealBottChern.ofRepresentative σ) := by
  cases n with
  | zero =>
    exact (weilFamily_eq_zero_of_dim_zero _).trans
      (weilFamily_eq_zero_of_dim_zero _).symm
  | succ m =>
    apply family_eq_of_toExisting_eq (Nat.succ_pos m)
    rw [currentBDivisorAnyOn_eq_existing]
    let S := ModelSystem.blowup (m + 1) X
    have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)
    have hz := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
    have hZ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hz
    have hsum := hT.add hZ
    have hp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent
      (toBookCurrent (semipositiveShiftCurrent T σ hσ))
    have hf := (currentBDivisorOn_congr S (semipositiveShiftCurrent_book_add T σ hσ)
      hp hsum).trans (currentBDivisorOn_add S hT hZ hsum)
    rw [currentBDivisorOn_smooth S σ hz] at hf
    have hTbridge := currentBDivisorAnyOn_eq_existing S T
    change currentBDivisorOn S _ hp = _
    exact hf.trans (congrArg (fun A => A +
      WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root
        (RealBottChern.ofRepresentative σ)) hTbridge.symm)

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
