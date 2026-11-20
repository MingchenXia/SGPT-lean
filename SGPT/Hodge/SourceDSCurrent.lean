import SGPT.Hodge.SourceDSBackground
import SGPT.Hodge.BDivChainDT
import SGPT.Okounkov.ThetaPotentialCurrentCombinations

set_option autoImplicit false
noncomputable section
universe u

open Set Filter
open scoped Topology

namespace SGPT.Hodge.BDivChain.SourceDSDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The genuine zero-potential positive current of the original smooth Kähler form. -/
def smoothKahlerCurrent (κ : KahlerBackground (m + 1) X) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  SGPT.PSH.BookCurrent.thetaPositiveCurrent κ.form (fun _ => (0 : EReal))
    ((LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr κ.isSemipositive)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The enlarged source potential presents precisely the old current plus this smooth current. -/
theorem sourcePotentialCurrent_enlargement
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (κ : KahlerBackground (m + 1) X) (u : SourceThetaPotentialL1 θ) :
    (sourcePotentialCurrent (enlargedBackground θ κ) (enlargedPotential κ u)).current =
      (sourcePotentialCurrent θ u).current + (smoothKahlerCurrent κ).current := by
  have hu := (isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property
  have hz : IsThetaPshPotential κ.form.val (fun _ : X => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr κ.isSemipositive
  obtain ⟨hsum, hcur⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hz
  have hp : (fun x => u.val x + (0 : EReal)) = u.val := by funext x; simp
  have hsum' : IsThetaPshPotential (atlasClosedFormToNative θ + κ.form).val u.val := by
    simpa only [hp] using hsum
  have hread : thetaPotentialCurrent (atlasClosedFormToNative θ + κ.form).val u.val hsum' =
      (sourcePotentialCurrent θ u).current + (smoothKahlerCurrent κ).current := by
    change thetaPotentialCurrent (atlasClosedFormToNative θ + κ.form).val u.val hsum' =
      thetaPotentialCurrent (atlasClosedFormToNative θ).val u.val hu +
        thetaPotentialCurrent κ.form.val (fun _ : X => (0 : EReal)) hz
    simpa only [hp] using hcur
  have hform : atlasClosedFormToNative (enlargedBackground θ κ) =
      atlasClosedFormToNative θ + κ.form := by
    simp only [enlargedBackground, sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]
  exact (PrimePushforward.thetaPotentialCurrent_congr (congrArg Subtype.val hform) rfl
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp (enlargedPotential κ u).property)
    hsum').trans hread

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- The actual smooth family is the Cartier family realized at the original root. -/
theorem smoothKahlerCurrent_bdivisor (κ : KahlerBackground (m + 1) X) :
    currentBDivisor (smoothKahlerCurrent κ) =
      WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root
        (RealBottChern.ofRepresentative κ.form) := by
  exact currentBDivisorOn_smooth (ModelSystem.blowup (m + 1) X) κ.form
    ((LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr κ.isSemipositive)

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- The whole original family shifts by one fixed smooth family. Existing additivity
uses the actual pulled currents, generic Lelong coefficients and true Siu sums. -/
theorem currentBDivisor_enlargement
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    (κ : KahlerBackground (m + 1) X) (u : SourceThetaPotentialL1 θ) :
    currentBDivisor (sourcePotentialCurrent (enlargedBackground θ κ) (enlargedPotential κ u)) =
      currentBDivisor (sourcePotentialCurrent θ u) + currentBDivisor (smoothKahlerCurrent κ) := by
  let S := ModelSystem.blowup (m + 1) X
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (sourcePotentialCurrent θ u)
  have hK := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (smoothKahlerCurrent κ)
  have hTK := hT.add hK
  exact (currentBDivisorOn_congr S (sourcePotentialCurrent_enlargement θ κ u)
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent
      (sourcePotentialCurrent (enlargedBackground θ κ) (enlargedPotential κ u))) hTK).trans
    (currentBDivisorOn_add S hT hK hTK)

/-- Original arbitrary-θ continuity: apply the already proved big-reference theorem
on the SAME potentials and subtract the actual fixed family modelwise. -/
theorem currentBDivisor_converges_of_unindexedDS (ω : KahlerBackground (m + 1) X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : unindexedDSTendsto ω θ F w v) :
    WeilBDivisorOn.Converges F (fun i => currentBDivisor (sourcePotentialCurrent θ (w i)))
      (currentBDivisor (sourcePotentialCurrent θ v)) := by
  rcases hlim with ⟨κ, hκ⟩
  have hconv := currentBDivisor_converges_of_dS ω (enlargedBackground θ κ)
    (enlargedBackground_isBig θ κ v) F (fun i => enlargedPotential κ (w i))
    (enlargedPotential κ v) hκ
  intro π
  have hp := hconv π
  rw [tendsto_euclideanTopology_iff] at hp ⊢
  intro f
  have hs := (hp f).sub_const (f ((currentBDivisor (smoothKahlerCurrent κ)).onModel π))
  simpa only [currentBDivisor_enlargement, WeilBDivisorOn.add_onModel,
    map_add, add_sub_cancel_right] using hs

end SGPT.Hodge.BDivChain.SourceDSDraft
