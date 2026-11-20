import SGPT.Hodge.BDivChainZeroCurrentBDivDraft

/-!
# Genuine theta-PSH presentations and modification pullback in dimension zero

A presentation here requires the actual native theta-PSH
predicate and equality to actual regular-distribution theta-potential chart
coefficients. The comparison is for that SAME pair `(theta,u)` and the SAME
actual modification map. This does not establish the positive-dimensional
presentation comparison or the full source theorem.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

/-- A real zero-dimensional theta-PSH presentation of the actual current:
original theta-PSH plus the original chart coefficients `θ + ddᶜ u`. -/
def IsPresentationZero (T : ClosedPositive (n := 0) (X := X))
    (θ : ClosedRealOneOneForm 0 X) (u : X → EReal) : Prop :=
  IsThetaPshPotential θ.val u ∧
    T.val = thetaCurrentZero θ u (chartLocallyIntegrable_zero u)

omit [CompactSpace X] in
/-- Every genuine theta-PSH potential presents the unique actual current in
dimension zero, using its genuine theta and distribution coefficients. -/
theorem isPresentationZero_of_isThetaPshPotential
    (T : ClosedPositive (n := 0) (X := X)) (θ : ClosedRealOneOneForm 0 X)
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsPresentationZero T θ u :=
  ⟨hu, eq_of_dim_zero _ _⟩

omit [CompactSpace X] in
/-- Every actual zero-dimensional current has a genuine theta-PSH
presentation, with θ and u both actually zero. -/
theorem exists_presentation_zero (T : ClosedPositive (n := 0) (X := X)) :
    ∃ (θ : ClosedRealOneOneForm 0 X) (u : X → EReal), IsPresentationZero T θ u := by
  refine ⟨0, fun _ => (0 : EReal), isPresentationZero_of_isThetaPshPotential T 0 ?_⟩
  exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (0 : ClosedRealOneOneForm 0 X))
    (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)

omit [CompactSpace X] in
/-- The actual theta-PSH potential of a presentation stays theta-PSH under
the actual modification map in dimension zero. -/
theorem thetaPshPotential_comp_modification_zero (π : Modification 0 X)
    (θ : ClosedRealOneOneForm 0 X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback π.isAnalyticModification.1 θ).val
      (u ∘ π.map) := by
  apply RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
  · intro y
    exact hu.1.quasiPlurisubharmonic.ne_top (π.map y)
  · intro y
    exact RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 (π.map y)

/-- Pullback of a genuine `(θ,u)` presentation is presented by the SAME
actual pulled-back form and composed potential. -/
theorem IsPresentationZero.pullCurrentAny (π : Modification 0 X)
    {T : ClosedPositive (n := 0) (X := X)} {θ : ClosedRealOneOneForm 0 X} {u : X → EReal}
    (h : IsPresentationZero T θ u) :
    IsPresentationZero (pullCurrentAny π T)
      (ClosedRealOneOneForm.pullback π.isAnalyticModification.1 θ) (u ∘ π.map) := by
  refine ⟨thetaPshPotential_comp_modification_zero π θ h.1, ?_⟩
  exact pullCurrentAny_zero_eq_thetaCurrent_unconditional π T θ u

end SGPT.Hodge.BDivChain.NativeDraft
