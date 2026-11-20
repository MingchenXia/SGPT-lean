import SGPT.TestCurve.TCActualCentralEigenspaces

/-! Literal actual central geometric multiplicities and original weight measures. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MeasureTheory
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin
open SGPT.TestCurve.TCOko
open scoped ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a) (Λ : GeomLinearization T)

/-- The actual original geometric central H0 weight measure, with covariant characters. -/
def geometricCentralWeightMeasure (m : ℕ) : Measure ℝ :=
  Measure.sum fun lam : ℤ =>
    (Module.finrank ℂ (geometricCentralWeight T Λ m lam) : ℝ≥0∞) •
      Measure.dirac ((lam : ℝ) / m)

/-- Literal quotient restriction maps original weights onto actual geometric eigenspaces. -/
theorem geometricCentralWeight_eq_map_quotient [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (m : ℕ)
    (hsurj : Function.Surjective (centralFiberRestriction T m)) (lam : ℤ) :
    geometricCentralWeight T Λ m lam =
      (centralWeight T m lam).map (centralFiberQuotientRestriction T m) := by
  rw [geometricCentralWeight_eq_restriction_weight T Λ E m hsurj lam,
    centralWeight, ← Submodule.map_comp]
  rfl

/-- Original ampleness produces actual central multiplicities and the literal induced jump measure. -/
theorem exists_eventual_geometricCentralWeightMeasure [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (hA : T.IsAmple) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      (∀ lam : ℤ, Module.finrank ℂ (geometricCentralWeight T Λ m lam) =
        Module.finrank ℂ (centralWeight T m lam)) ∧
      (0 < m → geometricCentralWeightMeasure T Λ m =
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_isAmple E T (GeomLinearization.toSectionLinearization E Λ) hA)).jumpMeasure m) := by
  obtain ⟨B₁, hB₁⟩ := exists_centralFiberRestriction_surjective T E hA
  obtain ⟨B₂, hB₂⟩ := exists_eventual_centralFiberBaseChange T E hA
  refine ⟨max B₁ B₂, fun m hm => ?_⟩
  have hs := hB₁ m (le_trans (le_max_left _ _) hm)
  obtain ⟨e, he⟩ := hB₂ m (le_trans (le_max_right _ _) hm)
  have hdim (lam : ℤ) : Module.finrank ℂ (geometricCentralWeight T Λ m lam) =
      Module.finrank ℂ (centralWeight T m lam) := by
    rw [geometricCentralWeight_eq_map_quotient T Λ E m hs lam, ← he]
    exact e.finrank_map_eq _
  refine ⟨hdim, fun hpos => ?_⟩
  have hmeasure : geometricCentralWeightMeasure T Λ m = centralWeightMeasure T m := by
    unfold geometricCentralWeightMeasure centralWeightMeasure
    congr 1
    funext lam
    rw [hdim]
  exact hmeasure.trans (centralWeightMeasure_eq_jumpMeasure T E
    (filtrationFinitelyGenerated_of_isAmple E T (GeomLinearization.toSectionLinearization E Λ) hA) hpos)

end SGPT.TestCurve.CentralFiber
