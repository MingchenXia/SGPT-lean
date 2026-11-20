import SGPT.Projective.OriginalModificationPullbackDefinition
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

/-! Genuine dimension-zero pulled original coefficient membership, values and SAME original body.
No modification/flag/cone/equality certificate or replacement zero-body is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalModification.Zero
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.LineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

section NativeZero
variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel 0) Z] [IsComplexManifold 0 Z]

private theorem all_holomorphic (F : Z → ℂ) (z : Z) : HolomorphicAt 0 F z := by
  refine Eventually.of_forall fun y => ?_
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (fun _ : Z => F y) y :=
    mdifferentiableAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [(RooftopDimZero.isOpen_singleton_of_dim_zero rfl y).mem_nhds rfl] with w hw
  exact congrArg F (mem_singleton_iff.mp hw)

private theorem finite_weight_genuine (ψ : Z → EReal)
    (hψ : ∀ z, ψ z ≠ ⊥ ∧ ψ z ≠ ⊤) : IsGlobalQuasiPshPotential (n := 0) ψ :=
  (RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (0 : ClosedRealOneOneForm 0 Z))
    (fun z => (hψ z).2) (fun z => (hψ z).1)).quasiPshPotential

private theorem all_coefficients_mem (ψ : Z → EReal) (hψ : ∀ z, ψ z ≠ ⊥ ∧ ψ z ≠ ⊤)
    (c : ℝ) (hc : 0 < c) (F : Z → ℂ) (z : Z) : (multiplierIdeal (n := 0) c ψ).mem z F :=
  (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
    (finite_weight_genuine ψ hψ) hc z F).mpr (all_holomorphic F z)
end NativeZero

section OriginalZero
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f)
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
  {φ : SchemeComplexPoint f → EReal}
  (hφ : letI := E.isSeparated; letI := E.quasiCompact;
    IsThetaPshPotential (H.curvature a).val φ)
include hφ

/-- Actual theta-PSH nondegeneracy forces finiteness at EVERY original dim0 point. -/
theorem potential_finite : ∀ p : SchemeComplexPoint f, φ p ≠ ⊥ ∧ φ p ≠ ⊤ := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p
  exact ⟨RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hφ.2 p,
    hφ.1.quasiPlurisubharmonic.ne_top p⟩

/-- EVERY original section has actual original multiplier membership in EVERY degree. -/
theorem isMultiplierSection_all (k : ℕ) (s : bundlePowerGlobalSections L k) :
    IsMultiplierSection f 0 E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr fun U α p _ => ?_
  exact all_coefficients_mem φ (potential_finite f E a H hφ) (k : ℝ)
    (by exact_mod_cast hk) _ p

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel 0) Z] [IsComplexManifold 0 Z]
  (π : Z → SchemeComplexPoint f)

/-- EVERY original pulled coefficient has actual membership for arbitrary pi and actual dim0 Z. -/
theorem isPullbackMultiplierSection_all (k : ℕ) (s : bundlePowerGlobalSections L k) :
    AllDimensions.IsPullbackMultiplierSection f 0 E π φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr fun U α z _ => ?_
  exact all_coefficients_mem (fun w => φ (π w))
    (fun w => potential_finite f E a H hφ (π w)) (k : ℝ)
    (by exact_mod_cast hk) _ z

/-- Literal original and actual pulled membership coincide, with original coefficients/weights. -/
theorem isPullbackMultiplierSection_iff (k : ℕ) (s : bundlePowerGlobalSections L k) :
    AllDimensions.IsPullbackMultiplierSection f 0 E π φ k s ↔ IsMultiplierSection f 0 E φ k s :=
  iff_of_true (isPullbackMultiplierSection_all f E a H hφ π k s)
    (isMultiplierSection_all f E a H hφ k s)

variable [IsIntegral X]
  (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X)

/-- SAME arbitrary original valuation/centre/atlas and genuine original section values. -/
theorem pullbackValues_eq_multiplierSectionSet :
    AllDimensions.pullbackValues f 0 E a v c π φ =
      AlgebraicValuation.multiplierSectionSet f 0 E v c a φ := by
  change AlgebraicValuation.sectionValueSet v c a
      (fun k s => AllDimensions.IsPullbackMultiplierSection f 0 E π φ k s) =
    AlgebraicValuation.sectionValueSet v c a (fun k s => IsMultiplierSection f 0 E φ k s)
  apply congrArg (AlgebraicValuation.sectionValueSet v c a)
  funext k s
  exact propext (isPullbackMultiplierSection_iff f E a H hφ π k s)

/-- ANY cone uses the SAME actual original setBody; no fake zero-body or body certificate. -/
theorem pullbackBody_eq_partialBody (C : AdmissibleCone 0) :
    AllDimensions.pullbackBody f 0 E a v c C π φ = ValGen.partialBody f 0 E v c a C φ := by
  change ValGen.setBody C (AllDimensions.pullbackValues f 0 E a v c π φ) =
    ValGen.setBody C (AlgebraicValuation.multiplierSectionSet f 0 E v c a φ)
  rw [pullbackValues_eq_multiplierSectionSet f E a H hφ π v c]

end OriginalZero
end SGPT.Okounkov.OriginalModification.Zero
