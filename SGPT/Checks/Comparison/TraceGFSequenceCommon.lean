import SGPT.Checks.Comparison.TraceGFSequenceData
import SGPT.Checks.Comparison.TraceGivenInfimum
import SGPT.Checks.Comparison.SourceDXZPOrder
import SGPT.NAPotential.ProjectiveLimit
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-! SAME actual zeroth perturbation background for the actual GF curves
and the GIVEN original curve. Blueprint: trace-na-general-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeGFSequence

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.TraceComparison.GFTwist
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {r : ℕ}
  [SmoothOfRelativeDimension (r+1) f] [IsIntegral X] [IsProjective f]
  {EX : ClosedProjectiveEmbedding f}
local instance proper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance pointManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
  {LQ : RationalPicardSpace X} {κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)}
  {Γ : SourceNAPotential θ}
  (S : NativeGFSequence f r EX θ LQ (naPotentialAnAt (r+1) EX Γ κX) κX)

/-- The SAME actual zeroth perturbation form for every member and the
given original curve. -/
def commonForm := twistForm f (r+1) EX S.atlas S.metric θ (S.epsilon 0 : ℝ)

omit [IsIntegral X] in
theorem member_to_common_semipositive (i : ℕ) :
    (atlasClosedFormToNative S.commonForm -
      atlasClosedFormToNative (twistForm f (r+1) EX S.atlas S.metric θ (S.epsilon i : ℝ))).val.IsSemipositive := by
  rw [commonForm,twistForm_native,twistForm_native]
  have h : (atlasClosedFormToNative θ + (S.epsilon 0 : ℝ) • S.metric.curvature S.atlas) -
      (atlasClosedFormToNative θ + (S.epsilon i : ℝ) • S.metric.curvature S.atlas) =
      ((S.epsilon 0 : ℝ) - (S.epsilon i : ℝ)) • S.metric.curvature S.atlas := by module
  rw [h]
  exact Pending.KahlerDomination.isSemipositive_smul
    (KahlerBackground.isSemipositive ⟨S.metric.curvature S.atlas,S.kahler⟩)
    (sub_nonneg.mpr (by exact_mod_cast S.strictAnti.antitone (Nat.zero_le i)))

omit [IsIntegral X] in
theorem original_to_common_semipositive :
    (atlasClosedFormToNative S.commonForm - atlasClosedFormToNative θ).val.IsSemipositive := by
  rw [commonForm,twistForm_native]
  have h : (atlasClosedFormToNative θ + (S.epsilon 0 : ℝ) • S.metric.curvature S.atlas) -
      atlasClosedFormToNative θ = (S.epsilon 0 : ℝ) • S.metric.curvature S.atlas := by module
  rw [h]
  exact Pending.KahlerDomination.isSemipositive_smul
    (KahlerBackground.isSemipositive ⟨S.metric.curvature S.atlas,S.kahler⟩)
    (by exact_mod_cast (S.positive 0).le)

/-- The actual ORIGINAL I-transition of every actual original GF curve. -/
def commonMember (i : ℕ) : SourceNAPotential S.commonForm :=
  (S.member i).transition (S.member_to_common_semipositive i)

/-- The actual ORIGINAL I-transition of the GIVEN original curve to the
SAME actual zeroth background. -/
def commonGiven : SourceNAPotential S.commonForm :=
  Γ.transition S.original_to_common_semipositive

omit [IsIntegral X] in
theorem commonMember_An (i : ℕ) :
    naPotentialAnAt (r+1) EX (S.commonMember i) κX =
      naPotentialAnAt (r+1) EX (S.member i) κX := by
  have h := (S.member i).transition_POrder_equivalent (sourceKahlerFormRepresentative κX)
    (S.member_to_common_semipositive i)
  exact funext fun v => BJ.SourceDXZPOrder.naPotentialAnAt_eq_of_POrder_equivalent
    (r+1) EX h.2 h.1 κX v

omit [IsIntegral X] in
theorem commonGiven_An :
    naPotentialAnAt (r+1) EX S.commonGiven κX = naPotentialAnAt (r+1) EX Γ κX := by
  have h := Γ.transition_POrder_equivalent (sourceKahlerFormRepresentative κX)
    S.original_to_common_semipositive
  exact funext fun v => BJ.SourceDXZPOrder.naPotentialAnAt_eq_of_POrder_equivalent
    (r+1) EX h.2 h.1 κX v

/-- The ACTUAL original common-background family has its true intrinsic
orders and cutoff bound manufactured internally, and its ACTUAL original
NA infimum is the SAME transitioned GIVEN curve. -/
theorem exists_common_decreasingInf_eq (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f)) :
    ∃ (ha : ∀ i j, i ≤ j → SourceNAPOrder (S.commonMember j) (S.commonMember i))
      (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (S.commonMember i))),
      SourceNAPotential.decreasingInf omegaX S.commonMember ha hb = S.commonGiven := by
  apply exists_decreasingInf_eq_of_An_antitone_tendsto f r EX omegaX κX S.commonGiven S.commonMember
  · intro v i j hij
    simp only [S.commonMember_An]
    exact S.antitone v hij
  · intro v
    simpa only [S.commonMember_An,S.commonGiven_An] using S.tendsto v

/-- The GIVEN original curve lies below EVERY original varying-class GF
curve, with the actual transitions/order/infimum produced internally. -/
theorem original_le_member (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f)) (i : ℕ) :
    SourceNAPOrder Γ (S.member i) := by
  obtain ⟨ha,hb,hInf⟩ := S.exists_common_decreasingInf_eq omegaX
  have hlow : SourceNAPOrder S.commonGiven (S.commonMember i) := by
    rw [← hInf]
    exact SourceNAPotential.decreasingInf_le omegaX S.commonMember ha hb i
  exact (Γ.transition_POrder_equivalent omegaX S.original_to_common_semipositive).1.trans
    (hlow.trans ((S.member i).transition_POrder_equivalent omegaX
      (S.member_to_common_semipositive i)).2)

end SGPT.NAPotential.TraceComparison.NativeGFSequence
