import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.PSH.MultiplierIdealInfSkoda
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open scoped Topology

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual ordinary reference monotonicity from the ENTIRE original
admissible set, including empty families and infinite values. -/
theorem partialEnvelope_mono_singularity
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    {phi psi : X → EReal} (K : Set X) (v : K → EReal)
    (h : SGPT.PSH.SingularityLE phi psi) :
    partialEnvelope theta phi K v ≤ partialEnvelope theta psi K v := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro u
  exact le_iSup (fun w : partialCompetitors theta psi K v => w.val x)
    ⟨u.val, u.property.1, u.property.2.1,
      SGPT.PSH.singularityLE_trans u.property.2.2 h⟩

/-- EXACT original open contact gap in source935-938, with the same
partial envelope and continuous weight; no closed/regularized substitute. -/
def sourceEnvelopeGap (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (v : C(X, ℝ)) (delta : ℝ) : Set X :=
  {x | partialEnvelope theta phi univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x <
    ((v x - delta : ℝ) : EReal)}

private theorem shifted_lt_iff (a : EReal) (b d : ℝ) :
    a + ((-b : ℝ) : EReal) < ((-d : ℝ) : EReal) ↔ a < ((b - d : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.bot_add]
    exact iff_of_true (EReal.bot_lt_coe _) (EReal.bot_lt_coe _)
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

/-- True source contact gaps are open from the ACTUAL envelope USC and
original continuous weight. No output openness/regularity certificate. -/
theorem sourceEnvelopeGap_isOpen
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (v : C(X, ℝ)) (delta : ℝ) :
    IsOpen (sourceEnvelopeGap theta phi v delta) := by
  have hu := upperSemicontinuous_add_coe_continuous
    (upperSemicontinuous_partialEnvelope theta phi univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal))) v.continuous.neg
  convert hu.isOpen_preimage ((-delta : ℝ) : EReal) using 1
  ext x
  exact (shifted_lt_iff _ (v x) delta).symm

/-- The ORIGINAL scaled-reference envelopes decrease for any compact
QPSH phi and actual positive increasing alpha. The global finite upper
bound is produced internally and absorbed by original singularity order;
no normalization or envelope monotonicity certificate is supplied. -/
theorem sourceScaledReferenceEnvelopes_antitone [CompactSpace X] [Nonempty X]
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (phi : X → EReal) (hphi : IsGlobalQuasiPshPotential (n := n) phi) (v : C(X, ℝ))
    (alpha : ℕ → ℝ) (ha : Monotone alpha) (hpos : ∀ k, 0 < alpha k) :
    Antitone (fun k => partialEnvelope theta (fun x => ((alpha k : ℝ) : EReal) * phi x)
      univ (fun y : ↥(univ : Set X) => (v y.val : EReal))) := by
  obtain ⟨A, hA⟩ := exists_real_upper_bound_of_upperSemicontinuous
    hphi.1.upperSemicontinuous hphi.1.ne_top
  intro m k hmk
  apply partialEnvelope_mono_singularity
  refine ⟨(alpha k - alpha m) * A, ?_⟩
  intro x _
  exact SGPT.PSH.MultiplierIdealInf.coe_mul_le_coe_mul_add (hpos m) (ha hmk) (hA x)

end SGPT.Bergman.ContactConcentration
