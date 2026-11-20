import SGPT.PSH.SourceTestCurveJoinEnvelope
import SGPT.PSH.SourceTestCurveSum

/-! # The genuine original ordinary-model binary join

The actual raw envelope's PSH and mass have been proved independently.
Ordinary-envelope mothers now manufacture all original test-curve fields.
The I-good/I-model clause and join LUB/limit laws remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The literal raw upper concave envelope retains the original zero bound. -/
theorem sourceTestCurveRawConcaveMaximum_le_zero (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) : sourceTestCurveRawConcaveMaximum Γ Δ τ ≤ 0 := by
  intro x
  have hk : (0 : EReal) ≤ sourceTestCurveJoinConvexEnvelope Γ Δ x τ :=
    sourceTestCurveJoinConvexEnvelope_nonneg Γ Δ x τ
  change -sourceTestCurveJoinConvexEnvelope Γ Δ x τ ≤ (0 : EReal)
  simpa only [neg_zero] using EReal.neg_le_neg_iff.mpr hk

/-- Actual convex epigraphs manufacture all strict raw chords, retaining poles. -/
theorem sourceTestCurveRawConcaveMaximum_convexComb_le (Γ Δ : SourceTestCurvePredata θ)
    (a b : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceTestCurveRawConcaveMaximum Γ Δ a)
      (sourceTestCurveRawConcaveMaximum Γ Δ b) ≤
        sourceTestCurveRawConcaveMaximum Γ Δ (t*a+(1-t)*b) := by
  intro x
  have ht : 0 < 1-t := sub_pos.mpr ht1
  have hz : (0 : EReal) < ⊤ := by simp
  have haTop := ne_of_lt ((sourceTestCurveRawConcaveMaximum_le_zero Γ Δ a x).trans_lt hz)
  have hbTop := ne_of_lt ((sourceTestCurveRawConcaveMaximum_le_zero Γ Δ b x).trans_lt hz)
  have hc : SGPT.Convex.IsConvex (fun s => -sourceTestCurveRawConcaveMaximum Γ Δ s x) := by
    simpa only [sourceTestCurveRawConcaveMaximum,neg_neg] using
      sourceTestCurveJoinConvexEnvelope_convex Γ Δ x
  cases haVal : sourceTestCurveRawConcaveMaximum Γ Δ a x using EReal.rec with
  | top => exact False.elim (haTop haVal)
  | bot =>
    simp only [convexComb, haVal, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  | coe u =>
    cases hbVal : sourceTestCurveRawConcaveMaximum Γ Δ b x using EReal.rec with
    | top => exact False.elim (hbTop hbVal)
    | bot =>
      simp only [convexComb, hbVal, EReal.coe_mul_bot_of_pos ht, EReal.add_bot]
      exact bot_le
    | coe v =>
      have hpa : (a,-u) ∈ SGPT.Convex.epigraph
          (fun s => -sourceTestCurveRawConcaveMaximum Γ Δ s x) := by
        change -sourceTestCurveRawConcaveMaximum Γ Δ a x ≤ ((-u : ℝ) : EReal)
        rw [haVal,EReal.coe_neg]
      have hpb : (b,-v) ∈ SGPT.Convex.epigraph
          (fun s => -sourceTestCurveRawConcaveMaximum Γ Δ s x) := by
        change -sourceTestCurveRawConcaveMaximum Γ Δ b x ≤ ((-v : ℝ) : EReal)
        rw [hbVal,EReal.coe_neg]
      have hh := hc hpa hpb ht0.le ht.le (show t+(1-t)=1 by ring)
      change -sourceTestCurveRawConcaveMaximum Γ Δ (t*a+(1-t)*b) x ≤
        ((t*(-u)+(1-t)*(-v) : ℝ) : EReal) at hh
      have he : ((t*(-u)+(1-t)*(-v) : ℝ) : EReal) =
          -((t*u+(1-t)*v : ℝ) : EReal) := by
        rw [← EReal.coe_neg]
        congr 1
        ring
      rw [he] at hh
      simpa only [convexComb,haVal,hbVal,← EReal.coe_mul,← EReal.coe_add] using
        (EReal.neg_le_neg_iff.mp hh)

variable [CompactSpace M] [ConnectedSpace M]

/-- The proved actual inverse formula supplies whole-parameter antitonicity. -/
theorem sourceTestCurveRawConcaveMaximum_antitone (Γ Δ : SourceTestCurvePredata θ)
    (x : M) : Antitone (fun τ => sourceTestCurveRawConcaveMaximum Γ Δ τ x) := by
  intro a b hab
  change sourceTestCurveRawConcaveMaximum Γ Δ b x ≤ sourceTestCurveRawConcaveMaximum Γ Δ a x
  rw [sourceTestCurveRawConcaveMaximum_eq_inverse,
    sourceTestCurveRawConcaveMaximum_eq_inverse]
  apply iInf_mono
  intro t
  exact EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe (mul_le_mul_of_nonneg_left hab t.2.le))

variable [MeasurableSpace M] [BorelSpace M]

/-- Genuine raw PSH and actual positive mass manufacture each literal P-model. -/
theorem sourceTestCurveJoinSlice_model (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    SourceModelPotential θ (sourceSingularityEnvelope θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) :=
  sourceOrdinaryEnvelope_model omega
    (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hτ.le)
    (sourceTestCurveRawConcaveMaximum_mass_positive omega Γ Δ hτ)

/-- Every actual preliminary field of the original ordinary-model binary join. -/
def SourceTestCurve.joinPredata (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : SourceTestCurvePredata θ where
  max := max Γ.max Δ.max
  potential r := sourceSingularityEnvelope θ
    (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.1)
  thetaPSH r := (sourceTestCurveJoinSlice_model omega Γ Δ r.2).thetaPSH
  antitone x := by
    intro a b hab
    exact sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun y _ =>
      sourceTestCurveRawConcaveMaximum_antitone Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata y hab) x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords
    intro a b t ht0 ht1
    apply (sourceOrdinaryEnvelope_convexComb_le
      (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata a.2.le)
      (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata b.2.le) ht0 ht1).trans
    exact sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun y _ =>
      sourceTestCurveRawConcaveMaximum_convexComb_le Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata a.1 b.1 ht0 ht1 y)
  fixedPoint r := (sourceTestCurveJoinSlice_model omega Γ Δ r.2).choose_spec.1.symm

/-- The genuine original join, with positive ACTUAL spatial USC-limit mass. -/
def SourceTestCurve.join (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : SourceTestCurve θ where
  toSourceTestCurvePredata := SourceTestCurve.joinPredata omega Γ Δ
  positiveLimitMass := by
    let S := SourceTestCurve.joinPredata omega Γ Δ
    let r : Iio S.max := ⟨S.max-1,by change S.max-1 < S.max; linarith⟩
    have hm : SourceModelPotential θ (S.potential r) :=
      sourceTestCurveJoinSlice_model omega Γ Δ r.2
    have hle : S.potential r ≤ sourceTestCurveLimit S := by
      intro x
      change S.potential r x ≤ uscRegularization (fun y => ⨆ q, S.potential q y) x
      exact (le_iSup (fun q => S.potential q x) r).trans
        (le_uscRegularization (fun y => ⨆ q, S.potential q y) x)
    exact hm.choose_spec.2.trans_le (sourcePotentialNonPluripolarMass_mono omega
      hm.thetaPSH S.limit_thetaPSH (MoreSingularOn.of_le fun x _ => hle x))

/-- The literal original cutoff is the maximum of the actual input cutoffs. -/
theorem SourceTestCurve.join_max (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    (SourceTestCurve.join omega Γ Δ).max = max Γ.max Δ.max := rfl

/-- The literal original P-envelope formula at every original strict index. -/
theorem SourceTestCurve.join_potential (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (r : Iio (SourceTestCurve.join omega Γ Δ).max) :
    (SourceTestCurve.join omega Γ Δ).potential r = sourceSingularityEnvelope θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.1) := rfl

/-- Original positive-union membership uses the genuinely manufactured model base. -/
theorem SourceTestCurve.join_mem_positive (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    SourceTestCurve.join omega Γ Δ ∈ SourceTestCurvesPositive θ :=
  (SourceTestCurve.join omega Γ Δ).mem_positive omega

/-- Every original strict slice of the first input is dominated by the join. -/
theorem SourceTestCurve.le_join_left (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < Γ.max) :
    Γ.potential ⟨τ,hτ⟩ ≤ (SourceTestCurve.join omega Γ Δ).potential
      ⟨τ,lt_of_lt_of_le hτ (le_max_left Γ.max Δ.max)⟩ := by
  rw [SourceTestCurve.join_potential,← Γ.fixedPoint ⟨τ,hτ⟩]
  apply sourceOrdinaryEnvelope_mono
  apply MoreSingularOn.of_le
  intro x _
  have hh := (le_max_left (sourceTestCurveAt Γ.toSourceTestCurvePredata τ x)
    (sourceTestCurveAt Δ.toSourceTestCurvePredata τ x)).trans
      (sourceTestCurveRawConcaveMaximum_ge Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ x)
  simpa only [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hτ] using hh

/-- Every original strict slice of the second input is dominated by the join. -/
theorem SourceTestCurve.le_join_right (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < Δ.max) :
    Δ.potential ⟨τ,hτ⟩ ≤ (SourceTestCurve.join omega Γ Δ).potential
      ⟨τ,lt_of_lt_of_le hτ (le_max_right Γ.max Δ.max)⟩ := by
  rw [SourceTestCurve.join_potential,← Δ.fixedPoint ⟨τ,hτ⟩]
  apply sourceOrdinaryEnvelope_mono
  apply MoreSingularOn.of_le
  intro x _
  have hh := (le_max_right (sourceTestCurveAt Γ.toSourceTestCurvePredata τ x)
    (sourceTestCurveAt Δ.toSourceTestCurvePredata τ x)).trans
      (sourceTestCurveRawConcaveMaximum_ge Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ x)
  simpa only [sourceTestCurveAt_of_lt Δ.toSourceTestCurvePredata hτ] using hh

end SGPT.PSH.VariableComplexAtlas
