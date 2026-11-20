import SGPT.Envelopes.SourceObstacleConcentration
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.POrderAffineRooftop
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination

/-- Literal printed REAL-root interval, including both infinite-upper conventions. -/
def SourceAffineCoefficient (n : ℕ) (p q : ℝ≥0∞) (a : ℝ) : Prop :=
  1 < a ∧ (n = 0 ∨ p = q ∨
    a < (q.toReal / (q.toReal - p.toReal)) ^ ((n : ℝ)⁻¹))

/-- Exact printed interval equals the actual polynomial domain; geometric
consumers below PRODUCE the finite masses before any real readback. -/
theorem sourceAffineCoefficient_iff {n : ℕ} {p q : ℝ≥0∞} {a : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hq : q ≠ ⊤) :
    SourceAffineCoefficient n p q a ↔ ConvexCombEnvelopeMass.IsAdmissibleWeight n p q a := by
  have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
  have hgapfin : q - p ≠ ⊤ := ne_top_of_le_ne_top hq tsub_le_self
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpfin
  have hqR : 0 < q.toReal := ENNReal.toReal_pos (hp.trans_le hpq).ne' hq
  unfold SourceAffineCoefficient ConvexCombEnvelopeMass.IsAdmissibleWeight
  apply and_congr_right
  intro ha
  have ha0 : 0 < a := zero_lt_one.trans ha
  have heq : ENNReal.ofReal (a ^ n) * (q - p) < q ↔
      a ^ n * (q.toReal - p.toReal) < q.toReal := by
    rw [← ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgapfin) hq,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha0.le n),
      ENNReal.toReal_sub_of_le hpq hq]
  rw [heq]
  by_cases hn : n = 0
  · simp only [hn, true_or, pow_zero, one_mul]
    constructor
    · intro _; linarith
    · intro _; trivial
  by_cases hpqe : p = q
  · simp [hpqe, hqR]
  have hpqR : p.toReal < q.toReal :=
    (ENNReal.toReal_lt_toReal hpfin hq).mpr (lt_of_le_of_ne hpq hpqe)
  have hd : 0 < q.toReal - p.toReal := sub_pos.mpr hpqR
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp only [hn, hpqe, false_or]
  rw [Real.lt_rpow_inv_iff_of_pos ha0.le (div_nonneg hqR.le hd.le) hnR,
    Real.rpow_natCast, lt_div_iff₀ hd]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v η : M → EReal}

/-- The ORIGINAL additive order supplies the actual fixed-background P order. -/
theorem sourceAffine_precedence_to_pOrder (huv : SGPT.PSH.SingularityLE u v) :
    FirstPass.POrder.POrderWith (atlasClosedFormToNative θ) u v :=
  FirstPass.POrder.pOrderWith_of_moreSingular huv

/-- ALL genuine source-QE competitors equal ALL pointwise barriers, poles included. -/
theorem sourceAffine_competitor_iff
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hη : (ofFixedModel n M).IsThetaPSH θ η) {a : ℝ} (ha : 1 < a) :
    SourceQuasiEverywhere (n := n) (fun x => η x ≤ convexComb a u v x) ↔
      convexComb a⁻¹ η v ≤ u := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hηn := (isThetaPSH_iff_nativeThetaPotential θ η).mp hη
  constructor
  · intro h
    exact ConvexCombEnvelopeMass.barrier_of_mem_rooftopCompetitors hun hvn ha hηn
      ⟨hηn, (sourceQuasiEverywhere_iff_native _).mp h⟩
  · intro h
    exact (sourceQuasiEverywhere_iff_native _).mpr
      (ConvexCombEnvelopeMass.mem_rooftopCompetitors_of_barrier hvn ha hηn h).2

/-- The EXISTING source envelope is the printed USC supremum over every
pointwise barrier; the operation and empty-family convention are unchanged. -/
theorem sourceAffineEnvelope_eq_barrierSup
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {a : ℝ} (ha : 1 < a) :
    sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v) =
      uscRegularization (fun x => ⨆ η : {η : M → EReal //
        (ofFixedModel n M).IsThetaPSH θ η ∧ convexComb a⁻¹ η v ≤ u}, η.1 x) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro η
    exact le_iSup (fun z : {η : M → EReal //
      (ofFixedModel n M).IsThetaPSH θ η ∧ convexComb a⁻¹ η v ≤ u} => z.1 x)
      ⟨η.1, η.2.1, (sourceAffine_competitor_iff hu hv η.2.1 ha).mp η.2.2.1⟩
  · apply iSup_le
    intro η
    exact le_iSup
      (fun z : sourceRelativeEnvelopeCompetitors θ (fun _ => ⊤) (convexComb a u v) => z.1 x)
      ⟨η.1, η.2.1, (sourceAffine_competitor_iff hu hv η.2.1 ha).mpr η.2.2,
        sourceObstacle_topReference η.1⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal diagonal mass is the SAME actual native mass. -/
theorem sourceAffine_mass_eq_native (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ =
      diagonalPotentialMass (atlasClosedFormToNative θ) u
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) := rfl

omit [ConnectedSpace M] in
/-- Actual finiteness is produced before original REAL-rpow mass readback. -/
theorem sourceAffine_mass_lt_top (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ < ⊤ :=
  DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) univ

omit [ConnectedSpace M] in
/-- Original additive comparison manufactures both mass order and admissibility. -/
theorem sourceAffineCoefficient_admissible (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a :=
  (sourceAffineCoefficient_iff hpos (sourcePotentialNonPluripolarMass_mono ω hu hv huv)
    (sourceAffine_mass_lt_top ω hv).ne).mp ha

/-- WHOLE original positive-affine envelope lemma, with the printed coefficient
interval, actual positive envelope and every quantitative bound from its proof. -/
theorem sourcePositiveAffineEnvelope (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    ∃ hE : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)),
      0 < sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ ∧
      convexComb a⁻¹ (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) v ≤ u ∧
      ∀ a' : ℝ, a < a' →
        SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
          (sourcePotentialNonPluripolarMeasure θ v hv univ) a' →
        ENNReal.ofReal (((a' - a) / a') ^ n) *
            sourcePotentialNonPluripolarMeasure θ u hu univ ≤
          sourcePotentialNonPluripolarMeasure θ
            (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ := by
  obtain ⟨hEn, hquant, hEpos, hbar⟩ := POrderAffineRooftop.xiaTheorem611 ω
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hpos
    (sourceAffine_precedence_to_pOrder huv) (sourceAffineCoefficient_admissible ω hu hv huv hpos ha)
  have hEn' : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) := by
    simpa only [sourceObstacleEnvelope_eq_native] using hEn
  refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr hEn', ?_, ?_, ?_⟩
  · simpa only [sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure, diagonalPotentialMass] using hEpos
  · simpa only [sourceObstacleEnvelope_eq_native] using hbar
  · intro a' haa' ha'
    have ha'0 : 0 < a' := zero_lt_one.trans ha'.1
    have heq : 1 - a / a' = (a' - a) / a' := by field_simp
    simpa only [heq, sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure, diagonalPotentialMass] using
      hquant a' haa' (sourceAffineCoefficient_admissible ω hu hv huv hpos ha')

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- ONE manufactured comparison constant converts any actual positive-weight
barrier to the original additive singularity bound. No finite-locus cancellation. -/
theorem sourceAffineBarrier_precedence
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (huv : SGPT.PSH.SingularityLE u v) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbar : convexComb ε η v ≤ u) : SGPT.PSH.SingularityLE η u := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp huv
  let D : ℝ := ε⁻¹ * (1 - ε) * C
  have hcancel : ε * (-D) + (1 - ε) * C = 0 := by
    dsimp [D]; field_simp; ring
  have hshift := POrderAffineRooftop.convexComb_add_const hε0 hε1 η v (-D) C
  simp only [hcancel, EReal.coe_zero, add_zero] at hshift
  have hηn := (isThetaPSH_iff_nativeThetaPotential θ η).mp hη
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hb : convexComb ε (fun x => η x + ((-D : ℝ) : EReal)) u ≤ u := by
    calc
      _ ≤ convexComb ε (fun x => η x + ((-D : ℝ) : EReal))
          (fun x => v x + (C : EReal)) := convexComb_mono hε0.le hε1.le le_rfl hC
      _ = convexComb ε η v := hshift
      _ ≤ u := hbar
  have hle := RelativeFullMassEpsilonBarrier.epsilonBarrier_le_reference
    hun.1 hun.2 (hηn.add_const (-D)).1 le_rfl hε0 hb
  exact (singularityLE_iff_exists_real _ _).mpr
    ⟨D, fun x => POrderAffineRooftop.le_add_coe_of_add_neg_le (hle x)⟩

/-- Required original prose: the actual affine envelope is additively more
singular than u; no output-order certificate is assumed. -/
theorem sourcePositiveAffineEnvelope_precedence (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    SGPT.PSH.SingularityLE
      (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) u := by
  obtain ⟨hE, _, hbar, _⟩ := sourcePositiveAffineEnvelope ω hu hv huv hpos ha
  exact sourceAffineBarrier_precedence hu hE huv (inv_pos.mpr (zero_lt_one.trans ha.1))
    (inv_lt_one_of_one_lt₀ ha.1) hbar

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The original pointwise-order variant follows from the same actual barrier. -/
theorem sourceAffineBarrier_le_left
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (huv : u ≤ v) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbar : convexComb ε η v ≤ u) : η ≤ u := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  exact RelativeFullMassEpsilonBarrier.epsilonBarrier_le_reference hun.1 hun.2
    ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).1 le_rfl hε0
    ((convexComb_mono hε0.le hε1.le le_rfl huv).trans hbar)

omit [ConnectedSpace M] in
/-- Finite translations preserve the SAME original diagonal mass. -/
theorem sourceAffine_mass_add_const (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ) :
    sourcePotentialNonPluripolarMeasure θ (fun x => u x + (c : EReal))
      (sourceThetaPSH_add_const hu c) univ = sourcePotentialNonPluripolarMeasure θ u hu univ :=
  RooftopConvexCombBarrierModelReduction.diagonalPotentialMass_add_const (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) c
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceThetaPSH_add_const hu c))

/-- Original additive-preceq equal-mass pairs admit the whole epsilon barrier.
The ordered native producer is applied only AFTER a manufactured finite shift;
its SAME produced potential is translated back with exactly cancelled weights. -/
theorem sourceEqualMass_epsilonBarrier (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hmass : sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ η : M → EReal, ∃ hη : (ofFixedModel n M).IsThetaPSH θ η,
      sourcePotentialNonPluripolarMeasure θ η hη univ =
        sourcePotentialNonPluripolarMeasure θ u hu univ ∧ convexComb ε η v ≤ u := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp huv
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hvC := hvn.add_const C
  have hm : diagonalPotentialMass (atlasClosedFormToNative θ) u hun =
      diagonalPotentialMass (atlasClosedFormToNative θ) (fun x => v x + (C : EReal)) hvC := by
    rw [RooftopConvexCombBarrierModelReduction.diagonalPotentialMass_add_const]
    exact hmass
  obtain ⟨η₀, hη₀, hmη, hbη⟩ := RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier
    ω (atlasClosedFormToNative θ) hvC hun hC hpos hm hε0 hε1
  let D : ℝ := ε⁻¹ * (1 - ε) * C
  have hηD := hη₀.add_const D
  refine ⟨fun x => η₀ x + (D : EReal),
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hηD, ?_, ?_⟩
  · exact (RooftopConvexCombBarrierModelReduction.diagonalPotentialMass_add_const (atlasClosedFormToNative θ) hη₀ D hηD).trans hmη
  · have hcancel : ε * D + (1 - ε) * (-C) = 0 := by
      dsimp [D]; field_simp; ring
    have hs := POrderAffineRooftop.convexComb_add_const hε0 hε1 η₀
      (fun x => v x + (C : EReal)) D (-C)
    simp only [hcancel, EReal.coe_zero, add_zero,
      RooftopEnvelopeNormalization.add_coe_add_neg] at hs
    exact hs.le.trans hbη

/-- The original pointwise variant for the ACTUAL produced affine envelope. -/
theorem sourcePositiveAffineEnvelope_le_left (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : u ≤ v) (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v) ≤ u := by
  have hp : SGPT.PSH.SingularityLE u v := MoreSingularOn.of_le (fun x _ => huv x)
  obtain ⟨hE, _, hbar, _⟩ := sourcePositiveAffineEnvelope ω hu hv hp hpos ha
  exact sourceAffineBarrier_le_left hu hE huv (inv_pos.mpr (zero_lt_one.trans ha.1))
    (inv_lt_one_of_one_lt₀ ha.1) hbar

/-- WHOLE original equal-positive-mass corollary, including BOTH clauses and
its printed EXPLICIT ordinary envelope witness, on the full additive-preceq domain. -/
theorem sourceEqualMass_affineEnvelope (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hmass : sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ hE : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb ε⁻¹ u v)),
      sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb ε⁻¹ u v)) hE univ =
          sourcePotentialNonPluripolarMeasure θ u hu univ ∧
      convexComb ε (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb ε⁻¹ u v)) v ≤ u := by
  have ha1 : 1 < ε⁻¹ := by
    have hi := mul_inv_cancel₀ hε0.ne'
    nlinarith
  have ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) ε⁻¹ :=
    ⟨ha1, Or.inr (Or.inl hmass)⟩
  obtain ⟨hE, _, hbE, _⟩ := sourcePositiveAffineEnvelope ω hu hv huv hpos ha
  obtain ⟨η, hη, hmη, hbη⟩ := sourceEqualMass_epsilonBarrier ω hu hv huv hpos hmass hε0 hε1
  have hηle : η ≤ sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb ε⁻¹ u v) := by
    rw [sourceObstacleEnvelope_eq_native]
    have hηn := (isThetaPSH_iff_nativeThetaPotential θ η).mp hη
    have hc := ConvexCombEnvelopeMass.mem_rooftopCompetitors_of_barrier
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) ha1 hηn (by simpa using hbη)
    exact le_rooftopEnvelope hηn hc.2
  refine ⟨hE, le_antisymm ?_ ?_, by simpa only [inv_inv] using hbE⟩
  · exact sourcePotentialNonPluripolarMass_mono ω hE hu
      (sourcePositiveAffineEnvelope_precedence ω hu hv huv hpos ha)
  · rw [← hmη]
    exact sourcePotentialNonPluripolarMass_mono ω hη hE
      (MoreSingularOn.of_le (fun x _ => hηle x))

end SGPT.PSH.VariableComplexAtlas
