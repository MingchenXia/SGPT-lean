import SGPT.Envelopes.SourcePositiveAffineEnvelopes
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes
import SGPT.PSH.SourceMixedPOrderMonotonicity
import SGPT.PSH.SourcePMassCharacterization

set_option autoImplicit false

/-! The entire original `thm:pathoenvelope`, for the actual source obstacle
envelope and genuine global P-order, retaining both infinite-upper cases. -/

noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}

/-- True global P-order internally supplies the positive-background comparison
for the actual affine producer, with every quantitative mass bound retained. -/
theorem sourcePOrderAffineEnvelope_basic (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    ∃ hE : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)),
      0 < sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ ∧
      convexComb a⁻¹ (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) v ≤ u ∧
      ∀ b : ℝ, a < b →
        SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
          (sourcePotentialNonPluripolarMeasure θ v hv univ) b →
        ENNReal.ofReal (((b - a) / b) ^ n) *
            sourcePotentialNonPluripolarMeasure θ u hu univ ≤
          sourcePotentialNonPluripolarMeasure θ
            (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hpq : sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure θ v hv univ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω
        (fun _ : Fin n => hu) (fun _ => hv) (fun _ => huv)
  have hadm (b : ℝ)
      (hb : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
        (sourcePotentialNonPluripolarMeasure θ v hv univ) b) :=
    (sourceAffineCoefficient_iff hupos hpq (sourceAffine_mass_lt_top ω hv).ne).mp hb
  have hfixed := (GlobalPComparison.sourcePOrder_iff_positive_background ω
    (atlasClosedFormToNative θ) hun hvn hupos hvpos).mp huv
  obtain ⟨hEn, hquant, hEpos, hbar⟩ := POrderAffineRooftop.xiaTheorem611 ω
    (atlasClosedFormToNative θ) hun hvn hupos hfixed (hadm a ha)
  have hEn' : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) := by
    simpa only [sourceObstacleEnvelope_eq_native] using hEn
  refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr hEn', ?_, ?_, ?_⟩
  · simpa only [sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure,
      diagonalPotentialMass] using hEpos
  · simpa only [sourceObstacleEnvelope_eq_native] using hbar
  · intro b hab hb
    have hb0 : 0 < b := zero_lt_one.trans hb.1
    have heq : 1 - a / b = (b - a) / b := by field_simp
    simpa only [heq, sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure,
      diagonalPotentialMass] using hquant b hab (hadm b hb)

/-- Actual ordinary-envelope concavity and finite-locus PSH comparison turn a
positive-weight barrier into genuine global P-order. -/
theorem sourcePOrderBarrier_precedence (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {w : M → EReal} (hw : (ofFixedModel n M).IsThetaPSH θ w)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (hwpos : 0 < sourcePotentialNonPluripolarMeasure θ w hw univ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hbar : convexComb t w v ≤ u) :
    GlobalPComparison.sourcePOrder (n := n) w u := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hwn := (isThetaPSH_iff_nativeThetaPotential θ w).mp hw
  have hfixed := (GlobalPComparison.sourcePOrder_iff_positive_background ω
    (atlasClosedFormToNative θ) hun hvn hupos hvpos).mp huv
  have hPuPv : sourceSingularityEnvelope θ u ≤ sourceSingularityEnvelope θ v := by
    simpa only [sourceSingularityEnvelope_eq_native, POrder.POrderWith] using hfixed
  have hPbar : convexComb t (sourceSingularityEnvelope θ w)
      (sourceSingularityEnvelope θ v) ≤ sourceSingularityEnvelope θ u :=
    (sourceOrdinaryEnvelope_convexComb_le hw hv ht0 ht1).trans
      (sourceOrdinaryEnvelope_mono (θ := θ) (MoreSingularOn.of_le fun x _ => hbar x))
  have hPwPu := sourceAffineBarrier_le_left
    (sourceOrdinaryEnvelope_genuine hu) (sourceOrdinaryEnvelope_genuine hw)
    hPuPv ht0 ht1 hPbar
  apply (GlobalPComparison.sourcePOrder_iff_positive_background ω
    (atlasClosedFormToNative θ) hwn hun hwpos hupos).mpr
  simpa only [sourceSingularityEnvelope_eq_native, POrder.POrderWith] using hPwPu

/-- The original actual affine envelope is globally P-below its first input;
its genuine membership, positive mass and barrier are manufactured internally. -/
theorem sourcePOrderAffineEnvelope_precedence (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    GlobalPComparison.sourcePOrder (n := n)
      (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) u := by
  obtain ⟨hE, hEpos, hbar, _⟩ := sourcePOrderAffineEnvelope_basic ω hu hv hupos hvpos huv ha
  exact sourcePOrderBarrier_precedence ω hu hv hE hupos hvpos hEpos huv
    (inv_pos.mpr (zero_lt_one.trans ha.1)) (inv_lt_one_of_one_lt₀ ha.1) hbar

/-- For global P-equivalent positive inputs every a>1 is allowed. The actual
quantitative mass bounds converge to the original mass, including n=0. -/
theorem sourcePOrderAffineEnvelope_of_sourcePEquivalent (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huv : GlobalPComparison.sourcePEquivalent (n := n) u v) {a : ℝ} (ha : 1 < a) :
    ∃ hE : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ =
        sourcePotentialNonPluripolarMeasure θ u hu univ ∧
      GlobalPComparison.sourcePEquivalent (n := n)
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) u ∧
      convexComb a⁻¹ (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) v ≤ u := by
  have hmass : sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω
        (fun _ : Fin n => hu) (fun _ => hv) (fun _ => huv)
  have hadm (b : ℝ) (hb : 1 < b) :
      SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
        (sourcePotentialNonPluripolarMeasure θ v hv univ) b :=
    ⟨hb, Or.inr (Or.inl hmass)⟩
  obtain ⟨hE, hEpos, hbar, hquant⟩ :=
    sourcePOrderAffineEnvelope_basic ω hu hv hupos hvpos huv.1 (hadm a ha)
  have hEu := sourcePOrderAffineEnvelope_precedence ω hu hv hupos hvpos huv.1 (hadm a ha)
  have hupper : sourcePotentialNonPluripolarMeasure θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ ≤
      sourcePotentialNonPluripolarMeasure θ u hu univ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω
        (fun _ : Fin n => hE) (fun _ => hu) (fun _ => hEu)
  have hlower : sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ := by
    let r : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
    let b : ℕ → ℝ := fun j => a * ((j : ℝ) + 2)
    have ha0 : 0 < a := zero_lt_one.trans ha
    have hden (j : ℕ) : 0 < (j : ℝ) + 2 := by positivity
    have hab (j : ℕ) : a < b j := by
      dsimp [b]
      nlinarith [mul_nonneg ha0.le (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hquantj (j : ℕ) : ENNReal.ofReal ((r j) ^ n) *
        sourcePotentialNonPluripolarMeasure θ u hu univ ≤
        sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ := by
      have hratio : (b j - a) / b j = r j := by
        dsimp [b, r]
        field_simp [ha0.ne', (hden j).ne']
      simpa only [hratio] using hquant (b j) (hab j) (hadm (b j) (ha.trans (hab j)))
    have hrec : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
      have h := (tendsto_add_atTop_iff_nat 1).2
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
    have hr : Tendsto r atTop (𝓝 1) := by
      simpa only [r, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hrec
    have hcoeff : Tendsto (fun j => ENNReal.ofReal ((r j) ^ n)) atTop (𝓝 1) := by
      simpa only [one_pow, ENNReal.ofReal_one, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto ((1 : ℝ) ^ n)).comp (hr.pow n)
    have hlim : Tendsto (fun j => ENNReal.ofReal ((r j) ^ n) *
        sourcePotentialNonPluripolarMeasure θ u hu univ) atTop
        (𝓝 (sourcePotentialNonPluripolarMeasure θ u hu univ)) := by
      simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoeff
        (Or.inr (sourceAffine_mass_lt_top ω hu).ne)
    exact le_of_tendsto' hlim hquantj
  have hEmass := le_antisymm hupper hlower
  exact ⟨hE, hEmass,
    (sourcePEquivalent_iff_diagonalMass_eq_of_positive ω hE hu hEpos hupos hEu).mpr hEmass,
    hbar⟩

/-- Entire original `thm:pathoenvelope`: the unchanged actual source envelope,
full printed coefficient interval, positive mass, global P-order and barrier,
and the additional global P-equivalence clause. -/
theorem sourcePOrderAffineEnvelope (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) {a : ℝ}
    (ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ u hu univ)
      (sourcePotentialNonPluripolarMeasure θ v hv univ) a) :
    ∃ hE : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)),
      0 < sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) hE univ ∧
      GlobalPComparison.sourcePOrder (n := n)
        (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) u ∧
      convexComb a⁻¹ (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) v ≤ u ∧
      (GlobalPComparison.sourcePEquivalent (n := n) u v →
        GlobalPComparison.sourcePEquivalent (n := n)
          (sourceRelativeEnvelope θ (fun _ => ⊤) (convexComb a u v)) u) := by
  obtain ⟨hE, hEpos, hbar, _⟩ := sourcePOrderAffineEnvelope_basic ω hu hv hupos hvpos huv ha
  refine ⟨hE, hEpos, sourcePOrderAffineEnvelope_precedence ω hu hv hupos hvpos huv ha, hbar, ?_⟩
  intro heq
  obtain ⟨_, _, hEq, _⟩ :=
    sourcePOrderAffineEnvelope_of_sourcePEquivalent ω hu hv hupos hvpos heq ha.1
  exact hEq

end SGPT.PSH.VariableComplexAtlas
