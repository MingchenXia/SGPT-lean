import SGPT.Foundations.Analysis.Pending.AnalyticModificationOrderedNativeLelongLimit
import SGPT.Foundations.Analysis.Pending.PositiveNativeDivisorialLelongLimit

set_option autoImplicit false

/-! # General positive native limits under natural analytic modifications -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationPositiveNativeLelongLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass MixedMass
  DemaillyApproximantDivisorialLelong ThetaPshL1Topology
  SingularCanonicalSingularityDistance AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback

noncomputable section

private theorem eventually_admissible_moving {n : ℕ} {I : Type*} (F : Filter I)
    {a b : I → ℝ≥0∞} {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (ha : Tendsto a F (𝓝 L)) (hb : Tendsto b F (𝓝 L)) {t : ℝ} (ht : 1 < t) :
    ∀ᶠ i in F, 0 < a i ∧ ConvexCombEnvelopeMass.IsAdmissibleWeight n (a i) (b i) t := by
  have hsub : Tendsto (fun i => b i - a i) F (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hb ha (Or.inr hLtop)
  have hmul : Tendsto (fun i => ENNReal.ofReal (t ^ n) * (b i - a i)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (t ^ n)) hsub (Or.inr ENNReal.ofReal_ne_top)
  have h1 := hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne'))
  have h2 := hb.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))
  have h3 := ha.eventually (lt_mem_nhds hL)
  filter_upwards [h1, h2, h3] with i hi1 hi2 hi3
  exact ⟨hi3, ht, hi1.trans hi2⟩

private theorem scalar_tendsto {I : Type*} (F : Filter I) {a z : I → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ⊤) (ha : ∀ i, a i ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hz : Tendsto z F (𝓝 L)) (hle : ∀ i, z i ≤ a i)
    (hbound : ∀ C : ℕ, 2 ≤ C → ∀ᶠ i in F,
      ENNReal.ofReal (C : ℝ) * a i ≤ ENNReal.ofReal B +
        ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * L) :
    Tendsto a F (𝓝 L) := by
  have hzfinite (i : I) : z i ≠ ⊤ := ne_top_of_le_ne_top (ha i) (hle i)
  have hzreal : Tendsto (fun i => (z i).toReal) F (𝓝 L.toReal) :=
    (ENNReal.tendsto_toReal hL).comp hz
  have hr : Tendsto (fun i => (a i).toReal) F (𝓝 L.toReal) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro r hr
      filter_upwards [hzreal.eventually (lt_mem_nhds hr)] with i hi
      exact hi.trans_le ((ENNReal.toReal_le_toReal (hzfinite i) (ha i)).mpr (hle i))
    · intro r hr
      have hε : 0 < r - L.toReal := sub_pos.mpr hr
      obtain ⟨C, hC⟩ := exists_nat_gt (B / (r - L.toReal) + 2)
      have htwo : (2 : ℝ) < C :=
        lt_of_le_of_lt (le_add_of_nonneg_left (div_nonneg hB hε.le)) hC
      have hC2 : 2 ≤ C := by exact_mod_cast htwo.le
      have hdiv : B / (r - L.toReal) < C :=
        lt_of_le_of_lt (le_add_of_nonneg_right (by norm_num)) hC
      have hCe : B < (C : ℝ) * (r - L.toReal) := (div_lt_iff₀ hε).mp hdiv
      filter_upwards [hbound C hC2] with i hi
      have hi' : (C : ℝ) * (a i).toReal ≤ B + ((C - 1 : ℕ) : ℝ) * L.toReal := by
        have hf1 : ENNReal.ofReal (C : ℝ) * a i ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha i)
        have hfm : ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * L ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
        have hf2 : ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * L ≠ ⊤ :=
          ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hfm⟩
        have := (ENNReal.toReal_le_toReal hf1 hf2).mpr hi
        simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hfm, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Nat.cast_nonneg C), ENNReal.toReal_ofReal hB,
          ENNReal.toReal_ofReal (Nat.cast_nonneg (C - 1))] using this
      have hc : ((C - 1 : ℕ) : ℝ) = (C : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc] at hi'
      have hLpos : 0 ≤ L.toReal := ENNReal.toReal_nonneg
      have hCpos : 0 < (C : ℝ) := by exact_mod_cast (by omega : 0 < C)
      nlinarith
  have ht := ENNReal.continuous_ofReal.tendsto L.toReal |>.comp hr
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (ha _), ENNReal.ofReal_toReal hL]
    using ht

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- No order or model hypothesis is required: actual maximum continuity and
both actual mass limits internally supply every positive Rooftop barrier. -/
theorem tendsto_divisorialLelongNumber_comp_of_native_positive
    (omega : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) {I : Type*} (F : Filter I)
    (w : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : 0 < diagonalPotentialMass θ u.val u.property)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (E : Set Y) :
    Tendsto (fun i => divisorialLelongNumber m (fun y => (w i).val (π y)) E) F
      (𝓝 (divisorialLelongNumber m (fun y => u.val (π y)) E)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  let z : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((w i).val x) (u.val x), IsThetaPshPotential.max (w i).property u.property⟩
  have hzlim : Tendsto z F (𝓝 u) := by
    have hmax := SingularNativeMaximumContinuity.tendsto_native_max
      omega θ hbig F w (fun _ => u) u u hlim tendsto_const_nhds
    have heq : (⟨fun x => max (u.val x) (u.val x),
        IsThetaPshPotential.max u.property u.property⟩ : ThetaPshL1 θ.val) = u := by
      ext x
      exact max_self _
    rw [heq] at hmax
    exact hmax
  have hfinite (v : ThetaPshL1 θ.val) : diagonalPotentialMass θ v.val v.property ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin (m + 1) => v.property.1)).ne
  have masslim {a : I → ThetaPshL1 θ.val} {p : ThetaPshL1 θ.val}
      (ha : Tendsto a F (𝓝 p)) : Tendsto (fun i => diagonalPotentialMass θ (a i).val
        (a i).property) F (𝓝 (diagonalPotentialMass θ p.val p.property)) := by
    have h := ((SingularCanonicalSingularityMassLipschitz.diagonalPotentialMass_uniformContinuous
      omega θ hbig).continuous.tendsto p).comp ha
    have he := (ENNReal.continuous_ofReal.tendsto
      (diagonalPotentialMass θ p.val p.property).toReal).comp h
    simpa only [Function.comp_def, ENNReal.ofReal_toReal (hfinite _)] using he
  have hmassw := masslim hlim
  have hmassz := masslim hzlim
  have huz (i : I) : u.val ≤ (z i).val := fun x => le_max_right _ _
  have hwz (i : I) : (w i).val ≤ (z i).val := fun x => le_max_left _ _
  have hνz := AnalyticModificationOrderedNativeLelongLimit.tendsto_divisorialLelongNumber_comp_of_ordered_native
    omega θ hbig hπ F z u huz hpos hzlim E
  have hνorder {a b : Y → EReal} (hab : a ≤ b) :
      divisorialLelongNumber m b E ≤ divisorialLelongNumber m a E := by
    unfold divisorialLelongNumber
    exact iInf_mono fun x => iInf_mono fun _ =>
      KahlerCurrentMax.lelongNumber_le_of_eventually_le (Eventually.of_forall hab)
  obtain ⟨B, hB, hbarrier⟩ :=
    DivisorialRooftopLelongEstimate.exists_uniform_divisorial_rooftop_estimate β
  have hbound (C : ℕ) (hC : 2 ≤ C) : ∀ᶠ i in F,
      ENNReal.ofReal (C : ℝ) * divisorialLelongNumber m (fun y => (w i).val (π y)) E ≤
        ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) *
          divisorialLelongNumber m (fun y => u.val (π y)) E := by
    have ht : (1 : ℝ) < ((2 * C : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 < 2 * C)
    have hadm := eventually_admissible_moving (n := m + 1) F
      hpos (hfinite u) hmassw hmassz ht
    filter_upwards [hadm] with i hi
    obtain ⟨h, hh, hbar, _⟩ := PositiveCurrentRooftop.exists_positiveRooftop
      omega θ hbig (w i).property (z i).property (hwz i) hi.1 (by omega : 1 ≤ C) hi.2
    apply (hbarrier (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hh)
      (isThetaPshPotential_comp_of_isAnalyticModification hπ θ (z i).property)
      hC (fun y => hbar (π y)) E).trans
    gcongr
    exact hνorder (fun y => huz i (π y))
  by_cases hE : E.Nonempty
  · obtain ⟨x, hx⟩ := hE
    have hνfinite (v : ThetaPshL1 θ.val) : divisorialLelongNumber m (fun y => v.val (π y)) E ≠ ⊤ :=
      ne_top_of_le_ne_top
        (LelongNumberAdditivity.lelongNumber_ne_top (Nat.succ_pos m)
          (isThetaPshPotential_comp_of_isAnalyticModification hπ θ v.property).1.quasiPlurisubharmonic
          (isThetaPshPotential_comp_of_isAnalyticModification hπ θ v.property).2 x)
        (divisorialLelongNumber_le hx)
    exact scalar_tendsto F (hνfinite u) (fun i => hνfinite (w i)) hB hνz
      (fun i => hνorder (fun y => hwz i (π y))) hbound
  · have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    simpa only [he, divisorialLelongNumber, Set.mem_empty_iff_false, iInf_false,
      iInf_top] using (tendsto_const_nhds (x := (⊤ : ℝ≥0∞)) :
        Tendsto (fun _ : I => (⊤ : ℝ≥0∞)) F (𝓝 ⊤))

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationPositiveNativeLelongLimit
