import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.OrderedNativeDivisorialLelongLimit

set_option autoImplicit false

/-! # Ordered native limits under natural general analytic modifications -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationOrderedNativeLelongLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass MixedMass
  DemaillyApproximantDivisorialLelong ThetaPshL1Topology
  SingularCanonicalSingularityDistance AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback

noncomputable section

private theorem eventually_admissible {n : ℕ} {I : Type*} (F : Filter I)
    {b : I → ℝ≥0∞} {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hb : Tendsto b F (𝓝 L)) {t : ℝ} (ht : 1 < t) :
    ∀ᶠ i in F, ConvexCombEnvelopeMass.IsAdmissibleWeight n L (b i) t := by
  have hsub : Tendsto (fun i => b i - L) F (𝓝 0) := by
    have := ENNReal.Tendsto.sub hb (tendsto_const_nhds (x := L)) (Or.inr hLtop)
    simpa using this
  have hmul : Tendsto (fun i => ENNReal.ofReal (t ^ n) * (b i - L)) F (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) hsub
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have h1 : ∀ᶠ i in F, ENNReal.ofReal (t ^ n) * (b i - L) < L / 2 :=
    hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne'))
  have h2 : ∀ᶠ i in F, L / 2 < b i :=
    hb.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))
  filter_upwards [h1, h2] with i hi1 hi2
  exact ⟨ht, hi1.trans hi2⟩

private theorem scalar_tendsto {I : Type*} (F : Filter I) {a : I → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hupper : ∀ i, a i ≤ L)
    (hbound : ∀ C : ℕ, 2 ≤ C → ∀ᶠ i in F,
      ENNReal.ofReal (C : ℝ) * L ≤ ENNReal.ofReal B +
        ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * a i) :
    Tendsto a F (𝓝 L) := by
  have ha (i : I) : a i ≠ ⊤ := ne_top_of_le_ne_top hL (hupper i)
  have hr : Tendsto (fun i => (a i).toReal) F (𝓝 L.toReal) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro r hr
      have hε : 0 < L.toReal - r := sub_pos.mpr hr
      obtain ⟨C, hC⟩ := exists_nat_gt (B / (L.toReal - r) + 2)
      have htwo : (2 : ℝ) < C :=
        lt_of_le_of_lt (le_add_of_nonneg_left (div_nonneg hB hε.le)) hC
      have hC2 : 2 ≤ C := by exact_mod_cast htwo.le
      have hdiv : B / (L.toReal - r) < C :=
        lt_of_le_of_lt (le_add_of_nonneg_right (by norm_num)) hC
      have hCe : B < (C : ℝ) * (L.toReal - r) := (div_lt_iff₀ hε).mp hdiv
      filter_upwards [hbound C hC2] with i hi
      have hi' : (C : ℝ) * L.toReal ≤ B + ((C - 1 : ℕ) : ℝ) * (a i).toReal := by
        have hf1 : ENNReal.ofReal (C : ℝ) * L ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
        have hfm : ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * a i ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha i)
        have hf2 : ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) * a i ≠ ⊤ := by
          exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hfm⟩
        have := (ENNReal.toReal_le_toReal hf1 hf2).mpr hi
        simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hfm, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Nat.cast_nonneg C), ENNReal.toReal_ofReal hB,
          ENNReal.toReal_ofReal (Nat.cast_nonneg (C - 1))] using this
      have hc : ((C - 1 : ℕ) : ℝ) = (C : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc] at hi'
      have hapos : 0 ≤ (a i).toReal := ENNReal.toReal_nonneg
      have hCpos : 0 < (C : ℝ) := by exact_mod_cast (by omega : 0 < C)
      nlinarith
    · intro r hr
      exact Eventually.of_forall fun i =>
        ((ENNReal.toReal_le_toReal (ha i) hL).mpr (hupper i)).trans_lt hr
  have ht := ENNReal.continuous_ofReal.tendsto L.toReal |>.comp hr
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (ha _), ENNReal.ofReal_toReal hL]
    using ht

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Native convergence on the original manifold supplies actual Rooftop
barriers; genuine composition gives the scalar limit on every upstairs set. -/
theorem tendsto_divisorialLelongNumber_comp_of_ordered_native
    (omega : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hle : ∀ i, u.val ≤ (w i).val)
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
  have huπ := isThetaPshPotential_comp_of_isAnalyticModification hπ θ u.property
  have hmass :=
    (SingularCanonicalSingularityOrderedMassCriterion.tendsto_native_iff_diagonalPotentialMass_of_le
      omega θ hbig F w u hle hpos).mp hlim
  have hfinite : diagonalPotentialMass θ u.val u.property ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin (m + 1) => u.property.1)).ne
  obtain ⟨B, hB, hbarrier⟩ :=
    DivisorialRooftopLelongEstimate.exists_uniform_divisorial_rooftop_estimate β
  have hupper (i : I) : divisorialLelongNumber m (fun y => (w i).val (π y)) E ≤
      divisorialLelongNumber m (fun y => u.val (π y)) E := by
    unfold divisorialLelongNumber
    exact iInf_mono fun x => iInf_mono fun _ =>
      KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall fun y => hle i (π y))
  have hbound (C : ℕ) (hC : 2 ≤ C) : ∀ᶠ i in F,
      ENNReal.ofReal (C : ℝ) * divisorialLelongNumber m (fun y => u.val (π y)) E ≤
        ENNReal.ofReal B + ENNReal.ofReal ((C - 1 : ℕ) : ℝ) *
          divisorialLelongNumber m (fun y => (w i).val (π y)) E := by
    have ht : (1 : ℝ) < ((2 * C : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 < 2 * C)
    have hadm := eventually_admissible (n := m + 1) F hpos hfinite hmass ht
    filter_upwards [hadm] with i hi
    obtain ⟨h, hh, hbar, _⟩ := PositiveCurrentRooftop.exists_positiveRooftop
      omega θ hbig u.property (w i).property (hle i) hpos (by omega : 1 ≤ C) hi
    exact hbarrier (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hh)
      (isThetaPshPotential_comp_of_isAnalyticModification hπ θ (w i).property)
      hC (fun y => hbar (π y)) E
  by_cases hE : E.Nonempty
  · obtain ⟨x, hx⟩ := hE
    have hν : divisorialLelongNumber m (fun y => u.val (π y)) E ≠ ⊤ :=
      ne_top_of_le_ne_top
        (LelongNumberAdditivity.lelongNumber_ne_top (Nat.succ_pos m)
          huπ.1.quasiPlurisubharmonic huπ.2 x)
        (divisorialLelongNumber_le hx)
    exact scalar_tendsto F hν hB hupper hbound
  · have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    simpa only [he, divisorialLelongNumber, Set.mem_empty_iff_false, iInf_false,
      iInf_top] using (tendsto_const_nhds (x := (⊤ : ℝ≥0∞)) :
        Tendsto (fun _ : I => (⊤ : ℝ≥0∞)) F (𝓝 ⊤))

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationOrderedNativeLelongLimit
