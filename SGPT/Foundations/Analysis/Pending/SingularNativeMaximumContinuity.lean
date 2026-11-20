import SGPT.Foundations.Analysis.Pending.ActualMaximumMassOrderedContinuity
import SGPT.Foundations.Analysis.Pending.ActualMovingOrderedSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz

set_option autoImplicit false

/-! # Actual joint maximum continuity in the defining native singularity topology

SGPT PDF0240--0241 Proposition 6.2.4, with an independent fixed-weight
arbitrary-filter proof. True actual upper maximum masses, the actual
moving ordered distance and actual positive background transport are
internally produced. No model sandwich or maximum-limit input is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativeMaximumContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MixedMass RelativeEnergy ThetaPshL1Topology ConvexCombEnvelopeMass
  GlobalMixedMassMonotone ActualMaximumMassAdmissibleBarrier
  ActualMaximumMassOrderedContinuity ActualMovingOrderedSingularityDistance
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassLipschitz
  SingularCanonicalSingularityMaximumCriterion SingularCanonicalSingularityOrderedMassCriterion
  SingularNativeBackgroundIndependence SingularPositiveCommonBackgroundExistence

noncomputable section

private theorem eventually_positive_admissible_of_common_limit
    {n : ℕ} {I : Type*} {F : Filter I} {L : ℝ≥0∞} {a b : I → ℝ≥0∞}
    (hL : 0 < L) (hLtop : L ≠ ⊤) (ha : Tendsto a F (𝓝 L))
    (hb : Tendsto b F (𝓝 L)) {q : ℝ} (hq : 1 < q) :
    ∀ᶠ i in F, 0 < a i ∧ IsAdmissibleWeight n (a i) (b i) q := by
  have hsub : Tendsto (fun i => b i - a i) F (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hb ha (Or.inr hLtop)
  have hmul : Tendsto (fun i => ENNReal.ofReal (q ^ n) * (b i - a i)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (q ^ n)) hsub (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [ha.eventually (lt_mem_nhds hL),
    hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne')),
    hb.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))] with i hi h1 h2
  exact ⟨hi, hq, h1.trans h2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_native_max_of_positive_targets
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    (a b : I → ThetaPshL1 θ.val) (p q : ThetaPshL1 θ.val)
    (hppos : 0 < diagonalPotentialMass θ p.val p.property)
    (hqpos : 0 < diagonalPotentialMass θ q.val q.property)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace p))
    (hb : Tendsto b F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace q)) :
    Tendsto (fun i => (⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨fun x => max (p.val x) (q.val x), IsThetaPshPotential.max p.property q.property⟩) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let A : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((a i).val x) (p.val x), IsThetaPshPotential.max (a i).property p.property⟩
  let B : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((b i).val x) (q.val x), IsThetaPshPotential.max (b i).property q.property⟩
  let X : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((A i).val x) ((B i).val x),
      IsThetaPshPotential.max (A i).property (B i).property⟩
  let Z : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩
  let t : ThetaPshL1 θ.val :=
    ⟨fun x => max (p.val x) (q.val x), IsThetaPshPotential.max p.property q.property⟩
  let mass : ThetaPshL1 θ.val → ℝ≥0∞ := fun w => diagonalPotentialMass θ w.val w.property
  have hfinite (w : ThetaPshL1 θ.val) : mass w ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => w.property.1)).ne
  have masslim {r : I → ThetaPshL1 θ.val} {s : ThetaPshL1 θ.val}
      (hr : Tendsto r F (𝓝 s)) : Tendsto (fun i => mass (r i)) F (𝓝 (mass s)) := by
    have h := ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto s).comp hr
    have he := (ENNReal.continuous_ofReal.tendsto (mass s).toReal).comp h
    simpa only [Function.comp_def, mass, ENNReal.ofReal_toReal (hfinite _)] using he
  have hA : Tendsto A F (𝓝 p) :=
    ((tendsto_native_iff_max_and_endpointMixedMass omega θ hbig F a p).mp ha).1
  have hB : Tendsto B F (𝓝 q) :=
    ((tendsto_native_iff_max_and_endpointMixedMass omega θ hbig F b q).mp hb).1
  have hma := masslim ha
  have hmb := masslim hb
  have hmA := masslim hA
  have hmB := masslim hB
  have hmX : Tendsto (fun i => mass (X i)) F (𝓝 (mass t)) :=
    tendsto_diagonalPotentialMass_max_of_le_of_diagonal_tendsto omega F
      p.property q.property (fun i => (A i).property) (fun i => (B i).property)
      (fun i x => le_max_right ((a i).val x) (p.val x))
      (fun i x => le_max_right ((b i).val x) (q.val x)) hppos hqpos hmA hmB
  have htpos : 0 < mass t := hppos.trans_le
    (globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => p.property) (fun _ : Fin n => t.property)
      (fun _ => MoreSingularOn.of_le fun x _ => le_max_left (p.val x) (q.val x)))
  have htX (i : I) : t.val ≤ (X i).val := fun x =>
    max_le_max (le_max_right ((a i).val x) (p.val x))
      (le_max_right ((b i).val x) (q.val x))
  have hXnative : Tendsto X F (𝓝 t) :=
    ((tendsto_native_iff_diagonalPotentialMass_of_le omega θ hbig F X t htX htpos)).mpr hmX
  have hZX (i : I) : (Z i).val ≤ (X i).val := fun x =>
    max_le_max (le_max_left ((a i).val x) (p.val x))
      (le_max_left ((b i).val x) (q.val x))
  let x : I → ℝ := fun i => (mass (X i)).toReal
  let y : I → ℝ := fun i => (mass (Z i)).toReal
  let m : ℝ := (mass t).toReal
  have hxlim : Tendsto x F (𝓝 m) := (ENNReal.continuousAt_toReal (hfinite t)).tendsto.comp hmX
  have hyx (i : I) : y i ≤ x i := ENNReal.toReal_mono (hfinite (X i))
    (globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => (Z i).property) (fun _ : Fin n => (X i).property)
      (fun _ => MoreSingularOn.of_le fun z _ => hZX i z))
  have hylim : Tendsto y F (𝓝 m) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hcoef : Tendsto (fun r : ℝ => ((1 - r⁻¹) ^ n) ^ 2 * m) atTop (𝓝 m) := by
      have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      simpa only [sub_zero, one_pow, one_mul] using
        ((((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow n).pow 2).mul_const m
    obtain ⟨r, hr, hrm⟩ := ((eventually_gt_atTop (1 : ℝ)).and
      (hcoef.eventually (lt_mem_nhds (sub_lt_self m hε)))).exists
    let c : ℝ := (1 - r⁻¹) ^ n
    have hc : 0 < c := pow_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hr)) n
    have hscaled : Tendsto (fun i => c ^ 2 * x i) F (𝓝 (c ^ 2 * m)) :=
      (tendsto_const_nhds (x := c ^ 2)).mul hxlim
    have hadmA : ∀ᶠ i in F, 0 < mass (a i) ∧ IsAdmissibleWeight n (mass (a i)) (mass (A i)) r :=
      eventually_positive_admissible_of_common_limit hppos (hfinite p) hma hmA hr
    have hadmB : ∀ᶠ i in F, 0 < mass (b i) ∧ IsAdmissibleWeight n (mass (b i)) (mass (B i)) r :=
      eventually_positive_admissible_of_common_limit hqpos (hfinite q) hmb hmB hr
    filter_upwards [hadmA, hadmB, hscaled.eventually (lt_mem_nhds hrm),
      hxlim.eventually (gt_mem_nhds (lt_add_of_pos_right m hε))] with i hiA hiB hilo hihi
    let Y : ThetaPshL1 θ.val :=
      ⟨fun z => max ((a i).val z) ((B i).val z), IsThetaPshPotential.max (a i).property (B i).property⟩
    have hm1 : ENNReal.ofReal c * mass (X i) ≤ mass Y :=
      diagonalPotentialMass_max_le_of_admissibleWeight omega (a i).property (A i).property
        (B i).property (fun z => le_max_left ((a i).val z) (p.val z)) hiA.1 hiA.2
    have hm2 : ENNReal.ofReal c * mass Y ≤ mass (Z i) := by
      have h := diagonalPotentialMass_max_le_of_admissibleWeight omega (b i).property (B i).property
        (a i).property (fun z => le_max_left ((b i).val z) (q.val z)) hiB.1 hiB.2
      simpa only [mass, Y, Z, max_comm] using h
    have h1 : c * x i ≤ (mass Y).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using
        ENNReal.toReal_mono (hfinite Y) hm1
    have h2 : c * (mass Y).toReal ≤ y i := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using
        ENNReal.toReal_mono (hfinite (Z i)) hm2
    have hbound : c ^ 2 * x i ≤ y i := by
      simpa only [pow_two, mul_assoc] using (mul_le_mul_of_nonneg_left h1 hc.le).trans h2
    have hlo : m - ε < y i := hilo.trans_le hbound
    have hup : y i < m + ε := (hyx i).trans_lt hihi
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hmZ : Tendsto (fun i => mass (Z i)) F (𝓝 (mass t)) := by
    have h := ENNReal.tendsto_ofReal hylim
    simpa only [y, m, ENNReal.ofReal_toReal (hfinite _)] using h
  have hdZX : Tendsto (fun i => dist (Z i) (X i)) F (𝓝 0) := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig] using
      tendsto_singularityDistance_toReal_zero_of_le_of_common_diagonal_limit omega θ hbig F
        (fun i => (Z i).property) (fun i => (X i).property) hZX htpos (hfinite t) hmZ hmX
  have hdXt : Tendsto (fun i => dist (X i) t) F (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hXnative
  change Tendsto Z F (𝓝 t)
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun i => dist_triangle (Z i) (X i) t)
    (by simpa only [zero_add] using hdZX.add hdXt)

/-- The genuine pointwise maximum preserves both incoming native limits for
every filter, including zero original target masses. -/
theorem tendsto_native_max
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    (a b : I → ThetaPshL1 θ.val) (p q : ThetaPshL1 θ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace p))
    (hb : Tendsto b F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace q)) :
    Tendsto (fun i => (⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨fun x => max (p.val x) (q.val x), IsThetaPshPotential.max p.property q.property⟩) := by
  let γ := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ p.property zero_lt_one
  let A : I → ThetaPshL1 γ.val := fun i =>
    ⟨(a i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (a i).property omega.isSemipositive⟩
  let B : I → ThetaPshL1 γ.val := fun i =>
    ⟨(b i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (b i).property omega.isSemipositive⟩
  let P : ThetaPshL1 γ.val :=
    ⟨p.val, LocalPotentials.isThetaPshPotential_add_of_semipositive p.property omega.isSemipositive⟩
  let Q : ThetaPshL1 γ.val :=
    ⟨q.val, LocalPotentials.isThetaPshPotential_add_of_semipositive q.property omega.isSemipositive⟩
  have hPpos : 0 < diagonalPotentialMass γ P.val P.property := by
    simpa only [HasPositivePotentialMass, one_smul] using
      hasPositivePotentialMass_add_smul omega p.property zero_lt_one
  have hQpos : 0 < diagonalPotentialMass γ Q.val Q.property := by
    simpa only [HasPositivePotentialMass, one_smul] using
      hasPositivePotentialMass_add_smul omega q.property zero_lt_one
  have hA : Tendsto A F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace P) :=
    (tendsto_native_iff_add_kahler omega θ hbig F a p).mp ha
  have hB : Tendsto B F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace Q) :=
    (tendsto_native_iff_add_kahler omega θ hbig F b q).mp hb
  have hmax := tendsto_native_max_of_positive_targets omega γ hγ F A B P Q hPpos hQpos hA hB
  exact (tendsto_native_iff_add_kahler omega θ hbig F
    (fun i => (⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩ : ThetaPshL1 θ.val))
    ⟨fun x => max (p.val x) (q.val x), IsThetaPshPotential.max p.property q.property⟩).mpr hmax

end
end SGPT.Foundations.Analysis.Pending.SingularNativeMaximumContinuity
