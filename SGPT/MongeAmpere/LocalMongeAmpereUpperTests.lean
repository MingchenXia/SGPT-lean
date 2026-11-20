import SGPT.MongeAmpere.LocalSmoothDensityBoundedMaxApproximation
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCompactMassEquality
import SGPT.Foundations.Analysis.Pending.BedfordTaylorLocalComparison
import SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
import SGPT.Foundations.Analysis.Pending.DeterminantTraceInf
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false

/-! Smooth upper tests for the actual local Monge–Ampère measures. -/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Laplacian
open scoped Topology ContDiff ComplexOrder MatrixOrder

namespace SGPT.MongeAmpere

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ}

/-- A genuine extended-real PSH function forces every smooth upper test to
have nonnegative Levi form and a positive semidefinite actual Hessian. -/
theorem complexHessian_posSemidef_of_smooth_upper_test
    {Ω : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) {x : ComplexModel n} (hx : x ∈ Ω)
    {q : ComplexModel n → ℝ} (hq : ContDiff ℝ ∞ q)
    (heq : u x = (q x : EReal))
    (hupper : ∀ᶠ z in 𝓝 x, u z ≤ (q z : EReal)) :
    (complexHessian q x).PosSemidef ∧ ∀ v, 0 ≤ leviForm q x v := by
  have hq2 : ContDiff ℝ 2 q :=
    hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlevi : ∀ v, 0 ≤ leviForm q x v := by
    intro v
    obtain ⟨V, hVo, hxV, huV⟩ := hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hupper (hVo.mem_nhds hxV))
    have hballUpper : ∀ z ∈ Metric.ball x ε, u z ≤ (q z : EReal) :=
      fun z hz => (hball hz).1
    have hballV : Metric.ball x ε ⊆ V := fun z hz => (hball hz).2
    obtain ⟨R, hR, L, hL, hLball, _, hdiscs⟩ :=
      exists_compact_affineClosedDisc_family isCompact_singleton Metric.isOpen_ball
        (singleton_subset_iff.mpr (Metric.mem_ball_self hε)) v
    have hmean : ∀ r ∈ Ioo 0 R,
        q x ≤ Real.circleAverage (fun ζ : ℂ => q (x + ζ • v)) 0 r := by
      intro r hr
      have hDball : affineClosedDisc x v r ⊆ Metric.ball x ε :=
        (hdiscs x (mem_singleton x) r hr.2.le).trans hLball
      obtain ⟨y, hy, hmax⟩ :=
        (hq.continuous.upperSemicontinuous.upperSemicontinuousOn
          (affineClosedDisc x v r)).exists_isMaxOn
        ⟨x, center_mem_affineClosedDisc x v hr.1.le⟩
        (isCompact_affineClosedDisc x v r)
      have hCq : ∀ z ∈ affineClosedDisc x v r, q z ≤ q y :=
        fun z hz => hmax hz
      have hCu : ∀ z ∈ affineClosedDisc x v r, u z ≤ (q y : EReal) := by
        intro z hz
        exact (hballUpper z (hDball hz)).trans (EReal.coe_le_coe_iff.mpr (hCq z hz))
      have hint : IntervalIntegrable
          (fun t : ℝ => q (x + circleMap 0 r t • v)) volume 0 (2 * Real.pi) := by
        apply Continuous.intervalIntegrable
        fun_prop
      apply (circleDeficit_coe_le_iff x v r (q y) hint
        (fun t => hCq _ (circle_mem_affineClosedDisc x v hr.1.le t))
        (hCq x (center_mem_affineClosedDisc x v hr.1.le))).mp
      have hsub := huV.submean x v r hr.1 (hDball.trans hballV) (q y) hCu
      rw [heq] at hsub
      exact (circleDeficit_antitone x v r (q y)
        (fun t => hballUpper _
          (hDball (circle_mem_affineClosedDisc x v hr.1.le t)))).trans hsub
    have hline : ContDiff ℝ 2 (fun ζ : ℂ => q (x + ζ • v)) :=
      hq2.comp (contDiff_const.add (complexLineLinear v).contDiff)
    have hlap : 0 ≤ Δ (fun ζ : ℂ => q (x + ζ • v)) 0 :=
      laplacian_nonneg_of_circleAverage_submean hline 0 hR (by simpa using hmean)
    simpa using (laplacian_complexLine_nonneg_iff hq2 x v 0).mp hlap
  exact ⟨SmoothDDCHessianPositivity.complexHessian_posSemidef_of_leviForm_nonneg
    hq2.contDiffAt hlevi, hlevi⟩

/-- Compact domination by a genuine smooth comparator gives comparison on
the same strict set for the actual canonical bounded BT measure. -/
theorem canonicalBedfordTaylorMeasure_gt_le_smoothMeasure (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u q : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hq : IsSmoothPshOn Ω q)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (houtside : ∀ z ∈ Ω, z ∉ K → u z ≤ q z) :
    canonicalBedfordTaylorMeasure Ω u hu {z | z ∈ Ω ∧ q z < u z} ≤
      smoothMeasure Ω q hq {z | z ∈ Ω ∧ q z < u z} := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := ComplexModel n
  let ν : Measure E := volume.restrict (Ω : Set E)
  let μ := canonicalBedfordTaylorMeasure Ω u hu
  let σ := smoothMeasure Ω q hq
  let S : ℝ → Set E := fun t => {z | z ∈ Ω ∧ u z = q z + t}
  have humE : Measurable (fun z : Ω => (u z : EReal)) := by
    have hsc : UpperSemicontinuousOn (fun z : Ω => (u z : EReal)) univ :=
      hu.1.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
        (fun z _ => z.property)
    exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hum : Measurable (fun z : Ω => u z) := by
    simpa only [EReal.toReal_coe] using humE.ereal_toReal
  have hqm : Measurable (fun z : Ω => q z) :=
    (continuousOn_iff_continuous_domRestrict.mp hq.1.continuousOn).measurable
  have hSm (t : ℝ) : MeasurableSet (S t) := by
    have hs := Ω.isOpen.measurableSet.subtype_image
      (measurableSet_eq_fun hum (hqm.add_const t))
    convert hs using 1
    ext z
    exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩,
      fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩
  have hdis : Pairwise (fun t s => Disjoint (S t) (S s)) := by
    intro t s hts
    apply disjoint_left.mpr
    intro z hzt hzs
    exact hts (by have := hzt.2.symm.trans hzs.2; linarith)
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := ν) hSm hdis
  have hlevels (j : ℕ) : ∃ t : ℝ,
      t ∈ {t | 0 < ν (S t)}ᶜ ∧ t ∈ Ioo (1 / ((j : ℝ) + 2)) (1 / ((j : ℝ) + 1)) := by
    apply (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo
    apply nonempty_Ioo.mpr
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose t ht using hlevels
  have ht0 (j : ℕ) : 0 < t j := (by positivity : 0 < 1 / ((j : ℝ) + 2)) |>.trans (ht j).2.1
  have htmono : Antitone t := by
    intro j k hjk
    rcases eq_or_lt_of_le hjk with rfl | hjk'
    · exact le_rfl
    · have hjkR : (j : ℝ) + 2 ≤ (k : ℝ) + 1 := by
        have : j + 1 ≤ k := Nat.succ_le_of_lt hjk'
        exact_mod_cast Nat.add_le_add_right this 1
      exact ((ht k).2.2.trans_le
        (one_div_le_one_div_of_le (by positivity) hjkR)).trans (ht j).2.1 |>.le
  have htlim : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun j => (ht0 j).le) (fun j => (ht j).2.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have htnull (j : ℕ) : ν (S (t j)) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp (ht j).1)
  obtain ⟨V', hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  let V : Opens E := ⟨V', hVo⟩
  have hVrel : RelativelyCompactIn V Ω := ⟨hVc, hVΩ⟩
  have hVsub : (V : Set E) ⊆ Ω := subset_closure.trans hVΩ
  have hσfinite : σ (V : Set E) < ⊤ :=
    (measure_mono (subset_closure : (V : Set E) ⊆ closure (V : Set E))).trans_lt
      (Pending.MongeAmpere.smoothMeasure_finiteOnCompacts hq hVc hVΩ)
  have hσac : σ ≪ ν := withDensity_absolutelyContinuous _ _
  let A : ℕ → Set E := fun j => {z | z ∈ Ω ∧ q z + t j < u z}
  have hAm (j : ℕ) : MeasurableSet (A j) := by
    have hs := Ω.isOpen.measurableSet.subtype_image
      (measurableSet_lt (hqm.add_const (t j)) hum)
    convert hs using 1
    ext z
    exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩,
      fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩
  have hAV (j : ℕ) : A j ⊆ (V : Set E) := by
    intro z hz
    apply hKV
    by_contra hzK
    have := houtside z hz.1 hzK
    linarith [ht0 j, hz.2]
  have hcompare (j : ℕ) : μ (A j) ≤ σ (A j) := by
    obtain ⟨hqs, hqsnp, hqssm⟩ := (truncationLimitMeasure_smooth_sub_const hq).2 (-t j)
    simp only [sub_neg_eq_add] at hqs hqsnp hqssm
    have hqb : IsLocallyBoundedPshOn Ω (fun z => q z + t j) :=
      LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
        hqs.2.1 hqs.1.continuousOn
    have hwb : IsLocallyBoundedPshOn Ω (fun z => max (u z) (q z + t j)) :=
      BedfordTaylor.IsLocallyBoundedPshOn.max hu hqb
    let ξ := canonicalBedfordTaylorMeasure Ω (fun z => max (u z) (q z + t j)) hwb
    have hξnp : truncationLimitMeasure Ω
        (fun z => ((max (u z) (q z + t j) : ℝ) : EReal)) hwb.1 = ξ :=
      truncationLimitMeasure_eq_canonical hwb
    have huNP : truncationLimitMeasure Ω (fun z => (u z : EReal)) hu.1 = μ :=
      truncationLimitMeasure_eq_canonical hu
    have hmass : ξ (V : Set E) = σ (V : Set E) := by
      have heq := BedfordTaylor.canonicalBedfordTaylorMeasure_eq_of_eqOn_compl
        hwb hqb hVrel hK hKV (fun z hz hzK =>
          max_eq_right ((houtside z hz hzK).trans (by linarith [ht0 j])))
      have hqBT : canonicalBedfordTaylorMeasure Ω (fun z => q z + t j) hqb = σ := by
        rw [← truncationLimitMeasure_eq_canonical hqb]
        exact hqsnp
      exact heq.trans (congrArg (fun m : Measure E => m (V : Set E)) hqBT)
    have hA : ξ.restrict (A j) = μ.restrict (A j) := by
      have hh := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq
        (fun _ : Fin n => hu.1) (fun _ => hqs.2.1)
        (fun _ => hu.1.max hqs.2.1)
      rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn,
        MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn] at hh
      simpa only [forall_const, ← EReal.coe_strictMono.monotone.map_max,
        EReal.coe_lt_coe_iff, hξnp, huNP] using hh
    let B : Set E := {z | z ∈ Ω ∧ u z < q z + t j}
    let Bv : Set E := B ∩ V
    have hBm : MeasurableSet B := by
      have hs := Ω.isOpen.measurableSet.subtype_image
        (measurableSet_lt hum (hqm.add_const (t j)))
      convert hs using 1
      ext z
      exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩,
        fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩
    have hBvm : MeasurableSet Bv := hBm.inter hVo.measurableSet
    have hB : ξ.restrict B = σ.restrict B := by
      have hh := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq
        (fun _ : Fin n => hqs.2.1) (fun _ => hu.1)
        (fun _ => hqs.2.1.max hu.1)
      rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn,
        MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn] at hh
      simpa only [forall_const, max_comm, ← EReal.coe_strictMono.monotone.map_max,
        EReal.coe_lt_coe_iff, hξnp, hqsnp] using hh
    have hBv : ξ.restrict Bv = σ.restrict Bv := by
      rw [← Measure.restrict_restrict_of_subset (inter_subset_left : Bv ⊆ B), hB,
        Measure.restrict_restrict_of_subset (inter_subset_left : Bv ⊆ B)]
    have hval (m₁ m₂ : Measure E) (D : Set E) (hDm : MeasurableSet D)
        (heq : m₁.restrict D = m₂.restrict D) : m₁ D = m₂ D := by
      have he := congrArg (fun m : Measure E => m D) heq
      simpa only [Measure.restrict_apply hDm, inter_self] using he
    have hAvalue : ξ (A j) = μ (A j) := hval _ _ _ (hAm j) hA
    have hBvalue : ξ Bv = σ Bv := hval _ _ _ hBvm hBv
    have hAB : Disjoint (A j) Bv := by
      apply disjoint_left.mpr
      intro z hzA hzB
      exact lt_asymm hzA.2 hzB.1.2
    have hσcontact : σ (S (t j)) = 0 := hσac (htnull j)
    have hcover : (V : Set E) ⊆ (A j ∪ Bv) ∪ S (t j) := by
      intro z hz
      rcases lt_trichotomy (q z + t j) (u z) with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hVsub hz, hlt⟩)
      · exact Or.inr ⟨hVsub hz, heq.symm⟩
      · exact Or.inl (Or.inr ⟨⟨hVsub hz, hgt⟩, hz⟩)
    have hsum : μ (A j) + σ Bv ≤ σ (A j) + σ Bv := by
      calc
        μ (A j) + σ Bv = ξ (A j ∪ Bv) := by
          rw [measure_union hAB hBvm, hAvalue, hBvalue]
        _ ≤ ξ (V : Set E) := measure_mono (union_subset (hAV j) inter_subset_right)
        _ = σ (V : Set E) := hmass
        _ ≤ σ ((A j ∪ Bv) ∪ S (t j)) := measure_mono hcover
        _ ≤ σ (A j ∪ Bv) + σ (S (t j)) := measure_union_le _ _
        _ = σ (A j) + σ Bv := by rw [hσcontact, add_zero, measure_union hAB hBvm]
    exact ENNReal.le_of_add_le_add_right
      ((measure_mono (inter_subset_right : Bv ⊆ (V : Set E))).trans_lt hσfinite).ne hsum
  have hAmono : Monotone A := by
    intro j k hjk z hz
    exact ⟨hz.1, by have := htmono hjk; have := hz.2; linarith⟩
  have hUnion : (⋃ j, A j) = {z | z ∈ Ω ∧ q z < u z} := by
    ext z
    constructor
    · intro hz'
      obtain ⟨j, hz⟩ := mem_iUnion.mp hz'
      exact ⟨hz.1, by linarith [ht0 j, hz.2]⟩
    · intro hz
      have htlt : ∀ᶠ j in atTop, t j < u z - q z :=
        htlim.eventually (gt_mem_nhds (sub_pos.mpr hz.2))
      obtain ⟨j, hj⟩ := htlt.exists
      exact mem_iUnion.mpr ⟨j, hz.1, by linarith⟩
  change μ {z | z ∈ Ω ∧ q z < u z} ≤ σ {z | z ∈ Ω ∧ q z < u z}
  rw [← hUnion, hAmono.measure_iUnion]
  exact iSup_le fun j => (hcompare j).trans (measure_mono (subset_iUnion A j))

end SGPT.MongeAmpere
