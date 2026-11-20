import SGPT.MongeAmpere.SmoothMongeAmpereMinkowski
import SGPT.Foundations.Analysis.Pending.MixedTruncationMaxLocality
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false

/-! Bounded maxima of the same genuine PSH input preserve an actual
Lebesgue Monge–Ampère lower bound at selected null smooth contact levels.
All non-pluripolar, bounded BT and smooth measures are the existing ones.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Distributions ComplexOrder MatrixOrder

namespace SGPT.MongeAmpere

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- Smooth potentials and every finite constant shift recover the actual
smooth density measure from the existing non-pluripolar prescription. -/
theorem truncationLimitMeasure_smooth_sub_const {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothPshOn Ω ρ) :
    truncationLimitMeasure Ω (fun z => (ρ z : EReal)) hρ.2.1 =
        smoothMeasure Ω ρ hρ ∧
      ∀ c : ℝ, ∃ hs : IsSmoothPshOn Ω (fun z => ρ z - c),
        truncationLimitMeasure Ω (fun z => ((ρ z - c : ℝ) : EReal)) hs.2.1 =
            smoothMeasure Ω ρ hρ ∧
          smoothMeasure Ω (fun z => ρ z - c) hs = smoothMeasure Ω ρ hρ := by
  have hbase {v : ComplexModel n → ℝ} (hv : IsSmoothPshOn Ω v) :
      truncationLimitMeasure Ω (fun z => (v z : EReal)) hv.2.1 =
        smoothMeasure Ω v hv := by
    have hvb : IsLocallyBoundedPshOn Ω v :=
      LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
        hv.2.1 hv.1.continuousOn
    rw [truncationLimitMeasure_eq_canonical hvb]
    have hint : ∀ φ : 𝓓(Ω, ℝ),
        (∫ z, φ z ∂canonicalBedfordTaylorMeasure Ω v hvb) =
          ∫ z, φ z ∂smoothMeasure Ω v hv := by
      intro φ
      obtain ⟨V, hVo, hφV, hVΩ, hVc⟩ :=
        exists_open_between_and_isCompact_closure
          φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
      let U : Opens (ComplexModel n) := ⟨V, hVo⟩
      have hU : RelativelyCompactIn U Ω := ⟨hVc, hVΩ⟩
      have hUΩ : U ≤ Ω := subset_closure.trans hVΩ
      have hvU : IsSmoothPshOn U v :=
        ⟨hv.1.mono hUΩ, hv.2.1.mono hUΩ, fun z hz => hv.2.2 z (hUΩ hz)⟩
      have ht := ((canonicalBedfordTaylorMeasure_spec Ω v hvb).2.2.2 U hU).2
        (fun _ => v) hvU.constantApproximation
        φ φ.continuous φ.hasCompactSupport hφV
      change Tendsto (fun _ : ℕ => ∫ z, φ z ∂smoothMeasure U v hvU) atTop
        (𝓝 (∫ z, φ z ∂canonicalBedfordTaylorMeasure Ω v hvb)) at ht
      have heq := (tendsto_nhds_unique tendsto_const_nhds ht).symm
      calc
        _ = ∫ z, φ z ∂smoothMeasure U v hvU := heq
        _ = ∫ z, φ z ∂smoothMeasure Ω v hv := by
          rw [← smoothMeasure_restrict hUΩ v hv hvU]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
            image_eq_zero_of_notMem_tsupport fun h => hz (hφV h)
    have heq := BedfordTaylor.restrict_eq_of_testFunction_integral_eq
      (fun _ hK hKΩ => canonicalBedfordTaylorMeasure_finiteOnCompacts hvb hK hKΩ)
      (fun _ hK hKΩ => Pending.MongeAmpere.smoothMeasure_finiteOnCompacts hv hK hKΩ) hint
    rw [Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (canonicalBedfordTaylorMeasure_compl Ω v hvb)),
      smoothMeasure_restrict le_rfl v hv hv] at heq
    exact heq
  refine ⟨hbase hρ, fun c => ?_⟩
  have hp : PlurisubharmonicOn (fun z => ((ρ z - c : ℝ) : EReal)) Ω := by
    have hc : PlurisubharmonicOn (fun _ : ComplexModel n => ((-c : ℝ) : EReal)) Ω :=
      fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z
    simpa only [sub_eq_add_neg, EReal.coe_add] using hρ.2.1.add hc
  have hH (z : ComplexModel n) (hz : z ∈ Ω) :
      complexHessian (fun w => ρ w - c) z = complexHessian ρ z := by
    have hρ2 : ContDiffAt ℝ 2 ρ z :=
      (hρ.1.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    simpa only [Pi.add_def, sub_eq_add_neg, complexHessian_const, add_zero] using
      complexHessian_add (u := ρ) (v := fun _ => -c) hρ2 contDiffAt_const
  have hs : IsSmoothPshOn Ω (fun z => ρ z - c) :=
    ⟨hρ.1.sub contDiffOn_const, hp, fun z hz => hH z hz ▸ hρ.2.2 z hz⟩
  have hsm : smoothMeasure Ω (fun z => ρ z - c) hs = smoothMeasure Ω ρ hρ := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    simp only [smoothDensity, hH z hz]
  exact ⟨hs, (hbase hs).trans hsm, hsm⟩

/-- S-finiteness selects increasing smooth-contact levels whose actual
Lebesgue contact sets are null, without making the original PSH input finite. -/
theorem exists_null_smooth_contact_levels {u : ComplexModel n → EReal}
    {ρ : ComplexModel n → ℝ} (hu : PlurisubharmonicOn u Ω)
    (hρ : ContDiffOn ℝ ∞ ρ Ω) :
    ∃ c : ℕ → ℝ, StrictMono c ∧
      (∀ j : ℕ, (j : ℝ) < c j ∧ c j < (j : ℝ) + 1) ∧
      Tendsto c atTop atTop ∧
      ∀ j, (volume.restrict (Ω : Set (ComplexModel n)))
        {z | z ∈ Ω ∧ u z = ((ρ z - c j : ℝ) : EReal)} = 0 := by
  classical
  let S : ℝ → Set (ComplexModel n) :=
    fun c => {z | z ∈ Ω ∧ u z = ((ρ z - c : ℝ) : EReal)}
  have hum : Measurable (fun z : Ω => u z) := by
    have hsc : UpperSemicontinuousOn (fun z : Ω => u z) univ :=
      hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
        (fun z _ => z.property)
    exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hρm : Measurable (fun z : Ω => ρ z) :=
    (continuousOn_iff_continuous_domRestrict.mp hρ.continuousOn).measurable
  have hS (c : ℝ) : MeasurableSet (S c) := by
    have hs := Ω.isOpen.measurableSet.subtype_image
      (measurableSet_eq_fun hum (hρm.sub_const c).coe_real_ereal)
    convert hs using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
  have hd : Pairwise (fun c d => Disjoint (S c) (S d)) := by
    intro c d hcd
    apply disjoint_left.mpr
    intro z hzc hzd
    have he : ρ z - c = ρ z - d := EReal.coe_injective (hzc.2.symm.trans hzd.2)
    exact hcd (by linarith)
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := volume.restrict (Ω : Set (ComplexModel n))) hS hd
  have hlevels (j : ℕ) : ∃ c : ℝ,
      c ∈ {c | 0 < (volume.restrict (Ω : Set (ComplexModel n))) (S c)}ᶜ ∧
        c ∈ Ioo (j : ℝ) ((j : ℝ) + 1) :=
    (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo
      (nonempty_Ioo.mpr (by linarith))
  choose c hc using hlevels
  refine ⟨c, ?_, fun j => (hc j).2, ?_, ?_⟩
  · intro j k hjk
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hjk
    exact (hc j).2.2.trans_le hjk' |>.trans (hc k).2.1
  · exact tendsto_atTop_mono (fun j => (hc j).2.1.le)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  · intro j
    exact nonpos_iff_eq_zero.mp (not_lt.mp (hc j).1)

/-- The literal maxima are locally bounded PSH, decrease to the same original
extended function, and preserve the two actual component lower bounds. -/
theorem exists_lower_bound_preserving_bounded_maxima (hn : 0 < n)
    {u : ComplexModel n → EReal} {ρ f : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn u Ω) (hρ : IsSmoothPshOn Ω ρ)
    (_hf : Measurable f) (_hf0 : ∀ z, 0 ≤ f z)
    (huf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ truncationLimitMeasure Ω u hu)
    (hρf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ smoothMeasure Ω ρ hρ) :
    ∃ c : ℕ → ℝ, StrictMono c ∧
      (∀ j : ℕ, (j : ℝ) < c j ∧ c j < (j : ℝ) + 1) ∧
      Tendsto c atTop atTop ∧
      (∀ j, (volume.restrict (Ω : Set (ComplexModel n)))
        {z | z ∈ Ω ∧ u z = ((ρ z - c j : ℝ) : EReal)} = 0) ∧
      ∃ (hmax : ∀ j, PlurisubharmonicOn
          (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) Ω)
        (hb : ∀ j, IsLocallyBoundedPshOn Ω
          (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal)),
        (∀ j z, z ∈ Ω →
          (((max (u z) ((ρ z - c j : ℝ) : EReal)).toReal : ℝ) : EReal) =
            max (u z) ((ρ z - c j : ℝ) : EReal)) ∧
        (∀ z ∈ Ω, Antitone (fun j => max (u z) ((ρ z - c j : ℝ) : EReal)) ∧
          Tendsto (fun j => max (u z) ((ρ z - c j : ℝ) : EReal)) atTop (𝓝 (u z))) ∧
        ∀ j, truncationLimitMeasure Ω
            (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) (hmax j) =
              canonicalBedfordTaylorMeasure Ω
                (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal) (hb j) ∧
          (volume.restrict (Ω : Set (ComplexModel n))).withDensity
            (fun z => ENNReal.ofReal (f z)) ≤
              truncationLimitMeasure Ω
                (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) (hmax j) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨c, hcmono, hcI, hctop, hcnull⟩ := exists_null_smooth_contact_levels hu hρ.1
  choose hs hsnp hssm using (truncationLimitMeasure_smooth_sub_const hρ).2
  let U : ℕ → ComplexModel n → EReal := fun j z => max (u z) ((ρ z - c j : ℝ) : EReal)
  have hmax (j : ℕ) : PlurisubharmonicOn (U j) Ω := hu.max (hs (c j)).2.1
  have hcoe (j : ℕ) (z : ComplexModel n) (hz : z ∈ Ω) :
      (((U j z).toReal : ℝ) : EReal) = U j z := by
    apply EReal.coe_toReal (hmax j z hz).ne_top
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le (le_max_right _ _))
  have hb (j : ℕ) : IsLocallyBoundedPshOn Ω (fun z => (U j z).toReal) := by
    refine ⟨fun z hz => (hmax j z hz).congr ?_, ?_⟩
    · filter_upwards [Ω.isOpen.mem_nhds hz] with w hw
      exact (hcoe j w hw).symm
    · intro z hz
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hz)
      have hclosed : closedBall z (r / 2) ⊆ Ω :=
        (closedBall_subset_ball (by linarith)).trans hball
      obtain ⟨A, hA0, hA⟩ := hu.exists_nonnegative_compact_upper_bound
        (isCompact_closedBall z (r / 2)) hclosed
      obtain ⟨D, hD⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
        (hρ.1.continuousOn.mono hclosed)
      have hc0 : 0 ≤ c j := (Nat.cast_nonneg j).trans (hcI j).1.le
      refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
        ball_subset_closedBall.trans hclosed, A + |D| + c j, ?_⟩
      intro w hw
      have hwK := ball_subset_closedBall hw
      have hwΩ := hclosed hwK
      have hDw' : |ρ w| ≤ D := by
        simpa only [Real.norm_eq_abs] using hD w hwK
      have hDw : |ρ w| ≤ |D| := hDw'.trans (le_abs_self D)
      have hlo : -|D| - c j ≤ (U j w).toReal := by
        apply EReal.coe_le_coe_iff.mp
        rw [hcoe j w hwΩ]
        exact (EReal.coe_le_coe_iff.mpr (by linarith [neg_le_of_abs_le hDw])).trans
          (le_max_right _ _)
      have hhi : (U j w).toReal ≤ A + |D| + c j := by
        apply EReal.coe_le_coe_iff.mp
        rw [hcoe j w hwΩ]
        exact max_le ((hA w hwK).trans (EReal.coe_le_coe_iff.mpr (by
          linarith [abs_nonneg D])))
          (EReal.coe_le_coe_iff.mpr (by linarith [le_of_abs_le hDw]))
      exact abs_le.mpr ⟨by linarith, hhi⟩
  refine ⟨c, hcmono, hcI, hctop, hcnull, hmax, hb, hcoe, ?_, ?_⟩
  · intro z _
    refine ⟨fun j k hjk => max_le_max le_rfl
      (EReal.coe_le_coe_iff.mpr (by linarith [hcmono.monotone hjk])), ?_⟩
    have hfloor : Tendsto (fun j => ρ z - c j) atTop atBot := by
      apply tendsto_atBot.mpr
      intro a
      filter_upwards [hctop.eventually (eventually_ge_atTop (ρ z - a))] with j hj
      linarith
    have hlimit : Tendsto (fun j => max (u z) ((ρ z - c j : ℝ) : EReal))
        atTop (𝓝 (max (u z) ⊥)) :=
      tendsto_const_nhds.max (EReal.tendsto_coe_atBot.comp hfloor)
    simpa only [max_eq_left bot_le] using hlimit
  · intro j
    have hbt : truncationLimitMeasure Ω (U j) (hmax j) =
        canonicalBedfordTaylorMeasure Ω (fun z => (U j z).toReal) (hb j) := by
      rw [← MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn (hmax j),
        MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn
          (fun _ => hb j) (fun _ => hmax j) (fun _ z hz => (hcoe j z hz).symm),
        MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_diagonal]
    refine ⟨hbt, ?_⟩
    let ν : Measure (ComplexModel n) := volume.restrict (Ω : Set (ComplexModel n))
    let μf := ν.withDensity (fun z => ENNReal.ofReal (f z))
    let A : Set (ComplexModel n) := {z | z ∈ Ω ∧ ((ρ z - c j : ℝ) : EReal) < u z}
    let B : Set (ComplexModel n) := {z | z ∈ Ω ∧ u z < ((ρ z - c j : ℝ) : EReal)}
    have hum : Measurable (fun z : Ω => u z) := by
      have hsc : UpperSemicontinuousOn (fun z : Ω => u z) univ :=
        hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
          (fun z _ => z.property)
      exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable
    have hsm : Measurable (fun z : Ω => ((ρ z - c j : ℝ) : EReal)) :=
      ((continuousOn_iff_continuous_domRestrict.mp hρ.1.continuousOn).measurable.sub_const
        (c j)).coe_real_ereal
    have hBm : MeasurableSet B := by
      have he := Ω.isOpen.measurableSet.subtype_image (measurableSet_lt hum hsm)
      convert he using 1
      ext z
      exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩, fun ⟨w, hw, hwz⟩ =>
        hwz ▸ ⟨w.property, hw⟩⟩
    have hdisj : Disjoint A B := by
      apply disjoint_left.mpr
      intro z hzA hzB
      exact lt_asymm hzA.2 hzB.2
    have hA : (truncationLimitMeasure Ω (U j) (hmax j)).restrict A =
        (truncationLimitMeasure Ω u hu).restrict A := by
      have h := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq
        (fun _ : Fin n => hu) (fun _ => (hs (c j)).2.1) (fun _ => hmax j)
      rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn (hmax j),
        MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hu] at h
      simpa only [forall_const] using h
    have hB : (truncationLimitMeasure Ω (U j) (hmax j)).restrict B =
        (smoothMeasure Ω ρ hρ).restrict B := by
      have hswap := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq
        (fun _ : Fin n => (hs (c j)).2.1) (fun _ => hu)
        (fun _ => (hs (c j)).2.1.max hu)
      rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn,
        MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn] at hswap
      simpa only [forall_const, max_comm, hsnp] using hswap
    have hweightac : μf ≪ ν := withDensity_absolutelyContinuous _ _
    have hweightΩ : ∀ᵐ z ∂μf, z ∈ Ω := by
      apply ae_iff.mpr
      apply hweightac
      change (volume.restrict (Ω : Set (ComplexModel n))) (Ω : Set (ComplexModel n))ᶜ = 0
      rw [Measure.restrict_apply Ω.isOpen.measurableSet.compl]
      simp only [compl_inter_self, measure_empty]
    have hweightcontact : μf {z | z ∈ Ω ∧ u z = ((ρ z - c j : ℝ) : EReal)} = 0 :=
      hweightac (hcnull j)
    have hweightne : ∀ᵐ z ∂μf,
        z ∉ {z | z ∈ Ω ∧ u z = ((ρ z - c j : ℝ) : EReal)} := by
      simpa only [ae_iff, not_not, mem_ofPred_eq] using hweightcontact
    have hweightres : μf.restrict (A ∪ B) = μf := by
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [hweightΩ, hweightne] with z hz hzne
      rcases lt_or_gt_of_ne (fun he => hzne ⟨hz, he⟩) with hlt | hgt
      · exact Or.inr ⟨hz, hlt⟩
      · exact Or.inl ⟨hz, hgt⟩
    calc
      μf = μf.restrict (A ∪ B) := hweightres.symm
      _ = μf.restrict A + μf.restrict B := Measure.restrict_union hdisj hBm
      _ ≤ (truncationLimitMeasure Ω (U j) (hmax j)).restrict A +
          (truncationLimitMeasure Ω (U j) (hmax j)).restrict B := by
        rw [hA, hB]
        exact add_le_add (Measure.restrict_mono_measure huf A)
          (Measure.restrict_mono_measure hρf B)
      _ = (truncationLimitMeasure Ω (U j) (hmax j)).restrict (A ∪ B) :=
        (Measure.restrict_union hdisj hBm).symm
      _ ≤ _ := Measure.restrict_le_self

/-- A normalized strict quadratic supplies the second component lower bound
internally, so only the original actual NP lower bound is assumed. -/
theorem exists_quadratic_lower_bound_preserving_bounded_maxima (hn : 0 < n)
    {u : ComplexModel n → EReal} {f : ComplexModel n → ℝ} {F : ℝ}
    (hu : PlurisubharmonicOn u Ω) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (_hF0 : 0 ≤ F) (hfF : ∀ z ∈ Ω, f z ≤ F)
    (huf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ truncationLimitMeasure Ω u hu) :
    let κ : ℝ := (n.factorial : ℝ) / Real.pi ^ n
    let C : ℝ := max 1 (F / κ)
    let ρ : ComplexModel n → ℝ := fun z => C * ‖z‖ ^ 2
    1 ≤ C ∧ ∃ hρ : IsSmoothPshOn Ω ρ,
      (∀ z, complexHessian ρ z = (C : ℂ) • 1 ∧
        (complexHessian ρ z).PosDef ∧ smoothDensity ρ z = κ * C ^ n) ∧
      (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (f z)) ≤ smoothMeasure Ω ρ hρ ∧
      ∃ c : ℕ → ℝ, StrictMono c ∧
        (∀ j : ℕ, (j : ℝ) < c j ∧ c j < (j : ℝ) + 1) ∧
        Tendsto c atTop atTop ∧
        (∀ j, (volume.restrict (Ω : Set (ComplexModel n)))
          {z | z ∈ Ω ∧ u z = ((ρ z - c j : ℝ) : EReal)} = 0) ∧
        ∃ (hmax : ∀ j, PlurisubharmonicOn
            (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) Ω)
          (hb : ∀ j, IsLocallyBoundedPshOn Ω
            (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal)),
          (∀ j z, z ∈ Ω →
            (((max (u z) ((ρ z - c j : ℝ) : EReal)).toReal : ℝ) : EReal) =
              max (u z) ((ρ z - c j : ℝ) : EReal)) ∧
          (∀ z ∈ Ω, Antitone (fun j => max (u z) ((ρ z - c j : ℝ) : EReal)) ∧
            Tendsto (fun j => max (u z) ((ρ z - c j : ℝ) : EReal)) atTop (𝓝 (u z))) ∧
          ∀ j, truncationLimitMeasure Ω
              (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) (hmax j) =
                canonicalBedfordTaylorMeasure Ω
                  (fun z => (max (u z) ((ρ z - c j : ℝ) : EReal)).toReal) (hb j) ∧
            (volume.restrict (Ω : Set (ComplexModel n))).withDensity
              (fun z => ENNReal.ofReal (f z)) ≤
                truncationLimitMeasure Ω
                  (fun z => max (u z) ((ρ z - c j : ℝ) : EReal)) (hmax j) := by
  classical
  dsimp only
  let κ : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  let C : ℝ := max 1 (F / κ)
  let ρ : ComplexModel n → ℝ := fun z => C * ‖z‖ ^ 2
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have he : ρ = C • (fun z : ComplexModel n => ‖z‖ ^ 2) := by
    funext z
    rfl
  have hH (z : ComplexModel n) : complexHessian ρ z = (C : ℂ) • 1 := by
    rw [he, complexHessian_smul (contDiff_norm_sq ℝ).contDiffAt C,
      complexHessian_norm_sq]
  have hPD (z : ComplexModel n) : (complexHessian ρ z).PosDef := by
    rw [hH z]
    exact Matrix.PosDef.one.smul (show (0 : ℂ) < (C : ℂ) by exact_mod_cast hC0)
  have hp : PlurisubharmonicOn (fun z => (ρ z : EReal)) Ω := by
    simpa only [ρ, EReal.coe_mul] using (isSmoothPshOn_norm_sq Ω).2.1.const_mul hC0
  have hρ : IsSmoothPshOn Ω ρ :=
    ⟨(contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn, hp,
      fun z _ => (hPD z).posSemidef⟩
  have hD (z : ComplexModel n) : smoothDensity ρ z = κ * C ^ n := by
    simp only [smoothDensity, hH z, Matrix.det_smul, Fintype.card_fin,
      Matrix.det_one, mul_one, ← Complex.ofReal_pow, Complex.ofReal_re]
    rfl
  have hCp : C ≤ C ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hC1 (Nat.succ_le_of_lt hn)
  have hFC : F ≤ κ * C := by
    have h := (div_le_iff₀ hκ).mp (le_max_right 1 (F / κ))
    simpa only [mul_comm] using h
  have hρf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ smoothMeasure Ω ρ hρ := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    apply ENNReal.ofReal_le_ofReal
    rw [hD z]
    exact (hfF z hz).trans (hFC.trans (mul_le_mul_of_nonneg_left hCp hκ.le))
  exact ⟨hC1, hρ, fun z => ⟨hH z, hPD z, hD z⟩, hρf,
    exists_lower_bound_preserving_bounded_maxima hn hu hρ hf hf0 huf hρf⟩

end SGPT.MongeAmpere
