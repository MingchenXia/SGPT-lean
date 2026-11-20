import SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityDecreasingConvergence
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Actual global capacity convergence of unbounded decreasing potentials

The capacity input of Darvas--Di Nezza--Lu Theorem 2.4, which cites
Guedj--Zeriahi Proposition 3.7. Actual compact smooth domination,
unbounded quasicontinuity, outer-zero pole covers and compact Dini remove
global boundedness and same-type assumptions. No Big or semipositivity
hypothesis on the original background, connectedness or n>0 is imposed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualUnboundedDecreasingCapacity

open FirstPass FirstPass.PositiveClasses ThetaCapacity CapacityWeightedConvergence
  ThetaCapacityDecreasingConvergence PluripolarOuterCapacity PluripolarCapacityZero

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem normalized_genuine
    (omega : KahlerBackground n M) {α : ClosedRealOneOneForm n M}
    {A b : ℝ} (hA : 0 < A) (hdom : (-α + A • omega.form).val.IsSemipositive)
    {u : M → EReal} (hu : IsThetaPshPotential α.val u) :
    IsThetaPshPotential omega.form.val (fun x => ((A⁻¹ : ℝ) : EReal) * (u x - (b : EReal))) := by
  have he : α + (-α + A • omega.form) = A • omega.form := by abel
  have hbg : IsThetaPshPotential (A • omega.form).val (fun x => u x - (b : EReal)) := by
    simpa only [he] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hu.sub_const b) hdom
  have hq := RestrictedApproximantComparison.isThetaPshPotential_smul hbg (inv_pos.mpr hA)
  have hf : A⁻¹ • (A • omega.form) = omega.form := by
    rw [smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
  simpa only [hf] using hq

private theorem normalized_toReal {A b : ℝ} {v : EReal} (hvt : v ≠ ⊤) (hvb : v ≠ ⊥) :
    (((A⁻¹ : ℝ) : EReal) * (v - (b : EReal))).toReal = A⁻¹ * (v.toReal - b) := by
  have he : ((A⁻¹ * (v.toReal - b) : ℝ) : EReal) =
      ((A⁻¹ : ℝ) : EReal) * (v - (b : EReal)) := by
    rw [EReal.coe_mul, EReal.coe_sub, EReal.coe_toReal hvt hvb]
  rw [← he, EReal.toReal_coe]

omit [BorelSpace M] in
private theorem capacity_gap_tendsto_off_outerZero
    (omega : KahlerBackground n M) {f : ℕ → M → ℝ} {g : M → ℝ} {Z : Set M}
    (hZ : OuterCapacityZero omega Z)
    (hq : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (f j))
    (hg : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) g)
    (hle : ∀ j x, x ∉ Z → g x ≤ f j x)
    (ha : ∀ x, x ∉ Z → Antitone fun j => f j x)
    (hl : ∀ x, x ∉ Z → Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | x ∉ Z ∧ δ ≤ |f j x - g x|}) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have heps : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨Gp, hGpo, hZGp, hGpc⟩ := hZ
    (ENNReal.ofReal (η.toReal / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨Gg, hGgo, hGgc, hGgg⟩ := hg
    (ENNReal.ofReal (η.toReal / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  choose G hGo hGc hGf using fun j : ℕ => hq j
    (ENNReal.ofReal (η.toReal / 2 / 2 / 2 ^ j))
    (ENNReal.ofReal_pos.mpr (by positivity))
  let H := Gp ∪ (Gg ∪ ⋃ j, G j)
  have hHo : IsOpen H := hGpo.union (hGgo.union (isOpen_iUnion hGo))
  have hUnion : thetaCapacity omega.form (fun _ => 0) (⋃ j, G j) ≤
      ENNReal.ofReal (η.toReal / 2) := by
    refine (thetaCapacity_iUnion_le _ _ G).trans ?_
    refine (ENNReal.tsum_le_tsum fun j => (hGc j).le).trans ?_
    rw [tsum_ofReal_geometric_half η.toReal heps]
  have hHc : thetaCapacity omega.form (fun _ => 0) H ≤ η := by
    have hi : thetaCapacity omega.form (fun _ => 0) (Gg ∪ ⋃ j, G j) ≤
        thetaCapacity omega.form (fun _ => 0) Gg +
          thetaCapacity omega.form (fun _ => 0) (⋃ j, G j) :=
      thetaCapacity_union_le omega.form (fun _ => 0) Gg (⋃ j, G j)
    have ho : thetaCapacity omega.form (fun _ => 0) H ≤
        thetaCapacity omega.form (fun _ => 0) Gp +
          thetaCapacity omega.form (fun _ => 0) (Gg ∪ ⋃ j, G j) :=
      thetaCapacity_union_le omega.form (fun _ => 0) Gp (Gg ∪ ⋃ j, G j)
    calc
      _ ≤ thetaCapacity omega.form (fun _ => 0) Gp +
          (thetaCapacity omega.form (fun _ => 0) Gg +
            thetaCapacity omega.form (fun _ => 0) (⋃ j, G j)) :=
        ho.trans (add_le_add le_rfl hi)
      _ ≤ ENNReal.ofReal (η.toReal / 4) +
          (ENNReal.ofReal (η.toReal / 4) + ENNReal.ofReal (η.toReal / 2)) :=
        add_le_add hGpc.le (add_le_add hGgc.le hUnion)
      _ = η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        have he : η.toReal / 4 + (η.toReal / 4 + η.toReal / 2) = η.toReal := by ring
        rw [he, ENNReal.ofReal_toReal htop]
  have hnotZ (x : M) (hx : x ∈ Hᶜ) : x ∉ Z := fun hxZ => hx (Or.inl (hZGp hxZ))
  have hf : ∀ j, ContinuousOn (f j) Hᶜ := fun j =>
    (hGf j).mono (compl_subset_compl.mpr fun x hx =>
      Or.inr (Or.inr (mem_iUnion.mpr ⟨j, hx⟩)))
  have hgg : ContinuousOn g Hᶜ := hGgg.mono (compl_subset_compl.mpr fun x hx =>
    Or.inr (Or.inl hx))
  obtain ⟨N, hN⟩ := exists_forall_lt_add_of_antitone_of_continuousOn
    hHo.isClosed_compl.isCompact hf hgg
    (fun x hx => ha x (hnotZ x hx)) (fun x hx => hl x (hnotZ x hx)) hδ
  filter_upwards [eventually_ge_atTop N] with j hj
  refine (thetaCapacity_mono ?_).trans hHc
  rintro x ⟨hxZ, hgap⟩
  by_contra hxH
  have hlt := hN j hj x hxH
  rw [abs_of_nonneg (sub_nonneg.mpr (hle j x hxZ))] at hgap
  linarith

/-- Genuine decreasing potentials in any smooth closed background converge in
the original Kähler capacity off their complete capacity-zero polar union.
No boundedness, same-type, Big, semipositivity or dimension assumption is made. -/
theorem polar_capacity_zero_and_tendsto_capacity
    (omega : KahlerBackground n M) {α : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ j, IsThetaPshPotential α.val (u j)) (hw : IsThetaPshPotential α.val w)
    (ha : ∀ x, Antitone fun j => u j x)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (w x))) :
    thetaCapacity omega.form (fun _ => 0) {x | w x = ⊥ ∨ ∃ j, u j x = ⊥} = 0 ∧
      ∀ δ : ℝ, 0 < δ → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
        {x | w x ≠ ⊥ ∧ δ ≤ |(u j x).toReal - (w x).toReal|}) atTop (𝓝 0) := by
  classical
  have hwu : ∀ j x, w x ≤ u j x := fun j x => (ha x).le_of_tendsto (hl x) j
  have hup : ∀ j x, w x ≠ ⊥ → u j x ≠ ⊥ := by
    intro j x hx he
    exact hx (bot_unique (by simpa only [he] using hwu j x))
  have hpolar : ManifoldLocallyPluripolar (n := n) {x | w x = ⊥} :=
    quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential
  have hunion : {x | w x = ⊥ ∨ ∃ j, u j x = ⊥} = {x | w x = ⊥} := by
    ext x
    constructor
    · rintro (hx | ⟨j, hx⟩)
      · exact hx
      · exact bot_unique (by simpa only [hx] using hwu j x)
    · exact Or.inl
  constructor
  · rw [hunion]
    exact thetaCapacity_eq_zero_of_manifoldLocallyPluripolar (fun _ => 0) hpolar
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ x, u 0 x ≤ (b : EReal) := by
    rcases isEmpty_or_nonempty M with hM | hM
    · exact ⟨0, fun x => isEmptyElim x⟩
    · exact (hu 0).exists_global_upper_bound
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-α)
  let qj : ℕ → M → EReal := fun j x => ((A⁻¹ : ℝ) : EReal) * (u j x - (b : EReal))
  let q : M → EReal := fun x => ((A⁻¹ : ℝ) : EReal) * (w x - (b : EReal))
  have hqj : ∀ j, IsThetaPshPotential omega.form.val (qj j) := fun j =>
    normalized_genuine omega hA hdom (hu j)
  have hq : IsThetaPshPotential omega.form.val q := normalized_genuine omega hA hdom hw
  have hbuj : ∀ j x, u j x ≤ (b : EReal) := fun j x =>
    (ha x (Nat.zero_le j)).trans (hb x)
  have hqj0 : ∀ j, qj j ≤ 0 := by
    intro j x
    exact EReal.mul_nonpos_iff.mpr (Or.inl
      ⟨EReal.coe_nonneg.mpr (inv_pos.mpr hA).le, EReal.sub_nonpos.mpr (hbuj j x)⟩)
  have hq0 : q ≤ 0 := by
    intro x
    exact EReal.mul_nonpos_iff.mpr (Or.inl
      ⟨EReal.coe_nonneg.mpr (inv_pos.mpr hA).le,
        EReal.sub_nonpos.mpr ((hwu 0 x).trans (hb x))⟩)
  have hcj := fun j => PoleCoalescingCapacity.quasiContinuousFor_toReal_of_le_zero
    omega omega.isSemipositive (hqj j) (hqj0 j)
  have hc := PoleCoalescingCapacity.quasiContinuousFor_toReal_of_le_zero
    omega omega.isSemipositive hq hq0
  have hjreal : ∀ j x, w x ≠ ⊥ →
      (qj j x).toReal = A⁻¹ * ((u j x).toReal - b) := fun j x hx =>
    normalized_toReal ((hu j).1.quasiPlurisubharmonic.ne_top x) (hup j x hx)
  have hreal : ∀ x, w x ≠ ⊥ → (q x).toReal = A⁻¹ * ((w x).toReal - b) :=
    fun x hx => normalized_toReal (hw.1.quasiPlurisubharmonic.ne_top x) hx
  have hleR : ∀ j x, w x ≠ ⊥ → (q x).toReal ≤ (qj j x).toReal := by
    intro j x hx
    rw [hreal x hx, hjreal j x hx]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (EReal.toReal_le_toReal (hwu j x) hx
        ((hu j).1.quasiPlurisubharmonic.ne_top x)) b) (inv_pos.mpr hA).le
  have haR : ∀ x, w x ≠ ⊥ → Antitone fun j => (qj j x).toReal := by
    intro x hx j k hjk
    change (qj k x).toReal ≤ (qj j x).toReal
    rw [hjreal k x hx, hjreal j x hx]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (EReal.toReal_le_toReal (ha x hjk) (hup k x hx)
        ((hu j).1.quasiPlurisubharmonic.ne_top x)) b) (inv_pos.mpr hA).le
  have hlR : ∀ x, w x ≠ ⊥ →
      Tendsto (fun j => (qj j x).toReal) atTop (𝓝 ((q x).toReal)) := by
    intro x hx
    have hr := (EReal.tendsto_toReal (hw.1.quasiPlurisubharmonic.ne_top x) hx).comp (hl x)
    have ht : Tendsto (fun j => A⁻¹ * ((u j x).toReal - b)) atTop
        (𝓝 (A⁻¹ * ((w x).toReal - b))) :=
      tendsto_const_nhds.mul (hr.sub tendsto_const_nhds)
    rw [hreal x hx]
    exact ht.congr' (Eventually.of_forall fun j => (hjreal j x hx).symm)
  intro δ hδ
  have hconv := capacity_gap_tendsto_off_outerZero omega
    (outerCapacityZero_of_manifoldLocallyPluripolar omega hpolar) hcj hc hleR haR hlR
    (mul_pos (inv_pos.mpr hA) hδ)
  have hcap : ∀ j, thetaCapacity omega.form (fun _ => 0)
      {x | w x ≠ ⊥ ∧ δ ≤ |(u j x).toReal - (w x).toReal|} ≤
        thetaCapacity omega.form (fun _ => 0)
          {x | w x ≠ ⊥ ∧ A⁻¹ * δ ≤ |(qj j x).toReal - (q x).toReal|} := by
    intro j
    apply thetaCapacity_mono
    rintro x ⟨hx, hgap⟩
    refine ⟨hx, ?_⟩
    rw [hjreal j x hx, hreal x hx]
    have he : A⁻¹ * ((u j x).toReal - b) - A⁻¹ * ((w x).toReal - b) =
        A⁻¹ * ((u j x).toReal - (w x).toReal) := by ring
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hA)]
    exact mul_le_mul_of_nonneg_left hgap (inv_pos.mpr hA).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => zero_le) hcap

end
end SGPT.Foundations.Analysis.Pending.ActualUnboundedDecreasingCapacity
