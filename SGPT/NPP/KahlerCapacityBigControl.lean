import SGPT.PSH.SourceCapacity
import SGPT.Foundations.Analysis.Pending.DivisorialDomination
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

/-!
# Kähler capacity is controlled by the capacity of a big class

For a Kähler background `ω` and a closed smooth real `(1,1)`-form `θ` with big
class, there is, for every `ε > 0`, a constant `C > 0` with

  `Cap_ω(E) ≤ ε + C · Cap_θ(E)`   for every Borel set `E`,

where `Cap_ω` is the Kähler capacity (reference `V_ω = 0`) and `Cap_θ` is the
source `θ`-capacity of `def:cap` (reference `V_θ`).  Consequently convergence to
`0` in `θ`-capacity implies convergence to `0` in Kähler capacity, and `θ`-capacity
zero implies Kähler-capacity zero.

This is one half of the comparison of capacities in source `thm:comp_capa`
(with `θ' = ω`); it is used below for `thm:pp_cap`.

Proof.  Bigness gives `δ > 0` and a normalized `ρ ≤ 0` that is `(θ - δω)`-psh.
The Kähler capacity of the sublevel `{ρ < -B}` is small for `B` large (the
quasi-psh function `ρ / H` is `ω`-psh for a suitable `H > 0`, and Kähler-capacity
sublevels of `ω`-psh functions shrink).  On `{ρ ≥ -B}`, for a Kähler competitor
`u` (`-1 ≤ u ≤ 0`), `A = ρ + δu` is `θ`-psh with `θ_A^n ≥ δ^n ω_u^n` (positive
multilinear expansion), the convex combination `W = tA + (1-t)V_θ` has
`θ_W^n ≥ t^n θ_A^n`, and `v = max(W, V_θ - 1)` agrees with `W` on `{ρ ≥ -B}`
for `t` small, so its measure is a `θ`-capacity competitor dominating
`(tδ)^n ω_u^n` there.

Ported (and re-checked) from the previous team's unadopted draft
`work/sgpt-active-lanes-20261102/npp-compact-capacity-bridge`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity DiagonalMass GlobalNonPluripolar
open GlobalMultilinearExpansion GlobalDiagonalScaling
open ThetaPshConvexCombination GlobalDiagonalConvexScaling
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The sum of a potential and a positive multiple of another one is psh for
the corresponding combination of the backgrounds. -/
theorem add_scaled_thetaPsh {α β : ClosedRealOneOneForm n M} {a b : M → EReal}
    (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential β.val b)
    {c : ℝ} (hc : 0 < c) :
    ThetaPlurisubharmonic (α + c • β).val (fun x => a x + (c : EReal) * b x) := by
  simpa only [one_smul, EReal.coe_one, one_mul] using
    thetaPlurisubharmonic_add_smul zero_lt_one hc ha.1 hb.1

/-- A strict reference plus `δ` times a Kähler competitor bounded below is a
genuine `θ`-psh potential. -/
theorem strict_reference_add_competitor_genuine (ω : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {δ : ℝ} (hδ : 0 < δ) {ρ u : M → EReal}
    (hρ : IsThetaPshPotential (θ - δ • ω.form).val ρ)
    (hu : IsThetaPshPotential ω.form.val u) (hlb : ∀ x, (-1 : EReal) ≤ u x) :
    IsThetaPshPotential θ.val (fun x => ρ x + (δ : EReal) * u x) := by
  refine ⟨?_, fun x U hU hxU => ?_⟩
  · simpa only [sub_add_cancel] using add_scaled_thetaPsh hρ hu hδ
  · obtain ⟨y, hy, hρy⟩ := hρ.2 x U hU hxU
    refine ⟨y, hy, ?_⟩
    have hubot : u y ≠ ⊥ := by
      intro he
      have h := hlb y
      rw [he] at h
      exact (EReal.coe_ne_bot (-1)) (le_bot_iff.mp h)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, u y = (r : EReal) :=
      ⟨(u y).toReal, (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top y) hubot).symm⟩
    change ρ y + (δ : EReal) * u y ≠ ⊥
    rw [hr, ← EReal.coe_mul]
    exact EReal.add_ne_bot_iff.mpr ⟨hρy, EReal.coe_ne_bot _⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Bigness produces `δ > 0`, a normalized `(θ - δω)`-psh `ρ ≤ 0`, and the
genuine minimal potential `V_θ ≥ ρ`, in every dimension. -/
theorem exists_normalized_strict_reference [Nonempty M] (ω : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : M → EReal,
      IsThetaPshPotential (θ - δ • ω.form).val ρ ∧ ρ ≤ 0 ∧
      IsThetaPshPotential θ.val ρ ∧
      IsThetaPshPotential θ.val (thetaPshSupremum θ.val) ∧
      ρ ≤ thetaPshSupremum θ.val := by
  obtain ⟨δ, hδ, u, hu⟩ :=
    DivisorialDomination.exists_isThetaPshPotential_sub_smul_of_isBigClass ω θ hbig
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, u x ≤ (C : EReal) := hu.exists_global_upper_bound
  let ρ : M → EReal := fun x => u x - (C : EReal)
  have hρ : IsThetaPshPotential (θ - δ • ω.form).val ρ := hu.sub_const C
  have hρ0 : ρ ≤ 0 := by
    intro x
    change u x - (C : EReal) ≤ (0 : EReal)
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot C))
      (Or.inl (EReal.coe_ne_top C))).mpr
    simpa only [zero_add] using hC x
  have hsemi : (δ • ω.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul ω.isSemipositive hδ.le
  have hρθ : IsThetaPshPotential θ.val ρ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hρ hsemi
    simpa only [sub_add_cancel] using h
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      hρθ.1.hasSmoothLocalPotentials ⟨ρ, hρθ⟩
  exact ⟨δ, hδ, ρ, hρ, hρ0, hρθ, hV, le_thetaPshSupremum hρθ hρ0⟩

/-- A normalized global quasi-psh reference has sublevel sets of arbitrarily
small Kähler capacity. -/
theorem exists_reference_tail_small (ω : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {ρ : M → EReal}
    (hρ : IsThetaPshPotential α.val ρ) (hρ0 : ρ ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ thetaCapacity ω.form (fun _ => 0) {x | ρ x < ((-B : ℝ) : EReal)} <
      ENNReal.ofReal ε := by
  obtain ⟨H, hH, hHρ⟩ :=
    GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul ω hρ.quasiPshPotential
  let q : M → EReal := fun x => ((H⁻¹ : ℝ) : EReal) * ρ x
  have hq : IsThetaPshPotential ω.form.val q := by
    have h := PotentialMassComparison.isThetaPshPotential_smul hHρ (inv_pos.mpr hH)
    have he : H⁻¹ • (H • ω.form) = ω.form := by
      rw [smul_smul, inv_mul_cancel₀ hH.ne', one_smul]
    simpa only [he] using h
  have hq0 : q ≤ 0 := by
    intro x
    have h0x : ρ x ≤ (0 : EReal) := hρ0 x
    change ((H⁻¹ : ℝ) : EReal) * ρ x ≤ (0 : EReal)
    have h := mul_le_mul_of_nonneg_left h0x
      (show (0 : EReal) ≤ ((H⁻¹ : ℝ) : EReal) from EReal.coe_le_coe_iff.mpr (inv_pos.mpr hH).le)
    simpa only [q, mul_zero] using h
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  have ht := ThetaCapacitySublevel.tendsto_thetaCapacity_sublevel ω hzero hq hq0
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  let B : ℝ := H * (k : ℝ)
  have hB : 0 ≤ B := mul_nonneg hH.le (Nat.cast_nonneg k)
  have hsets : {x | ρ x < ((-B : ℝ) : EReal)} =
      {x | q x < (0 : EReal) + ((-(k : ℝ) : ℝ) : EReal)} := by
    ext x
    change ρ x < ((-B : ℝ) : EReal) ↔ q x < (0 : EReal) + ((-(k : ℝ) : ℝ) : EReal)
    by_cases hb : ρ x = ⊥
    · simp only [hb, q, EReal.coe_mul_bot_of_pos (inv_pos.mpr hH), zero_add]
      constructor
      · intro _
        exact bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot _)
      · intro _
        exact bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot _)
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, ρ x = (r : EReal) :=
        ⟨(ρ x).toReal, (EReal.coe_toReal (hρ.1.quasiPlurisubharmonic.ne_top x) hb).symm⟩
      simp only [q, hr, zero_add, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
      rw [inv_mul_lt_iff₀ hH]
      dsimp only [B]
      ring_nf
  refine ⟨B, hB, ?_⟩
  rw [hsets]
  exact hk

/-- The positive multilinear expansion dominates its all-second term:
`c^n β_b^n ≤ (α + cβ)^n_{a + c b}`. -/
theorem diagonal_add_scaled_ge_right {α β : ClosedRealOneOneForm n M} {a b : M → EReal}
    (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential β.val b)
    {c : ℝ} (hc : 0 < c) (E : Set M) :
    ENNReal.ofReal (c ^ n) * globalMixedMeasure (fun _ : Fin n => β) (fun _ => b) (fun _ => hb.1) E ≤
      globalMixedMeasure (fun _ : Fin n => α + c • β)
        (fun _ x => a x + (c : EReal) * b x) (fun _ => add_scaled_thetaPsh ha hb hc) E := by
  classical
  let forms : Bool → ClosedRealOneOneForm n M := fun i => if i then β else α
  let pots : Bool → M → EReal := fun i => if i then b else a
  let w : Bool → ℝ := fun i => if i then c else 1
  have hw : ∀ i, 0 < w i := by
    intro i
    cases i <;> simp [w, hc]
  have hp : ∀ i, ThetaPlurisubharmonic (forms i).val (pots i) := by
    intro i
    cases i
    · exact ha.1
    · exact hb.1
  have hq : ∀ i, IsGlobalQuasiPshPotential (n := n) (pots i) := by
    intro i
    cases i
    · exact ha.quasiPshPotential
    · exact hb.quasiPshPotential
  have hform : sumForm Finset.univ w forms = α + c • β := by
    simp [sumForm, w, forms, add_comm]
  have hpot : sumPot Finset.univ w pots = fun x => a x + (c : EReal) * b x := by
    funext x
    simp [sumPot, w, pots, add_comm]
  let hs := fun _ : Fin n => thetaPlurisubharmonic_sumPot (Finset.univ_nonempty (α := Bool)) hw hp
  have he := globalMixedMeasure_diagonal_sumPot (Finset.univ_nonempty (α := Bool)) hw hp hq
  let F : (Fin n → Bool) → Measure M := fun g =>
    ENNReal.ofReal (∏ j, w (g j)) •
      globalMixedMeasure (fun j => forms (g j)) (fun j => pots (g j)) (fun j => hp (g j))
  have hle : F (fun _ => true) ≤
      ∑ g ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)), F g :=
    Finset.single_le_sum (fun _ _ => bot_le) (by simp)
  have hterm : F (fun _ => true) = ENNReal.ofReal (c ^ n) •
      globalMixedMeasure (fun _ : Fin n => β) (fun _ => b) (fun _ => hb.1) := by
    simp only [F, w, forms, pots, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ g ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)), F g) =
      globalMixedMeasure (fun _ : Fin n => α + c • β)
        (fun _ x => a x + (c : EReal) * b x) (fun _ => add_scaled_thetaPsh ha hb hc) := by
    apply he.symm.trans
    exact globalMixedMeasure_congr (congrArg (fun f => fun _ : Fin n => f) hform)
      (congrArg (fun f => fun _ : Fin n => f) hpot) hs (fun _ => add_scaled_thetaPsh ha hb hc)
  rw [hterm, hsum] at hle
  simpa only [Measure.smul_apply, smul_eq_mul] using hle E

/-- Explicit capacity comparison on a strict-reference superlevel set; the
constant is chosen before every Borel set and every competitor. -/
theorem kahlerCapacity_superlevel_le [Nonempty M] (ω : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {δ : ℝ} (hδ : 0 < δ) {ρ : M → EReal}
    (hρ : IsThetaPshPotential (θ - δ • ω.form).val ρ) (hρ0 : ρ ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M, MeasurableSet E →
      thetaCapacity ω.form (fun _ => 0) (E ∩ {x | ((-B : ℝ) : EReal) ≤ ρ x}) ≤
        ENNReal.ofReal C * thetaCapacityV θ E := by
  have hρθ : IsThetaPshPotential θ.val ρ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hρ
      (KahlerDomination.isSemipositive_smul ω.isSemipositive hδ.le)
    simpa only [sub_add_cancel] using h
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      hρθ.1.hasSmoothLocalPotentials ⟨ρ, hρθ⟩
  have hρV : ρ ≤ V := le_thetaPshSupremum hρθ hρ0
  have hV0 : V ≤ 0 := thetaPshSupremum_le_zero θ.val
  let t : ℝ := (2 * (B + δ + 1))⁻¹
  have hden : 0 < 2 * (B + δ + 1) := by positivity
  have ht0 : 0 < t := inv_pos.mpr hden
  have htEq : t * (2 * (B + δ + 1)) = 1 := inv_mul_cancel₀ hden.ne'
  have ht1 : t < 1 := by nlinarith
  have hp : 0 < (t * δ) ^ n := pow_pos (mul_pos ht0 hδ) n
  let C : ℝ := ((t * δ) ^ n)⁻¹
  have hC : 0 < C := inv_pos.mpr hp
  have hunit : ENNReal.ofReal C * ENNReal.ofReal ((t * δ) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul hC.le]
    dsimp only [C]
    rw [inv_mul_cancel₀ hp.ne', ENNReal.ofReal_one]
  refine ⟨C, hC, fun E hE => ?_⟩
  let G := E ∩ {x | ((-B : ℝ) : EReal) ≤ ρ x}
  have hG : MeasurableSet G := hE.inter
    (measurableSet_le measurable_const hρ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
  apply thetaCapacity_le_of_forall
  intro u hu hu0 huLow
  have hub : ∀ x, (-1 : EReal) ≤ u x := by
    intro x
    have h := (sub_one_le_iff_le_add_one (0 : EReal) (u x)).mpr (huLow x)
    simpa only [zero_sub] using h
  let A : M → EReal := fun x => ρ x + (δ : EReal) * u x
  have hA : IsThetaPshPotential θ.val A := strict_reference_add_competitor_genuine ω hδ hρ hu hub
  have hAV : A ≤ V := by
    intro x
    have hdu : (δ : EReal) * u x ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left (show u x ≤ (0 : EReal) from hu0 x)
        (show (0 : EReal) ≤ (δ : EReal) from EReal.coe_le_coe_iff.mpr hδ.le)
      simpa only [mul_zero] using h
    exact (add_le_of_nonpos_right hdu).trans (hρV x)
  let W : M → EReal := convexComb t A V
  have hW : IsThetaPshPotential θ.val W := isThetaPshPotential_convexComb hA hV ht0 ht1
  have hWV : W ≤ V := by
    have h := convexComb_mono ht0.le ht1.le hAV (le_refl V)
    rwa [convexComb_self ht0 ht1] at h
  let v : M → EReal := fun x => max (W x) (V x - 1)
  have hMinus : IsThetaPshPotential θ.val (fun x => V x - 1) := hV.sub_const 1
  have hv : IsThetaPshPotential θ.val v :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hW hMinus
  have hvV : v ≤ V := by
    intro x
    exact max_le (hWV x) ((sub_one_le_iff_le_add_one _ _).mpr
      (le_add_of_nonneg_right (show (0 : EReal) ≤ 1 by norm_num)))
  have hVv : ∀ x, V x ≤ v x + 1 := fun x =>
    (sub_one_le_iff_le_add_one _ _).mp (le_max_right _ _)
  have hstrict : ∀ x ∈ G, V x - 1 < W x := by
    intro x hx
    have hρbot : ρ x ≠ ⊥ := by
      intro he
      have h : ((-B : ℝ) : EReal) ≤ ρ x := hx.2
      rw [he] at h
      exact (EReal.coe_ne_bot (-B)) (le_bot_iff.mp h)
    have hVbot : V x ≠ ⊥ := fun he => hρbot (le_bot_iff.mp (he ▸ hρV x))
    have hubot : u x ≠ ⊥ := by
      intro he
      have h := hub x
      rw [he] at h
      exact (EReal.coe_ne_bot (-1)) (le_bot_iff.mp h)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ρ x = (r : EReal) :=
      ⟨(ρ x).toReal, (EReal.coe_toReal (hρ.1.quasiPlurisubharmonic.ne_top x) hρbot).symm⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, u x = (s : EReal) :=
      ⟨(u x).toReal, (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hubot).symm⟩
    obtain ⟨z, hz⟩ : ∃ z : ℝ, V x = (z : EReal) :=
      ⟨(V x).toReal, (EReal.coe_toReal (hV.1.quasiPlurisubharmonic.ne_top x) hVbot).symm⟩
    have hrB : -B ≤ r := by
      have h : ((-B : ℝ) : EReal) ≤ ρ x := hx.2
      rwa [hr, EReal.coe_le_coe_iff] at h
    have hs1 : (-1 : ℝ) ≤ s := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_neg, EReal.coe_one]
      simpa only [hs] using hub x
    have hz0 : z ≤ 0 := by
      have h : V x ≤ (0 : EReal) := hV0 x
      rwa [hz, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h
    have hgap : -(B + δ) ≤ r + δ * s - z := by
      nlinarith [mul_le_mul_of_nonneg_left hs1 hδ.le]
    have hstep := mul_le_mul_of_nonneg_left hgap ht0.le
    change V x - 1 < convexComb t A V x
    simp only [convexComb_apply, A, hr, hs, hz, ← EReal.coe_mul, ← EReal.coe_add,
      ← EReal.coe_one, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    nlinarith
  let S := {x | ∀ _i : Fin n, V x - 1 < W x}
  have hGS : G ⊆ S := fun x hx _ => hstrict x hx
  have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
    (fun _ : Fin n => hW.1) (fun _ : Fin n => hMinus.1) (fun _ : Fin n => hv.1)
  have heqG : globalMixedMeasure (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1) G =
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ => W) (fun _ => hW.1) G := by
    have h := congrArg (fun μ : Measure M => μ G) hloc
    rw [Measure.restrict_apply hG, Measure.restrict_apply hG] at h
    change globalMixedMeasure (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1) (G ∩ S) =
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ => W) (fun _ => hW.1) (G ∩ S) at h
    rwa [inter_eq_left.mpr hGS] at h
  have hpos := diagonal_add_scaled_ge_right hρ hu hδ G
  have hpos' : ENNReal.ofReal (δ ^ n) *
      globalMixedMeasure (fun _ : Fin n => ω.form) (fun _ => u) (fun _ => hu.1) G ≤
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ => A) (fun _ => hA.1) G := by
    simpa only [sub_add_cancel] using hpos
  have hmain : ENNReal.ofReal ((t * δ) ^ n) *
      globalMixedMeasure (fun _ : Fin n => ω.form) (fun _ => u) (fun _ => hu.1) G ≤
        thetaCapacityV θ E := by
    calc
      _ = ENNReal.ofReal (t ^ n) * (ENNReal.ofReal (δ ^ n) *
          globalMixedMeasure (fun _ : Fin n => ω.form) (fun _ => u) (fun _ => hu.1) G) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_pos ht0 n).le, ← mul_pow]
      _ ≤ ENNReal.ofReal (t ^ n) *
          globalMixedMeasure (fun _ : Fin n => θ) (fun _ => A) (fun _ => hA.1) G :=
        mul_le_mul' le_rfl hpos'
      _ ≤ globalMixedMeasure (fun _ : Fin n => θ) (fun _ => W) (fun _ => hW.1) G :=
        globalMixedMeasure_diagonal_convexComb_le hA hV ht0 ht1 G
      _ = globalMixedMeasure (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1) G := heqG.symm
      _ ≤ thetaCapacity θ V G := diagonalPotentialMeasure_le_thetaCapacity hv hvV hVv G
      _ ≤ thetaCapacityV θ E := thetaCapacity_mono inter_subset_left
  calc
    diagonalPotentialMeasure ω.form u hu G = ENNReal.ofReal C *
        (ENNReal.ofReal ((t * δ) ^ n) * diagonalPotentialMeasure ω.form u hu G) := by
      rw [← mul_assoc, hunit, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hmain

/-- `ε`-plus-linear control of the Kähler capacity by the capacity of a big
class: for every `ε > 0` there is `C > 0` such that
`Cap_ω(E) ≤ ε + C · Cap_θ(E)` for every Borel `E`. -/
theorem exists_big_capacity_control (ω : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M, MeasurableSet E →
      thetaCapacity ω.form (fun _ => 0) E ≤
        ENNReal.ofReal ε + ENNReal.ofReal C * thetaCapacityV θ E := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨1, by norm_num, fun E _ => ?_⟩
    have he : E = ∅ := by ext x; exact isEmptyElim x
    simp only [he, thetaCapacity_empty, zero_le]
  · obtain ⟨δ, hδ, ρ, hρ, hρ0, _hρθ, _hV, _hρV⟩ :=
      exists_normalized_strict_reference ω θ hbig
    obtain ⟨B, hB, hsmall⟩ := exists_reference_tail_small ω hρ hρ0 hε
    obtain ⟨C, hC, hcontrol⟩ := kahlerCapacity_superlevel_le ω hδ hρ hρ0 hB
    refine ⟨C, hC, fun E hE => ?_⟩
    have hsplit : E ⊆ {x | ρ x < ((-B : ℝ) : EReal)} ∪
        (E ∩ {x | ((-B : ℝ) : EReal) ≤ ρ x}) := by
      intro x hx
      by_cases h : ((-B : ℝ) : EReal) ≤ ρ x
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (lt_of_not_ge h)
    calc
      _ ≤ thetaCapacity ω.form (fun _ => 0)
          ({x | ρ x < ((-B : ℝ) : EReal)} ∪ (E ∩ {x | ((-B : ℝ) : EReal) ≤ ρ x})) :=
        thetaCapacity_mono hsplit
      _ ≤ thetaCapacity ω.form (fun _ => 0) {x | ρ x < ((-B : ℝ) : EReal)} +
          thetaCapacity ω.form (fun _ => 0) (E ∩ {x | ((-B : ℝ) : EReal) ≤ ρ x}) :=
        thetaCapacity_union_le _ _ _ _
      _ ≤ _ := add_le_add hsmall.le (hcontrol E hE)

/-- The same control stated with the source `θ`-capacity of `def:cap`. -/
theorem exists_source_capacity_control (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set M, MeasurableSet E →
      thetaCapacity ω.form (fun _ => 0) E ≤
        ENNReal.ofReal ε + ENNReal.ofReal C * sourceThetaCapacity θ E := by
  simpa only [sourceThetaCapacity_eq_native] using
    exists_big_capacity_control ω (atlasClosedFormToNative θ) hbig hε

/-- Convergence to `0` in the source `θ`-capacity (big `θ`) gives convergence to
`0` in Kähler capacity, along any filter. -/
theorem source_capacity_tendsto_implies_kahler (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} {l : Filter I} (E : I → Set M) (hE : ∀ i, MeasurableSet (E i))
    (hcap : Tendsto (fun i => sourceThetaCapacity θ (E i)) l (𝓝 0)) :
    Tendsto (fun i => thetaCapacity ω.form (fun _ => 0) (E i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  · let ε : ℝ := η.toReal / 2
    have hε : 0 < ε := half_pos (ENNReal.toReal_pos hη.ne' htop)
    obtain ⟨C, hC, hb⟩ := exists_source_capacity_control ω θ hbig hε
    have hsmall := (ENNReal.tendsto_nhds_zero.mp hcap)
      (ENNReal.ofReal (ε / C)) (ENNReal.ofReal_pos.mpr (div_pos hε hC))
    filter_upwards [hsmall] with i hi
    calc
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal C * sourceThetaCapacity θ (E i) := hb (E i) (hE i)
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
        add_le_add le_rfl (mul_le_mul' le_rfl hi)
      _ = ENNReal.ofReal ε + ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ ε hC.ne']
      _ = η := by
        rw [← ENNReal.ofReal_add hε.le hε.le]
        have he : ε + ε = η.toReal := by dsimp only [ε]; ring
        rw [he, ENNReal.ofReal_toReal htop]

/-- Source `θ`-capacity zero (big `θ`) forces Kähler capacity zero, on Borel sets. -/
theorem kahlerCapacity_eq_zero_of_source_capacity_eq_zero (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {E : Set M} (hE : MeasurableSet E) (h0 : sourceThetaCapacity θ E = 0) :
    thetaCapacity ω.form (fun _ => 0) E = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  obtain ⟨C, _hC, hb⟩ :=
    exists_source_capacity_control ω θ hbig (ε := (ε : ℝ)) (by exact_mod_cast hε)
  have h := hb E hE
  rw [h0, mul_zero, add_zero, ENNReal.ofReal_coe_nnreal] at h
  simpa only [zero_add] using h

end SGPT.NPP
