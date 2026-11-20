import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import Mathlib.MeasureTheory.Integral.Layercake

set_option autoImplicit false

/-!
# Upward closure of relative finite energy under a Kähler background

Xia, SGPT, Proposition 3.1.22 (`xia-sgpt:page-0134`), the `E¹` case: if
`u ≤ v ≤ φ`, `u ∈ E¹(X, θ; φ)` and `v` is a `θ`-PSH potential, then
`v ∈ E¹(X, θ; φ)`.  Xia derives it from the energy characterisation of `E¹`
(his Proposition 3.1.17), which this project does not have.  This module
proves it instead by the classical **fundamental inequality** of
Guedj--Zeriahi, which needs only tools already in the tree.  With
`w = (v + φ)/2` and `s > 0`,

  `θ_v^n {v < φ - 2s} ≤ 2^n θ_w^n {u < w - s} ≤ 2^n θ_u^n {u ≤ φ - s}`:

the first step is the diagonal convex-combination scaling
`θ_w^n ≥ 2^{-n} θ_v^n`
(`GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`);
the second is the comparison principle for two potentials of full relative
mass (`diagonalPotentialMeasure_comparison` below, from plurifine locality of
the maximum, `GlobalMaxLocality.globalMixedMeasure_restrict_max_eq`), applied
to `u` and `w - s`, whose maximum lies between `u` and `φ` and so has full
mass (`RelativeFullMass.of_between`).  The layer-cake formula then gives

  `∫ |φ - v| θ_v^n ≤ 2^{n+1} ∫ |φ - u| θ_u^n`.

**Hypotheses.**  The statement carries `0 < n` and a Kähler background
`omega`.  Both are used: full mass of `v` is `RelativeFullMass.of_between`,
which takes them (it rests on the monotonicity theorem), and `omega` also
makes the diagonal measures finite.  The interface
`RelativeFiniteEnergy.of_between` in `RelativeFiniteEnergyOrderClosure` states
the same conclusion WITHOUT these hypotheses; it is not changed here.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending

open FirstPass FirstPass.PositiveClasses
open DiagonalMass GlobalNonPluripolar ThetaPshConvexCombination

noncomputable section

namespace RelativeFullMassEnergyUpwardClosure

/-! ### Extended-real bookkeeping -/

/-- The finite value of the canonical absolute difference of two ordered reals. -/
theorem toReal_canonicalERealAbsDiff_coe_coe {x y : ℝ} (hxy : x ≤ y) :
    (canonicalERealAbsDiff (y : EReal) (x : EReal)).toReal = y - x := by
  rw [canonicalERealAbsDiff_coe_coe, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (by linarith)]

/-- A strict lower bound on the real part of the energy integrand forces both
values to be finite, with the expected real gap.  At a pole of `a` the
integrand is `0` or `⊤`, whose real part is `0`. -/
theorem exists_coe_of_lt_toReal {a b : EReal} (hab : a ≤ b) (hb : b ≠ ⊤) {t : ℝ}
    (ht : 0 < t) (h : t < (canonicalERealAbsDiff b a).toReal) :
    ∃ x y : ℝ, a = x ∧ b = y ∧ t < y - x := by
  induction a using EReal.rec with
  | bot =>
      exfalso
      by_cases hbb : b = ⊥
      · subst hbb
        simp at h
        linarith
      · rw [canonicalERealAbsDiff_bot_right hbb, ENNReal.toReal_top] at h
        linarith
  | top => exact absurd (top_le_iff.mp hab) hb
  | coe x =>
      induction b using EReal.rec with
      | bot => exact absurd hab (by simp)
      | top => exact absurd rfl hb
      | coe y =>
          refine ⟨x, y, rfl, rfl, ?_⟩
          rwa [toReal_canonicalERealAbsDiff_coe_coe (EReal.coe_le_coe_iff.mp hab)] at h

/-- The half convex combination of two reals, as extended reals. -/
theorem half_convexComb_coe (a b : ℝ) :
    (((1 / 2 : ℝ) : EReal) * (a : EReal) + ((1 - 1 / 2 : ℝ) : EReal) * (b : EReal)) =
      (((a + b) / 2 : ℝ) : EReal) := by
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  ring

/-- The half convex combination with a pole is a pole. -/
theorem half_convexComb_bot_left (b : EReal) :
    (((1 / 2 : ℝ) : EReal) * ⊥ + ((1 - 1 / 2 : ℝ) : EReal) * b) = ⊥ := by
  rw [EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add]

theorem half_convexComb_bot_right (a : EReal) :
    (((1 / 2 : ℝ) : EReal) * a + ((1 - 1 / 2 : ℝ) : EReal) * ⊥) = ⊥ := by
  rw [EReal.coe_mul_bot_of_pos (by norm_num), EReal.add_bot]

/-- The half convex combination lies below its larger argument. -/
theorem half_convexComb_le {a b : EReal} (hab : a ≤ b) (hb : b ≠ ⊤) :
    (((1 / 2 : ℝ) : EReal) * a + ((1 - 1 / 2 : ℝ) : EReal) * b) ≤ b := by
  induction a using EReal.rec with
  | bot => rw [half_convexComb_bot_left b]; exact bot_le
  | top => exact absurd (top_le_iff.mp hab) hb
  | coe x =>
      induction b using EReal.rec with
      | bot => exact absurd hab (by simp)
      | top => exact absurd rfl hb
      | coe y =>
          rw [half_convexComb_coe]
          exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_le_coe_iff.mp hab])

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### The comparison principle for the diagonal measure -/

omit [BorelSpace M] in
/-- The diagonal measure depends only on the potential, not on how it is written. -/
theorem diagonalPotentialMeasure_congr_fun {theta : ClosedRealOneOneForm n M}
    {f g : M → EReal} (hfg : f = g) (hf : IsThetaPshPotential theta.val f)
    (hg : IsThetaPshPotential theta.val g) :
    diagonalPotentialMeasure theta f hf = diagonalPotentialMeasure theta g hg := by
  subst hfg
  rfl

/-- **Comparison principle** (Xia, Proposition 3.1.15 (3.28), diagonal case,
in the form used by Guedj--Zeriahi).  If the maximum of `c` and `d` has the
same total diagonal mass as `c`, then `θ_d^n {c < d} ≤ θ_c^n {c ≤ d}`. -/
theorem diagonalPotentialMeasure_comparison (hn : 0 < n)
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {c d : M → EReal} (hc : IsThetaPshPotential theta.val c)
    (hd : IsThetaPshPotential theta.val d)
    (hm : IsThetaPshPotential theta.val (fun x => max (c x) (d x)))
    (hmass : diagonalPotentialMeasure theta (fun x => max (c x) (d x)) hm univ =
      diagonalPotentialMeasure theta c hc univ) :
    diagonalPotentialMeasure theta d hd {x | c x < d x} ≤
      diagonalPotentialMeasure theta c hc {x | c x ≤ d x} := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set μm := diagonalPotentialMeasure theta (fun x => max (c x) (d x)) hm with hμm
  set μc := diagonalPotentialMeasure theta c hc with hμc
  set μd := diagonalPotentialMeasure theta d hd with hμd
  have : IsFiniteMeasure μc :=
    globalMixedMeasure_isFiniteMeasure omega (fun _ => hc.1)
  have hcm : Measurable c := hc.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hdm : Measurable d := hd.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hS1 : MeasurableSet {x | d x < c x} := measurableSet_lt hdm hcm
  have hS2 : MeasurableSet {x | c x < d x} := measurableSet_lt hcm hdm
  -- locality on `{d < c}`
  have hloc1 : μm {x | d x < c x} = μc {x | d x < c x} := by
    have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (θ := fun _ : Fin n => theta) (u := fun _ => c) (w := fun _ => d)
      (fun _ => hc.1) (fun _ => hd.1) (fun _ => hm.1)
    simp only [forall_const] at h
    have h' := congrArg (fun ν : Measure M => ν univ) h
    simp only [Measure.restrict_apply_univ] at h'
    exact h'
  -- locality on `{c < d}`
  have hloc2 : μm {x | c x < d x} = μd {x | c x < d x} := by
    have hm' : IsThetaPshPotential theta.val (fun x => max (d x) (c x)) := by
      have hfun : (fun x => max (d x) (c x)) = fun x => max (c x) (d x) := by
        funext x
        exact max_comm _ _
      rw [hfun]
      exact hm
    have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (θ := fun _ : Fin n => theta) (u := fun _ => d) (w := fun _ => c)
      (fun _ => hd.1) (fun _ => hc.1) (fun _ => hm'.1)
    simp only [forall_const] at h
    have h' := congrArg (fun ν : Measure M => ν univ) h
    simp only [Measure.restrict_apply_univ] at h'
    have hcongr : diagonalPotentialMeasure theta (fun x => max (d x) (c x)) hm' = μm := by
      have hfun : (fun x => max (d x) (c x)) = fun x => max (c x) (d x) := by
        funext x
        exact max_comm _ _
      rw [hμm]
      exact diagonalPotentialMeasure_congr_fun hfun hm' hm
    rw [← hcongr]
    exact h'
  have hdisj : Disjoint {x | d x < c x} {x | c x < d x} := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact lt_asymm (show d x < c x from h1) (show c x < d x from h2)
  have hsplit : μc univ = μc {x | d x < c x} + μc {x | c x ≤ d x} := by
    have hcompl : {x | d x < c x}ᶜ = {x | c x ≤ d x} := by
      ext x
      simp only [mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [← measure_add_measure_compl hS1, hcompl]
  have hkey : μc {x | d x < c x} + μd {x | c x < d x} ≤
      μc {x | d x < c x} + μc {x | c x ≤ d x} := by
    calc μc {x | d x < c x} + μd {x | c x < d x}
        = μm {x | d x < c x} + μm {x | c x < d x} := by rw [hloc1, hloc2]
      _ = μm ({x | d x < c x} ∪ {x | c x < d x}) := (measure_union hdisj hS2).symm
      _ ≤ μm univ := measure_mono (subset_univ _)
      _ = μc univ := hmass
      _ = μc {x | d x < c x} + μc {x | c x ≤ d x} := hsplit
  exact (ENNReal.add_le_add_iff_left (measure_ne_top μc _)).mp hkey

/-! ### The fundamental inequality -/

/-- **Guedj--Zeriahi's fundamental inequality, relative form.**  For
`u ≤ v ≤ φ` with `u` of full relative mass and `t > 0`,

  `θ_v^n {t < |φ - v|} ≤ 2^n θ_u^n {t ≤ 2 |φ - u|}`,

with `|φ - ·|` the real part of the canonical extended absolute difference
(which is `0` at a pole of the potential). -/
theorem diagonalPotentialMeasure_superlevel_le [ConnectedSpace M] (hn : 0 < n)
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {phi u v : M → EReal} {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) {t : ℝ} (ht : 0 < t) :
    diagonalPotentialMeasure theta v hv
        {x | t < (canonicalERealAbsDiff (phi x) (v x)).toReal} ≤
      2 ^ n * diagonalPotentialMeasure theta u hu.plurisubharmonic
        {x | t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal} := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hphiP : IsThetaPshPotential theta.val phi := hphi.plurisubharmonic
  have huP : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hphitop : ∀ x, phi x ≠ ⊤ := fun x => hphiP.1.quasiPlurisubharmonic.ne_top x
  set s : ℝ := t / 2 with hs
  -- the midpoint potential and its downward translate
  let w : M → EReal := convexComb (1 / 2) v phi
  have hw : IsThetaPshPotential theta.val w :=
    isThetaPshPotential_convexComb hv hphiP (by norm_num) (by norm_num)
  let ws : M → EReal := fun x => w x + ((-s : ℝ) : EReal)
  have hws : IsThetaPshPotential theta.val ws := hw.add_const (-s)
  have hwle : ∀ x, w x ≤ phi x := fun x =>
    half_convexComb_le (hvphi x) (hphitop x)
  have hwsle : ∀ x, ws x ≤ phi x := by
    intro x
    refine le_trans ?_ (hwle x)
    have h0 : ((-s : ℝ) : EReal) ≤ 0 := EReal.coe_nonpos.mpr (by rw [hs]; linarith)
    show w x + ((-s : ℝ) : EReal) ≤ w x
    calc w x + ((-s : ℝ) : EReal) ≤ w x + 0 := add_le_add le_rfl h0
      _ = w x := add_zero _
  -- the maximum of `u` and `ws` has full relative mass
  have hmP : IsThetaPshPotential theta.val (fun x => max (u x) (ws x)) :=
    IsThetaPshPotential.max huP hws
  have hmfull : RelativeFullMass theta phi (fun x => max (u x) (ws x)) hphi :=
    hu.of_between hn omega hmP (fun x => le_max_left _ _)
      (fun x => max_le (hu.le_reference x) (hwsle x))
  have hmass : diagonalPotentialMeasure theta (fun x => max (u x) (ws x)) hmP univ =
      diagonalPotentialMeasure theta u huP univ := by
    have h1 := ((relativeFullMass_iff theta phi _ hphi hmP).1 hmfull).2
    have h2 := ((relativeFullMass_iff theta phi _ hphi huP).1 hu).2
    exact h1.trans h2.symm
  have hcomp := diagonalPotentialMeasure_comparison hn omega huP hws hmP hmass
  -- `ws` and `w` have the same measure; `w` dominates `2^{-n}` times `v`'s
  have hshift : diagonalPotentialMeasure theta ws hws = diagonalPotentialMeasure theta w hw :=
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const theta hw (-s) hws
  have hscale : ∀ S : Set M, diagonalPotentialMeasure theta v hv S ≤
      2 ^ n * diagonalPotentialMeasure theta w hw S := by
    intro S
    have h := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
      hv hphiP (t := 1 / 2) (by norm_num) (by norm_num) S
    have hhalf : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    rw [hhalf] at h
    have h2 : (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ n = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc diagonalPotentialMeasure theta v hv S
        = (2 : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞)⁻¹ ^ n * diagonalPotentialMeasure theta v hv S) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 ^ n * diagonalPotentialMeasure theta w hw S := by
          gcongr
          exact h
  -- the two set inclusions
  have hI1 : {x | t < (canonicalERealAbsDiff (phi x) (v x)).toReal} ⊆
      {x | u x < ws x} := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ := exists_coe_of_lt_toReal (hvphi x) (hphitop x) ht hx
    show u x < w x + ((-s : ℝ) : EReal)
    have hwx : w x = (((a + b) / 2 : ℝ) : EReal) := by
      show (((1 / 2 : ℝ) : EReal) * v x + ((1 - 1 / 2 : ℝ) : EReal) * phi x) = _
      rw [ha, hb, half_convexComb_coe]
    rw [hwx, ← EReal.coe_add]
    refine lt_of_le_of_lt ((huv x).trans_eq ha) (EReal.coe_lt_coe_iff.mpr ?_)
    rw [hs]
    linarith
  have hI2 : {x | u x ≤ ws x} ⊆
      {x | t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal} ∪ {x | u x = ⊥} := by
    intro x hx
    by_cases hub : u x = ⊥
    · exact Or.inr hub
    left
    have hutop : u x ≠ ⊤ := ne_top_of_le_ne_top (hphitop x) ((huv x).trans (hvphi x))
    obtain ⟨c, hc⟩ : ∃ c : ℝ, u x = c := ⟨(u x).toReal, (EReal.coe_toReal hutop hub).symm⟩
    have hvb : v x ≠ ⊥ := fun h => hub (le_bot_iff.mp ((huv x).trans_eq h))
    have hvtop : v x ≠ ⊤ := ne_top_of_le_ne_top (hphitop x) (hvphi x)
    obtain ⟨a, ha⟩ : ∃ a : ℝ, v x = a := ⟨(v x).toReal, (EReal.coe_toReal hvtop hvb).symm⟩
    have hphib : phi x ≠ ⊥ := fun h => hvb (le_bot_iff.mp ((hvphi x).trans_eq h))
    obtain ⟨b, hb⟩ : ∃ b : ℝ, phi x = b :=
      ⟨(phi x).toReal, (EReal.coe_toReal (hphitop x) hphib).symm⟩
    have hca : c ≤ a := EReal.coe_le_coe_iff.mp (by rw [← hc, ← ha]; exact huv x)
    have hab : a ≤ b := EReal.coe_le_coe_iff.mp (by rw [← ha, ← hb]; exact hvphi x)
    have hwsx : ws x = (((a + b) / 2 + -s : ℝ) : EReal) := by
      show (((1 / 2 : ℝ) : EReal) * v x + ((1 - 1 / 2 : ℝ) : EReal) * phi x) +
        ((-s : ℝ) : EReal) = _
      rw [ha, hb, half_convexComb_coe, ← EReal.coe_add]
    have hcw : c ≤ (a + b) / 2 + -s := by
      have h := hx
      simp only [Set.mem_ofPred_eq] at h
      rw [hc, hwsx] at h
      exact EReal.coe_le_coe_iff.mp h
    show t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal
    rw [hb, hc, toReal_canonicalERealAbsDiff_coe_coe (hca.trans hab)]
    rw [hs] at hcw
    linarith
  have hpole : diagonalPotentialMeasure theta u huP {x | u x = ⊥} = 0 :=
    GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => huP.1) ⟨0, hn⟩
  calc diagonalPotentialMeasure theta v hv
          {x | t < (canonicalERealAbsDiff (phi x) (v x)).toReal}
      ≤ diagonalPotentialMeasure theta v hv {x | u x < ws x} := measure_mono hI1
    _ ≤ 2 ^ n * diagonalPotentialMeasure theta w hw {x | u x < ws x} := hscale _
    _ = 2 ^ n * diagonalPotentialMeasure theta ws hws {x | u x < ws x} := by rw [hshift]
    _ ≤ 2 ^ n * diagonalPotentialMeasure theta u huP {x | u x ≤ ws x} := by
        gcongr
    _ ≤ 2 ^ n * (diagonalPotentialMeasure theta u huP
          {x | t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal} +
          diagonalPotentialMeasure theta u huP {x | u x = ⊥}) := by
        gcongr
        exact (measure_mono hI2).trans (measure_union_le _ _)
    _ = 2 ^ n * diagonalPotentialMeasure theta u hu.plurisubharmonic
          {x | t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal} := by
        rw [hpole, add_zero]

/-! ### The energy estimate -/

/-- The energy integrand agrees almost everywhere with the `ofReal` of its real
part: below the reference it is `⊤` only at poles of the potential, which the
potential's own measure does not charge. -/
theorem lintegral_canonicalERealAbsDiff_eq_ofReal_toReal (hn : 0 < n)
    {theta : ClosedRealOneOneForm n M} {phi f : M → EReal}
    (hphitop : ∀ x, phi x ≠ ⊤) (hf : IsThetaPshPotential theta.val f)
    (hfphi : ∀ x, f x ≤ phi x) :
    ∫⁻ x, canonicalERealAbsDiff (phi x) (f x) ∂ diagonalPotentialMeasure theta f hf =
      ∫⁻ x, ENNReal.ofReal (canonicalERealAbsDiff (phi x) (f x)).toReal
        ∂ diagonalPotentialMeasure theta f hf := by
  apply lintegral_congr_ae
  have hpole : diagonalPotentialMeasure theta f hf {x | f x = ⊥} = 0 :=
    GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => hf.1) ⟨0, hn⟩
  have hae : ∀ᵐ x ∂ diagonalPotentialMeasure theta f hf, f x ≠ ⊥ := by
    rw [ae_iff]
    simpa using hpole
  filter_upwards [hae] with x hx
  have hftop : f x ≠ ⊤ := hf.1.quasiPlurisubharmonic.ne_top x
  have hpb : phi x ≠ ⊥ := fun h => hx (le_bot_iff.mp ((hfphi x).trans_eq h))
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal hftop hx).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, phi x = b :=
    ⟨(phi x).toReal, (EReal.coe_toReal (hphitop x) hpb).symm⟩
  have hne : canonicalERealAbsDiff (phi x) (f x) ≠ ⊤ := by
    rw [ha, hb, canonicalERealAbsDiff_coe_coe]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_toReal hne).symm

variable [ConnectedSpace M] in
/-- **The energy estimate.**  For `u ≤ v ≤ φ` with `u` of full relative mass,
`∫ |φ - v| θ_v^n ≤ 2^n · 2 · ∫ |φ - u| θ_u^n`. -/
theorem relativeFiniteEnergyIntegral_le (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    relativeFiniteEnergyIntegral theta phi v hv ≤
      2 ^ n * (2 * relativeFiniteEnergyIntegral theta phi u hu.plurisubharmonic) := by
  have huP : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hphitop : ∀ x, phi x ≠ ⊤ := fun x =>
    hphi.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x
  have hphim : Measurable phi :=
    hphi.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum : Measurable u := huP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  set μv := diagonalPotentialMeasure theta v hv with hμv
  set μu := diagonalPotentialMeasure theta u huP with hμu
  let Gv : M → ℝ := fun x => (canonicalERealAbsDiff (phi x) (v x)).toReal
  let Gu : M → ℝ := fun x => (canonicalERealAbsDiff (phi x) (u x)).toReal
  have hGv : Measurable Gv := (hphim.canonicalERealAbsDiff hvm).ennreal_toReal
  have hGu : Measurable Gu := (hphim.canonicalERealAbsDiff hum).ennreal_toReal
  have hGu2 : Measurable fun x => 2 * Gu x := hGu.const_mul 2
  unfold relativeFiniteEnergyIntegral
  rw [lintegral_canonicalERealAbsDiff_eq_ofReal_toReal hn hphitop hv hvphi,
    lintegral_eq_lintegral_meas_lt μv
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hGv.aemeasurable]
  calc ∫⁻ t in Ioi 0, μv {a | t < Gv a}
      ≤ ∫⁻ t in Ioi 0, 2 ^ n * μu {a | t ≤ 2 * Gu a} := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        exact diagonalPotentialMeasure_superlevel_le hn omega hu hv huv hvphi ht
    _ = 2 ^ n * ∫⁻ t in Ioi 0, μu {a | t ≤ 2 * Gu a} :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    _ = 2 ^ n * ∫⁻ x, ENNReal.ofReal (2 * Gu x) ∂μu := by
        rw [lintegral_eq_lintegral_meas_le μu
          (Eventually.of_forall fun x => by positivity) hGu2.aemeasurable]
    _ = 2 ^ n * (2 * ∫⁻ x, ENNReal.ofReal (Gu x) ∂μu) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
        congr 2
        funext x
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ 2 ^ n * (2 * ∫⁻ x, canonicalERealAbsDiff (phi x) (u x) ∂μu) := by
        gcongr with x
        exact ENNReal.ofReal_toReal_le

end RelativeFullMassEnergyUpwardClosure

open RelativeFullMassEnergyUpwardClosure in
/-- **Xia, Proposition 3.1.22, `E¹` case, under a Kähler background.**  If
`u ≤ v ≤ φ`, `u ∈ E¹(X, θ; φ)` and `v` is a `θ`-PSH potential, then
`v ∈ E¹(X, θ; φ)`.  Proved by the Guedj--Zeriahi fundamental inequality,
`∫ |φ - v| θ_v^n ≤ 2^{n+1} ∫ |φ - u| θ_u^n`. -/
theorem RelativeFiniteEnergy.of_between_of_kahler {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    RelativeFiniteEnergy theta phi v hphi := by
  have hufull : RelativeFullMass theta phi u hphi := hu.fullMass
  have hfull : RelativeFullMass theta phi v hphi := hufull.of_between hn omega hv huv hvphi
  have hufin : relativeFiniteEnergyIntegral theta phi u hufull.plurisubharmonic < ⊤ :=
    ((relativeFiniteEnergy_iff theta phi u hphi hufull.plurisubharmonic).1 hu).2
  refine (relativeFiniteEnergy_iff theta phi v hphi hv).2 ⟨hfull, ?_⟩
  refine (relativeFiniteEnergyIntegral_le hn omega hufull hv huv hvphi).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hufin)

end

end SGPT.Foundations.Analysis.Pending
