import SGPT.Foundations.Analysis.Pending.ThetaCapacity
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

set_option autoImplicit false

/-!
# The comparison principle, and the capacity of sublevel sets

Run 0044 recorded (I-0267, r4 correction) that *the comparison principle for
locally bounded `θ`-PSH potentials is the true single bottleneck* of items 2,
5 and 6 of the Theorem 2.4.4 stack, and that it was not in this workspace.
It is one page away from what the workspace already had, and this module
supplies it:

  `θⁿ_b {a < b} ≤ θⁿ_a {a < b}`   whenever `b ≤ a + C` for one finite `C`.

The proof is Xia's inequality (2.17), `MaxMassDecomposition.measure_max_ge`
(`xia-sgpt:page-0076`), read on the whole manifold: the measure of
`max (b, a)` dominates `θⁿ_b` on `{a < b}` plus `θⁿ_a` on `{b ≤ a}`, while its
total mass is at most that of `a` because `max (b, a) ≤ a + max (C, 0)` and the
diagonal mass is monotone in the singularity order
(`SingularityEnvelopeMassProof.diagonalPotentialMass_mono_of_kahler`).
Subtracting the finite `θⁿ_a {b ≤ a}` from both sides leaves the comparison.

Note what is *not* assumed: neither potential is bounded, only `b` is
constrained relative to `a`, and the dimension is not assumed positive.

## The Guedj--Zeriahi estimate

The comparison principle is then used for its classical consequence, the decay
of the capacity of the sublevel sets of a `θ`-PSH potential relative to the
reference:

  `Cap_θ({w < V - k}, V) → 0`   as `k → ∞`   (`tendsto_thetaCapacity_sublevel`),

for `w ≤ V` both genuine `θ`-PSH potentials.  This is the statement item 2' of
I-0267 (quasi-continuity for potentials **not** bounded relative to the
reference, I-0282) was missing: the truncations `max (w, V - k)` are bounded
relative to `V` and differ from `w` only on `{w < V - k}`.

The quantitative form is `thetaCapacity_sublevel_le`; its proof is described at
that theorem.  What made it reachable without the multilinear expansion of the
non-pluripolar product is that the *lower* bound
`(1-1/t)ⁿ θⁿ_V ≤ θⁿ_{(1-1/t)V + (1/t)w_m}` — the direction
`GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le` already
proves — together with equality of the total masses already pins the excess of
`θⁿ_v` over `θⁿ_V` on any set.

Source: E. Bedford and B. A. Taylor, *A new capacity for plurisubharmonic
functions*, Acta Math. 149 (1982), Theorem 4.1; V. Guedj and A. Zeriahi,
*Intrinsic capacities on compact Kähler manifolds*, J. Geom. Anal. 15 (2005);
M. Xia, *Non-pluripolar products on vector bundles and Chern--Weil formulae*,
inequality (2.17) (`xia-sgpt:page-0076`) and Proposition 3.1.15, inequality
(3.27) (`xia-sgpt:page-0116`), which is Xia's comparison principle.  It is
**not** Xia's Proposition 1.2.10: that is the *domination* principle
(`θⁿ_φ{φ < ψ} = 0 ⟹ ψ ≤ φ`, `xia-sgpt:page-0079`), which does **not** follow
from what is proved here.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- If `b` is at finite distance below `a`, the maximum is too. -/
theorem moreSingularOn_max {a b : M → EReal} (hba : MoreSingularOn b a univ) :
    MoreSingularOn (fun x => max (b x) (a x)) a univ := by
  obtain ⟨C, hC⟩ := hba
  refine ⟨max C 0, fun x _ => ?_⟩
  have hCle : ((C : ℝ) : EReal) ≤ ((max C 0 : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.2 (le_max_left C 0)
  have h0 : (0 : EReal) ≤ ((max C 0 : ℝ) : EReal) := by
    exact_mod_cast le_max_right C 0
  refine max_le ((hC x (mem_univ x)).trans (by gcongr)) ?_
  calc a x = a x + (0 : EReal) := by rw [add_zero]
    _ ≤ a x + ((max C 0 : ℝ) : EReal) := by gcongr

/-- **The comparison principle.**  For genuine `θ`-PSH potentials `a`, `b` with
`b ≤ a + C` for one finite constant,

  `θⁿ_b {a < b} ≤ θⁿ_a {a < b}`.

This is the Bedford--Taylor comparison principle; it is Xia's Proposition
3.1.15, inequality (3.27), in the diagonal case `j = 0`, with his finite-energy
hypothesis replaced by a finite-distance one.  It is *not* his Proposition
1.2.10, which is the domination principle.  The
proof is Xia's inequality (2.17) (`MaxMassDecomposition.measure_max_ge`)
together with the fact that potentials at finite distance carry the same total
mass: the maximum contributes `θⁿ_b` on `{a < b}` and `θⁿ_a` on `{b ≤ a}`,
while its total mass is that of `a`. -/
theorem diagonalPotentialMeasure_lt_le (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {a b : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hba : MoreSingularOn b a univ) :
    diagonalPotentialMeasure theta b hb {x | a x < b x} ≤
      diagonalPotentialMeasure theta a ha {x | a x < b x} := by
  classical
  have hmax : IsThetaPshPotential theta.val (fun x => max (b x) (a x)) := IsThetaPshPotential.max hb ha
  have hkey := measure_max_ge omega hb ha hmax (E := univ) MeasurableSet.univ
  rw [univ_inter, univ_inter] at hkey
  -- the maximum carries the same total mass as `a`
  have hmass : diagonalPotentialMass theta (fun x => max (b x) (a x)) hmax ≤
      diagonalPotentialMass theta a ha :=
    diagonalPotentialMass_mono_of_kahler omega hmax ha (moreSingularOn_max hba)
  -- split the total mass of `a` along `{a < b}`
  have hm : MeasurableSet {x : M | a x < b x} := measurableSet_potential_lt hb ha
  have hsplit : diagonalPotentialMass theta a ha =
      diagonalPotentialMeasure theta a ha {x | a x < b x} +
        diagonalPotentialMeasure theta a ha {x | b x ≤ a x} := by
    have hcompl : {x : M | a x < b x}ᶜ = {x : M | b x ≤ a x} := by
      ext x; simp [not_lt]
    rw [← hcompl]
    exact (measure_add_measure_compl (μ := diagonalPotentialMeasure theta a ha) hm).symm
  have hfin : diagonalPotentialMeasure theta a ha {x | b x ≤ a x} ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega (fun _ => ha.1) _).ne
  have hle : diagonalPotentialMeasure theta b hb {x | a x < b x} +
      diagonalPotentialMeasure theta a ha {x | b x ≤ a x} ≤
      diagonalPotentialMeasure theta a ha {x | a x < b x} +
        diagonalPotentialMeasure theta a ha {x | b x ≤ a x} := by
    rw [← hsplit]
    exact hkey.trans hmass
  exact (ENNReal.add_le_add_iff_right hfin).mp hle

/-! ## The Guedj--Zeriahi estimate for sublevel sets -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- Adding a nonpositive constant decreases a potential. -/
theorem add_coe_le_self {V : M → EReal} {c : ℝ} (hc : c ≤ 0) (x : M) :
    V x + ((c : ℝ) : EReal) ≤ V x := by
  calc V x + ((c : ℝ) : EReal) ≤ V x + (0 : EReal) := by gcongr; exact_mod_cast hc
    _ = V x := by rw [add_zero]

/-- **The capacity of a sublevel set at a halved level.**  For genuine `θ`-PSH
potentials `V` (the reference) and `w ≤ V`, and any `t > 1`,

  `Cap_θ({w < V - 2t}, V) ≤ (1 - (1 - 1/t)ⁿ)·θⁿ_V(X) + θⁿ_V({w < V - t})`.

Both terms on the right tend to `0` as `t → ∞`
(`tendsto_thetaCapacity_sublevel`), so this is the Guedj--Zeriahi estimate: the
capacity of the sublevel sets of a `θ`-PSH potential relative to the reference
tends to zero.  It is what lifts quasi-continuity from bounded to arbitrary
`θ`-PSH potentials (I-0282, item 2' of I-0267).

The proof.  Truncate `w` at `V - m` with `m = 2t + 1`, so that the truncation
`w_m = max (w, V - m)` is still below `V - 2t` wherever `w` is; interpolate
`v = (1 - 1/t)·V + (1/t)·w_m`, a potential at finite distance from `V`.  For
any capacity competitor `u`, i.e. `V - 1 ≤ u ≤ V`, one has pointwise

  `{w < V - 2t} ⊆ {v < u - 1} ⊆ {w_m < V - t}`,

the first because `v ≤ (1-1/t)V + (1/t)(V - 2t) = V - 2 ≤ u - 1` with a strict
drop, the second because `v < u - 1 ≤ V - 1` forces `(1/t)(w_m - V) < -1`.  The
comparison principle for `v` and `u - 1` (at finite distance above `v`) turns
this into `θⁿ_u({w < V - 2t}) ≤ θⁿ_v({w_m < V - t})`.  Finally
`(1 - 1/t)ⁿ θⁿ_V ≤ θⁿ_v` as measures
(`GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`, whose
`≥`-direction is exactly what is needed) and the two have the same total mass,
so on any set `θⁿ_v` can exceed `θⁿ_V` by at most `1 - (1 - 1/t)ⁿ` times that
mass. -/
theorem thetaCapacity_sublevel_le (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hw : IsThetaPshPotential theta.val w)
    (hwV : w ≤ V) {t : ℝ} (ht : 1 < t) :
    thetaCapacity theta V {x | w x < V x + ((-(2 * t) : ℝ) : EReal)} ≤
      ENNReal.ofReal (1 - (1 - t⁻¹) ^ n) * diagonalPotentialMass theta V hV +
        diagonalPotentialMeasure theta V hV {x | w x < V x + ((-t : ℝ) : EReal)} := by
  classical
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  set s : ℝ := t⁻¹ with hs_def
  have hs0 : 0 < s := inv_pos.mpr ht0
  have hs1 : s < 1 := by rw [hs_def, inv_lt_one_iff₀]; exact Or.inr ht
  have hst : s * t = 1 := inv_mul_cancel₀ ht0.ne'
  set m : ℝ := 2 * t + 1 with hm_def
  have hm0 : 0 < m := by positivity
  -- the truncation `w_m = max (w, V - m)`
  have hVm : IsThetaPshPotential theta.val (fun x => V x + ((-m : ℝ) : EReal)) :=
    hV.add_const (-m)
  set wm : M → EReal := fun x => max (w x) (V x + ((-m : ℝ) : EReal)) with hwm_def
  have hwmP : IsThetaPshPotential theta.val wm := IsThetaPshPotential.max hw hVm
  have hwwm : w ≤ wm := fun x => le_max_left _ _
  have hwmV : wm ≤ V := fun x => max_le (hwV x) (add_coe_le_self (by linarith) x)
  -- the interpolation `v = (1 - s) V + s w_m`
  have h1s0 : 0 < 1 - s := by linarith
  have h1s1 : 1 - s < 1 := by linarith
  set v : M → EReal := convexComb (1 - s) V wm with hv_def
  have hv : IsThetaPshPotential theta.val v :=
    isThetaPshPotential_convexComb hV hwmP h1s0 h1s1
  have hvV : v ≤ V := by
    refine le_trans (convexComb_mono h1s0.le h1s1.le le_rfl hwmV) ?_
    rw [convexComb_self h1s0 h1s1]
  -- the real coordinates of `V`, `w_m` and `v` off the pole set of `V`
  have hreal : ∀ x, V x ≠ ⊥ → ∃ a c : ℝ, V x = (a : EReal) ∧ wm x = (c : EReal) ∧
      a - m ≤ c ∧ c ≤ a ∧ v x = (((1 - s) * a + s * c : ℝ) : EReal) := by
    intro x hbot
    have hVtop : V x ≠ ⊤ :=
      Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hV x
    obtain ⟨a, ha⟩ : ∃ a : ℝ, V x = (a : EReal) :=
      ⟨(V x).toReal, (EReal.coe_toReal hVtop hbot).symm⟩
    have hge : ((a - m : ℝ) : EReal) ≤ wm x := by
      refine le_trans (le_of_eq ?_) (le_max_right (w x) (V x + ((-m : ℝ) : EReal)))
      rw [ha, ← EReal.coe_add]
      congr 1
    have hwmbot : wm x ≠ ⊥ := by
      intro h
      rw [h] at hge
      exact EReal.coe_ne_bot _ (le_bot_iff.mp hge)
    have hle' : wm x ≤ (a : EReal) := ha ▸ hwmV x
    have hwmtop : wm x ≠ ⊤ := by
      intro h
      rw [h] at hle'
      exact absurd hle' (by simp)
    obtain ⟨c, hc⟩ : ∃ c : ℝ, wm x = (c : EReal) :=
      ⟨(wm x).toReal, (EReal.coe_toReal hwmtop hwmbot).symm⟩
    refine ⟨a, c, ha, hc, ?_, ?_, ?_⟩
    · rw [hc] at hge; exact EReal.coe_le_coe_iff.mp hge
    · rw [hc] at hle'; exact EReal.coe_le_coe_iff.mp hle'
    · rw [hv_def, convexComb_apply, ha, hc, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add]
      congr 1
      ring
  have hVv : ∀ x, V x ≤ v x + ((s * m : ℝ) : EReal) := by
    intro x
    rcases eq_or_ne (V x) ⊥ with hbot | hbot
    · rw [hbot]; exact bot_le
    obtain ⟨a, c, ha, -, hac, -, hvx⟩ := hreal x hbot
    rw [ha, hvx, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [mul_le_mul_of_nonneg_left hac hs0.le]
  -- the target set of the comparison step and its measurability
  set B : Set M := {x | wm x < V x + ((-t : ℝ) : EReal)} with hB_def
  have hBmeas : MeasurableSet B := measurableSet_potential_lt (hV.add_const (-t)) hwmP
  have hBsub : B ⊆ {x | w x < V x + ((-t : ℝ) : EReal)} :=
    fun x hx => lt_of_le_of_lt (hwwm x) hx
  -- the total masses of `v` and `V` agree
  have hmassv : diagonalPotentialMass theta v hv = diagonalPotentialMass theta V hV :=
    le_antisymm
      (diagonalPotentialMass_mono_of_kahler omega hv hV (MoreSingularOn.of_le fun x _ => hvV x))
      (diagonalPotentialMass_mono_of_kahler omega hV hv ⟨s * m, fun x _ => hVv x⟩)
  -- `(1 - s)ⁿ θⁿ_V ≤ θⁿ_v`
  have hdom : ∀ S : Set M, ENNReal.ofReal ((1 - s) ^ n) *
      diagonalPotentialMeasure theta V hV S ≤ diagonalPotentialMeasure theta v hv S := by
    intro S
    exact globalMixedMeasure_diagonal_convexComb_le hV hwmP h1s0 h1s1 S
  -- hence `θⁿ_v` exceeds `θⁿ_V` on `B` by at most `(1 - (1-s)ⁿ)` times the mass
  have hpow1 : (1 - s) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hpq : ENNReal.ofReal ((1 - s) ^ n) + ENNReal.ofReal (1 - (1 - s) ^ n) = 1 := by
    rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
    norm_num
  have hVfin : diagonalPotentialMeasure theta V hV Bᶜ ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega (fun _ => hV.1) _).ne
  have hcancel : ENNReal.ofReal ((1 - s) ^ n) *
      diagonalPotentialMeasure theta V hV Bᶜ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  have hvB : diagonalPotentialMeasure theta v hv B ≤
      ENNReal.ofReal (1 - (1 - s) ^ n) * diagonalPotentialMass theta V hV +
        diagonalPotentialMeasure theta V hV B := by
    refine (ENNReal.add_le_add_iff_right hcancel).mp ?_
    calc diagonalPotentialMeasure theta v hv B +
          ENNReal.ofReal ((1 - s) ^ n) * diagonalPotentialMeasure theta V hV Bᶜ
        ≤ diagonalPotentialMeasure theta v hv B +
            diagonalPotentialMeasure theta v hv Bᶜ := by
          gcongr
          exact hdom Bᶜ
      _ = diagonalPotentialMass theta V hV := by
          rw [← hmassv]
          exact measure_add_measure_compl hBmeas
      _ = diagonalPotentialMeasure theta V hV B +
            diagonalPotentialMeasure theta V hV Bᶜ :=
          (measure_add_measure_compl hBmeas).symm
      _ = diagonalPotentialMeasure theta V hV B +
            (ENNReal.ofReal ((1 - s) ^ n) + ENNReal.ofReal (1 - (1 - s) ^ n)) *
              diagonalPotentialMeasure theta V hV Bᶜ := by
          rw [hpq, one_mul]
      _ = (diagonalPotentialMeasure theta V hV B +
            ENNReal.ofReal (1 - (1 - s) ^ n) *
              diagonalPotentialMeasure theta V hV Bᶜ) +
            ENNReal.ofReal ((1 - s) ^ n) * diagonalPotentialMeasure theta V hV Bᶜ := by
          rw [add_mul]; ring
      _ ≤ (ENNReal.ofReal (1 - (1 - s) ^ n) * diagonalPotentialMass theta V hV +
            diagonalPotentialMeasure theta V hV B) +
            ENNReal.ofReal ((1 - s) ^ n) * diagonalPotentialMeasure theta V hV Bᶜ := by
          refine add_le_add ?_ le_rfl
          rw [add_comm (diagonalPotentialMeasure theta V hV B)]
          gcongr
          exact measure_mono (subset_univ _)
  -- now run one capacity competitor through the comparison principle
  refine thetaCapacity_le_of_forall fun u hu h1 h2 => ?_
  have hd : IsThetaPshPotential theta.val (fun x => u x + ((-1 : ℝ) : EReal)) :=
    hu.add_const (-1)
  have hdv : MoreSingularOn (fun x => u x + ((-1 : ℝ) : EReal)) v univ := by
    refine ⟨s * m - 1, fun x _ => ?_⟩
    calc u x + ((-1 : ℝ) : EReal) ≤ V x + ((-1 : ℝ) : EReal) := by gcongr; exact h1 x
      _ ≤ (v x + ((s * m : ℝ) : EReal)) + ((-1 : ℝ) : EReal) := by gcongr; exact hVv x
      _ = v x + ((s * m - 1 : ℝ) : EReal) := by
          have he : (s * m : ℝ) + (-1 : ℝ) = (s * m - 1 : ℝ) := by ring
          rw [add_assoc, ← EReal.coe_add, he]
  -- the real coordinate of `u` off the pole set of `V`
  have hureal : ∀ x, V x ≠ ⊥ → ∀ a : ℝ, V x = (a : EReal) →
      ∃ b : ℝ, u x = (b : EReal) ∧ a - 1 ≤ b ∧ b ≤ a := by
    intro x hbot a ha
    have hua : u x ≤ (a : EReal) := ha ▸ h1 x
    have hutop : u x ≠ ⊤ := by
      intro h
      rw [h] at hua
      exact absurd hua (by simp)
    have hlow := h2 x
    have hubot : u x ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_add, ha] at hlow
      exact absurd hlow (by simp)
    obtain ⟨b, hb⟩ : ∃ b : ℝ, u x = (b : EReal) :=
      ⟨(u x).toReal, (EReal.coe_toReal hutop hubot).symm⟩
    refine ⟨b, hb, ?_, ?_⟩
    · rw [ha, hb, ← EReal.coe_one, ← EReal.coe_add, EReal.coe_le_coe_iff] at hlow
      linarith
    · rw [hb] at hua; exact EReal.coe_le_coe_iff.mp hua
  have hsub1 : {x | w x < V x + ((-(2 * t) : ℝ) : EReal)} ⊆
      {x | v x < u x + ((-1 : ℝ) : EReal)} := by
    intro x hx
    have hxlt : w x < V x + ((-(2 * t) : ℝ) : EReal) := hx
    have hbot : V x ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_add] at hxlt
      exact absurd hxlt (by simp)
    obtain ⟨a, c, ha, hc, -, -, hvx⟩ := hreal x hbot
    obtain ⟨b, hb, hab, hba⟩ := hureal x hbot a ha
    -- `w x < a - 2t`, and `a - m < a - 2t`, so `c < a - 2t`
    have hwlt : w x < ((a - 2 * t : ℝ) : EReal) := by
      refine lt_of_lt_of_le hxlt (le_of_eq ?_)
      rw [ha, ← EReal.coe_add]
      congr 1
    have hclt : c < a - 2 * t := by
      have : wm x < ((a - 2 * t : ℝ) : EReal) := by
        refine max_lt hwlt ?_
        rw [ha, ← EReal.coe_add, EReal.coe_lt_coe_iff, hm_def]
        linarith
      rw [hc] at this
      exact EReal.coe_lt_coe_iff.mp this
    show v x < u x + ((-1 : ℝ) : EReal)
    rw [hvx, hb, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    have hmul := mul_lt_mul_of_pos_left hclt hs0
    have h2 : s * c < s * a - 2 := by nlinarith [hmul, hst]
    linarith [h2, hab]
  have hsub2 : {x | v x < u x + ((-1 : ℝ) : EReal)} ⊆ B := by
    intro x hx
    have hxlt : v x < u x + ((-1 : ℝ) : EReal) := hx
    have hbot : V x ≠ ⊥ := by
      intro h
      have hub : u x = ⊥ := le_bot_iff.mp (h ▸ h1 x)
      rw [hub, EReal.bot_add] at hxlt
      exact absurd hxlt (by simp)
    obtain ⟨a, c, ha, hc, -, -, hvx⟩ := hreal x hbot
    obtain ⟨b, hb, -, hba⟩ := hureal x hbot a ha
    rw [hvx, hb, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hxlt
    have hclt : c < a - t := by
      have h1' : s * c < s * a - 1 := by linarith
      have hkey : s * c < s * (a - t) := by nlinarith [hst, h1']
      exact lt_of_mul_lt_mul_left hkey hs0.le
    show wm x < V x + ((-t : ℝ) : EReal)
    rw [hc, ha, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith
  calc diagonalPotentialMeasure theta u hu {x | w x < V x + ((-(2 * t) : ℝ) : EReal)}
      = diagonalPotentialMeasure theta (fun x => u x + ((-1 : ℝ) : EReal)) hd
          {x | w x < V x + ((-(2 * t) : ℝ) : EReal)} := by
        rw [diagonalPotentialMeasure_add_const theta hu (-1) hd]
    _ ≤ diagonalPotentialMeasure theta (fun x => u x + ((-1 : ℝ) : EReal)) hd
          {x | v x < u x + ((-1 : ℝ) : EReal)} := measure_mono hsub1
    _ ≤ diagonalPotentialMeasure theta v hv {x | v x < u x + ((-1 : ℝ) : EReal)} :=
        diagonalPotentialMeasure_lt_le omega hv hd hdv
    _ ≤ diagonalPotentialMeasure theta v hv B := measure_mono hsub2
    _ ≤ ENNReal.ofReal (1 - (1 - s) ^ n) * diagonalPotentialMass theta V hV +
          diagonalPotentialMeasure theta V hV B := hvB
    _ ≤ ENNReal.ofReal (1 - (1 - s) ^ n) * diagonalPotentialMass theta V hV +
          diagonalPotentialMeasure theta V hV {x | w x < V x + ((-t : ℝ) : EReal)} := by
        gcongr

/-! ## The capacity of the sublevel sets tends to zero -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The sublevel sets of `w` relative to `V` shrink as the level grows. -/
theorem antitone_sublevel {V w : M → EReal} :
    Antitone fun k : ℕ => {x : M | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} := by
  intro k l hkl x hx
  simp only [mem_ofPred_eq] at hx ⊢
  refine lt_of_lt_of_le hx ?_
  gcongr

/-- **The reference measure of the sublevel sets tends to zero.**  Their
intersection is contained in the pole set of `w`, which is pluripolar, so the
diagonal non-pluripolar measure of `V` — a finite measure — does not charge
it. -/
theorem tendsto_diagonalPotentialMeasure_sublevel (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hw : IsThetaPshPotential theta.val w) :
    Tendsto (fun k : ℕ => diagonalPotentialMeasure theta V hV
      {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)}) atTop (𝓝 0) := by
  have hmeas : ∀ k : ℕ, MeasurableSet {x : M | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} :=
    fun k => measurableSet_potential_lt (hV.add_const (-(k : ℝ))) hw
  have hI : (⋂ k : ℕ, {x : M | w x < V x + ((-(k : ℝ) : ℝ) : EReal)}) ⊆
      {x : M | w x = ⊥} := by
    intro x hx
    simp only [mem_iInter, mem_ofPred_eq] at hx
    by_contra hwbot
    have hwtop : w x ≠ ⊤ :=
      Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hw x
    obtain ⟨d, hd⟩ : ∃ d : ℝ, w x = (d : EReal) :=
      ⟨(w x).toReal, (EReal.coe_toReal hwtop hwbot).symm⟩
    have hVbot : V x ≠ ⊥ := by
      intro h
      have h0 := hx 0
      rw [h, EReal.bot_add] at h0
      exact absurd h0 (by simp)
    have hVtop : V x ≠ ⊤ :=
      Pending.DominationPrincipleBarrier.ne_top_of_isThetaPshPotential hV x
    obtain ⟨a, ha⟩ : ∃ a : ℝ, V x = (a : EReal) :=
      ⟨(V x).toReal, (EReal.coe_toReal hVtop hVbot).symm⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (a - d)
    have hkx := hx k
    rw [hd, ha, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hkx
    linarith
  have hpole : diagonalPotentialMeasure theta V hV {x : M | w x = ⊥} = 0 :=
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (fun _ : Fin n => hV.1) hw
  have h := tendsto_measure_iInter_atTop
    (μ := diagonalPotentialMeasure theta V hV)
    (fun k => (hmeas k).nullMeasurableSet) antitone_sublevel
    ⟨0, (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega
      (fun _ : Fin n => hV.1) _).ne⟩
  rwa [measure_mono_null hI hpole] at h

/-- **Guedj--Zeriahi: the capacity of the sublevel sets tends to zero.**  For
genuine `θ`-PSH potentials `V` (the reference) and `w ≤ V`,

  `Cap_θ({w < V - k}, V) → 0`   as `k → ∞`.

This is what lifts a statement known for `θ`-PSH potentials *bounded relative
to the reference* to arbitrary ones: the truncations `max (w, V - k)` differ
from `w` only on `{w < V - k}`, a set of small capacity.  In particular it is
the input that item 2' of I-0267 (quasi-continuity for unbounded potentials,
I-0282) was missing.

The proof combines `thetaCapacity_sublevel_le` along the doubled sequence with
`tendsto_diagonalPotentialMeasure_sublevel`; the full sequence follows because
the capacities are antitone, so they converge to their infimum, which the
subsequence forces to be `0`. -/
theorem tendsto_thetaCapacity_sublevel (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hw : IsThetaPshPotential theta.val w)
    (hwV : w ≤ V) :
    Tendsto (fun k : ℕ => thetaCapacity theta V
      {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)}) atTop (𝓝 0) := by
  have hGanti : Antitone fun k : ℕ => thetaCapacity theta V
      {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} :=
    fun _ _ hkl => thetaCapacity_mono (antitone_sublevel (V := V) (w := w) hkl)
  have hmassfin : diagonalPotentialMass theta V hV ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega
      (fun _ : Fin n => hV.1) _).ne
  have hbound : ∀ k : ℕ, 2 ≤ k →
      thetaCapacity theta V {x | w x < V x + ((-((2 * k : ℕ) : ℝ) : ℝ) : EReal)} ≤
        ENNReal.ofReal (1 - (1 - (k : ℝ)⁻¹) ^ n) * diagonalPotentialMass theta V hV +
          diagonalPotentialMeasure theta V hV
            {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} := by
    intro k hk
    have hk1 : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_lt_two hk
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]
    exact thetaCapacity_sublevel_le omega hV hw hwV hk1
  have hCtendsto : Tendsto (fun k : ℕ =>
      ENNReal.ofReal (1 - (1 - (k : ℝ)⁻¹) ^ n) * diagonalPotentialMass theta V hV +
        diagonalPotentialMeasure theta V hV
          {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)}) atTop (𝓝 0) := by
    have hinv : Tendsto (fun k : ℕ => ((k : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have h2 : Tendsto (fun k : ℕ => (1 - (k : ℝ)⁻¹ : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    have h1 : Tendsto (fun k : ℕ => (1 - (1 - (k : ℝ)⁻¹) ^ n : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (h2.pow n)
    have h1' : Tendsto (fun k : ℕ =>
        ENNReal.ofReal (1 - (1 - (k : ℝ)⁻¹) ^ n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h4 := ENNReal.Tendsto.mul_const h1' (Or.inr hmassfin)
    rw [zero_mul] at h4
    simpa using h4.add (tendsto_diagonalPotentialMeasure_sublevel omega hV hw)
  have hdouble : Tendsto (fun k : ℕ => thetaCapacity theta V
      {x | w x < V x + ((-((2 * k : ℕ) : ℝ) : ℝ) : EReal)}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCtendsto
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 2] with k hk using hbound k hk
  have hlim := tendsto_atTop_iInf hGanti
  have hzero : (⨅ k : ℕ, thetaCapacity theta V
      {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)}) = 0 := by
    refine le_antisymm ?_ zero_le
    exact ge_of_tendsto hdouble (Eventually.of_forall fun k => iInf_le _ (2 * k))
  rwa [hzero] at hlim

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
