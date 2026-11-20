import SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
import SGPT.Foundations.Analysis.Pending.ThetaCapacityQuasiContinuity

set_option autoImplicit false

/-!
# Quasi-continuity of an unbounded potential over a continuous reference

`Pending.ThetaCapacityQuasiContinuity` proves Xia's Theorem 2.3.2 for a
`θ`-PSH potential that is **globally bounded**, over a globally bounded
reference `V`.  I-0282 records that this is the live gap in item 2 of the
Theorem 2.4.4 stack: `V_θ` is unbounded below as soon as `nK(θ) ≠ ∅`, and more
to the point the potentials one wants to quasi-continue are unbounded.

This module removes the boundedness of the *potential*, at the price of
continuity of the *reference*.  Given `w ≤ V` with `V` continuous and bounded,
for every `ε > 0` there is one open `G` with `Cap_θ(G, V) < ε` outside which
`w` is continuous on all of `M`.

Why continuity of the reference is what is used, and what it replaces.  The
truncations `w_k = max (w, V - k)` are bounded relative to `V`, so the bounded
theorem applies to each of them, and `w_k` *equals* `w` off the sublevel set
`{w < V - k}`, whose capacity tends to `0`
(`ThetaCapacitySublevel.tendsto_thetaCapacity_sublevel`).  So the only thing
missing is that `{w < V - k}` be *open*: the bounded theorem produces an open
exceptional set and the union of the two has to be open again.  `w` is upper
semicontinuous, so `{w < V - k}` is open exactly when `V` is lower
semicontinuous, i.e. — `V` being quasi-PSH, hence upper semicontinuous —
exactly when `V` is continuous.  Without that, what is needed instead is outer
regularity of `Cap_θ`, which this workspace does not have.

The hypothesis is satisfied in the case the rest of Section 2.4 is run in: a
semipositive `θ` with `V = 0`, and more generally any continuous reference
potential.

Source: M. Xia, *Non-pluripolar products on vector bundles and Chern--Weil
formulae*, Theorem 2.3.2 (`xia-sgpt:page-0063`); V. Guedj and A. Zeriahi,
*Intrinsic capacities on compact Kähler manifolds*, J. Geom. Anal. 15 (2005).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityUnboundedQuasiContinuity

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
open SGPT.Foundations.Analysis.Pending.ThetaCapacityQuasiContinuity
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- An upper semicontinuous function is below a continuous one on an open
set. -/
theorem isOpen_lt_of_upperSemicontinuous {X : Type*} [TopologicalSpace X]
    {f g : X → EReal} (hf : UpperSemicontinuous f) (hg : Continuous g) :
    IsOpen {x | f x < g x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨cc, hfc, hcg⟩ := exists_between (show f x < g x from hx)
  filter_upwards [hf x cc hfc, (isOpen_lt continuous_const hg).mem_nhds hcg]
    with y h1 h2 using h1.trans h2

/-- **Xia, Theorem 2.3.2 for an unbounded potential over a continuous
reference.**  For genuine `θ`-PSH potentials `V`, `w` with `w ≤ V`, `V`
globally bounded and continuous, and every `ε > 0`, there is one open `G` with
`Cap_θ(G, V) < ε` outside which `w` is continuous on all of `M`.

The exceptional set is the union of the one the bounded theorem gives for the
truncation `max (w, V - k)` and the sublevel set `{w < V - k}`, which is open
because `w` is upper semicontinuous and `V` is continuous, and whose capacity
is small for `k` large by the Guedj--Zeriahi estimate. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_compl_of_le
    (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hw : IsThetaPshPotential theta.val w)
    (hwV : w ≤ V) {c d : ℝ} (hcd : c ≤ d)
    (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (hVcont : Continuous fun x => (V x).toReal)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (w y).toReal) Gᶜ := by
  classical
  have heps2 : (0 : ℝ) < eps / 2 := by linarith
  -- `V` is real valued, and the coercion of its real form is `V` itself
  have hVreal : ∀ x, V x = (((V x).toReal : ℝ) : EReal) := by
    intro x
    refine (EReal.coe_toReal ?_ ?_).symm
    · exact fun h => absurd (h ▸ (hVbd x).2) (by simp)
    · exact fun h => absurd (h ▸ (hVbd x).1) (by simp)
  -- a level at which the sublevel set already has small capacity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, thetaCapacity theta V
      {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} < ENNReal.ofReal (eps / 2) :=
    ((tendsto_thetaCapacity_sublevel omega hV hw hwV).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 heps2))).exists
  set E : Set M := {x | w x < V x + ((-(k : ℝ) : ℝ) : EReal)} with hE_def
  -- `E` is open: `w` is upper semicontinuous and the right-hand side is continuous
  have hEopen : IsOpen E := by
    have hcont : Continuous fun x : M => V x + ((-(k : ℝ) : ℝ) : EReal) := by
      have : (fun x : M => V x + ((-(k : ℝ) : ℝ) : EReal)) =
          fun x : M => ((((V x).toReal - (k : ℝ)) : ℝ) : EReal) := by
        funext x
        rw [hVreal x, ← EReal.coe_add]
        congr 1
      rw [this]
      exact continuous_coe_real_ereal.comp (hVcont.sub continuous_const)
    exact isOpen_lt_of_upperSemicontinuous
      hw.1.quasiPlurisubharmonic.upperSemicontinuous hcont
  -- the truncation is a bounded potential
  set wk : M → EReal := fun x => max (w x) (V x + ((-(k : ℝ) : ℝ) : EReal)) with hwk_def
  have hwkP : IsThetaPshPotential theta.val wk :=
    IsThetaPshPotential.max hw (hV.add_const (-(k : ℝ)))
  have hknn : (-(k : ℝ)) ≤ 0 := neg_nonpos.2 (Nat.cast_nonneg k)
  have hwkb : IsBoundedPotential wk := by
    refine ⟨c - (k : ℝ), d, fun x => ⟨?_, ?_⟩⟩
    · calc ((c - (k : ℝ) : ℝ) : EReal) = (c : EReal) + ((-(k : ℝ) : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
        _ ≤ V x + ((-(k : ℝ) : ℝ) : EReal) := by gcongr; exact (hVbd x).1
        _ ≤ wk x := le_max_right _ _
    · exact le_trans (max_le (hwV x) (add_coe_le_self hknn x)) (hVbd x).2
  -- the bounded theorem, applied to the truncation
  obtain ⟨G', hG'open, hG'cap, hG'cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_compl hwkP hwkb hcd hVbd heps2
  refine ⟨G' ∪ E, hG'open.union hEopen, ?_, ?_⟩
  · calc thetaCapacity theta V (G' ∪ E)
        ≤ thetaCapacity theta V G' + thetaCapacity theta V E :=
          thetaCapacity_union_le theta V G' E
      _ < ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) :=
          ENNReal.add_lt_add hG'cap hk
      _ = ENNReal.ofReal eps := by
          rw [← ENNReal.ofReal_add heps2.le heps2.le]
          norm_num
  · refine ContinuousOn.congr (hG'cont.mono (compl_subset_compl.2 subset_union_left)) ?_
    intro y hy
    have hyE : y ∉ E := fun h => hy (Or.inr h)
    have hle : V y + ((-(k : ℝ) : ℝ) : EReal) ≤ w y := not_lt.mp hyE
    have hwy : wk y = w y := max_eq_left hle
    show (w y).toReal = (wk y).toReal
    rw [hwy]

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityUnboundedQuasiContinuity
