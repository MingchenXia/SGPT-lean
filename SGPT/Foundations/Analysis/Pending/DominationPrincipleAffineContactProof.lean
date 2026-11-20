import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable
import SGPT.Foundations.Analysis.Pending.RooftopAffineObstacleQuasiContinuity
import SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContactQE
import SGPT.Foundations.Analysis.Pending.RooftopDecreasingLimitQE
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.RooftopMinConcentration
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 at the affine obstacle `a phi + (1-a) psi` (I-0510, C6)

The ordered case of Xia's domination principle (Theorem 2.4.5, `xia-sgpt:page-0083`, (2.30))
applies Theorem 2.4.4 (`xia-sgpt:page-0079`, (2.23)) to the affine obstacle

  `eta = a phi + (1-a) psi`,   `a > 1`,   `phi <= psi`,

which is not upper semicontinuous.  This module proves that instance
(`xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le`, the statement of
`DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero` without its
two hypotheses `hpos`, `hmass`, which only Theorem 2.4.5 uses).

**Route.**  Xia's proof of Theorem 2.4.4 runs Step 1.2 (the obstacle truncated from below) and
Step 2 (a quasi-continuous bounded obstacle, approximated by Tietze extensions off sets of small
capacity).  For the affine obstacle Step 2 is not needed, because `eta` is the sum of an upper
semicontinuous function `a phi` and a **lower** semicontinuous one `(1-a) psi`.  After the
normalisation `phi <= psi <= 0`, with `g_m` continuous and decreasing to `phi`, the functions

  `H_m = min (a g_m + (1-a) psi, 0)`

are bounded, lower semicontinuous, decreasing in `m`, lie above `eta` everywhere, and decrease
to `eta` off the pole set of `psi` (`affineMajorant`).  Their envelopes `p_m = P_theta(H_m)`
are therefore an admissible family for Xia's Step 1.2 in its measurable form
(`RooftopTruncationConcentrationMeasurable.diagonalPotentialMeasure_lt_eq_zero_of_antitone_family`):

* `theta^n_{p_m}` is carried by `{p_m = H_m}` — Theorem 2.4.4 for a bounded lower
  semicontinuous obstacle (`PolydiskPatchBalayageContactQE`), hence gives no mass to
  `{p_m < eta}`;
* `p_m` decreases to `P_theta(eta)`: the envelopes commute with the decreasing limit
  (`RooftopDecreasingLimitQE`, with Xia's (2.20) quasi-everywhere and countable stability of
  pluripolarity), and the limit obstacle agrees with `eta` quasi-everywhere, which the envelope
  does not see (`rooftopEnvelope_congr_qe`);
* the reference truncations of `eta` are quasi-continuous (`RooftopAffineObstacleQuasiContinuity`).

The classes that are not big carry no non-pluripolar mass (`NonBigPotentialMass`), and in
dimension `0` the obstacle is itself a competitor, so the non-contact set is empty.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactProof

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.RooftopAffineObstacleQuasiContinuity
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

noncomputable section

/-! ### Quasi-everywhere invariance of the envelope -/

section Congr

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {theta : SmoothRealForm n M 2}

/-- Obstacles that agree quasi-everywhere have the same competitors: competitors are only
asked to lie below the obstacle quasi-everywhere. -/
theorem rooftopCompetitors_congr_qe {f g : M → EReal}
    (h : QuasiEverywhere (n := n) fun x => f x = g x) :
    rooftopCompetitors theta f = rooftopCompetitors theta g := by
  ext u
  constructor
  · rintro ⟨hu, huf⟩
    exact ⟨hu, (quasiEverywhere_and huf h).mono fun x hx => hx.2 ▸ hx.1⟩
  · rintro ⟨hu, hug⟩
    exact ⟨hu, (quasiEverywhere_and hug h).mono fun x hx => hx.2.symm ▸ hx.1⟩

/-- **The rooftop envelope does not see the obstacle on a pluripolar set.** -/
theorem rooftopEnvelope_congr_qe {f g : M → EReal}
    (h : QuasiEverywhere (n := n) fun x => f x = g x) :
    rooftopEnvelope theta f = rooftopEnvelope theta g := by
  unfold rooftopEnvelope rooftopSupremum
  rw [rooftopCompetitors_congr_qe h]

end Congr

/-! ### The lower semicontinuous majorants of the affine obstacle -/

section Majorant

/-- A negative multiple of a nonpositive extended real is nonnegative. -/
theorem coe_mul_nonneg_of_nonpos {c : ℝ} (hc : c ≤ 0) {y : EReal} (hy : y ≤ 0) :
    0 ≤ (c : EReal) * y :=
  EReal.mul_nonneg_iff.mpr (Or.inr ⟨EReal.coe_nonpos.mpr hc, hy⟩)

/-- Multiplication by a nonzero real is continuous on `EReal`. -/
theorem continuous_coe_mul {c : ℝ} (hc : c ≠ 0) : Continuous fun t : EReal => (c : EReal) * t :=
  continuous_iff_continuousAt.mpr fun t =>
    (EReal.continuousAt_mul (p := ((c : EReal), t)) (Or.inl (by simpa using hc))
      (Or.inl (by simpa using hc)) (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).comp
      (continuousAt_const.prodMk continuousAt_id)

/-- `x ↦ c * u x` is lower semicontinuous for `c < 0` and `u` upper semicontinuous. -/
theorem lowerSemicontinuous_coe_mul_of_neg {X : Type*} [TopologicalSpace X] {c : ℝ}
    (hc : c < 0) {u : X → EReal} (hu : UpperSemicontinuous u) :
    LowerSemicontinuous fun x => (c : EReal) * u x := by
  have hanti : Antitone fun t : EReal => (c : EReal) * t := by
    intro s t hst
    show (c : EReal) * t ≤ (c : EReal) * s
    rw [mul_comm (c : EReal) t, mul_comm (c : EReal) s]
    exact EReal.mul_le_mul_of_nonpos_right hst (EReal.coe_nonpos.mpr hc.le)
  exact (continuous_coe_mul hc.ne).comp_upperSemicontinuous_antitone hu hanti

/-- The `EReal` form of the majorant: `min (a g + (1-a) psi, 0)`. -/
def affineMajorantE {X : Type*} (a : ℝ) (g : X → ℝ) (psi : X → EReal) (x : X) : EReal :=
  min (((a * g x : ℝ) : EReal) + ((1 - a : ℝ) : EReal) * psi x) 0

/-- **The majorant** `H = min (a g + (1-a) psi, 0)`, as a real function. -/
def affineMajorant {X : Type*} (a : ℝ) (g : X → ℝ) (psi : X → EReal) (x : X) : ℝ :=
  (affineMajorantE a g psi x).toReal

variable {X : Type*} {a : ℝ} {g : X → ℝ} {psi : X → EReal}

theorem affineMajorantE_le_zero (x : X) : affineMajorantE a g psi x ≤ 0 := min_le_right _ _

theorem min_coe_le_affineMajorantE (ha : 1 ≤ a) (hpsi0 : ∀ x, psi x ≤ 0) (x : X) :
    ((min (a * g x) 0 : ℝ) : EReal) ≤ affineMajorantE a g psi x := by
  refine le_min ?_ ?_
  · refine (EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans ?_
    exact le_add_of_nonneg_right (coe_mul_nonneg_of_nonpos (by linarith) (hpsi0 x))
  · exact EReal.coe_le_coe_iff.mpr (min_le_right _ _) |>.trans_eq (by simp)

theorem coe_affineMajorant (ha : 1 ≤ a) (hpsi0 : ∀ x, psi x ≤ 0) (x : X) :
    ((affineMajorant a g psi x : ℝ) : EReal) = affineMajorantE a g psi x := by
  refine EReal.coe_toReal (ne_top_of_le_ne_top (by simp) (affineMajorantE_le_zero x)) ?_
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (min_coe_le_affineMajorantE ha hpsi0 x)

theorem affineMajorant_le_zero (x : X) : affineMajorant a g psi x ≤ 0 :=
  EReal.toReal_nonpos (affineMajorantE_le_zero x)

theorem abs_affineMajorant_le (ha : 1 ≤ a) (hpsi0 : ∀ x, psi x ≤ 0) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) (x : X) : |affineMajorant a g psi x| ≤ a * B := by
  have h0 := affineMajorant_le_zero (a := a) (g := g) (psi := psi) x
  have h1 : min (a * g x) 0 ≤ affineMajorant a g psi x := by
    have := min_coe_le_affineMajorantE (g := g) ha hpsi0 x
    rwa [← coe_affineMajorant ha hpsi0, EReal.coe_le_coe_iff] at this
  have hg : -B ≤ g x := (abs_le.mp (hB x)).1
  have ha0 : 0 ≤ a := by linarith
  rw [abs_of_nonpos h0]
  have : -(a * B) ≤ min (a * g x) 0 := le_min (by nlinarith) (by nlinarith [abs_nonneg (g x),
    (abs_le.mp (hB x)).2])
  linarith

theorem lowerSemicontinuous_affineMajorant [TopologicalSpace X] (ha : 1 < a)
    (hg : Continuous g) (hpsi : UpperSemicontinuous psi) (hpsi0 : ∀ x, psi x ≤ 0) :
    LowerSemicontinuous (affineMajorant a g psi) := by
  have hE : LowerSemicontinuous (affineMajorantE a g psi) := by
    have h1 : LowerSemicontinuous fun x => ((a * g x : ℝ) : EReal) :=
      (continuous_coe_real_ereal.comp (continuous_const.mul hg)).lowerSemicontinuous
    have h2 : LowerSemicontinuous fun x => ((1 - a : ℝ) : EReal) * psi x :=
      lowerSemicontinuous_coe_mul_of_neg (by linarith) hpsi
    have h12 : LowerSemicontinuous fun x =>
        ((a * g x : ℝ) : EReal) + ((1 - a : ℝ) : EReal) * psi x :=
      h1.add' h2 fun x => EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
        (Or.inl (EReal.coe_ne_bot _))
    exact h12.inf lowerSemicontinuous_const
  intro x r hr
  have hr' : (r : EReal) < affineMajorantE a g psi x := by
    rw [← coe_affineMajorant ha.le hpsi0]; exact EReal.coe_lt_coe_iff.mpr hr
  filter_upwards [hE x r hr'] with y hy
  rw [← coe_affineMajorant ha.le hpsi0] at hy
  exact EReal.coe_lt_coe_iff.mp hy

/-- The majorants decrease with the continuous functions they are built from. -/
theorem affineMajorant_antitone (ha : 1 ≤ a) (hpsi0 : ∀ x, psi x ≤ 0) {g : ℕ → X → ℝ}
    (hganti : ∀ x, Antitone fun m => g m x) (x : X) :
    Antitone fun m => affineMajorant a (g m) psi x := by
  intro i j hij
  rw [← EReal.coe_le_coe_iff, coe_affineMajorant ha hpsi0, coe_affineMajorant ha hpsi0]
  refine min_le_min_right _ (add_le_add ?_ le_rfl)
  exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (hganti x hij) (by linarith))

/-- **The majorants lie above the affine obstacle.** -/
theorem convexComb_le_affineMajorant (ha : 1 < a) {phi : X → EReal}
    (hle : ∀ x, phi x ≤ psi x) (hpsi0 : ∀ x, psi x ≤ 0)
    (hgmaj : ∀ x, phi x ≤ ((g x : ℝ) : EReal)) (x : X) :
    convexComb a phi psi x ≤ ((affineMajorant a g psi x : ℝ) : EReal) := by
  rw [coe_affineMajorant ha.le hpsi0]
  refine le_min ?_ ?_
  · rw [convexComb_apply, EReal.coe_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hgmaj x) (EReal.coe_nonneg.mpr (by linarith))) le_rfl
  · exact (coe_mul_add_coe_mul_le ha (hle x) (ne_top_of_le_ne_top (by simp) (hpsi0 x))).trans
      ((hle x).trans (hpsi0 x))

/-- **The majorants decrease to the affine obstacle off the poles of `psi`.** -/
theorem iInf_affineMajorant_eq (ha : 1 < a) {phi : X → EReal} {g : ℕ → X → ℝ}
    (hle : ∀ x, phi x ≤ psi x) (hpsi0 : ∀ x, psi x ≤ 0)
    (hganti : ∀ x, Antitone fun m => g m x)
    (hginf : ∀ x, (⨅ m : ℕ, ((g m x : ℝ) : EReal)) = phi x) {x : X} (hx : psi x ≠ ⊥) :
    (⨅ m : ℕ, ((affineMajorant a (g m) psi x : ℝ) : EReal)) = convexComb a phi psi x := by
  have hanti : Antitone fun m => ((affineMajorant a (g m) psi x : ℝ) : EReal) :=
    fun i j hij => EReal.coe_le_coe_iff.mpr (affineMajorant_antitone ha.le hpsi0 hganti x hij)
  have hpsitop : psi x ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hpsi0 x)
  set r : ℝ := (1 - a) * (psi x).toReal with hrdef
  have hr : ((1 - a : ℝ) : EReal) * psi x = (r : EReal) := by
    rw [hrdef, EReal.coe_mul, EReal.coe_toReal hpsitop hx]
  -- the continuous parts converge to `a phi`
  have hgt : Tendsto (fun m => ((g m x : ℝ) : EReal)) atTop (𝓝 (phi x)) := by
    rw [← hginf x]
    exact tendsto_atTop_iInf fun i j hij => EReal.coe_le_coe_iff.mpr (hganti x hij)
  have hagt : Tendsto (fun m => ((a * g m x : ℝ) : EReal)) atTop (𝓝 ((a : EReal) * phi x)) := by
    have := ((continuous_coe_mul (c := a) (by linarith)).tendsto (phi x)).comp hgt
    simpa only [Function.comp_def, EReal.coe_mul] using this
  have hsum : Tendsto (fun m => ((a * g m x : ℝ) : EReal) + (r : EReal)) atTop
      (𝓝 ((a : EReal) * phi x + (r : EReal))) :=
    ((EReal.continuousAt_add (p := ((a : EReal) * phi x, (r : EReal)))
      (Or.inr (EReal.coe_ne_bot r)) (Or.inr (EReal.coe_ne_top r))).tendsto).comp
      (hagt.prodMk_nhds tendsto_const_nhds)
  have hlim : Tendsto (fun m => ((affineMajorant a (g m) psi x : ℝ) : EReal)) atTop
      (𝓝 (min ((a : EReal) * phi x + (r : EReal)) 0)) := by
    have := hsum.min (tendsto_const_nhds (x := (0 : EReal)))
    refine this.congr fun m => ?_
    rw [coe_affineMajorant ha.le hpsi0, affineMajorantE, hr]
  have heta0 : convexComb a phi psi x ≤ 0 :=
    (coe_mul_add_coe_mul_le ha (hle x) hpsitop).trans ((hle x).trans (hpsi0 x))
  rw [tendsto_nhds_unique (tendsto_atTop_iInf hanti) hlim, ← hr, ← convexComb_apply]
  exact min_eq_left heta0

end Majorant

/-! ### Theorem 2.4.4 at the affine obstacle -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia's Theorem 2.4.4 at the affine obstacle, normalised form** (`n > 0`, big class,
`phi <= psi <= 0`). -/
theorem diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero_of_nonpos (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hle : ∀ x, phi x ≤ psi x) (hpsi0 : ∀ x, psi x ≤ 0) {a : ℝ} (ha : 1 < a)
    (heta : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x < convexComb a phi psi x} = 0 := by
  classical
  set eta : M → EReal := convexComb a phi psi with hetadef
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  have hV : IsThetaPshPotential theta.val V :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨_, hphi⟩
  have hV0 : ∀ x, V x ≤ (0 : EReal) := fun x => by
    simpa [hVdef] using thetaPshSupremum_le_zero theta.val x
  have hpsitop : ∀ x, psi x ≠ ⊤ := fun x => ne_top_of_le_ne_top (by simp) (hpsi0 x)
  have hphitop : ∀ x, phi x ≠ ⊤ := fun x => ne_top_of_le_ne_top (hpsitop x) (hle x)
  have heta0 : ∀ x, eta x ≤ 0 := fun x =>
    (convexComb_le_left ha hle hpsitop x).trans ((hle x).trans (hpsi0 x))
  have hcount := PluripolarOuterCapacity.countablyStablePluripolar omega (n := n) (M := M)
  -- the continuous majorants of `phi` and the lower semicontinuous majorants of `eta`
  obtain ⟨-, g, hgcont, hgmaj, -, hganti, hginf⟩ :=
    exists_continuous_antitone_majorants n hphi.1.quasiPlurisubharmonic.upperSemicontinuous
      hphitop
  have hgB : ∀ m, ∃ B : ℝ, ∀ x, |g m x| ≤ B := fun m => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hgcont m).continuousOn
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x (mem_univ x)⟩
  choose B hB using hgB
  set H : ℕ → M → ℝ := fun m => affineMajorant a (g m) psi with hHdef
  have hpsiusc : UpperSemicontinuous psi := hpsi.1.quasiPlurisubharmonic.upperSemicontinuous
  have hHlsc : ∀ m, LowerSemicontinuous (H m) := fun m =>
    lowerSemicontinuous_affineMajorant ha (hgcont m) hpsiusc hpsi0
  have hHabs : ∀ m x, |H m x| ≤ a * B m := fun m x =>
    abs_affineMajorant_le ha.le hpsi0 (hB m) x
  have hH0 : ∀ m x, H m x ≤ 0 := fun m x => affineMajorant_le_zero x
  have hetaH : ∀ m x, eta x ≤ ((H m x : ℝ) : EReal) := fun m x =>
    convexComb_le_affineMajorant ha hle hpsi0 (hgmaj m) x
  have hHanti : ∀ x, Antitone fun m => H m x := fun x =>
    affineMajorant_antitone ha.le hpsi0 hganti x
  -- the envelopes of the majorants
  set p : ℕ → M → EReal := fun m => rooftopEnvelope theta.val fun x => ((H m x : ℝ) : EReal)
    with hpdef
  have hp : ∀ m, IsThetaPshPotential theta.val (p m) := by
    intro m
    refine isThetaPshPotential_rooftop_of_nonempty ?_
      (rooftopCompetitors_bddAbove (theta := theta) (B := 0) (hH0 m))
    refine ⟨fun x => V x + ((-(a * B m) : ℝ) : EReal), hV.add_const _,
      quasiEverywhere_of_forall fun x => ?_⟩
    calc V x + ((-(a * B m) : ℝ) : EReal) ≤ 0 + ((-(a * B m) : ℝ) : EReal) :=
          add_le_add (hV0 x) le_rfl
      _ = ((-(a * B m) : ℝ) : EReal) := zero_add _
      _ ≤ ((H m x : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (abs_le.mp (hHabs m x)).1
  have hple : ∀ m, QuasiEverywhere (n := n)
      (fun x => p m x ≤ ((H m x : ℝ) : EReal)) := fun m =>
    PolydiskPatchBalayageContactQE.rooftopEnvelope_le_quasiEverywhere_of_kahler omega theta (hp m)
  have hp0 : ∀ m x, p m x ≤ 0 := by
    intro m x
    have h := le_coe_of_ae_in_charts_le (F := fun _ => (0 : ℝ)) (hp m).1 continuous_const
      (fun e => by
        filter_upwards [(hple m).ae_in_chart e volume] with z hz
        exact hz.trans (EReal.coe_le_coe_iff.mpr (hH0 m _))) x
    simpa using h
  have hpanti : ∀ x, Antitone fun m => p m x := fun x i j hij =>
    rooftopEnvelope_mono (θ := theta.val)
      (fun y => EReal.coe_le_coe_iff.mpr (hHanti y hij)) x
  have hwp : ∀ m x, rooftopEnvelope theta.val eta x ≤ p m x := fun m x =>
    rooftopEnvelope_mono (θ := theta.val) (fun y => hetaH m y) x
  -- the limit obstacle agrees with `eta` off the poles of `psi`
  set etaT : M → EReal := fun x => ⨅ m : ℕ, ((H m x : ℝ) : EReal) with hetaTdef
  have hqe : QuasiEverywhere (n := n) fun x => etaT x = eta x := by
    refine ManifoldLocallyPluripolar.mono
      (quasiPsh_poles_manifoldLocallyPluripolar hpsi.quasiPshPotential) fun x hx => ?_
    by_contra hbot
    exact hx (iInf_affineMajorant_eq ha hle hpsi0 hganti hginf hbot)
  have henv : rooftopEnvelope theta.val etaT = rooftopEnvelope theta.val eta :=
    rooftopEnvelope_congr_qe hqe
  have hne : (rooftopCompetitors theta.val etaT).Nonempty := by
    rw [rooftopCompetitors_congr_qe hqe]
    exact rooftopCompetitors_nonempty_of_isThetaPshPotential heta
  have hplim : ∀ x, Tendsto (fun m => p m x) atTop (𝓝 (rooftopEnvelope theta.val eta x)) := by
    intro x
    rw [← henv]
    exact RooftopDecreasingLimitQE.tendsto_rooftopEnvelope_of_antitone_qe hcount
      (F := fun m y => ((H m y : ℝ) : EReal)) (fun y => rfl)
      (fun y i j hij => EReal.coe_le_coe_iff.mpr (hHanti y hij)) (fun m => (hp m).1) hple hne x
  have hzero : ∀ m, diagonalPotentialMeasure theta (p m) (hp m) {y | p m y < eta y} = 0 := by
    intro m
    refine measure_mono_null (fun y hy => lt_of_lt_of_le hy (hetaH m y)) ?_
    exact PolydiskPatchBalayageContactQE.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_kahler
      hn omega theta hbig hV (hHlsc m) (hHabs m) (hp m)
  have hmeas : Measurable eta :=
    measurable_convexComb hphi.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      hpsiusc.measurable a
  exact diagonalPotentialMeasure_lt_eq_zero_of_antitone_family hn hbig hV hmeas heta0
    (refTruncationsQuasiContinuous_convexComb hphi hpsi hV hle hpsi0 ha) hp hp0 hpanti heta
    hwp hplim hzero

/-! ### Normalisation, non-big classes, dimension zero -/

/-- Scaling by any real number distributes over a finite real shift in `EReal`. -/
theorem coe_mul_add_coe' (c : ℝ) (y : EReal) (r : ℝ) :
    (c : EReal) * (y + (r : EReal)) = (c : EReal) * y + ((c * r : ℝ) : EReal) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · induction y using EReal.rec with
    | bot => rw [EReal.bot_add, EReal.coe_mul_bot_of_neg hc, EReal.top_add_coe]
    | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_neg hc, EReal.bot_add]
    | coe y => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]
  · simp
  · exact coe_mul_add_coe hc y r

/-- **The affine obstacle commutes with a common shift** (`a + (1-a) = 1`). -/
theorem convexComb_add_const {X : Type*} (a : ℝ) (phi psi : X → EReal) (r : ℝ) :
    convexComb a (fun x => phi x + (r : EReal)) (fun x => psi x + (r : EReal)) =
      fun x => convexComb a phi psi x + (r : EReal) := by
  funext x
  simp only [convexComb_apply]
  rw [coe_mul_add_coe', coe_mul_add_coe', add_add_add_comm, ← EReal.coe_add]
  congr 2
  ring

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] [Nonempty M] in
/-- **In dimension `0` the affine obstacle is a competitor of itself**, so the non-contact set
is empty. -/
theorem convexComb_le_rooftopEnvelope_of_dim_zero (hn : n = 0)
    {theta : SmoothRealForm n M 2} {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta phi) (hpsi : IsThetaPshPotential theta psi) (a : ℝ)
    (x : M) : convexComb a phi psi x ≤ rooftopEnvelope theta (convexComb a phi psi) x := by
  have hreal : ∀ {u : M → EReal}, IsThetaPshPotential theta u → ∀ y, ∃ r : ℝ, u y = (r : EReal) :=
    fun {u} hu y => ⟨(u y).toReal, (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top y)
      (RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero hn hu.2 y)).symm⟩
  have hfin : ∀ y, ∃ r : ℝ, convexComb a phi psi y = (r : EReal) := by
    intro y
    obtain ⟨s, hs⟩ := hreal hphi y
    obtain ⟨t, ht⟩ := hreal hpsi y
    exact ⟨a * s + (1 - a) * t, by
      rw [convexComb_apply, hs, ht, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]⟩
  have heta : IsThetaPshPotential theta (convexComb a phi psi) := by
    refine RooftopDimZero.isThetaPshPotential_of_dim_zero hn hphi.1.hasSmoothLocalPotentials
      (fun y => ?_) (fun y => ?_)
    · obtain ⟨r, hr⟩ := hfin y; rw [hr]; exact EReal.coe_ne_top r
    · obtain ⟨r, hr⟩ := hfin y; rw [hr]; exact EReal.coe_ne_bot r
  exact le_rooftopEnvelope heta (quasiEverywhere_of_forall fun y => le_rfl) x

/-- **Xia, SGPT, Theorem 2.4.4 at the affine obstacle, for a big class** — the same statement as
`xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le` with `IsBigClass {θ}` assumed.  This form
does not pass through `NonBigPotentialMass` and hence not through the named input
`UniformAmbientVolumeBigness` (Boucksom 4.8): `#print axioms` is clean.  Any dimension. -/
theorem xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le_of_isBigClass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi) (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {a : ℝ} (ha : 1 < a)
    (heta : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (convexComb a phi psi)) heta
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- dimension `0`: the non-contact set is empty
    have hemp : {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx =>
        (not_lt.mpr (convexComb_le_rooftopEnvelope_of_dim_zero hn hphi hpsi a x)) hx
    rw [hemp]
    exact measure_empty
  -- Step 1.1: normalise both potentials by one common constant
  obtain ⟨A, hA⟩ := hpsi.exists_global_upper_bound
  have hphi' : IsThetaPshPotential theta.val (fun x => phi x + ((-A : ℝ) : EReal)) :=
    hphi.add_const _
  have hpsi' : IsThetaPshPotential theta.val (fun x => psi x + ((-A : ℝ) : EReal)) :=
    hpsi.add_const _
  have hle' : ∀ x, phi x + ((-A : ℝ) : EReal) ≤ psi x + ((-A : ℝ) : EReal) := fun x =>
    add_le_add (hle x) le_rfl
  have hpsi'0 : ∀ x, psi x + ((-A : ℝ) : EReal) ≤ 0 := by
    intro x
    calc psi x + ((-A : ℝ) : EReal) ≤ (A : EReal) + ((-A : ℝ) : EReal) := add_le_add (hA x) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hcomb := convexComb_add_const a phi psi (-A)
  have henv : rooftopEnvelope theta.val (convexComb a (fun x => phi x + ((-A : ℝ) : EReal))
      (fun x => psi x + ((-A : ℝ) : EReal))) =
      fun x => rooftopEnvelope theta.val (convexComb a phi psi) x + ((-A : ℝ) : EReal) := by
    rw [hcomb]
    exact RooftopEnvelopeNormalization.rooftopEnvelope_add_const theta.val _ (-A)
  have hwshift : IsThetaPshPotential theta.val
      (fun x => rooftopEnvelope theta.val (convexComb a phi psi) x + ((-A : ℝ) : EReal)) :=
    heta.add_const _
  have heta' : IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (convexComb a (fun x => phi x + ((-A : ℝ) : EReal)) (fun x => psi x + ((-A : ℝ) : EReal)))) := by
    rw [henv]; exact hwshift
  have hzero := diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero_of_nonpos hn omega
    theta hbig hphi' hpsi' hle' hpsi'0 ha heta'
  -- transport the measure and the set back
  have hmeaseq : diagonalPotentialMeasure theta (rooftopEnvelope theta.val
      (convexComb a (fun x => phi x + ((-A : ℝ) : EReal))
        (fun x => psi x + ((-A : ℝ) : EReal)))) heta' =
      diagonalPotentialMeasure theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta := by
    rw [MaxMassDecomposition.diagonalPotentialMeasure_congr heta' hwshift henv]
    exact DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const theta heta (-A) hwshift
  have hseteq : {y : M | rooftopEnvelope theta.val (convexComb a
        (fun x => phi x + ((-A : ℝ) : EReal)) (fun x => psi x + ((-A : ℝ) : EReal))) y <
        convexComb a (fun x => phi x + ((-A : ℝ) : EReal))
          (fun x => psi x + ((-A : ℝ) : EReal)) y} =
      {x : M | rooftopEnvelope theta.val (convexComb a phi psi) x < convexComb a phi psi x} := by
    ext y
    show rooftopEnvelope theta.val (convexComb a
        (fun x => phi x + ((-A : ℝ) : EReal)) (fun x => psi x + ((-A : ℝ) : EReal))) y <
        convexComb a (fun x => phi x + ((-A : ℝ) : EReal))
          (fun x => psi x + ((-A : ℝ) : EReal)) y ↔ _
    rw [congrFun henv y, congrFun hcomb y]
    exact RooftopMinConcentration.add_coe_lt_add_coe_iff (-A)
  rw [← hmeaseq, ← hseteq]
  exact hzero

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, (2.23)) at the affine obstacle of
Theorem 2.4.5** (`xia-sgpt:page-0083`, (2.30)): for `theta`-PSH potentials `phi <= psi` and
`a > 1`, if `P_theta(a phi + (1-a) psi)` is a `theta`-PSH potential then its non-pluripolar
Monge--Ampère measure gives no mass to `{P_theta(a phi + (1-a) psi) < a phi + (1-a) psi}`.

This is `DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`
without the hypotheses `hpos`, `hmass` (used only by Theorem 2.4.5 itself).  Any dimension,
any class. -/
theorem xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi) {a : ℝ} (ha : 1 < a)
    (heta : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (convexComb a phi psi)) heta
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- dimension `0`: the non-contact set is empty
    have hemp : {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx =>
        (not_lt.mpr (convexComb_le_rooftopEnvelope_of_dim_zero hn hphi hpsi a x)) hx
    rw [hemp]
    exact measure_empty
  by_cases hbig : IsBigClass (RealBottChern.ofRepresentative theta)
  · exact xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le_of_isBigClass omega theta hphi
      hpsi hle hbig ha heta
  · exact NonBigPotentialMass.diagonalPotentialMeasure_eq_zero_of_not_isBigClass omega theta
      heta hbig _

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactProof
