import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeBarrierInterface
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOneAssembly
import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

set_option autoImplicit false

/-!
# Xia's Lemma 2.4.4: the envelope of an affine obstacle, and its mass

Xia, SGPT, Lemma 2.4.4 (`xia-sgpt:page-0083`).  For `φ ≤ ψ` in `PSH(X, θ)`
with `∫ θ_φ^n > 0` and any

  `a ∈ (1, (∫θ_ψ^n / (∫θ_ψ^n - ∫θ_φ^n))^{1/n})`   (2.28)

there is `η ∈ PSH(X, θ)_{>0}` with `a⁻¹ η + (1 - a⁻¹) ψ ≤ φ`  (2.29).

The source proof splits in two.

* **Step 1** (`xia-sgpt:page-0083`--`xia-sgpt:page-0086`) produces *one*
  `η ∈ PSH(X, θ)` satisfying (2.29) — that is, it shows the competitor family
  of the affine obstacle `a φ + (1 - a) ψ` is **nonempty**.  Its proof is a
  transfinite induction on `P_θ[ψ_α]` followed by the contradiction argument
  of Step 1.3, which uses Theorem 2.4.4, Lemma 2.4.2, Corollary 2.4.1,
  Theorem 2.4.3 and multilinearity of the non-pluripolar product.  Step 1 is
  assembled in `Pending.RooftopConvexCombBarrierStepOneAssembly` (see the
  docstring of `exists_thetaPsh_convexCombBarrier` below for what it still
  rests on).

* **Step 2** (`xia-sgpt:page-0086`--`xia-sgpt:page-0087`) upgrades `PSH` to
  `PSH_{>0}` through the quantitative estimate

  `∫ θ_{P_θ(aφ+(1-a)ψ)}^n ≥ ((a' - a)/a')^n ∫ θ_φ^n`   (2.38)

  for every admissible `a' > a`.  **This module proves Step 2**, from the
  chain inequality (2.37) and the convex-combination lower bound
  `tⁿ θ_φ^n ≤ θ_{tφ+(1-t)η}^n` of `Pending.GlobalDiagonalConvexScaling`.

The envelope itself is the workspace's `rooftopEnvelope` of the obstacle
`convexComb a phi psi`; the two facts (2.30) (it is a genuine `θ`-PSH
potential) and (2.31) (it satisfies (2.29) itself) are proved here from Step 1
exactly as the source proves them, and they are what makes (2.37) meaningful.

The order of the arguments follows the source: `phi` is Xia's `φ`, the more
singular potential, and `psi` is Xia's `ψ`.

The standing hypotheses of Xia's Section 2.4 — `M` connected, compact,
Kähler — are kept throughout.  They are not decorative: the monotonicity
theorem 2.4.3 used in the mass estimate is the Kähler statement.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [Nonempty M] in
/-- The pointwise commutation of a convex combination. -/
theorem convexComb_symm (t : ℝ) (u v : M → EReal) :
    convexComb t u v = convexComb (1 - t) v u := by
  funext x
  simp only [convexComb_apply, sub_sub_cancel]
  exact add_comm _ _

section Envelope

variable {theta : ClosedRealOneOneForm n M} {phi psi : M → EReal}

/-- **Xia, SGPT, Lemma 2.4.4, Step 1 — sourced interface wrapper**
(`xia-sgpt:page-0083`, proof body on `xia-sgpt:page-0084`--`page-0086`).
For `phi ≤ psi` of positive mass and an admissible weight `a`, the affine
obstacle `a phi + (1 - a) psi` admits at least one `theta`-PSH competitor:
some `eta ∈ PSH(X, theta)` satisfies (2.29).

This is *only* the nonemptiness of the competitor family — the source's
Step 1.  Its positive mass, which is what Lemma 2.4.4 finally asserts, is
Step 2 and is **proved** below in `ofReal_pow_mul_mass_le_mass_rooftopEnvelope`.

The source proof is the transfinite induction on `P_theta[psi_alpha]` of
Step 1.2 followed by the contradiction of Step 1.3; the latter uses Xia's
Theorem 2.4.4 (envelope concentration), Lemma 2.4.2, Corollary 2.4.1, the
monotonicity Theorem 2.4.3 and multilinearity of the non-pluripolar product.
Step 1 is NO LONGER taken from a named interface (the former
`xiaLemma244_step1_exists_thetaPsh_convexCombBarrier` was retired by the
human's decision I-0661).  It is assembled, sorry-free, in
`Pending.RooftopConvexCombBarrierStepOneAssembly` from Step 1.1, (2.34) and the
truncated-limit contradiction.  Of the two obligations that assembly used to
leave, the transfinite `P`-chain stabilization of Step 1.2 is now PROVED, by
Zorn's lemma and Choquet, in `Pending.ThetaPshModelReference`
(`exists_thetaPsh_modelReference`).  So the `sorryAx` of the theorem below
reaches exactly ONE named obligation.  Since run 0087's `d1e55ff36` that obligation
is no longer Step 1.3 nondegeneracy: Step 1.3 is proved in
`Pending.ThetaPshTruncatedAffineLimitMassChain`
(`exists_ne_bot_truncatedAffineLimit`), and the surviving root one step further
down is
`Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`,
the affine form of Xia's Theorem 2.4.4.  (The superseded
`xiaLemma244_step13_hasNondegenerateTruncatedAffineLimit`, which had no
consumers, was retired by I-0661.)
Theorem 2.4.4 itself is still open in this workspace
(`Pending.RooftopContactConcentration`, `Pending.DominationPrinciple`).

Degenerate cases are covered by the hypotheses rather than excluded: in
dimension `0` every `a > 1` is admissible and the statement is the honest
content of the source's footnote; `hpos` forbids `phi ≡ -∞`, which
`IsThetaPshPotential` already excludes locally. -/
theorem exists_thetaPsh_convexCombBarrier [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧
      convexComb a⁻¹ eta psi ≤ phi :=
  RooftopConvexCombBarrierStepOneAssembly.exists_thetaPsh_convexCombBarrier_of_interfaces
    omega theta hphi hpsi hle hpos ha

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- The affine obstacle of Xia's (2.30) lies below the more singular
potential. -/
theorem convexComb_le_left (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi) {a : ℝ} (ha : 1 < a) :
    convexComb a phi psi ≤ phi := fun x =>
  convexCombValue_le_left ha (hle x) (hpsi.1.quasiPlurisubharmonic.ne_top x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- Every competitor of the affine obstacle lies below `phi` everywhere. -/
theorem competitor_le_left (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    {a : ℝ} (ha : 1 < a) {g : M → EReal}
    (hg : g ∈ rooftopCompetitors theta.val (convexComb a phi psi)) :
    g ≤ phi :=
  hg.1.1.le_of_quasiEverywhere_le hphi.1
    (hg.2.mono fun y hy => hy.trans (convexComb_le_left hpsi hle ha y))

omit [MeasurableSpace M] [BorelSpace M] in
/-- The competitor family of the affine obstacle is uniformly bounded above,
because `phi` is. -/
theorem rooftopCompetitors_convexComb_bddAbove
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta.val (convexComb a phi psi),
      ∀ x, g x ≤ (B : EReal) := by
  obtain ⟨B, hB⟩ := hphi.exists_global_upper_bound
  exact ⟨B, fun g hg x =>
    (competitor_le_left hphi hpsi hle ha hg x).trans (hB x)⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- A barrier in the sense of (2.29) is a competitor of the affine obstacle:
`psi` is finite quasi-everywhere, and there the two readings agree. -/
theorem mem_rooftopCompetitors_of_barrier
    (hpsi : IsThetaPshPotential theta.val psi) {a : ℝ} (ha : 1 < a)
    {eta : M → EReal} (heta : IsThetaPshPotential theta.val eta)
    (hbar : convexComb a⁻¹ eta psi ≤ phi) :
    eta ∈ rooftopCompetitors theta.val (convexComb a phi psi) := by
  refine ⟨heta, ?_⟩
  refine (quasiPsh_finite_quasiEverywhere hpsi.quasiPshPotential).mono ?_
  rintro x ⟨hb, ht⟩
  exact (convexCombValue_le_iff ha hb ht).mp (hbar x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- Conversely, a `theta`-PSH competitor of the affine obstacle satisfies
(2.29) everywhere.  Both sides are genuine potentials, so the
quasi-everywhere identity of the two readings propagates. -/
theorem barrier_of_mem_rooftopCompetitors
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) {a : ℝ} (ha : 1 < a)
    {eta : M → EReal} (heta : IsThetaPshPotential theta.val eta)
    (hcomp : eta ∈ rooftopCompetitors theta.val (convexComb a phi psi)) :
    convexComb a⁻¹ eta psi ≤ phi := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have heps1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hW : IsThetaPshPotential theta.val (convexComb a⁻¹ eta psi) :=
    isThetaPshPotential_convexComb heta hpsi heps0 heps1
  refine hW.1.le_of_quasiEverywhere_le hphi.1 ?_
  refine (quasiEverywhere_and (quasiPsh_finite_quasiEverywhere hpsi.quasiPshPotential)
    hcomp.2).mono ?_
  rintro x ⟨⟨hb, ht⟩, hx⟩
  exact (convexCombValue_le_iff ha hb ht).mpr hx

variable [ConnectedSpace M]

/-- **Xia's (2.30) and (2.31), from Step 1.**  For an admissible weight the
Perron envelope `P_theta(a phi + (1 - a) psi)` is a genuine `theta`-PSH
potential, and it satisfies the barrier inequality (2.29) itself.

This is the source's own derivation: Step 1 makes the competitor family
nonempty, the obstacle lies below `phi` so the family is uniformly bounded
above, and the envelope inequality `P_theta(f) ≤ f` — here in the Lebesgue
form of `Pending.RooftopEnvelopeAeObstacle` — turns back into (2.29). -/
theorem isThetaPshPotential_rooftopEnvelope_convexComb
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a) :
    IsThetaPshPotential theta.val
        (rooftopEnvelope theta.val (convexComb a phi psi)) ∧
      convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi
        ≤ phi := by
  have ha1 : 1 < a := ha.one_lt
  obtain ⟨eta, heta, hbar⟩ :=
    exists_thetaPsh_convexCombBarrier omega theta hphi hpsi hle hpos ha
  have hne : (rooftopCompetitors theta.val (convexComb a phi psi)).Nonempty :=
    ⟨eta, mem_rooftopCompetitors_of_barrier hpsi ha1 heta hbar⟩
  have hbound := rooftopCompetitors_convexComb_bddAbove hphi hpsi hle ha1
  have hpsh : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi)) :=
    isThetaPshPotential_rooftop_of_nonempty hne hbound
  refine ⟨hpsh, ?_⟩
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha1
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have heps1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  have hW : IsThetaPshPotential theta.val
      (convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi) :=
    isThetaPshPotential_convexComb hpsh hpsi heps0 heps1
  refine ThetaPlurisubharmonic.le_of_ae_in_charts_le hW.1 hphi.1 ?_
  intro e
  have hae1 := ae_rooftopEnvelope_le_obstacle theta hne hbound e
  have hae2 := (quasiPsh_finite_quasiEverywhere
    (u := psi) hpsi.quasiPshPotential).ae_in_chart e volume
  filter_upwards [hae1, hae2] with z h1 h2
  exact (convexCombValue_le_iff ha1 h2.1 h2.2).mpr h1

/-- **Xia's (2.37).**  For `1 < a < a'`, both admissible, the `a`-envelope
dominates the convex combination, with weight `a / a'`, of the `a'`-envelope
with `phi`.  The proof is the pointwise chain inequality
`ConvexCombObstacleAlgebra.convexCombValue_chain`, applied where `phi` and
`psi` are finite — quasi-everywhere — together with (2.31) at `a'`. -/
theorem convexComb_rooftopEnvelope_le_rooftopEnvelope
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a a' : ℝ} (ha1 : 1 < a) (haa : a < a')
    (ha' : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a') :
    convexComb (a / a')
        (rooftopEnvelope theta.val (convexComb a' phi psi)) phi ≤
      rooftopEnvelope theta.val (convexComb a phi psi) := by
  obtain ⟨hpsh', hbar'⟩ :=
    isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hpsi hle hpos ha'
  set E' := rooftopEnvelope theta.val (convexComb a' phi psi) with hE'
  have ha'1 : 1 < a' := ha'.one_lt
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha1
  have ha'0 : (0 : ℝ) < a' := lt_trans zero_lt_one ha'1
  have hc0 : (0 : ℝ) < a / a' := div_pos ha0 ha'0
  have hc1 : a / a' < 1 := (div_lt_one ha'0).mpr haa
  -- the combination is a genuine potential
  have hW : IsThetaPshPotential theta.val (convexComb (a / a') E' phi) :=
    isThetaPshPotential_convexComb hpsh' hphi hc0 hc1
  -- it is a quasi-everywhere competitor of the `a`-obstacle
  refine le_rooftopEnvelope hW ?_
  have hcomp' : E' ∈ rooftopCompetitors theta.val (convexComb a' phi psi) :=
    mem_rooftopCompetitors_of_barrier hpsi ha'1 hpsh' hbar'
  refine (quasiEverywhere_and
    (quasiEverywhere_and
      (quasiPsh_finite_quasiEverywhere (u := phi) hphi.quasiPshPotential)
      (quasiPsh_finite_quasiEverywhere (u := psi) hpsi.quasiPshPotential))
    hcomp'.2).mono ?_
  rintro x ⟨⟨⟨hpb, hpt⟩, ⟨hqb, hqt⟩⟩, hx⟩
  exact convexCombValue_chain ha1 haa (hle x) hpb hpt hqb hqt hx

/-- **Xia's estimate (2.38).**  For `1 < a < a'` with `a'` admissible,

  `((a' - a)/a')ⁿ ∫θ_phi^n ≤ ∫θ_{P_theta(a phi + (1-a) psi)}^n`.

In particular the `a`-envelope has positive mass as soon as `phi` does, which
is the conclusion `η ∈ PSH(X, θ)_{>0}` of Lemma 2.4.4.  The two ingredients
are (2.37) and the convex-combination lower bound
`tⁿ θ^n_phi ≤ θ^n_{t phi + (1-t) E'}` of
`Pending.GlobalDiagonalConvexScaling`, composed with the monotonicity theorem
2.4.3 in the form `Pending.diagonalPotentialMass_mono_of_kahler`. -/
theorem ofReal_pow_mul_mass_le_mass_rooftopEnvelope
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a a' : ℝ} (ha : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a)
    (haa : a < a')
    (ha' : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a')
    (hEa : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    ENNReal.ofReal ((1 - a / a') ^ n) * diagonalPotentialMass theta phi hphi ≤
      diagonalPotentialMass theta
        (rooftopEnvelope theta.val (convexComb a phi psi)) hEa := by
  have ha1 : 1 < a := ha.one_lt
  have ha'1 : 1 < a' := ha'.one_lt
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha1
  have ha'0 : (0 : ℝ) < a' := lt_trans zero_lt_one ha'1
  have hc0 : (0 : ℝ) < a / a' := div_pos ha0 ha'0
  have hc1 : a / a' < 1 := (div_lt_one ha'0).mpr haa
  have ht0 : (0 : ℝ) < 1 - a / a' := by linarith
  have ht1 : (1 : ℝ) - a / a' < 1 := by linarith
  obtain ⟨hpsh', -⟩ :=
    isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hpsi hle hpos ha'
  set E' := rooftopEnvelope theta.val (convexComb a' phi psi) with hE'
  have hW : IsThetaPshPotential theta.val (convexComb (a / a') E' phi) :=
    isThetaPshPotential_convexComb hpsh' hphi hc0 hc1
  have hsymm : convexComb (1 - a / a') phi E' = convexComb (a / a') E' phi := by
    rw [convexComb_symm (1 - a / a') phi E', sub_sub_cancel]
  -- the convex-combination lower bound for the mass
  have hlow := globalMixedMeasure_diagonal_convexComb_le
    (θ := theta) (a := phi) (b := E') hphi hpsh' ht0 ht1 Set.univ
  have hstep :
      ENNReal.ofReal ((1 - a / a') ^ n) * diagonalPotentialMass theta phi hphi ≤
        diagonalPotentialMass theta (convexComb (a / a') E' phi) hW := by
    refine le_trans hlow ?_
    exact le_of_eq (by
      simp only [diagonalPotentialMass, diagonalPotentialMeasure]
      exact congrArg (fun μ : Measure M => μ Set.univ)
        (globalMixedMeasure_congr rfl (funext fun _ => hsymm)
          (fun _ => (isThetaPshPotential_convexComb hphi hpsh' ht0 ht1).1)
          (fun _ => hW.1)))
  refine hstep.trans ?_
  refine diagonalPotentialMass_mono_of_kahler omega hW hEa
    (MoreSingularOn.of_le fun x _ => ?_)
  exact convexComb_rooftopEnvelope_le_rooftopEnvelope omega theta hphi hpsi hle
    hpos ha1 haa ha' x

end Envelope

end

end SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
