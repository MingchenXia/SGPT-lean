import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.RegularizedMaxERealPshRoute
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# The `ε`-barrier of an equal-mass pair, and the common lower barrier

Xia, SGPT, Corollary 2.4.3 (`xia-sgpt:page-0087`) states: for
`φ, ψ ∈ PSH(X, θ)_{>0}` with `φ ≤ ψ` and `∫ θ_φ^n = ∫ θ_ψ^n`, and any
`ε ∈ (0,1)`, there is `η ∈ PSH(X, θ)` with

  (1) `∫ θ_η^n = ∫ θ_φ^n`,   (2) `ε η + (1 - ε) ψ ≤ φ`.

That is exactly the situation of the relative full-mass class `E(X, θ; φ)`,
with `φ` the full-mass potential and `ψ` the reference; both clauses are
recorded in the named interface `exists_thetaPsh_epsilonBarrier` below.  The
corollary is the equal-mass reading of Lemma 2.4.4 (whose statement page is
not in the reference corpus; its proof body is transcribed on
`xia-sgpt:page-0084`--`xia-sgpt:page-0086`), together with the estimate (2.38)
on `xia-sgpt:page-0087` which supplies clause (1).

What this file *proves* from that interface is the step Xia's later arguments
actually need and which is missing from the workspace: **two relative
full-mass potentials admit a common `θ`-PSH lower barrier.**  The construction
is the balanced convex combination of the two `ε`-barriers at `ε = 1/2`,

  `w := ½ η_u + ½ η_v`,

which lies below `u` because `η_v ≤ φ`, and below `v` because `η_u ≤ φ`.  The
order relation `η ≤ φ` is *not* assumed: it is derived from the barrier
inequality quasi-everywhere (where `φ` is finite) and then propagated to all
of `M` by `ThetaPlurisubharmonic.le_of_quasiEverywhere_le`.

**`exists_thetaPsh_epsilonBarrier` is no longer an interface: it is proved.**
Xia proves this corollary *by constructing* the envelope
`P_theta(eps⁻¹ u + (1 - eps⁻¹) phi)`, and that is the proof given below.  The
route is the one the source takes on `xia-sgpt:page-0087`, through
`Pending.ConvexCombEnvelopeMass`:

* clause (2) and the potential itself are (2.30)/(2.31), i.e.
  `ConvexCombEnvelopeMass.isThetaPshPotential_rooftopEnvelope_convexComb` at
  the weight `a = eps⁻¹`, admissible because the two masses agree;
* `≤` of clause (1) is the monotonicity theorem 2.4.3 applied to `eta ≤ u`,
  which holds because every competitor of the obstacle does;
* `≥` of clause (1) is the estimate (2.38),
  `ConvexCombEnvelopeMass.ofReal_pow_mul_mass_le_mass_rooftopEnvelope`, in
  Xia's limit `a' → ∞`: taking `a' = eps⁻¹ / (1 - t)` turns it into
  `tⁿ ∫θ_u^n ≤ ∫θ_eta^n` for every `t ∈ (0,1)`.

The derivation cites no module that depends on this one, so nothing is
circular.  In particular it does **not** cite `RooftopConvexCombBarrier` or
`DominationPrincipleMiddleStage.isThetaPshPotential_rooftopEnvelope_convexComb`,
which derive the envelope form *from* this corollary; the single remaining
source-level interface behind both is
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`, Step 1 of
Lemma 2.4.4 (`xia-sgpt:page-0084`--`xia-sgpt:page-0086`).

The statements are deliberately phrased with bare `IsThetaPshPotential` and
`diagonalPotentialMass` hypotheses rather than with `IsModelPotential` and
`RelativeFullMass`, so that this module sits *upstream* of
`Pending.RelativeFullMass` and can be consumed there.  The standing hypotheses
of Xia's Section 2.4 — connected, compact, Kähler — are kept throughout.
-/

open Set MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, SGPT, Corollary 2.4.3 (`xia-sgpt:page-0087`), proved from Lemma
2.4.4.**  Stated there as: for `φ, ψ ∈ PSH(X, θ)_{>0}` with
`φ ≤ ψ` and `∫ θ_φ^n = ∫ θ_ψ^n`, and any `ε ∈ (0,1)`, there is
`η ∈ PSH(X, θ)` with

  (1) `∫ θ_η^n = ∫ θ_φ^n`,   (2) `ε η + (1 - ε) ψ ≤ φ`.

Here `φ` is `u` and `ψ` is `phi`; both clauses are kept.  The proof is the source's: take
`η = P_θ(ε⁻¹ u + (1 - ε⁻¹) phi)`.  Clause (2) and the fact that this envelope
is a genuine potential are (2.30)/(2.31); clause (1) is the estimate (2.38) in
the limit `a' → ∞` for `≥`, and the monotonicity theorem 2.4.3 for `≤`.  The
only source input left is Step 1 of Lemma 2.4.4,
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`.

The standing hypotheses of Xia's Section 2.4 are kept: `M` is a connected
compact Kähler manifold, the Kähler background being `omega`.  They are not
decorative — the monotonicity theorem 2.4.3 used throughout that section is
the Kähler statement, and without `omega` the diagonal mass is not even known
to be finite. -/
theorem exists_thetaPsh_epsilonBarrier [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi u : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (hle : u ≤ phi)
    (hpos : 0 < diagonalPotentialMass theta u hu)
    (hmass : diagonalPotentialMass theta u hu = diagonalPotentialMass theta phi hphi)
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps < 1) :
    ∃ eta : M → EReal, ∃ heta : IsThetaPshPotential theta.val eta,
      diagonalPotentialMass theta eta heta = diagonalPotentialMass theta u hu ∧
        convexComb eps eta phi ≤ u := by
  classical
  have hinvpos : (0 : ℝ) < eps⁻¹ := inv_pos.mpr heps0
  have ha1 : (1 : ℝ) < eps⁻¹ := by
    have h := mul_inv_cancel₀ (ne_of_gt heps0)
    nlinarith
  -- With equal masses every weight `> 1` is admissible.
  have hadm : ∀ b : ℝ, 1 < b →
      ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta u hu)
        (diagonalPotentialMass theta phi hphi) b := by
    intro b hb
    rw [← hmass]
    exact ConvexCombEnvelopeMass.isAdmissibleWeight_of_eq hpos hb
  obtain ⟨hE, hbar⟩ :=
    ConvexCombEnvelopeMass.isThetaPshPotential_rooftopEnvelope_convexComb omega theta
      hu hphi hle hpos (hadm _ ha1)
  set E : M → EReal := rooftopEnvelope theta.val (convexComb eps⁻¹ u phi) with hEdef
  refine ⟨E, hE, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · -- `E` is a competitor of the obstacle, hence `E ≤ u`; monotonicity (Thm 2.4.3).
      have hcomp :=
        ConvexCombEnvelopeMass.mem_rooftopCompetitors_of_barrier hphi ha1 hE hbar
      have hEle : E ≤ u :=
        ConvexCombEnvelopeMass.competitor_le_left hu hphi hle ha1 hcomp
      exact diagonalPotentialMass_mono_of_kahler omega hE hu
        (MoreSingularOn.of_le fun x _ ↦ hEle x)
    · -- Xia's `a' → ∞` in (2.38).
      refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
      rcases eq_or_ne c 0 with rfl | hc0
      · simp
      have hcne : c ≠ ⊤ := hc.ne_top
      have hr0 : 0 < c.toReal := ENNReal.toReal_pos hc0 hcne
      have hr1 : c.toReal < 1 := by
        have h := (ENNReal.toReal_lt_toReal hcne (by simp)).mpr hc
        simpa using h
      obtain ⟨t, ht0, ht1, htc⟩ :
          ∃ t : ℝ, 0 < t ∧ t < 1 ∧ c ≤ ENNReal.ofReal (t ^ n) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
          rw [hn]
          simpa using hc.le
        · have hnne : n ≠ 0 := hn.ne'
          have hexp : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
          refine ⟨c.toReal ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos hr0 _,
            Real.rpow_lt_one hr0.le hr1 hexp, ?_⟩
          rw [Real.rpow_inv_natCast_pow hr0.le hnne, ENNReal.ofReal_toReal hcne]
      have h1t : (0 : ℝ) < 1 - t := by linarith
      have h1tne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
      have hinvne : (eps⁻¹ : ℝ) ≠ 0 := ne_of_gt hinvpos
      have haa : eps⁻¹ < eps⁻¹ / (1 - t) := by
        rw [lt_div_iff₀ h1t]
        nlinarith
      have hratio : eps⁻¹ / (eps⁻¹ / (1 - t)) = 1 - t := by field_simp
      have key :=
        ConvexCombEnvelopeMass.ofReal_pow_mul_mass_le_mass_rooftopEnvelope omega theta
          hu hphi hle hpos (hadm _ ha1) haa (hadm _ (ha1.trans haa)) hE
      rw [hratio, sub_sub_cancel] at key
      exact le_trans (by gcongr) key
  · rw [inv_inv] at hbar
    exact hbar

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- An `ε`-barrier is automatically more singular than the reference.  Where
`phi` is finite the barrier inequality can be cancelled; the finite locus of a
genuine `θ`-PSH potential is quasi-everything, and two `θ`-PSH potentials
comparable quasi-everywhere are comparable everywhere. -/
theorem epsilonBarrier_le_reference
    {theta : ClosedRealOneOneForm n M} {phi u eta : M → EReal}
    (hphi : ThetaPlurisubharmonic theta.val phi)
    (hphind : LocallyNondegenerate phi)
    (heta : ThetaPlurisubharmonic theta.val eta)
    (hle : u ≤ phi) {eps : ℝ} (heps0 : 0 < eps)
    (hbar : convexComb eps eta phi ≤ u) :
    eta ≤ phi := by
  refine heta.le_of_quasiEverywhere_le hphi ?_
  refine (quasiPsh_finite_quasiEverywhere
    (u := phi) ⟨hphi.quasiPlurisubharmonic, hphind⟩).mono ?_
  rintro x ⟨hbot, htop⟩
  have hx : (eps : EReal) * eta x + ((1 - eps : ℝ) : EReal) * phi x ≤ phi x :=
    (hbar x).trans (hle x)
  lift phi x to ℝ using ⟨htop, hbot⟩ with p hp
  rw [← EReal.coe_mul] at hx
  have hsplit : (p : EReal) = ((eps * p : ℝ) : EReal) + (((1 - eps) * p : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  rw [hsplit] at hx
  have hcancel : (eps : EReal) * eta x ≤ ((eps * p : ℝ) : EReal) :=
    (EReal.addLECancellable_coe _).add_le_add_iff_right.mp hx
  have h2 := mul_le_mul_of_nonneg_left hcancel
    (EReal.coe_nonneg.mpr (le_of_lt (inv_pos.mpr heps0)))
  rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ heps0.ne', EReal.coe_one,
    one_mul, ← EReal.coe_mul, inv_mul_cancel_left₀ heps0.ne'] at h2
  exact h2

/-- **A common `θ`-PSH lower barrier for two relative full-mass potentials.**
This is the input that `Pending.RelativeFullMass` needs at
`rooftopCompetitors_nonempty_min_add_const_of_common_thetaPsh_lower_qe`, and
which relative full mass alone does not supply.  The barrier is the balanced
convex combination of the two `ε`-barriers at `ε = 1/2`: it lies below `u`
because `η_v ≤ phi`, and below `v` because `η_u ≤ phi`. -/
theorem exists_common_thetaPsh_lower [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi u v : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hule : u ≤ phi) (hvle : v ≤ phi)
    (hupos : 0 < diagonalPotentialMass theta u hu)
    (hvpos : 0 < diagonalPotentialMass theta v hv)
    (humass : diagonalPotentialMass theta u hu =
      diagonalPotentialMass theta phi hphi)
    (hvmass : diagonalPotentialMass theta v hv =
      diagonalPotentialMass theta phi hphi) :
    ∃ w : M → EReal, IsThetaPshPotential theta.val w ∧ w ≤ u ∧ w ≤ v := by
  have hhalf0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨etaU, hetaU, -, hbarU⟩ :=
    exists_thetaPsh_epsilonBarrier omega theta hphi hu hule hupos humass
      hhalf0 hhalf1
  obtain ⟨etaV, hetaV, -, hbarV⟩ :=
    exists_thetaPsh_epsilonBarrier omega theta hphi hv hvle hvpos hvmass
      hhalf0 hhalf1
  have hUle : etaU ≤ phi :=
    epsilonBarrier_le_reference hphi.1 hphi.2 hetaU.1 hule hhalf0 hbarU
  have hVle : etaV ≤ phi :=
    epsilonBarrier_le_reference hphi.1 hphi.2 hetaV.1 hvle hhalf0 hbarV
  refine ⟨convexComb (1 / 2 : ℝ) etaU etaV,
    isThetaPshPotential_convexComb hetaU hetaV hhalf0 hhalf1, ?_, ?_⟩
  · exact (convexComb_mono hhalf0.le hhalf1.le le_rfl hVle).trans hbarU
  · refine le_trans ?_ hbarV
    rw [convexComb_half_comm etaV phi]
    exact convexComb_mono hhalf0.le hhalf1.le hUle le_rfl

/-- The shifted form actually consumed by the rooftop argument: a common
`θ`-PSH barrier below `u` and below `v + C` for a prescribed finite
translation `C`.  A downward shift by `min C 0` converts the unshifted
barrier. -/
theorem exists_common_thetaPsh_lower_add_const [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi u v : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hule : u ≤ phi) (hvle : v ≤ phi)
    (hupos : 0 < diagonalPotentialMass theta u hu)
    (hvpos : 0 < diagonalPotentialMass theta v hv)
    (humass : diagonalPotentialMass theta u hu =
      diagonalPotentialMass theta phi hphi)
    (hvmass : diagonalPotentialMass theta v hv =
      diagonalPotentialMass theta phi hphi) (C : ℝ) :
    ∃ w : M → EReal, IsThetaPshPotential theta.val w ∧ w ≤ u ∧
      w ≤ fun x => v x + (C : EReal) := by
  obtain ⟨w, hw, hwu, hwv⟩ := exists_common_thetaPsh_lower omega theta hphi hu hv
    hule hvle hupos hvpos humass hvmass
  refine ⟨fun x => w x + ((min C 0 : ℝ) : EReal), hw.add_const _, ?_, ?_⟩
  · intro x
    calc w x + ((min C 0 : ℝ) : EReal) ≤ w x + ((0 : ℝ) : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (min_le_right _ _))
      _ = w x := by simp
      _ ≤ u x := hwu x
  · intro x
    calc w x + ((min C 0 : ℝ) : EReal) ≤ v x + ((min C 0 : ℝ) : EReal) :=
          add_le_add (hwv x) le_rfl
      _ ≤ v x + (C : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (min_le_left _ _))

end

end SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
