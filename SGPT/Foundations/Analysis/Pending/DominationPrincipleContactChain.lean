import SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactInterface
import SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChainCore
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier
import SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

set_option autoImplicit false

/-!
# The measure chain in the proof of Xia's Theorem 2.4.5

This module carries out the displayed computation on `xia-sgpt:page-0088`, the
analytic middle of the ordered case of the domination principle.  The data are
`phi <= psi` in `PSH(X, theta)` of the same positive mass, the hypothesis
(2.40) that `theta^n_phi` does not charge `{phi < psi}`, and a parameter
`a > 1`.  Writing

  `eta_a := P_theta (a phi + (1 - a) psi)`,
  `gamma_a := a^{-1} eta_a + (1 - a^{-1}) psi`,
  `D_a := {gamma_a = phi}`,

the source chain is

  `a^{-n} theta^n_{eta_a}
     = 1_{D_a} a^{-n} theta^n_{eta_a}`                     (Theorem 2.4.4)
  `  <= 1_{D_a} theta^n_{gamma_a}`                         (multilinearity)
  `  <= 1_{D_a} theta^n_phi`                               (Lemma 2.4.2)
  `  = 1_{D_a cap {phi = psi}} theta^n_phi`                (2.40),

and then `eta_a = phi` on `D_a cap {phi = psi}`, so `theta^n_{eta_a}` is
carried by `{eta_a = phi}`; since the two ends have the same mass, `theta^n_phi`
is carried by `{eta_a = phi}` as well, which is the statement consumed by
`Pending.DominationPrincipleMiddleStage`.

Everything here is PROVED except for the imported, source-anchored affine
instance of the envelope concentration theorem 2.4.4
(`Pending.DominationPrincipleAffineContactInterface`); the multilinearity step
is
`Pending.NonPluripolarConvexCombLower`.  The remaining inputs are already
available: Lemma 2.4.2 through
`Pending.RooftopContactConcentration.measure_le_of_subset_contact`, the
envelope barrier (2.29) through `Pending.RooftopConvexCombBarrier`, the mass
clause (2.38) through `Pending.RelativeFullMassEpsilonBarrier`, and mass
monotonicity through `Pending.diagonalPotentialMass_mono_of_kahler`.

The first three lines of the chain are Xia's inequality (2.35) in its general
form, `ofReal_pow_smul_measure_le_contact`: it takes the concentration
statement as a hypothesis, so it also serves the *other* place the source runs
this computation, inside the proof of Lemma 2.4.4 on `xia-sgpt:page-0085`.
There the data are `p = varphi ∨ (phi - k)` and `eta = eta_k`; here they are
`p = phi` and `eta = eta_a`.  Because that second consumer sits below
`Pending.ConvexCombEnvelopeMass` and this module sits above it, (2.35) lives in
its own module, `Pending.DominationPrincipleContactChainCore`, with its
statement and its full name unchanged.

The pointwise `EReal` algebra used below —
`convexCombValue_le_left`, `convexCombValue_le_iff`,
`le_convexCombValue_of_convexCombValue_le`, `eq_of_convexCombValue_eq` — all
lives in one place, `Pending.RooftopConvexCombBarrier.ERealAlgebra`.

The contact set is handled through `{x | not (eta x < a p x + (1 - a) u x)}`
rather than through `D` directly: the former is contained in the latter,
because for `u x` finite the map `E |-> a^{-1} E + (1 - a^{-1}) u x` inverts
`A |-> a A + (1 - a) u x`, and at a common pole both readings degenerate to
`-infinity`.  No measurability of any contact set is used: the mass step goes
through the measurable hull of the *complement*, which is where the contact
comparison is applied.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
open SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier
open SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
open SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Source-interface wrapper (Xia, SGPT, Theorem 2.4.4,
`xia-sgpt:page-0079`, equation (2.23)), specialised to the obstacle
`a phi + (1 - a) psi` of the proof of Theorem 2.4.5.**  The non-pluripolar
Monge--Ampere measure of `P_theta(a phi + (1 - a) psi)` gives no mass to the
set where the envelope stays strictly below its obstacle.

The general statement is about `P_theta(f)` for a quasi-continuous `f`, and the
workspace still cannot express that hypothesis for the reference it needs.
Xia's Theorem 2.3.2 is available for a globally bounded potential against a
globally bounded reference (`Pending.ThetaCapacityQuasiContinuity`) and, since
run 0050, for an *unbounded* potential against a bounded **continuous**
reference (`Pending.ThetaCapacityUnboundedQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_compl_of_le`).
Neither covers `V_theta` itself, which is unbounded below as soon as
`nK(theta)` is nonempty and is not continuous; closing that is outer
regularity of `Cap_theta`, not a further analytic input.  So the
theorem is still recorded for the two obstacles its consumers need:
`min {phi, psi}` in `Pending.RooftopContactConcentration`, and the affine
combination here. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_convexComb_noncontact_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hmass : diagonalPotentialMass theta phi hphi =
      diagonalPotentialMass theta psi hpsi)
    {a : ℝ} (ha : 1 < a)
    (heta : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (convexComb a phi psi)) heta
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = 0 :=
  xiaTheorem244_affineObstacle_noncontact_eq_zero omega theta hphi hpsi hle hpos hmass ha heta


/-- **The measure chain of `xia-sgpt:page-0088`, proved from the two named
interfaces above.**  Under the hypotheses of the ordered case of Xia's Theorem
2.4.5 — `phi ≤ psi` of the same positive mass and the non-charging hypothesis
(2.40) — the Perron barrier `eta_a = P_theta(a phi + (1 - a) psi)` meets `phi`
off a `theta^n_phi`-null set.

The proof is Xia's.  The envelope lies below `phi` and carries its mass; the
concentration theorem 2.4.4 puts `theta^n_{eta_a}` on the contact set with the
obstacle, which is exactly `D_a = {gamma_a = phi}`; multilinearity and Lemma
2.4.2 push `a^{-n} theta^n_{eta_a}` below `1_{D_a} theta^n_phi`, which (2.40)
confines to `{phi = psi}`, where `eta_a = phi`.  Equality of the two total
masses then transfers the conclusion from `theta^n_{eta_a}` to
`theta^n_phi`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hmass : diagonalPotentialMass theta phi hphi =
      diagonalPotentialMass theta psi hpsi)
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0)
    {a : ℝ} (ha : 1 < a) :
    diagonalPotentialMeasure theta phi hphi
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x < phi x} = 0 := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have heps1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  obtain ⟨hepsh, hbar⟩ :=
    isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hpsi hle hpos
      hmass ha
  set f : M → EReal := convexComb a phi psi with hfdef
  set e : M → EReal := rooftopEnvelope theta.val f
  have hpsitop : ∀ x, psi x ≠ ⊤ := fun x => hpsi.1.quasiPlurisubharmonic.ne_top x
  have hetatop : ∀ x, e x ≠ ⊤ := fun x => hepsh.1.quasiPlurisubharmonic.ne_top x
  have hphitop : ∀ x, phi x ≠ ⊤ := fun x => hphi.1.quasiPlurisubharmonic.ne_top x
  have hpsifin : QuasiEverywhere (n := n) (fun x => psi x ≠ ⊥ ∧ psi x ≠ ⊤) :=
    quasiPsh_finite_quasiEverywhere hpsi.quasiPshPotential
  -- the obstacle lies below `phi`
  have hfle : f ≤ phi := fun x => convexCombValue_le_left ha (hle x) (hpsitop x)
  -- so does the envelope
  have hephi : e ≤ phi := by
    refine hepsh.1.le_of_quasiEverywhere_le hphi.1 (hpsifin.mono ?_)
    rintro x ⟨hb, ht⟩
    exact ((convexCombValue_le_iff ha hb ht).mp (hbar x)).trans (hfle x)
  -- the envelope's measure is carried by `{e = phi}`
  set T : Set M := {x : M | e x ≠ phi x} with hTdef
  have hTmem : ∀ x : M, e x ≠ phi x → x ∈ T := fun _ h => h
  -- on `D_a` the barrier meets `phi`, and where `phi = psi` the envelope does
  have hTD : T ∩ {x : M | convexComb a⁻¹ e psi x = phi x} ⊆
      {x : M | phi x < psi x} := by
    rintro x ⟨hxT, hxD⟩
    rcases lt_or_eq_of_le (hle x) with h | h
    · exact h
    · refine absurd (eq_of_convexCombValue_eq ha (hephi x) (hphitop x) ?_) hxT
      have hxD' : ((a⁻¹ : ℝ) : EReal) * e x + ((1 - a⁻¹ : ℝ) : EReal) * psi x
          = phi x := hxD
      rwa [← h] at hxD'
  have hkey : diagonalPotentialMeasure theta e hepsh T = 0 := by
    have h1 := ofReal_pow_smul_measure_le_contact omega theta hphi hpsi hepsh ha
      hle hbar
      (diagonalPotentialMeasure_rooftopEnvelope_convexComb_noncontact_eq_zero
        omega theta hphi hpsi hle hpos hmass ha hepsh) T
    have h3 : diagonalPotentialMeasure theta phi hphi
        (T ∩ {x : M | convexComb a⁻¹ e psi x = phi x}) = 0 := by
      have h := measure_mono (μ := diagonalPotentialMeasure theta phi hphi) hTD
      rw [hzero] at h
      exact le_antisymm h zero_le
    rw [h3] at h1
    have hne : ENNReal.ofReal (a⁻¹ ^ n) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos heps0 n
    exact (mul_eq_zero.mp (le_antisymm h1 zero_le)).resolve_left hne
  -- the envelope carries the mass of `phi`
  have hmasseq : diagonalPotentialMass theta e hepsh =
      diagonalPotentialMass theta phi hphi := by
    refine le_antisymm (diagonalPotentialMass_mono_of_kahler omega hepsh hphi
      (MoreSingularOn.of_le fun x _ => hephi x)) ?_
    obtain ⟨eta, hetapsh, hetamass, hetabar⟩ :=
      exists_thetaPsh_epsilonBarrier omega theta hpsi hphi hle hpos hmass heps0 heps1
    have hcomp : eta ≤ e := by
      refine le_rooftopEnvelope hetapsh (hpsifin.mono ?_)
      rintro x ⟨hb, ht⟩
      exact (convexCombValue_le_iff ha hb ht).mp (hetabar x)
    calc diagonalPotentialMass theta phi hphi
        = diagonalPotentialMass theta eta hetapsh := hetamass.symm
      _ ≤ diagonalPotentialMass theta e hepsh :=
          diagonalPotentialMass_mono_of_kahler omega hetapsh hepsh
            (MoreSingularOn.of_le fun x _ => hcomp x)
  -- transfer the conclusion to `theta^n_phi` through the measurable hull of `T`
  set A : Set M := toMeasurable (diagonalPotentialMeasure theta e hepsh) T with hAdef
  have hAmeas : MeasurableSet A := measurableSet_toMeasurable _ _
  have hnuA : diagonalPotentialMeasure theta e hepsh A = 0 := by
    rw [hAdef, measure_toMeasurable]
    exact hkey
  have hTA : T ⊆ A := subset_toMeasurable _ _
  have hAcompl : Aᶜ ⊆ {x : M | e x = phi x} := by
    intro x hx
    by_contra hcon
    exact hx (hTA hcon)
  have huniv : diagonalPotentialMass theta phi hphi ≤
      diagonalPotentialMeasure theta phi hphi Aᶜ := by
    rw [← hmasseq]
    calc diagonalPotentialMass theta e hepsh
        = diagonalPotentialMeasure theta e hepsh univ := rfl
      _ ≤ diagonalPotentialMeasure theta e hepsh (Aᶜ ∪ A) := by
          refine measure_mono fun x _ => ?_
          by_cases hxA : x ∈ A
          · exact Or.inr hxA
          · exact Or.inl hxA
      _ ≤ diagonalPotentialMeasure theta e hepsh Aᶜ +
            diagonalPotentialMeasure theta e hepsh A := measure_union_le _ _
      _ = diagonalPotentialMeasure theta e hepsh Aᶜ := by rw [hnuA, add_zero]
      _ ≤ diagonalPotentialMeasure theta phi hphi Aᶜ :=
          measure_le_of_subset_contact omega theta hepsh hphi hephi _ hAcompl
  have hfin : diagonalPotentialMeasure theta phi hphi Aᶜ ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega
      (fun _ : Fin n => hphi.1) Aᶜ).ne
  have hsplit : diagonalPotentialMeasure theta phi hphi Aᶜ +
      diagonalPotentialMeasure theta phi hphi A =
      diagonalPotentialMass theta phi hphi := by
    rw [add_comm]
    exact measure_add_measure_compl hAmeas
  have hmuA : diagonalPotentialMeasure theta phi hphi A = 0 := by
    have hle' : diagonalPotentialMeasure theta phi hphi Aᶜ +
        diagonalPotentialMeasure theta phi hphi A ≤
        diagonalPotentialMeasure theta phi hphi Aᶜ + 0 := by
      rw [add_zero, hsplit]
      exact huniv
    simpa using (ENNReal.add_le_add_iff_left hfin).mp hle'
  have hfinal : {x : M | e x < phi x} ⊆ A :=
    fun x hx => hTA (hTmem x (ne_of_lt hx))
  exact le_antisymm ((measure_mono hfinal).trans hmuA.le) zero_le

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain
