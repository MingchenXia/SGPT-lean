import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# The two elementary ends of Xia's domination principle

Xia, SGPT, Theorem 2.4.5 (`xia-sgpt:page-0087`--`xia-sgpt:page-0089`) is proved
in three stages.  This file proves the first and the last of them; the middle
stage is the genuinely analytic one (the envelope concentration Theorem 2.4.4,
`xia-sgpt:page-0079`, and the contact-set comparison Lemma 2.4.2,
`xia-sgpt:page-0076`) and is not touched here.

* **Opening reduction** (`le_of_ordered_case`).  The source replaces `psi` by
  `max phi psi`, which has the reference mass by the monotonicity theorem
  2.4.3, has the same strict comparison locus `{phi < psi}`, and dominates
  `phi`.  Hence the general statement follows from its special case
  `phi ≤ psi`.
* **Closing descent** (`le_of_iInf_barrier`).  The middle stage produces, for
  every `a > 1`, a potential `eta a` with
  `a⁻¹ (eta a) + (1 - a⁻¹) psi ≤ phi` — this is exactly inequality (2.29) of
  Xia's Lemma 2.4.4, `xia-sgpt:page-0083`, for
  `eta a = P_theta (a * phi + (1 - a) * psi)`, the family built in
  `Pending.DominationPrincipleBarrier`.  Wherever `phi x < psi x` that inequality forces
  `eta a x → -∞` as `a → ∞`, so the pointwise infimum is `-∞` there.  Since
  that infimum is assumed to be a genuine `theta`-PSH potential, its pole set
  is pluripolar, so `psi ≤ phi` quasi-everywhere and hence everywhere.

Both ends are stated for an arbitrary family `eta : ℝ → M → EReal` satisfying
the barrier inequality, so that they compose with whatever construction the
middle stage eventually supplies.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
open SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ## Opening reduction: from the general statement to the ordered one -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The singularity order is stable under pointwise maxima on the left. -/
theorem moreSingularOn_max {u v w : M → EReal}
    (hu : MoreSingularOn u w univ) (hv : MoreSingularOn v w univ) :
    MoreSingularOn (fun x => Max.max (u x) (v x)) w univ := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  refine ⟨Max.max C D, fun x _ => ?_⟩
  refine max_le ?_ ?_
  · exact (hC x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left C D)))
  · exact (hD x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right C D)))

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Replacing the challenger by its maximum with the reference does not change
the strict comparison locus. -/
theorem lt_max_setOf (u v : M → EReal) :
    {x | u x < Max.max (u x) (v x)} = {x | u x < v x} := by
  ext x
  simp only [mem_ofPred_eq, lt_max_iff, lt_self_iff_false, false_or]

/-- The maximum of two potentials of the reference mass again has the
reference mass.  This is Xia's opening line for Theorem 2.4.5:
`∫ θ^n_{φ ∨ ψ} = ∫ θ^n_ϕ`, by the monotonicity theorem 2.4.3 applied in both
directions. -/
theorem diagonalPotentialMass_max_eq (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi psi eta : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (heta : IsThetaPshPotential theta.val eta)
    (hphieta : MoreSingularOn phi eta univ) (hpsieta : MoreSingularOn psi eta univ)
    (hphimass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta eta heta) :
    diagonalPotentialMass theta (fun x => Max.max (phi x) (psi x))
        (IsThetaPshPotential.max hphi hpsi) = diagonalPotentialMass theta eta heta := by
  refine le_antisymm ?_ ?_
  · exact diagonalPotentialMass_mono_of_kahler omega (IsThetaPshPotential.max hphi hpsi) heta
      (moreSingularOn_max hphieta hpsieta)
  · exact hphimass ▸ diagonalPotentialMass_mono_of_kahler omega hphi
      (IsThetaPshPotential.max hphi hpsi) (MoreSingularOn.of_le fun x _ => le_max_left _ _)

/-- **Xia's opening reduction for Theorem 2.4.5.**  If the domination
principle is known whenever the challenger dominates the reference, it holds
in general: replace `psi` by `max phi psi`. -/
theorem le_of_ordered_case (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi psi eta : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (heta : IsThetaPshPotential theta.val eta)
    (hphipos : HasPositivePotentialMass theta phi hphi)
    (hphieta : MoreSingularOn phi eta univ) (hpsieta : MoreSingularOn psi eta univ)
    (hphimass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta eta heta)
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0)
    (hordered : ∀ chi : M → EReal, ∀ hchi : IsThetaPshPotential theta.val chi,
      phi ≤ chi → HasPositivePotentialMass theta chi hchi →
      MoreSingularOn chi eta univ →
      diagonalPotentialMass theta chi hchi = diagonalPotentialMass theta eta heta →
      diagonalPotentialMeasure theta phi hphi {x | phi x < chi x} = 0 →
      chi ≤ phi) :
    psi ≤ phi := by
  have hmax : IsThetaPshPotential theta.val (fun x => Max.max (phi x) (psi x)) :=
    IsThetaPshPotential.max hphi hpsi
  have hmassmax : diagonalPotentialMass theta _ hmax =
      diagonalPotentialMass theta eta heta :=
    diagonalPotentialMass_max_eq omega hphi hpsi heta hphieta hpsieta hphimass
  have hposmax : HasPositivePotentialMass theta _ hmax := by
    change 0 < diagonalPotentialMass theta _ hmax
    rw [hmassmax, ← hphimass]
    exact hphipos
  have hzeromax : diagonalPotentialMeasure theta phi hphi
      {x | phi x < Max.max (phi x) (psi x)} = 0 := by
    rw [lt_max_setOf]
    exact hzero
  have hconc := hordered _ hmax (fun x => le_max_left _ _) hposmax
    (moreSingularOn_max hphieta hpsieta) hmassmax hzeromax
  exact fun x => (le_max_right (phi x) (psi x)).trans (hconc x)

/-! ## Closing descent: the pointwise infimum of the barrier family -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Cancel a finite additive term against a finite bound. -/
theorem le_sub_of_add_coe_le_coe {A : EReal} {c q : ℝ}
    (h : A + (c : EReal) ≤ (q : EReal)) : A ≤ ((q - c : ℝ) : EReal) := by
  have hsplit : ((q : ℝ) : EReal) = ((q - c : ℝ) : EReal) + (c : EReal) := by
    rw [← EReal.coe_add]; congr 1; ring
  rw [hsplit] at h
  exact (EReal.addLECancellable_coe c).add_le_add_iff_right.mp h

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Divide a positive finite scalar out of an upper bound. -/
theorem le_div_of_coe_mul_le_coe {eps : ℝ} (heps : 0 < eps) {A : EReal} {s : ℝ}
    (h : (eps : EReal) * A ≤ (s : EReal)) : A ≤ ((s / eps : ℝ) : EReal) := by
  have h2 := mul_le_mul_of_nonneg_left h
    (EReal.coe_nonneg.mpr (le_of_lt (inv_pos.mpr heps)))
  rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ heps.ne', EReal.coe_one, one_mul,
    ← EReal.coe_mul] at h2
  simpa [div_eq_inv_mul] using h2

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **The pointwise step of Xia's closing descent.**  At a point where the
reference is strictly below the challenger, the barrier family (2.29) has
pointwise infimum `-∞`. -/
theorem iInf_eq_bot_of_lt {phi psi : M → EReal} {eta : ℝ → M → EReal} {x : M}
    (hpsitop : psi x ≠ ⊤)
    (hbar : ∀ a : ℝ, 1 < a → convexComb a⁻¹ (eta a) psi x ≤ phi x)
    (hlt : phi x < psi x) :
    ⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x = ⊥ := by
  have hpsibot : psi x ≠ ⊥ := (bot_le.trans_lt hlt).ne'
  lift psi x to ℝ using ⟨hpsitop, hpsibot⟩ with p hp
  -- the family becomes arbitrarily negative at `x`
  have key : ∀ r : ℝ, ∃ a : Ioi (1 : ℝ), eta (a : ℝ) x ≤ (r : EReal) := by
    intro r
    by_cases hphibot : phi x = ⊥
    · refine ⟨⟨2, by norm_num⟩, ?_⟩
      have h2 := hbar 2 (by norm_num)
      rw [convexComb_apply, hphibot, ← hp, ← EReal.coe_mul] at h2
      have hb : (((2 : ℝ)⁻¹ : ℝ) : EReal) * eta 2 x = ⊥ :=
        (EReal.add_eq_bot_iff.mp (le_bot_iff.mp h2)).resolve_right (EReal.coe_ne_bot _)
      have := eq_bot_of_coe_mul_eq_bot (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) hb
      simp [this]
    · have hphitop : phi x ≠ ⊤ := by
        intro h
        rw [h] at hlt
        exact absurd hlt (by simp)
      lift phi x to ℝ using ⟨hphitop, hphibot⟩ with q hq
      have hqp : q < p := EReal.coe_lt_coe_iff.mp hlt
      set a : ℝ := Max.max 2 ((r - p) / (q - p)) with ha
      have ha1 : 1 < a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have ha0 : 0 < a := lt_trans zero_lt_one ha1
      have hbnd : a * (q - p) + p ≤ r := by
        have hneg : q - p < 0 := by linarith
        have hge : (r - p) / (q - p) ≤ a := le_max_right _ _
        have := mul_le_mul_of_nonpos_right hge hneg.le
        rw [div_mul_cancel₀ _ hneg.ne] at this
        linarith
      refine ⟨⟨a, ha1⟩, ?_⟩
      have hb := hbar a ha1
      rw [convexComb_apply, ← hp, ← EReal.coe_mul] at hb
      have h1 := le_sub_of_add_coe_le_coe hb
      have h2 := le_div_of_coe_mul_le_coe (inv_pos.mpr ha0) h1
      refine h2.trans (EReal.coe_le_coe_iff.mpr ?_)
      have hval : (q - (1 - a⁻¹) * p) / a⁻¹ = a * (q - p) + p := by
        field_simp
        ring
      rw [hval]
      exact hbnd
  refine le_antisymm ?_ bot_le
  by_contra hcon
  obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hcon)
  obtain ⟨a, hax⟩ := key r
  exact absurd ((iInf_le (fun a : Ioi (1 : ℝ) => eta (a : ℝ) x) a).trans hax) (not_le.mpr hr)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **Xia's closing descent for Theorem 2.4.5.**  If for every `a > 1` there is
a `theta`-PSH barrier `eta a` with `a⁻¹ (eta a) + (1 - a⁻¹) psi ≤ phi`
(inequality (2.29) of Lemma 2.4.4, `xia-sgpt:page-0083`), and the pointwise
infimum of the family is itself a genuine `theta`-PSH potential, then
`psi ≤ phi`.  Only nondegeneracy of that infimum is used: its pole set is
pluripolar, and the barrier inequality forces the infimum to be `-∞`
wherever `phi < psi`. -/
theorem le_of_iInf_barrier {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} {eta : ℝ → M → EReal}
    (hphi : ThetaPlurisubharmonic theta phi) (hpsi : ThetaPlurisubharmonic theta psi)
    (hbar : ∀ a : ℝ, 1 < a → convexComb a⁻¹ (eta a) psi ≤ phi)
    (hinf : IsThetaPshPotential theta (fun x => ⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x)) :
    psi ≤ phi := by
  refine hpsi.le_of_quasiEverywhere_le hphi ?_
  refine (quasiPsh_finite_quasiEverywhere
    (u := fun x => ⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) hinf.quasiPshPotential).mono ?_
  rintro x ⟨hbot, -⟩
  by_contra hx
  exact hbot (iInf_eq_bot_of_lt (hpsi.quasiPlurisubharmonic.ne_top x)
    (fun a ha => hbar a ha x) (not_le.mp hx))

/-! ## The measure-theoretic core of the closing step

Xia concludes the proof of Theorem 2.4.5 from `∫_X e^{η_a} θ^n_φ = ∫_X e^φ θ^n_φ > 0`.
The same conclusion follows from the set-theoretic form of the same input: each
`{eta a < phi}` is `θ^n_φ`-null, the family is antitone, so the pointwise
infimum already agrees with `phi` off a null set, and `θ^n_φ` has positive mass
and does not charge the pluripolar pole set of `phi`.
-/

/-- The diagonal non-pluripolar measure does not charge pluripolar sets. -/
theorem diagonalPotentialMeasure_doesNotChargeManifoldPluripolar
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) :
    DoesNotChargeManifoldPluripolar (n := n) (diagonalPotentialMeasure theta u hu) :=
  GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
    (θ := fun _ : Fin n => theta) (u := fun _ => u) (fun _ => hu.1)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- For an antitone barrier family the locus where the pointwise infimum drops
below the reference is a countable union of the individual loci. -/
theorem setOf_iInf_lt_eq_iUnion {eta : ℝ → M → EReal} {phi : M → EReal}
    (hanti : ∀ a b : ℝ, 1 < a → a ≤ b → eta b ≤ eta a) :
    {x | (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) < phi x}
      = ⋃ k : ℕ, {x | eta (2 + (k : ℝ)) x < phi x} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    obtain ⟨⟨a, ha⟩, hax⟩ := iInf_lt_iff.mp h
    obtain ⟨k, hk⟩ := exists_nat_ge a
    exact ⟨k, lt_of_le_of_lt (hanti a (2 + (k : ℝ)) ha (by linarith) x) hax⟩
  · rintro ⟨k, hk⟩
    exact lt_of_le_of_lt
      (iInf_le (fun a : Ioi (1 : ℝ) => eta (a : ℝ) x)
        ⟨2 + (k : ℝ), by
          simp only [mem_Ioi]
          have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith⟩) hk

/-- **The closing step of Theorem 2.4.5, in measure-theoretic form.**  If every
member of an antitone family of barriers lies below the reference and agrees
with it off a `θ^n_φ`-null set, the pointwise infimum meets the reference at a
point where the reference is finite.  In particular the infimum is not
identically `-∞`, which is what Xia's exponential estimate is used for. -/
theorem exists_iInf_eq_of_null_barrier
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal} {eta : ℝ → M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpos : HasPositivePotentialMass theta phi hphi)
    (hanti : ∀ a b : ℝ, 1 < a → a ≤ b → eta b ≤ eta a)
    (hle : ∀ a : ℝ, 1 < a → eta a ≤ phi)
    (hnull : ∀ a : ℝ, 1 < a →
      diagonalPotentialMeasure theta phi hphi {x | eta a x < phi x} = 0) :
    ∃ x : M, (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) = phi x ∧ phi x ≠ ⊥ := by
  set mu := diagonalPotentialMeasure theta phi hphi with hmu
  have h1 : mu {x | (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) < phi x} = 0 := by
    rw [setOf_iInf_lt_eq_iUnion hanti]
    refine measure_iUnion_null fun k => hnull (2 + (k : ℝ)) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : mu {x | phi x = ⊥} = 0 :=
    diagonalPotentialMeasure_doesNotChargeManifoldPluripolar theta hphi _
      (quasiPsh_poles_manifoldLocallyPluripolar hphi.quasiPshPotential)
  have h3 : mu ({x | (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) < phi x} ∪
      {x | phi x = ⊥}) = 0 := measure_union_null h1 h2
  have hne : ({x | (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) < phi x} ∪
      {x | phi x = ⊥})ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro huniv
    rw [huniv] at h3
    exact absurd h3 (ne_of_gt hpos)
  obtain ⟨x, hx⟩ := hne
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_lt] at hx
  refine ⟨x, le_antisymm ?_ hx.1, hx.2⟩
  exact (iInf_le (fun a : Ioi (1 : ℝ) => eta (a : ℝ) x)
    ⟨2, by simp only [mem_Ioi]; norm_num⟩).trans (hle 2 (by norm_num) x)

/-! ## The closing stage of Theorem 2.4.5, assembled -/

/-- **The closing stage of Xia's Theorem 2.4.5.**  Suppose the middle,
analytic stage has produced for every `a > 1` a `theta`-PSH barrier `eta a`
which

* lies below the reference `phi` and is antitone in `a`;
* satisfies inequality (2.29) of Lemma 2.4.4, `a⁻¹ (eta a) + (1 - a⁻¹) psi ≤ phi`;
* agrees with `phi` off a `theta^n_phi`-null set.

Then `psi ≤ phi`.  The pointwise infimum of the family is `theta`-PSH
(`thetaPlurisubharmonic_iInf_of_antitone`), meets `phi` at a point where `phi`
is finite (`exists_iInf_eq_of_null_barrier`), hence is a genuine potential by
the identity principle, and `le_of_iInf_barrier` concludes. -/
theorem le_of_null_barrier_family [ConnectedSpace M]
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal} {eta : ℝ → M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : ThetaPlurisubharmonic theta.val psi)
    (hpos : HasPositivePotentialMass theta phi hphi)
    (heta : ∀ a : ℝ, 1 < a → ThetaPlurisubharmonic theta.val (eta a))
    (hanti : ∀ a b : ℝ, 1 < a → a ≤ b → eta b ≤ eta a)
    (hle : ∀ a : ℝ, 1 < a → eta a ≤ phi)
    (hbar : ∀ a : ℝ, 1 < a → convexComb a⁻¹ (eta a) psi ≤ phi)
    (hnull : ∀ a : ℝ, 1 < a →
      diagonalPotentialMeasure theta phi hphi {x | eta a x < phi x} = 0) :
    psi ≤ phi := by
  have hshift : ∀ k : ℕ, (1 : ℝ) < 2 + (k : ℝ) := by
    intro k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfun : (fun x : M => ⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x)
      = fun x : M => ⨅ k : ℕ, eta (2 + (k : ℝ)) x :=
    funext fun x => iInf_Ioi_eq_iInf_nat hanti x
  have hpshnat : ThetaPlurisubharmonic theta.val
      (fun x : M => ⨅ k : ℕ, eta (2 + (k : ℝ)) x) := by
    refine thetaPlurisubharmonic_iInf_of_antitone (fun k => heta _ (hshift k)) ?_
    intro x j k hjk
    have : (2 : ℝ) + (j : ℝ) ≤ 2 + (k : ℝ) := by
      have := Nat.cast_le (α := ℝ).mpr hjk
      linarith
    exact hanti (2 + (j : ℝ)) (2 + (k : ℝ)) (hshift j) this x
  obtain ⟨x₀, hx₀eq, hx₀ne⟩ :=
    exists_iInf_eq_of_null_barrier theta hphi hpos hanti hle hnull
  refine le_of_iInf_barrier hphi.1 hpsi hbar ?_
  rw [hfun]
  refine isThetaPshPotential_of_exists_ne_bot hpshnat ⟨x₀, ?_⟩
  rw [← congrFun hfun x₀, hx₀eq]
  exact hx₀ne

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction
