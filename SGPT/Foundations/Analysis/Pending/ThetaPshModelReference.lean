import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

set_option autoImplicit false

/-!
# Stabilization of the `P`-chain of Xia's Step 1.2, by Zorn's lemma

Xia's Lemma 2.4.4, Step 1.2 (`xia-sgpt:page-0084`) replaces the less singular
potential `ψ` by the limit of the increasing *transfinite* sequence

  `ψ_0 = ψ`,  `ψ_{α+1} = P_θ[ψ_α]`,  `ψ_α = sup*_{β<α} ψ_β` at limit ordinals,

and stabilizes it because `PSH(X, θ)` is a set.  What the rest of Step 1 uses is
only the *existence* of a `θ`-PSH `Φ` with `ψ ≤ Φ ≤ 0`, `P_θ[Φ] = Φ` and
`∫ θ_Φ^n = ∫ θ_ψ^n`.

This module proves that existence.  The ordinal recursion is replaced by Zorn's
lemma on the set of admissible references

  `modelCandidates θ ψ m = {u : θ-PSH, ψ ≤ u ≤ 0, ∫ θ_u^n = m}`,   `m = ∫ θ_ψ^n`,

which is exactly Xia's transfinite argument with the bookkeeping done once:

* the *successor* step becomes maximality.  If `u` is maximal then `P_θ[u]` is
  again a candidate — `θ`-PSH (`singularityEnvelope_isThetaPshPotential`),
  above `u` because a normalized potential is its own competitor
  (`self_le_singularityEnvelope`), below `0`
  (`singularityEnvelope_le_zero`), and of the same mass by Xia's (2.32), i.e.
  `singularityEnvelopeMassPreserving` — so `u ≤ P_θ[u] ≤ u`;
* the *limit ordinal* step becomes the chain condition.  A chain need not be
  countable, but by **Choquet's lemma** its regularized supremum is already the
  regularized supremum of a countable subfamily
  (`exists_seq_uscRegularization_iSup_eq`), and the running maxima of a sequence
  inside a chain stay inside the chain, so the limit is the regularized limit of
  an *increasing sequence* of candidates.  Xia's Corollary 2.4.1 in the form
  `IncreasingLimitMassLe` (proved in `Pending.IncreasingLimitMass`) then bounds
  its mass by `m` from above, and monotonicity of the mass in the singularity
  order (`diagonalPotentialMass_mono_of_kahler`, Xia's Theorem 2.4.3) bounds it
  by `m` from below.

`M` is second countable because `IsComplexManifold` extends
`SecondCountableTopology`; this is what makes Choquet's lemma applicable and is
the only reason the uncountable chain causes no trouble.

## Why this is not the positive-mass idempotence of `P_θ`

`Pending.RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass`
and Xia's Theorem 3.1.2, (3.9), in general would give the fixed point in
one step with `Φ = P_θ[ψ]`, and neither may be used: the first is circular in
Lean (its `sorryAx` is Step 1 of Lemma 2.4.4 itself), the second is circular in
the source order (Xia proves Theorem 3.1.2 from the domination principle,
Theorem 2.4.5, which is downstream of Lemma 2.4.4).  Nothing used below is
downstream of Lemma 2.4.4: Choquet's lemma is Proposition 1.2.3, Corollary 2.4.1
comes from DDNL, Theorem 2.6, and Proposition 3.1.3 (`(2.32)`) is proved from
those two.

## Degenerate cases

Nothing here assumes `0 < n` or positive mass.  In dimension `0` a compact
connected manifold is a point and the non-pluripolar product is the empty
product, so every candidate has the same mass and the argument still produces a
`P`-fixed `Φ` (there, `Φ = 0`).  `IsThetaPshPotential` excludes `u ≡ -∞` near
any point, and `ψ` itself is a candidate, so the set Zorn is applied to is
nonempty; the empty chain is handled separately by `ψ`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaPshModelReference

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

/-! ### Running maxima of a sequence inside a chain -/

/-- The running maxima of a sequence taking values in a chain of functions stay
in the chain: a finite nonempty subset of a totally ordered set has a greatest
element, and here that element is one of the two arguments of each `max`. -/
theorem runningMax_mem_of_isChain {Y : Type*} {c : Set (Y → EReal)}
    (hc : IsChain (· ≤ ·) c) {s : ℕ → Y → EReal} (hs : ∀ k, s k ∈ c) :
    ∀ k, runningMax s k ∈ c := by
  intro k
  induction k with
  | zero => simpa only [runningMax] using hs 0
  | succ m ih =>
      rcases hc.total ih (hs (m + 1)) with h | h
      · have hEq : runningMax s (m + 1) = s (m + 1) := by
          funext x
          exact max_eq_right (h x)
        rw [hEq]
        exact hs (m + 1)
      · have hEq : runningMax s (m + 1) = runningMax s m := by
          funext x
          exact max_eq_left (h x)
        rw [hEq]
        exact ih

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-! ### The admissible references -/

/-- The set Zorn's lemma is applied to: normalized `θ`-PSH potentials above `ψ`
whose diagonal non-pluripolar mass is the prescribed value `m`. -/
def modelCandidates (theta : ClosedRealOneOneForm n M) (psi : M → EReal)
    (m : ℝ≥0∞) : Set (M → EReal) :=
  {u | ∃ hu : IsThetaPshPotential theta.val u,
    psi ≤ u ∧ u ≤ 0 ∧ diagonalPotentialMass theta u hu = m}

omit [BorelSpace M] [Nonempty M] in
/-- The mass clause of membership, read off against any chosen proof of
`θ`-plurisubharmonicity. -/
theorem diagonalPotentialMass_of_mem_modelCandidates
    {theta : ClosedRealOneOneForm n M} {psi u : M → EReal} {m : ℝ≥0∞}
    (hmem : u ∈ modelCandidates theta psi m)
    (hu : IsThetaPshPotential theta.val u) :
    diagonalPotentialMass theta u hu = m := by
  obtain ⟨hu', _, _, hmass⟩ := hmem
  rw [diagonalPotentialMass_proof_independent hu hu']
  exact hmass

omit [BorelSpace M] [Nonempty M] in
theorem isThetaPshPotential_of_mem_modelCandidates
    {theta : ClosedRealOneOneForm n M} {psi u : M → EReal} {m : ℝ≥0∞}
    (hmem : u ∈ modelCandidates theta psi m) :
    IsThetaPshPotential theta.val u :=
  hmem.choose

omit [BorelSpace M] [Nonempty M] in
theorem le_of_mem_modelCandidates {theta : ClosedRealOneOneForm n M}
    {psi u : M → EReal} {m : ℝ≥0∞} (hmem : u ∈ modelCandidates theta psi m) :
    psi ≤ u :=
  hmem.choose_spec.1

omit [BorelSpace M] [Nonempty M] in
theorem le_zero_of_mem_modelCandidates {theta : ClosedRealOneOneForm n M}
    {psi u : M → EReal} {m : ℝ≥0∞} (hmem : u ∈ modelCandidates theta psi m) :
    u ≤ 0 :=
  hmem.choose_spec.2.1

omit [BorelSpace M] [Nonempty M] in
/-- `ψ` is itself a candidate, so the set is nonempty. -/
theorem self_mem_modelCandidates (theta : ClosedRealOneOneForm n M)
    {psi : M → EReal} (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0) :
    psi ∈ modelCandidates theta psi (diagonalPotentialMass theta psi hpsi) :=
  ⟨hpsi, le_rfl, hpsi0, rfl⟩

/-! ### The limit-ordinal step: every chain has an upper bound -/

omit [Nonempty M] in
/-- **Xia's limit-ordinal step**, as the chain condition of Zorn's lemma.  The
regularized supremum of a nonempty chain of candidates is again a candidate.

Choquet's lemma reduces the (possibly uncountable) chain to a sequence inside
it; its running maxima stay in the chain and increase, so Corollary 2.4.1
(`increasingLimitMassLe`) applies and caps the mass of the limit by `m`, while
Theorem 2.4.3 (`diagonalPotentialMass_mono_of_kahler`) bounds it below by the
mass of `ψ`, which is `m`. -/
theorem exists_upperBound_of_chain (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {psi : M → EReal}
    (hpsi : IsThetaPshPotential theta.val psi)
    {c : Set (M → EReal)}
    (hcs : c ⊆ modelCandidates theta psi (diagonalPotentialMass theta psi hpsi))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ ub ∈ modelCandidates theta psi (diagonalPotentialMass theta psi hpsi),
      ∀ z ∈ c, z ≤ ub := by
  classical
  set m := diagonalPotentialMass theta psi hpsi with hm
  -- Choquet's lemma: a sequence inside the chain with the same regularized sup.
  obtain ⟨s, hsc, hsSup⟩ := exists_seq_uscRegularization_iSup_eq (X := M) hne
  set v : ℕ → M → EReal := runningMax s with hv
  have hvc : ∀ k, v k ∈ c := runningMax_mem_of_isChain hc hsc
  have hvmono : Monotone v := runningMax_monotone s
  have hvP : ∀ k, IsThetaPshPotential theta.val (v k) := fun k =>
    isThetaPshPotential_of_mem_modelCandidates (hcs (hvc k))
  have hv0 : ∀ k, v k ≤ 0 := fun k => le_zero_of_mem_modelCandidates (hcs (hvc k))
  have hvmass : ∀ k, diagonalPotentialMass theta (v k) (hvP k) = m := fun k =>
    diagonalPotentialMass_of_mem_modelCandidates (hcs (hvc k)) (hvP k)
  -- the two regularized suprema agree
  have hiSup : (⨆ k, v k) = ⨆ k, s k := by
    funext x
    simp only [iSup_apply]
    exact iSup_runningMax s x
  set Phi : M → EReal := uscRegularization (⨆ k, v k) with hPhi
  have hPhiSup : Phi = uscRegularization (sSup c) := by
    rw [hPhi, hiSup, hsSup]
  -- `Phi` is a theta-PSH potential
  have hv0le : v 0 ≤ ⨆ k, v k := le_iSup (fun k => v k) 0
  have hv0Phi : v 0 ≤ Phi := hv0le.trans (le_uscRegularization _)
  have hlocal : HasSmoothLocalPotentials theta.val := hpsi.1.hasSmoothLocalPotentials
  have hrange : sSup (Set.range v) = ⨆ k, v k := sSup_range
  have hPhiPsh : IsThetaPshPotential theta.val Phi := by
    refine ⟨?_, (hvP 0).2.mono hv0Phi⟩
    have := thetaPlurisubharmonic_uscRegularization_sSup (θ := theta.val)
      (F := Set.range v) hlocal ⟨v 0, Set.mem_range_self 0⟩
      (by rintro _ ⟨k, rfl⟩; exact hvP k) (by rintro _ ⟨k, rfl⟩; exact hv0 k)
    rwa [hrange] at this
  -- normalizations
  have hpsiPhi : psi ≤ Phi :=
    (le_of_mem_modelCandidates (hcs (hvc 0))).trans hv0Phi
  have hPhi0 : Phi ≤ 0 :=
    uscRegularization_le upperSemicontinuous_const (iSup_le hv0)
  -- the mass is unchanged
  have hmassLe : diagonalPotentialMass theta Phi hPhiPsh ≤ m := by
    have hle := increasingLimitMassLe theta v hvP hvmono hv0 hPhiPsh
    refine hle.trans ?_
    exact iSup_le fun k => (hvmass k).le
  have hmassGe : m ≤ diagonalPotentialMass theta Phi hPhiPsh := by
    refine diagonalPotentialMass_mono_of_kahler omega hpsi hPhiPsh ⟨0, ?_⟩
    intro x _
    simpa using hpsiPhi x
  refine ⟨Phi, ⟨hPhiPsh, hpsiPhi, hPhi0, le_antisymm hmassLe hmassGe⟩, ?_⟩
  intro z hz
  rw [hPhiSup]
  exact (le_sSup hz).trans (le_uscRegularization _)

/-! ### The successor step and the stabilization -/

/-- **Xia, SGPT, Lemma 2.4.4, Step 1.2** (`xia-sgpt:page-0084`): the increasing
transfinite `P_θ`-chain started at a normalized `θ`-PSH potential `ψ`
stabilizes.  There is a `θ`-PSH potential `Φ` with `ψ ≤ Φ ≤ 0`, fixed by the
`P`-envelope, and of the same diagonal non-pluripolar mass as `ψ`. -/
theorem exists_thetaPsh_modelReference (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {psi : M → EReal}
    (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0) :
    ∃ (Phi : M → EReal) (hPhi : IsThetaPshPotential theta.val Phi),
      psi ≤ Phi ∧ Phi ≤ 0 ∧ singularityEnvelope theta.val Phi = Phi ∧
        diagonalPotentialMass theta Phi hPhi = diagonalPotentialMass theta psi hpsi := by
  classical
  set m := diagonalPotentialMass theta psi hpsi with hm
  set S := modelCandidates theta psi m with hS
  have hlocal : HasSmoothLocalPotentials theta.val := hpsi.1.hasSmoothLocalPotentials
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨psi, self_mem_modelCandidates theta hpsi hpsi0, by simp⟩
    · exact exists_upperBound_of_chain omega theta hpsi hcs hc hne
  -- Zorn's lemma on `S`
  obtain ⟨u, huS, hmax⟩ := zorn_le₀ S hchain
  · have huP : IsThetaPshPotential theta.val u :=
      isThetaPshPotential_of_mem_modelCandidates huS
    have hu0 : u ≤ 0 := le_zero_of_mem_modelCandidates huS
    have hpsiu : psi ≤ u := le_of_mem_modelCandidates huS
    have humass : diagonalPotentialMass theta u huP = m :=
      diagonalPotentialMass_of_mem_modelCandidates huS huP
    -- the successor step: `P_θ[u]` is again a candidate above `u`
    have hPP : IsThetaPshPotential theta.val (singularityEnvelope theta.val u) :=
      singularityEnvelope_isThetaPshPotential theta.val theta.property.1
        theta.property.2 hlocal u huP
    have huPu : u ≤ singularityEnvelope theta.val u :=
      self_le_singularityEnvelope huP hu0
    have hPmass : diagonalPotentialMass theta (singularityEnvelope theta.val u) hPP = m := by
      rw [singularityEnvelopeMassPreserving omega theta u huP hPP]
      exact humass
    have hPmem : singularityEnvelope theta.val u ∈ S :=
      ⟨hPP, hpsiu.trans huPu, singularityEnvelope_le_zero theta.val u, hPmass⟩
    have hfix : singularityEnvelope theta.val u = u :=
      le_antisymm (hmax hPmem huPu) huPu
    exact ⟨u, huP, hpsiu, hu0, hfix, humass⟩

end Manifold

end

end SGPT.Foundations.Analysis.Pending.ThetaPshModelReference
