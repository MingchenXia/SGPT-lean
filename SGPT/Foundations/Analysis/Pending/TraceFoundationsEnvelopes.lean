import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope
import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.FirstPass.POrder

set_option autoImplicit false

/-!
# The `P`-envelope, multiplier ideals and the relative full-mass class

Two results of Xia, *Singularities in global pluripotential theory* (SGPT), on the singularity
envelope `P_θ[φ] = sup* {ψ ∈ PSH(X, θ) : ψ ≤ 0, ψ ⪯ φ}` of a fixed background `θ`.

* **`P`-order controls multiplier ideals** (Xia, Corollary 6.1.1, `xia-sgpt:page-0214`; blueprint
  `trace:porder-multiplier`): if `P_θ[φ] ≤ P_θ[ψ]`, then `I(λφ) ⊆ I(λψ)` for every `λ > 0`.  The
  chain is `I(φ) ⊆ I(P_θ[φ]) ⊆ I(P_θ[ψ]) ⊆ I(ψ)`; the last inclusion is Xia's Proposition 3.2.9,
  which rests on strong openness (`Pending.increasingStrongOpenness_ofRegularRoute`).  No
  positive-mass or connectedness hypothesis.
* **Full mass and the envelope, normalized variant** (Xia, Proposition 3.1.14,
  `xia-sgpt:page-0115`--`page-0116`; blueprint `trace:full-mass-envelope-normalized`): the
  repository predicate `RelativeFullMass` requires `u ≤ φ`. For a model potential `φ` and a
  theta-PSH potential `u ≤ 0`, this predicate is equivalent to `P_θ[u] = φ`; for arbitrary `u`,
  the envelope equality is equivalent to membership of a suitable translate `u - C` in that
  normalized class. The example `u = φ + 1` separates this repository normalized class from
  the source class. Xia's actual class permits `u ⪯ φ`, and his unnormalized criterion is
  formalized by `RelativePreceqStatements.relativeFullMassPreceq_iff_singularityEnvelope_eq`.
  The additional normalization here belongs to the normalized variant, not to Xia's statement.

The setting is a compact complex manifold with a closed real `(1,1)`-form; the second item also
uses a Kähler background and connectedness, the standing hypotheses of the diagonal mass
(blueprint `trace:diagonal-mass`).
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.TraceFoundationsEnvelopes

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope FirstPass.POrder DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### `P`-order and multiplier ideals -/

/-- **`P`-order controls multiplier ideals** (Xia SGPT, Corollary 6.1.1, `xia-sgpt:page-0214`;
blueprint `trace:porder-multiplier`).  On a nonempty compact complex manifold, for theta-PSH
potentials `φ, ψ` with `P_θ[φ] ≤ P_θ[ψ]`, every multiplier ideal of `φ` is contained in the
corresponding one of `ψ`: `I(λφ) ⊆ I(λψ)` for every `λ > 0`. -/
theorem iOrderOnManifold_of_pOrderWith [CompactSpace M] [Nonempty M]
    (θ : ClosedRealOneOneForm n M) {φ ψ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (h : POrderWith θ φ ψ) :
    IOrderOnManifold (n := n) φ ψ := by
  have hlocal : HasSmoothLocalPotentials θ.val := hφ.1.hasSmoothLocalPotentials
  have hPψ : IsThetaPshPotential θ.val (singularityEnvelope θ.val ψ) :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2 hlocal ψ hψ
  exact ((iOrderOnManifold_singularityEnvelope θ.property.1 θ.property.2 hlocal hφ).trans
    (iOrderOnManifold_of_le hPψ.1.quasiPlurisubharmonic h)).trans
    (iOrderOnManifold_singularityEnvelope_self_of_strongOpenness
      (increasingStrongOpenness_ofRegularRoute n) hlocal hψ)

/-! ### Full mass and the singularity envelope -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **Full mass gives the model envelope** (Xia SGPT, Proposition 3.1.14, (1) ⇒ (2)): for
`u ∈ E(X, θ; φ)`, `P_θ[u] = φ`. -/
theorem singularityEnvelope_eq_of_relativeFullMass (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u : M → EReal} {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) :
    singularityEnvelope theta.val u = phi := by
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hphi0 : phi ≤ 0 := by
    rw [hphi.envelope_eq]
    exact singularityEnvelope_le_zero theta.val phi
  apply le_antisymm
  · calc singularityEnvelope theta.val u ≤ singularityEnvelope theta.val phi :=
          singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hu.le_reference x)
      _ = phi := hphi.envelope_eq.symm
  · refine equalMassLeSingularityEnvelope omega theta u phi hu.plurisubharmonic
      hphi.plurisubharmonic ?_ hphi0 (MoreSingularOn.of_le fun x _ => hu.le_reference x)
      humass
    change 0 < diagonalPotentialMass theta u hu.plurisubharmonic
    rw [humass]
    exact hphi.positive_mass

/-- **The model envelope gives normalized full mass.** This is the normalized variant of Xia
SGPT, Proposition 3.1.14, (2) ⇒ (1): if `u ≤ 0` is theta-PSH and `P_θ[u] = φ`, then the repository
predicate `RelativeFullMass theta phi u hphi`, which requires `u ≤ φ`, holds. The assumption
`u ≤ 0` is needed for this normalized variant; Xia's source class instead uses `u ⪯ φ`. -/
theorem relativeFullMass_of_singularityEnvelope_eq (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u : M → EReal} (hphi : IsModelPotential theta phi)
    (hu : IsThetaPshPotential theta.val u) (hu0 : u ≤ 0)
    (hP : singularityEnvelope theta.val u = phi) :
    RelativeFullMass theta phi u hphi := by
  have hle : u ≤ phi := hP ▸ self_le_singularityEnvelope hu hu0
  have hPpsh : IsThetaPshPotential theta.val (singularityEnvelope theta.val u) :=
    hP ▸ hphi.plurisubharmonic
  have hmass := singularityEnvelopeMassPreserving omega theta u hu hPpsh
  have key : ∀ (w : M → EReal) (hw : IsThetaPshPotential theta.val w), w = phi →
      diagonalPotentialMass theta w hw = diagonalPotentialMass theta phi hphi.plurisubharmonic := by
    rintro w hw rfl
    rfl
  refine (relativeFullMass_iff theta phi u hphi hu).2 ⟨hle, ?_⟩
  rw [← hmass]
  exact key _ hPpsh hP

/-- **Full mass and the singularity envelope, normalized form** (Xia SGPT, Proposition 3.1.14;
blueprint `trace:full-mass-envelope-normalized`): for a theta-PSH potential `u ≤ 0`,
`u ∈ E(X, θ; φ) ↔ P_θ[u] = φ`. -/
theorem relativeFullMass_iff_singularityEnvelope_eq (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u : M → EReal} (hphi : IsModelPotential theta phi)
    (hu : IsThetaPshPotential theta.val u) (hu0 : u ≤ 0) :
    RelativeFullMass theta phi u hphi ↔ singularityEnvelope theta.val u = phi :=
  ⟨singularityEnvelope_eq_of_relativeFullMass omega,
    relativeFullMass_of_singularityEnvelope_eq omega hphi hu hu0⟩

/-- **Full mass and the singularity envelope, general form** (blueprint
`trace:full-mass-envelope-normalized`): for any theta-PSH potential `u`, `P_θ[u] = φ` if and only if
some translate `u - C` lies in `E(X, θ; φ)`. -/
theorem singularityEnvelope_eq_iff_exists_relativeFullMass_sub (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u : M → EReal} (hphi : IsModelPotential theta phi)
    (hu : IsThetaPshPotential theta.val u) :
    singularityEnvelope theta.val u = phi ↔
      ∃ C : ℝ, RelativeFullMass theta phi (fun x => u x + ((-C : ℝ) : EReal)) hphi := by
  constructor
  · intro hP
    obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
    refine ⟨C, relativeFullMass_of_singularityEnvelope_eq omega hphi (hu.add_const (-C))
      (fun x => ?_) ?_⟩
    · have h := add_le_add (hC x) (le_refl ((-C : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    · rw [singularityEnvelope_add_const]
      exact hP
  · rintro ⟨C, hC⟩
    rw [← singularityEnvelope_add_const theta.val u (-C)]
    exact singularityEnvelope_eq_of_relativeFullMass omega hC

omit [BorelSpace M] [ConnectedSpace M] in
/-- **The normalized repository class differs from the source class.** For a model potential
`φ`, the theta-PSH potential `u = φ + 1` has `P_θ[u] = φ` but does not satisfy the repository
predicate `RelativeFullMass`, because that predicate requires `u ≤ φ`. This is the distinction
in `trace:full-mass-envelope-normalized`; it is not a counterexample to Xia's source-preceq
criterion, whose class requires only `u ⪯ φ`. -/
theorem exists_singularityEnvelope_eq_not_relativeFullMass [Nonempty M]
    {theta : ClosedRealOneOneForm n M} {phi : M → EReal} (hphi : IsModelPotential theta phi) :
    ∃ u : M → EReal, IsThetaPshPotential theta.val u ∧
      singularityEnvelope theta.val u = phi ∧ ¬ RelativeFullMass theta phi u hphi := by
  refine ⟨fun x => phi x + ((1 : ℝ) : EReal), hphi.plurisubharmonic.add_const 1, ?_, ?_⟩
  · rw [singularityEnvelope_add_const]
    exact hphi.envelope_eq.symm
  · intro h
    obtain ⟨x⟩ := ‹Nonempty M›
    obtain ⟨y, -, hy⟩ := hphi.plurisubharmonic.2 x univ isOpen_univ (mem_univ x)
    have htop : phi y ≠ ⊤ := hphi.plurisubharmonic.1.quasiPlurisubharmonic.ne_top y
    have hle : phi y + ((1 : ℝ) : EReal) ≤ phi y := h.le_reference y
    obtain ⟨r, hr⟩ : ∃ r : ℝ, phi y = r := ⟨(phi y).toReal, (EReal.coe_toReal htop hy).symm⟩
    rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    linarith

end

end SGPT.Foundations.Analysis.Pending.TraceFoundationsEnvelopes
