import SGPT.Foundations.Analysis.FirstPass.Envelopes
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

set_option autoImplicit false

/-!
# The background-specific P-preorder

Source: `transcendental-nakamaye-revised-20260831:sec:npp` and
`xia-sgpt:page-0224`.

The manuscript defines the background-independent P-preorder using one,
equivalently every, sufficiently positive common background.  The independence
theorem is analytic, so this verified core records the exact comparison for a
fixed closed real `(1,1)`-form.  It is intentionally distinct from bounded
singularity order (`MoreSingularOn`).
-/

namespace SGPT.Foundations.Analysis.FirstPass.POrder

noncomputable section

open PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The P-preorder computed in the fixed background `θ`.

Positive mass of the compared potentials is a hypothesis of the source's
background-independence theorem, not part of this pointwise definition. -/
def POrderWith (θ : ClosedRealOneOneForm n M) (φ ψ : M → EReal) : Prop :=
  singularityEnvelope θ.val φ ≤ singularityEnvelope θ.val ψ

/-- P-equivalence in a fixed background.  This compares singularity envelopes,
not bounded additive singularity types. -/
def PEquivalentWith (θ : ClosedRealOneOneForm n M) (φ ψ : M → EReal) : Prop :=
  POrderWith θ φ ψ ∧ POrderWith θ ψ φ

theorem pOrderWith_refl (θ : ClosedRealOneOneForm n M) (φ : M → EReal) :
    POrderWith θ φ φ :=
  le_rfl

theorem POrderWith.trans {θ : ClosedRealOneOneForm n M} {φ ψ η : M → EReal}
    (hφψ : POrderWith θ φ ψ) (hψη : POrderWith θ ψ η) :
    POrderWith θ φ η :=
  le_trans hφψ hψη

theorem PEquivalentWith.refl (θ : ClosedRealOneOneForm n M) (φ : M → EReal) :
    PEquivalentWith θ φ φ :=
  ⟨pOrderWith_refl θ φ, pOrderWith_refl θ φ⟩

theorem PEquivalentWith.symm {θ : ClosedRealOneOneForm n M} {φ ψ : M → EReal}
    (h : PEquivalentWith θ φ ψ) : PEquivalentWith θ ψ φ :=
  ⟨h.2, h.1⟩

theorem PEquivalentWith.trans {θ : ClosedRealOneOneForm n M} {φ ψ η : M → EReal}
    (hφψ : PEquivalentWith θ φ ψ) (hψη : PEquivalentWith θ ψ η) :
    PEquivalentWith θ φ η :=
  ⟨hφψ.1.trans hψη.1, hψη.2.trans hφψ.2⟩

theorem pEquivalentWith_iff_envelope_eq {θ : ClosedRealOneOneForm n M}
    {φ ψ : M → EReal} :
    PEquivalentWith θ φ ψ ↔
      singularityEnvelope θ.val φ = singularityEnvelope θ.val ψ := by
  exact ⟨fun h => le_antisymm h.1 h.2,
    fun h => ⟨h.le, h.ge⟩⟩

/-- Bounded additive singularity comparison implies the fixed-background
P-order.  The converse is false in general. -/
theorem pOrderWith_of_moreSingular {θ : ClosedRealOneOneForm n M}
    {φ ψ : M → EReal} (h : MoreSingularOn φ ψ Set.univ) :
    POrderWith θ φ ψ :=
  singularityEnvelope_mono h

/-- Equal bounded singularity type implies P-equivalence.  This is only the
easy direction of the hierarchy used in the manuscript. -/
theorem pEquivalentWith_of_sameSingularityType {θ : ClosedRealOneOneForm n M}
    {φ ψ : M → EReal} (h : SameSingularityTypeOn φ ψ Set.univ) :
    PEquivalentWith θ φ ψ := by
  rw [pEquivalentWith_iff_envelope_eq]
  exact singularityEnvelope_eq_of_sameSingularityType h

theorem pEquivalentWith_add_const (θ : ClosedRealOneOneForm n M)
    (φ : M → EReal) (c : ℝ) :
    PEquivalentWith θ (fun x => φ x + (c : EReal)) φ := by
  rw [pEquivalentWith_iff_envelope_eq]
  exact singularityEnvelope_add_const θ.val φ c

end

end SGPT.Foundations.Analysis.FirstPass.POrder
