import SGPT.Foundations.Analysis.FirstPass.QuasiPshSingularities

/-!
# Source global additive singularity comparison

SGPT `def:parorder` uses these formulas on compact manifolds and quasi-PSH
functions. They also make sense for every extended-real function, including
the source's additional bottom function. Reuse the main branch's exact real
additive comparison and its existing preorder/equivalence proofs.
-/

namespace SGPT.PSH

open Set

variable {X : Type*}

/-- One actual global finite additive constant, in the source direction. -/
def SingularityLE (u v : X → EReal) : Prop :=
  SGPT.Foundations.Analysis.MoreSingularOn u v Set.univ

/-- Source equality of singularity type is mutual additive comparison. -/
def SingularityEquiv (u v : X → EReal) : Prop :=
  SGPT.Foundations.Analysis.SameSingularityTypeOn u v Set.univ

theorem singularityLE_iff_exists_real (u v : X → EReal) :
    SingularityLE u v ↔ ∃ C : ℝ, ∀ x : X, u x ≤ v x + (C : EReal) := by
  simp only [SingularityLE, SGPT.Foundations.Analysis.MoreSingularOn, Set.mem_univ,
    forall_const]

theorem singularityEquiv_iff (u v : X → EReal) :
    SingularityEquiv u v ↔ SingularityLE u v ∧ SingularityLE v u := Iff.rfl

theorem singularityLE_refl (u : X → EReal) : SingularityLE u u :=
  SGPT.Foundations.Analysis.MoreSingularOn.refl u Set.univ

theorem singularityLE_trans {u v w : X → EReal}
    (huv : SingularityLE u v) (hvw : SingularityLE v w) : SingularityLE u w :=
  SGPT.Foundations.Analysis.MoreSingularOn.trans huv hvw

theorem singularityEquiv_refl (u : X → EReal) : SingularityEquiv u u :=
  SGPT.Foundations.Analysis.SameSingularityTypeOn.refl u Set.univ

theorem singularityEquiv_symm {u v : X → EReal}
    (huv : SingularityEquiv u v) : SingularityEquiv v u :=
  SGPT.Foundations.Analysis.SameSingularityTypeOn.symm huv

theorem singularityEquiv_trans {u v w : X → EReal}
    (huv : SingularityEquiv u v) (hvw : SingularityEquiv v w) : SingularityEquiv u w :=
  SGPT.Foundations.Analysis.SameSingularityTypeOn.trans huv hvw

/-- The source's explicitly included constant bottom function. -/
theorem bot_singularityLE (u : X → EReal) : SingularityLE (fun _ ↦ ⊥) u :=
  SGPT.Foundations.Analysis.MoreSingularOn.of_le (fun _ _ ↦ bot_le)

end SGPT.PSH
