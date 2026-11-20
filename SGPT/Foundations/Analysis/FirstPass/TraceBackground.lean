import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

set_option autoImplicit false

/-!
# Background data for trace approximants

Source: SGPT, Definition 8.1.1 and its footnote on
`xia-sgpt:page-0277`.

The target Kähler form must dominate the pullback of every varying ambient
background used by the restricted approximants.  Ordinary composition with
the target map is named explicitly and is not identified with a trace.
-/

namespace SGPT.Foundations.Analysis.FirstPass.TraceBackground

noncomputable section

open PositiveClasses ClosedRealOneOneForm
open scoped Manifold ContDiff

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A closed real form dominates another when their difference is
semipositive on every complex tangent line. -/
def FormDominates (β γ : ClosedRealOneOneForm k V) : Prop :=
  (β - γ).val.IsSemipositive

/-- A fixed target Kähler background large enough for every restricted term
of an approximation with backgrounds `θ + ε_j ω`. -/
def IsAdmissibleTraceBackground
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (ε : ℕ → ℝ) (β : ClosedRealOneOneForm k V) : Prop :=
  β.val.IsKahler ∧
    ∀ j, FormDominates β (pullback hι (θ + ε j • omega.form))

/-- Literal composition with the target map.  For singular potentials this
can be identically negative infinity even when the ambient potential is
locally nondegenerate, so it is not called a trace. -/
def ordinaryRestriction (ι : V → M) (u : M → EReal) : V → EReal :=
  u ∘ ι

omit [TopologicalSpace V] [TopologicalSpace M] in
@[simp] theorem ordinaryRestriction_apply (ι : V → M) (u : M → EReal) (x : V) :
    ordinaryRestriction ι u x = u (ι x) := rfl

theorem IsAdmissibleTraceBackground.isKahler {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {ε : ℕ → ℝ} {β : ClosedRealOneOneForm k V}
    (h : IsAdmissibleTraceBackground hι omega θ ε β) : β.val.IsKahler :=
  h.1

theorem IsAdmissibleTraceBackground.dominates {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {ε : ℕ → ℝ} {β : ClosedRealOneOneForm k V}
    (h : IsAdmissibleTraceBackground hι omega θ ε β) (j : ℕ) :
    FormDominates β (pullback hι (θ + ε j • omega.form)) :=
  h.2 j

end

end SGPT.Foundations.Analysis.FirstPass.TraceBackground
