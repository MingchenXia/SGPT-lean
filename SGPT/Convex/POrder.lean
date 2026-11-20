import SGPT.Convex.Subgradient

/-!
# The actual convex P-singularity order

The source relation uses closed raw subgradient images. For proper closed
functions, the checked image theorem identifies these with the actual closed
effective domains of their conjugates.
-/

namespace SGPT.Convex

open Set

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]

/-- Exact source `def:convexPorder`, using closed actual raw subgradient images. -/
def PSingularityLE (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop :=
  _root_.closure (rawSubgradientImage B f) ⊆ _root_.closure (rawSubgradientImage B g)

/-- The source equivalence relation associated to the actual P-order. -/
def PSingularityEquiv (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop :=
  PSingularityLE B f g ∧ PSingularityLE B g f

/-- The actual source P-order is reflexive. -/
theorem pSingularityLE_refl (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) :
    PSingularityLE B f f := Subset.rfl

/-- The actual source P-order is transitive. -/
theorem pSingularityLE_trans (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f g h : E → EReal}
    (hfg : PSingularityLE B f g) (hgh : PSingularityLE B g h) :
    PSingularityLE B f h := hfg.trans hgh

/-- Actual mutual source P-order is exactly equality of actual closed subgradient images. -/
theorem pSingularityEquiv_iff_closure_eq (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    (f g : E → EReal) :
    PSingularityEquiv B f g ↔
      _root_.closure (rawSubgradientImage B f) = _root_.closure (rawSubgradientImage B g) := by
  exact ⟨fun h ↦ subset_antisymm h.1 h.2, fun h ↦ ⟨h.subset, h.symm.subset⟩⟩

/-- Source P-equivalence is reflexive. -/
theorem pSingularityEquiv_refl (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) :
    PSingularityEquiv B f f := ⟨Subset.rfl, Subset.rfl⟩

/-- Source P-equivalence is symmetric. -/
theorem pSingularityEquiv_symm (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f g : E → EReal}
    (hfg : PSingularityEquiv B f g) : PSingularityEquiv B g f := ⟨hfg.2, hfg.1⟩

/-- Source P-equivalence is transitive. -/
theorem pSingularityEquiv_trans (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f g h : E → EReal}
    (hfg : PSingularityEquiv B f g) (hgh : PSingularityEquiv B g h) :
    PSingularityEquiv B f h := ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

section PerfectPairing

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Actual closed conjugate domains characterize the source P-order on proper
lower semicontinuous convex functions. -/
theorem pSingularityLE_iff_conjugate_domain
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (hlf : LowerSemicontinuous f) (hlg : LowerSemicontinuous g) :
    PSingularityLE B f g ↔
      _root_.closure (effectiveDomain (conjugate B f)) ⊆
        _root_.closure (effectiveDomain (conjugate B g)) := by
  unfold PSingularityLE
  rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf hlf,
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg hlg]

/-- Actual closed conjugate-domain equality characterizes source P-equivalence. -/
theorem pSingularityEquiv_iff_conjugate_domain
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (hlf : LowerSemicontinuous f) (hlg : LowerSemicontinuous g) :
    PSingularityEquiv B f g ↔
      _root_.closure (effectiveDomain (conjugate B f)) =
        _root_.closure (effectiveDomain (conjugate B g)) := by
  rw [pSingularityEquiv_iff_closure_eq,
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf hlf,
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg hlg]

end PerfectPairing

end SGPT.Convex
