import SGPT.Trace.BertiniSmooth

/-! Literal original analytic Bertini in dimension zero, for arbitrary weights. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped Topology Manifold ContDiff
namespace SGPT.Trace.Bertini
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {N : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
  (p : X → ComplexProjectiveSpace N)

omit [IsComplexManifold 0 X] in
/-- The actual original smooth hypersurface condition forces an empty member in dimension zero. -/
theorem member_eq_empty_of_smooth_zero_dim {l : HyperplaneSpace N}
    (hl : IsSmoothHypersurfaceMember 0 p l) : member p l = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨e, v, _he, hv⟩ := hl x hx (chartIndex (p x)) (mem_affineChart_chartIndex (p x))
  have hzero : v = 0 := Subsingleton.elim _ _
  exact hv (by simp [DerivativeIdeal.chartDeriv, hzero])

/-- Exact original book good-set conclusion in dimension zero; the weight is arbitrary. -/
theorem coPluripolar_bertiniGoodSet_zero_dim [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hN : 1 ≤ N) (φ : X → EReal) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      (bertiniGoodSet p hp φ) := by
  refine (locallyPluripolar_singularMemberSet p hp hN).mono ?_
  intro l hbad hl
  exact hbad (mem_bertiniGoodSet_of_member_eq_empty p hp φ
    (member_eq_empty_of_smooth_zero_dim p hl))

end SGPT.Trace.Bertini
