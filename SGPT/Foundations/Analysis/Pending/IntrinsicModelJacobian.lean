import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.CommonStrictUnramifiedPoint
import SGPT.Foundations.Analysis.Pending.OverBaseJacobianOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IntrinsicModelJacobian

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong AnalyticModificationLocalDiscrepancy
  ActualFlatNormalOrder

universe u

/-- Original common-model maps and literal equal strict transforms produce equal actual local Jacobian orders. -/
theorem exists_common_localJacobianOrder_eq {m : ℕ} {X Y₀ Y₁ Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀] [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁] [IsComplexManifold (m + 1) Y₁]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hπ₀ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π₀)
    (hπ₁ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π₁)
    (hg₀ : IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : IsAnalyticModification (n := m + 1) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁)
    (V₀ : ClosedIrreducibleAnalyticSubvariety (m + 1) Y₀)
    (V₁ : ClosedIrreducibleAnalyticSubvariety (m + 1) Y₁)
    (hE₀ : ∀ y ∈ V₀.carrier, RegularAtDim (n := m + 1) V₀.carrier y m)
    (hE₁ : ∀ y ∈ V₁.carrier, RegularAtDim (n := m + 1) V₁.carrier y m)
    (hstrict : strictTransform (m + 1) g₀ V₀.carrier = strictTransform (m + 1) g₁ V₁.carrier) :
    ∃ (z : Z) (Φ₀ : DivisorFlattening (m := m) V₀.carrier (g₀ z))
      (Φ₁ : DivisorFlattening (m := m) V₁.carrier (g₁ z)),
      g₀ z ∈ V₀.carrier ∧ g₁ z ∈ V₁.carrier ∧
        flatJacobianOrder hπ₀ Φ₀ = flatJacobianOrder hπ₁ Φ₁ := by
  obtain ⟨y₀, hy₀⟩ := V₀.nonempty
  have hdim : V₀.dim = m :=
    (AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V₀ (hE₀ y₀ hy₀)).symm
  have hcodim : V₀.dim + 1 = m + 1 := by rw [hdim]
  obtain ⟨W, hW₀, _, _, _⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hg₀ V₀ hcodim
  have hW₁ : W.carrier = strictTransform (m + 1) g₁ V₁.carrier := hW₀.trans hstrict
  obtain ⟨z, hzreg, hz₀, hz₁⟩ :=
    CommonStrictUnramifiedPoint.exists_common_regular_unramified_point hg₀.1 hg₁.1 V₀ V₁ W hW₀ hW₁
  have hzW : z ∈ W.carrier := hzreg.2.1
  have hzg₀ : g₀ z ∈ V₀.carrier := by
    have h : z ∈ strictTransform (m + 1) g₀ V₀.carrier := hW₀ ▸ hzW
    exact closure_minimal sdiff_subset (V₀.isClosed_carrier.preimage hg₀.1.continuous) h
  have hzg₁ : g₁ z ∈ V₁.carrier := by
    have h : z ∈ strictTransform (m + 1) g₁ V₁.carrier := hW₁ ▸ hzW
    exact closure_minimal sdiff_subset (V₁.isClosed_carrier.preimage hg₁.1.continuous) h
  obtain ⟨Φ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE₀ (g₀ z) hzg₀)
  obtain ⟨Φ₁⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE₁ (g₁ z) hzg₁)
  have hO₀ : IsOpen (exceptionalLocus (m + 1) g₀)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg₀.1
  have hO₁ : IsOpen (exceptionalLocus (m + 1) g₁)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg₁.1
  have hWO₀ : ∀ w ∈ (exceptionalLocus (m + 1) g₀)ᶜ, w ∈ W.carrier ↔ g₀ w ∈ V₀.carrier := by
    intro w hw
    rw [hW₀]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg₀.1.continuous V₀.isClosed_carrier hw
  have hWO₁ : ∀ w ∈ (exceptionalLocus (m + 1) g₁)ᶜ, w ∈ W.carrier ↔ g₁ w ∈ V₁.carrier := by
    intro w hw
    rw [hW₁]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg₁.1.continuous V₁.isClosed_carrier hw
  have hWreg : RegularAtDim (n := m + 1) W.carrier z m :=
    RegularAtDimTransport.regularAtDim_of_preimage hg₀.1 hz₀ hO₀ hz₀ hWO₀ (hE₀ (g₀ z) hzg₀)
  obtain ⟨Ω⟩ := DivisorFlattening.nonempty_of_regularAtDim hWreg
  have hsets₀ : ∀ᶠ w in 𝓝 z, w ∈ W.carrier ↔ g₀ w ∈ V₀.carrier := by
    filter_upwards [hO₀.mem_nhds hz₀] with w hw
    exact hWO₀ w hw
  have hsets₁ : ∀ᶠ w in 𝓝 z, w ∈ W.carrier ↔ g₁ w ∈ V₁.carrier := by
    filter_upwards [hO₁.mem_nhds hz₁] with w hw
    exact hWO₁ w hw
  have hJ₀ := OverBaseJacobianOrder.flatJacobianOrder_comp_eq_of_not_exceptional
    hπ₀ hg₀.1 hz₀ Φ₀ Ω hsets₀
  have hJ₁ := OverBaseJacobianOrder.flatJacobianOrder_comp_eq_of_not_exceptional
    hπ₁ hg₁.1 hz₁ Φ₁ Ω hsets₁
  have hsame (a b : Z → X)
      (ha : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ a)
      (hb : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ b)
      (hab : a = b) : flatJacobianOrder ha Ω = flatJacobianOrder hb Ω := by
    subst b
    rfl
  exact ⟨z, Φ₀, Φ₁, hzg₀, hzg₁,
    hJ₀.symm.trans ((hsame _ _ (hπ₀.comp hg₀.1) (hπ₁.comp hg₁.1) hcomm).trans hJ₁)⟩

end SGPT.Foundations.Analysis.Pending.IntrinsicModelJacobian
