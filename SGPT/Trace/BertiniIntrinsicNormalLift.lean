import SGPT.Trace.BertiniIntrinsicTangentSequence

/-! Actual intrinsic normal right inverse and normal-lift-independent contraction.
All vectors, tangent maps, normal fibres and top covectors are the ORIGINAL
native objects; no normal or contraction-independence certificate is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual original physical normal-line scalar coordinate times the
internally produced ORIGINAL native normal gives a genuine linear lift. -/
def originalIntrinsicNormalLift
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q) →ₗ[ℂ]
      TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q) := by
  have hpoint := c.tangentPoint_chart_coordinates q
  let A := nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
    ((mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2)
  exact {
    toFun := fun w => A w • c.originalIntrinsicNormal q
    map_add' := by intro u v; rw [map_add, add_smul]
    map_smul' := by intro a v; rw [map_smul, smul_smul]; rfl }

theorem originalIntrinsicNormalLift_spec
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (w : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)) :
    c.originalIntrinsicConormal hp q (c.originalIntrinsicNormalLift hp q w) = w := by
  have hpoint := c.tangentPoint_chart_coordinates q
  let A := nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
    ((mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2)
  change c.originalIntrinsicConormal hp q (A w • c.originalIntrinsicNormal q) = w
  rw [map_smul, c.originalIntrinsicNormal_spec hp q]
  apply A.injective
  rw [map_smul]
  have hA : A (nativeBertiniCoordinateSection ⟨p, hp⟩ c.j (c.tangentPoint q)) = 1 :=
    nativeBertiniCoordinateFiberEquiv_coordinate _ _ _ _
  rw [hA, smul_eq_mul, mul_one]

/-- An actual native ambient top covector vanishes on any tuple in the
actual original intrinsic conormal kernel. Nontriviality is produced. -/
theorem originalNativeTopForm_zero_in_kernel
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (α : (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q))
    (hv : ∀ i, c.originalIntrinsicConormal hp q (v i) = 0) : α v = 0 := by
  let A := nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1
  let : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) :=
    A.symm.finiteDimensional
  apply α.map_linearDependent
  intro hli
  have hdim : Fintype.card (Fin (d + 1)) =
      Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) := by
    simpa using A.finrank_eq.symm
  have htop := hli.span_eq_top_of_card_eq_finrank hdim
  have hle : Submodule.span ℂ (Set.range v) ≤ LinearMap.ker (c.originalIntrinsicConormal hp q) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  rw [htop] at hle
  have hz : c.originalIntrinsicConormal hp q (c.originalIntrinsicNormal q) = 0 := hle Submodule.mem_top
  rw [c.originalIntrinsicNormal_spec hp q] at hz
  have hpoint := c.tangentPoint_chart_coordinates q
  exact (nativeBertiniCoordinateSection_ne_zero ⟨p, hp⟩ c.j (c.tangentPoint q)
    ((mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2)) hz

/-- Intrinsic normal contraction on the ORIGINAL native member is
independent of a lift of the SAME actual original physical normal vector. -/
theorem originalNativeContraction_independent
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ (α : (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
      (ν ν' : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q))
      (_hν : c.originalIntrinsicConormal hp q ν = c.originalIntrinsicConormal hp q ν')
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      α (Matrix.vecCons ν (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) =
        α (Matrix.vecCons ν' (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  intro α ν ν' hν v
  have hzero := c.originalNativeTopForm_zero_in_kernel hp q α
    (Matrix.vecCons (ν - ν') (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) (by
      intro i
      cases i using Fin.cases with
      | zero => change c.originalIntrinsicConormal hp q (ν - ν') = 0; rw [map_sub, hν, sub_self]
      | succ i =>
        have h : c.originalIntrinsicConormal hp q (c.originalIntrinsicTangentEquiv hp q hsm (v i)).val = 0 :=
          (c.originalIntrinsicTangentEquiv hp q hsm (v i)).property
        rwa [c.originalIntrinsicTangentEquiv_apply hp q hsm (v i)] at h)
  have hsub : α (Matrix.vecCons (ν - ν') (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) =
      α (Matrix.vecCons ν (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) -
        α (Matrix.vecCons ν' (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) :=
    congrArg (fun β => β (fun i => c.originalNativeInclusionDifferential hp q hsm (v i)))
      ((α.curryLeft).map_sub ν ν')
  exact sub_eq_zero.mp (hsub.symm.trans hzero)

end SGPT.Trace.Bertini.SliceChart
