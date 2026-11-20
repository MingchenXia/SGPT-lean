import SGPT.Trace.BertiniOriginalResidueCoefficient

/-! The ACTUAL original canonical residue, tensored with the ORIGINAL L,
has its actual coefficient norm in the ORIGINAL physical L metric.

This is a local coefficient density identity, before global holomorphic
adjunction gluing or the coordinate-independent Hodge integral. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft

private def canonicalTupleEvaluation {k : ℕ} {C V : Type*}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup V] [Module ℂ V]
    (F : C ≃ₗ[ℂ] (V [⋀^Fin k]→ₗ[ℂ] ℂ)) (v : Fin k → V) : C →ₗ[ℂ] ℂ where
  toFun α := F α v
  map_add' α β := by rw [map_add, AlternatingMap.add_apply]
  map_smul' a α := by rw [map_smul, AlternatingMap.smul_apply]; rfl

private def scalarTensorValue {C V : Type*}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup V] [Module ℂ V]
    (a : C →ₗ[ℂ] ℂ) : TensorProduct ℂ C V →ₗ[ℂ] V :=
  (TensorProduct.lid ℂ V).toLinearMap.comp (TensorProduct.map a LinearMap.id)

namespace SliceChart

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  [CompactSpace Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual ambient canonical coefficient times actual physical P coordinate. -/
def originalAmbientCanonicalNormalCoefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    TensorProduct ℂ
      ((nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      ((nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map
    (canonicalTupleEvaluation
      (nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1)
      (Matrix.vecCons (EuclideanSpace.single c.m 1) (fun j => EuclideanSpace.single (c.m.succAbove j) 1)))
    (nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
      ((mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q).1).mp
        (c.tangentPoint_chart_coordinates q).2.2)).toLinearMap)

theorem originalAmbientCanonicalNormalCoefficient_tmul
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
    (w : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)) :
    c.originalAmbientCanonicalNormalCoefficient hp q (α ⊗ₜ[ℂ] w) =
      nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α
        (Matrix.vecCons (EuclideanSpace.single c.m 1) (fun j => EuclideanSpace.single (c.m.succAbove j) 1)) *
      nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
        ((mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q).1).mp
          (c.tangentPoint_chart_coordinates q).2.2) w := rfl

/-- The actual ambient coefficient vector in the original PHYSICAL L fibre. -/
def originalAmbientLValue
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (L : HermitianHolomorphicLineBundle (d + 1) Y) :
    TensorProduct ℂ
      (TensorProduct ℂ ((nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
        ((nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)))
      (L.Fiber (c.tangentPoint q)) →ₗ[ℂ] L.Fiber (c.tangentPoint q) :=
  scalarTensorValue (c.originalAmbientCanonicalNormalCoefficient hp q)

/-- Tensor the ACTUAL original adjunction with id on the SAME original L,
then evaluate the ACTUAL native canonical covector on the ACTUAL original
parameter tangent tuple. Its value lies in the original PHYSICAL L fibre. -/
def originalResidueLValue
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d)
    (L : HermitianHolomorphicLineBundle (d + 1) Y) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    TensorProduct ℂ
      (TensorProduct ℂ ((nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
        ((nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)))
      (L.Fiber (c.tangentPoint q)) →ₗ[ℂ] L.Fiber (c.tangentPoint q) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  exact (scalarTensorValue (canonicalTupleEvaluation
    (nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q))
    (fun j => c.originalSliceParameterTangentEquiv hp q hsm (EuclideanSpace.single j 1)))).comp
      (TensorProduct.map (c.originalSliceAdjunctionFiberEquiv hp q hsm).toLinearMap LinearMap.id)

theorem originalResidueLValue_eq_normalDivision
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d)
    (L : HermitianHolomorphicLineBundle (d + 1) Y) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ T, c.originalResidueLValue hp q hsm L T =
      (c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue hp q L T := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  let F := canonicalTupleEvaluation
    (nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q))
    (fun j => c.originalSliceParameterTangentEquiv hp q hsm (EuclideanSpace.single j 1))
  have hs (A) : F (c.originalSliceAdjunctionFiberEquiv hp q hsm A) =
      (c.tangentNormalDenominator q)⁻¹ * c.originalAmbientCanonicalNormalCoefficient hp q A := by
    induction A using TensorProduct.induction_on with
    | zero => simp
    | tmul α w =>
      change nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceAdjunctionFiberEquiv hp q hsm (α ⊗ₜ[ℂ] w))
        (fun j => c.originalSliceParameterTangentEquiv hp q hsm (EuclideanSpace.single j 1)) = _
      rw [c.originalAdjunctionResidue_parameter_coefficient hp q hsm,
        c.originalAmbientCanonicalNormalCoefficient_tmul hp q]
      ring
    | add A B hA hB => rw [map_add, map_add, map_add, hA, hB]; ring
  intro T
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul A l =>
    change F (c.originalSliceAdjunctionFiberEquiv hp q hsm A) • l =
      (c.tangentNormalDenominator q)⁻¹ • (c.originalAmbientCanonicalNormalCoefficient hp q A • l)
    rw [hs, smul_smul]
  | add A B hA hB => rw [map_add, map_add, smul_add, hA, hB]

/-- Local coefficient density of the ACTUAL original canonical residue,
using ONLY the ORIGINAL physical L metric and ORIGINAL extended weight. -/
def originalWeightedResidueDensity
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d)
    (L : HermitianHolomorphicLineBundle (d + 1) Y)
    (T : TensorProduct ℂ
      (TensorProduct ℂ ((nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
        ((nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)))
      (L.Fiber (c.tangentPoint q))) : ℝ≥0∞ :=
  ENNReal.ofReal (‖c.originalResidueLValue hp q hsm L T‖ ^ 2) *
    multiplierWeight 1 (φ (c.tangentPoint q))

theorem originalWeightedResidueDensity_eq_normalDivision
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d)
    (L : HermitianHolomorphicLineBundle (d + 1) Y)
    (T : TensorProduct ℂ
      (TensorProduct ℂ ((nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
        ((nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)))
      (L.Fiber (c.tangentPoint q))) :
    c.originalWeightedResidueDensity hp q hsm L T =
      ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue hp q L T‖ ^ 2) *
        multiplierWeight 1 (φ (c.tangentPoint q)) := by
  rw [originalWeightedResidueDensity, c.originalResidueLValue_eq_normalDivision hp q hsm L T]

end SliceChart
end SGPT.Trace.Bertini
