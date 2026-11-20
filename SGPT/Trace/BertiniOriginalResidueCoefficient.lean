import SGPT.Trace.BertiniOriginalSliceDifferential

/-! Actual original canonical residue coefficient along the actual original
d-variable inverse-flattening parametrization. The source Hodge metric and
global holomorphic adjunction gluing remain separate assertions. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

private theorem normalColumnCancellation {d : ℕ}
    (α : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1)) (u : Fin d → ComplexModel (d + 1)) (a : Fin d → ℂ) :
    α (Matrix.vecCons ν (fun i => u i + a i • ν)) = α (Matrix.vecCons ν u) := by
  classical
  let w (s : Finset (Fin d)) : Fin d → ComplexModel (d + 1) :=
    fun i => u i + (if i ∈ s then a i else 0) • ν
  have hs (s : Finset (Fin d)) : α (Matrix.vecCons ν (w s)) = α (Matrix.vecCons ν u) := by
    induction s using Finset.induction_on with
    | empty => simp [w]
    | @insert i s hi ih =>
      have hw : w (insert i s) = Function.update (w s) i (w s i + a i • ν) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [w, hi]
        · simp [w, hj]
      rw [hw]
      change (α.curryLeft ν) (Function.update (w s) i (w s i + a i • ν)) = _
      rw [AlternatingMap.map_update_add, Function.update_eq_self, AlternatingMap.map_update_smul]
      have hz : (α.curryLeft ν) (Function.update (w s) i ν) = 0 := by
        apply α.map_eq_zero_of_eq (Matrix.vecCons ν (Function.update (w s) i ν))
          (i := 0) (j := i.succ)
        · simp
        · intro h
          have hval := congrArg Fin.val h
          change (0 : ℕ) = i.val + 1 at hval
          omega
      rw [hz, smul_zero, add_zero]
      exact ih
  simpa [w] using hs Finset.univ

private def removeNormalCoordinate {d : ℕ} (m : Fin (d + 1)) :
    ComplexModel (d + 1) →ₗ[ℂ] ComplexModel d where
  toFun v := WithLp.toLp 2 (fun j => v (m.succAbove j))
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

namespace SliceChart

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The derivative of the ACTUAL original d-variable parametrization
is an isomorphism onto the ACTUAL original coordinate conormal kernel.
Its inverse is the literal deletion of the original normal coordinate. -/
def originalTangentKernelEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    ComplexModel d ≃ₗ[ℂ] LinearMap.ker (c.originalMemberConormal q).toLinearMap where
  toFun v := ⟨fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v,
    c.originalTangentCoordinateMap_fderiv_conormal hp q v⟩
  invFun w := removeNormalCoordinate c.m w.val
  left_inv v := by
    ext j
    exact c.originalTangentCoordinateMap_fderiv_succAbove q v j
  right_inv w := by
    apply Subtype.ext
    let v := removeNormalCoordinate c.m w.val
    have hsplit : w.val = tangentCoordinateInsert c.m v + w.val c.m • EuclideanSpace.single c.m 1 := by
      ext i
      rcases Fin.eq_self_or_eq_succAbove c.m i with rfl | ⟨j, rfl⟩ <;>
        simp [tangentCoordinateInsert, v, removeNormalCoordinate, Fin.succAbove_ne]
    have hzero : c.originalMemberConormal q w.val = 0 := w.property
    rw [hsplit, map_add, map_smul, c.originalMemberConormal_normal hp q, smul_eq_mul] at hzero
    have hscalar : w.val c.m = -((c.tangentNormalDenominator q)⁻¹ *
        c.originalMemberConormal q (tangentCoordinateInsert c.m v)) := by
      apply (mul_left_cancel₀ (c.tangentNormalDenominator_ne_zero hp q))
      field_simp [c.tangentNormalDenominator_ne_zero hp q]
      linear_combination hzero
    change fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v = w.val
    rw [c.originalTangentCoordinateMap_fderiv_eq hp q, hsplit, hscalar, neg_smul, sub_eq_add_neg]
  map_add' u v := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul _ _ _

/-- Actual parameter tangent space to actual ORIGINAL native member tangent.
No incoming tangent/frame/parametrization isomorphism is supplied. -/
def originalSliceParameterTangentEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ComplexModel d ≃ₗ[ℂ] TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  exact (c.originalTangentKernelEquiv hp q).trans (c.originalSliceNativeTangentEquiv hp q hsm).symm

theorem originalSliceParameterTangentEquiv_coordinates
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ v : ComplexModel d,
      (c.originalSliceNativeTangentEquiv hp q hsm (c.originalSliceParameterTangentEquiv hp q hsm v)).val =
      fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  intro v
  change ((c.originalSliceNativeTangentEquiv hp q hsm)
    ((c.originalSliceNativeTangentEquiv hp q hsm).symm (c.originalTangentKernelEquiv hp q v))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem originalResidue_coordinate_coefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (α : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) :
    α (Matrix.vecCons (c.originalNormalizedNormal q)
      (fun j => fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val (EuclideanSpace.single j 1))) =
    (c.tangentNormalDenominator q)⁻¹ *
      α (Matrix.vecCons (EuclideanSpace.single c.m 1)
        (fun j => EuclideanSpace.single (c.m.succAbove j) 1)) := by
  let u : Fin d → ComplexModel (d + 1) := fun j => EuclideanSpace.single (c.m.succAbove j) 1
  let a : Fin d → ℂ := fun j => -((c.tangentNormalDenominator q)⁻¹ * c.originalMemberConormal q (u j))
  have hI (j : Fin d) : tangentCoordinateInsert c.m (EuclideanSpace.single j 1) = u j := by
    ext i
    rcases Fin.eq_self_or_eq_succAbove c.m i with rfl | ⟨k, rfl⟩ <;>
      simp [tangentCoordinateInsert, u]
  have hD : (fun j => fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val
      (EuclideanSpace.single j 1)) = fun j => u j + a j • EuclideanSpace.single c.m 1 := by
    funext j
    rw [c.originalTangentCoordinateMap_fderiv_eq hp q, hI]
    simp only [a, neg_smul, sub_eq_add_neg]
  rw [hD, originalNormalizedNormal, AlternatingMap.map_vecCons_smul,
    normalColumnCancellation]
  rfl

variable [CompactSpace Y]

theorem originalCanonicalResidue_parameter_coefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceCanonicalFiberResidueEquiv hp q hsm α)
        (fun j => c.originalSliceParameterTangentEquiv hp q hsm (EuclideanSpace.single j 1)) =
      (c.tangentNormalDenominator q)⁻¹ *
        nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α
          (Matrix.vecCons (EuclideanSpace.single c.m 1)
            (fun j => EuclideanSpace.single (c.m.succAbove j) 1)) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α
  rw [c.originalSliceCanonicalFiberResidueEquiv_apply hp q hsm]
  simp_rw [c.originalSliceParameterTangentEquiv_coordinates hp q hsm]
  exact c.originalResidue_coordinate_coefficient hp q _

theorem originalAdjunctionResidue_parameter_coefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (w : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceAdjunctionFiberEquiv hp q hsm (α ⊗ₜ[ℂ] w))
        (fun j => c.originalSliceParameterTangentEquiv hp q hsm (EuclideanSpace.single j 1)) =
      nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
        ((mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q).1).mp
          (c.tangentPoint_chart_coordinates q).2.2) w *
        ((c.tangentNormalDenominator q)⁻¹ *
          nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α
            (Matrix.vecCons (EuclideanSpace.single c.m 1)
              (fun j => EuclideanSpace.single (c.m.succAbove j) 1))) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α w
  rw [c.originalSliceAdjunctionFiberEquiv_tmul, map_smul, AlternatingMap.smul_apply,
    c.originalCanonicalResidue_parameter_coefficient hp q hsm]
  rfl

end SliceChart
end SGPT.Trace.Bertini
