import SGPT.Trace.BertiniIntrinsicAdjunctionContraction

/-! Literal derivative of the original moving member parametrization.

The conormal, inverse flattening, native member and normal denominator are
the original objects. No tangent parametrization/derivative certificate is
supplied. Global holomorphic adjunction and Hodge gluing remain downstream.
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
open scoped ProductComplexManifold
open ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual original ambient coordinates of the member parametrization,
with exactly the original d remaining complex coordinates. -/
def originalTangentCoordinateMap (ζ : ComplexModel N) (b : ComplexModel d) :
    ComplexModel (d + 1) := c.slice ζ (c.tangentLift b)

theorem differentiableAt_originalTangentCoordinateMap
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    DifferentiableAt ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val := by
  have hL : Differentiable ℂ c.tangentLift :=
    (differentiable_const (EuclideanSpace.single c.m (c.z₀ c.m))).add
      (tangentCoordinateInsert c.m).differentiable
  have hκ : Differentiable ℂ (fun b : ComplexModel d =>
      flatProj c.m (prodModelEquiv N (d + 1) (q.1.val, c.tangentLift b))) :=
    (flatProj c.m).differentiable.comp ((prodModelEquiv N (d + 1)).differentiable.comp
      ((differentiable_const q.1.val).prodMk hL))
  have ht := c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  have hi := (c.Φ.invFun_holomorphic _ ht).differentiableAt (c.Φ.isOpen_target.mem_nhds ht)
  exact (differentiable_snd.comp (prodModelEquiv N (d + 1)).symm.differentiable).differentiableAt.comp
    q.2.val (hi.comp q.2.val hκ.differentiableAt)

theorem originalTangentCoordinateMap_succAbove
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (j : Fin d) :
    c.originalTangentCoordinateMap q.1.val q.2.val (c.m.succAbove j) = q.2.val j := by
  let t := flatProj c.m (prodModelEquiv N (d + 1) (q.1.val, c.tangentLift q.2.val))
  have ht : t ∈ c.Φ.target := c.mapsTo_target q.1.val q.1.property
    (c.tangentLift q.2.val) q.2.property
  have heq := congrArg (fun w : ComplexModel (N + (d + 1)) =>
    ((prodModelEquiv N (d + 1)).symm w).2 (c.m.succAbove j)) (c.Φ.right_inv t ht)
  rw [c.toFun_eq] at heq
  simpa [flatMap, t, flatProj_apply, slDir, slCoord_apply, originalTangentCoordinateMap,
    slice, tangentLift, tangentCoordinateInsert, Fin.succAbove_ne] using heq

theorem originalTangentCoordinateMap_fderiv_succAbove
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (v : ComplexModel d) (j : Fin d) :
    fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v (c.m.succAbove j) = v j := by
  have hH := c.differentiableAt_originalTangentCoordinateMap q
  have heq : (fun b : ComplexModel d => c.originalTangentCoordinateMap q.1.val b (c.m.succAbove j))
      =ᶠ[𝓝 q.2.val] (fun b => b j) := by
    filter_upwards [c.isOpen_tangentPatch.mem_nhds q.2.property] with b hb
    exact c.originalTangentCoordinateMap_succAbove (q.1, ⟨b, hb⟩) j
  have hd := ((EuclideanSpace.proj (c.m.succAbove j) : ComplexModel (d + 1) →L[ℂ] ℂ).hasFDerivAt.comp
    q.2.val hH.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hD := hd.unique (EuclideanSpace.proj j : ComplexModel d →L[ℂ] ℂ).hasFDerivAt
  exact DFunLike.congr_fun hD v

theorem originalTangentCoordinateMap_fderiv_conormal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (v : ComplexModel d) :
    c.originalMemberConormal q (fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v) = 0 := by
  have hpoint := c.tangentPoint_chart_coordinates q
  have hH := c.differentiableAt_originalTangentCoordinateMap q
  have hg := (hasFDerivAt_pairing_chartLift p hp hpoint.2.2
    (affineLift c.i q.1.val)).differentiableAt
  rw [hpoint.2.1] at hg
  have hG : DifferentiableAt ℂ (c.originalFixedMemberEquation q)
      (c.originalTangentCoordinateMap q.1.val q.2.val) := hg
  have heq : (c.originalFixedMemberEquation q ∘ c.originalTangentCoordinateMap q.1.val)
      =ᶠ[𝓝 q.2.val] (fun _ => (0 : ℂ)) := by
    filter_upwards [c.isOpen_tangentPatch.mem_nhds q.2.property] with b hb
    have hbpoint := c.tangentPoint_chart_coordinates (q.1, ⟨b, hb⟩)
    have hpx := (mem_chartLiftDomain_iff p hbpoint.1).mp hbpoint.2.2
    have hz := c.originalFixedMemberEquation_zero q hbpoint.1 hpx
      (c.tangentPoint_mem_member (q.1, ⟨b, hb⟩))
    rwa [hbpoint.2.1] at hz
  have hD := (hG.hasFDerivAt.comp q.2.val hH.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hzero := hD.unique (hasFDerivAt_const (0 : ℂ) q.2.val)
  have hdf := c.originalFixedMemberEquation_fderiv hp q
  rw [hpoint.2.1] at hdf
  change fderiv ℂ (c.originalFixedMemberEquation q)
    (c.originalTangentCoordinateMap q.1.val q.2.val) = c.originalMemberConormal q at hdf
  rw [hdf] at hzero
  exact DFunLike.congr_fun hzero v

theorem originalTangentCoordinateMap_fderiv_eq
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (v : ComplexModel d) :
    fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v =
      tangentCoordinateInsert c.m v -
        ((c.tangentNormalDenominator q)⁻¹ * c.originalMemberConormal q (tangentCoordinateInsert c.m v)) •
          EuclideanSpace.single c.m 1 := by
  let D := fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val
  have hsplit : D v = tangentCoordinateInsert c.m v + (D v c.m) • EuclideanSpace.single c.m 1 := by
    ext i
    rcases Fin.eq_self_or_eq_succAbove c.m i with rfl | ⟨j, rfl⟩
    · simp [tangentCoordinateInsert]
    · simpa [tangentCoordinateInsert, Fin.succAbove_ne] using
        c.originalTangentCoordinateMap_fderiv_succAbove q v j
  have hzero := c.originalTangentCoordinateMap_fderiv_conormal hp q v
  change c.originalMemberConormal q (D v) = 0 at hzero
  rw [hsplit, map_add, map_smul, c.originalMemberConormal_normal hp q, smul_eq_mul] at hzero
  have hscalar : D v c.m = -((c.tangentNormalDenominator q)⁻¹ *
      c.originalMemberConormal q (tangentCoordinateInsert c.m v)) := by
    apply (mul_left_cancel₀ (c.tangentNormalDenominator_ne_zero hp q))
    field_simp [c.tangentNormalDenominator_ne_zero hp q]
    linear_combination hzero
  rw [hsplit, hscalar, neg_smul, sub_eq_add_neg]

end SGPT.Trace.Bertini.SliceChart
