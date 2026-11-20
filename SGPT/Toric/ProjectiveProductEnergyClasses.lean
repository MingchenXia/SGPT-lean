import SGPT.Toric.ProjectiveProductUnnormalizedEnergy
import SGPT.Toric.TropicalFullMassCriterion

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ En

/-- The actual original native NP and real Alexandrov totals share the same
whole multivalued Newton closure and literal factorial. -/
theorem projectiveProductMixedMeasure_univ_eq_alexandrov {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    DiagonalMass.diagonalPotentialMass (projectiveProductFSBackground n).form u hu =
      alexandrovMeasure B volume (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) univ := by
  have hg := projectiveProductToricProfile_mem_growthClass hu hi
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass B (isCompact_euclideanUnitCube n)
      (nonempty_euclideanUnitCube n) hg)
  change GlobalNonPluripolar.globalMixedMeasure
    (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => u) (fun _ => hu.1) univ = _
  rw [projectiveProductMixedMeasure_univ_eq_NewtonBody hu hi,
    alexandrovMeasure_univ_eq_closure_rawSubgradientImage B hg.1 hlsc,
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg.1 hlsc]
  simp [convexNewtonBody]

/-- Actual compact native source bounds and the produced same-source NP total
give original native full mass exactly as the original convex full-mass class. -/
theorem projectiveProduct_mem_relativeFullMassPreceq_iff_fullMassClass {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeFullMassPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈ FullMassClass B (euclideanUnitCube n) := by
  let : Nonempty X := ⟨(projectiveProductCoordinates n).symm (fun _ => projectiveOrigin)⟩
  have hupper : MoreSingularOn u (fun _ : X => (0 : EReal)) univ := by
    obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, by simpa using hC⟩
  have hm := projectiveProductMixedMeasure_univ_eq_alexandrov hu hi
  have hzero : DiagonalMass.diagonalPotentialMass (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) (isModelPotential_projectiveProductZero n).plurisubharmonic =
      (n.factorial : ENNReal) * volume (euclideanUnitCube n) := by
    change GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form)
      (fun _ => fun _ : X => (0 : EReal)) _ univ = _
    rw [projectiveProductZeroMixedMeasure_univ, volume_euclideanUnitCube, mul_one]
  have hc : (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈
      FullMassClass B (euclideanUnitCube n) ↔
      alexandrovMeasure B volume (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) univ =
        (n.factorial : ENNReal) * volume (euclideanUnitCube n) := by
    simpa using mem_fullMassClass_iff_alexandrovMeasure_univ_eq_euclidean B
      (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n) (convex_euclideanUnitCube n)
      (projectiveProductToricProfile_mem_growthClass hu hi)
  constructor
  · rintro ⟨_hw, _horder, hmass⟩
    apply hc.mpr
    change DiagonalMass.diagonalPotentialMass (projectiveProductFSBackground n).form u hu =
      DiagonalMass.diagonalPotentialMass (projectiveProductFSBackground n).form
        (fun _ : X => (0 : EReal)) (isModelPotential_projectiveProductZero n).plurisubharmonic at hmass
    rwa [hm, hzero] at hmass
  · intro hfull
    refine ⟨hu, hupper, ?_⟩
    rw [hm, hzero]
    exact hc.mp hfull

/-- The actual original closed Newton body of the manufactured source profile. -/
def projectiveProductToricNewtonBody (u : X → EReal) : Set En :=
  convexNewtonBody (projectiveProductToricLegendre u)

private theorem native_newton_eq_subgradient_closure {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    projectiveProductToricNewtonBody u =
      closure (rawSubgradientImage B (fun x => (projectiveProductToricEuclideanProfile u x : EReal))) := by
  have hg := projectiveProductToricProfile_mem_growthClass hu hi
  exact (closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg.1
    (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_mem_growthClass B
      (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n) hg))).symm

private theorem cube_interior_nonempty (n : ℕ) : (interior (euclideanUnitCube n)).Nonempty := by
  let m : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  let U : Set (EuclideanSpace ℝ (Fin n)) := ⋂ i : Fin n, {x | 0 < x i ∧ x i < 1}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    have heval : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by fun_prop
    exact (isOpen_lt continuous_const heval).inter (isOpen_lt heval continuous_const)
  have hm : m ∈ U := by norm_num [U, m]
  have hsub : U ⊆ euclideanUnitCube n := by
    intro y hy i
    have hi := mem_iInter.mp hy i
    exact ⟨hi.1.le, hi.2.le⟩
  exact ⟨m, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hm) hsub)⟩

/-- The original convex full-mass class is exactly the literal whole Newton cube;
the actual cube has nonempty interior even in zero dimension. -/
theorem projectiveProduct_mem_fullMassClass_iff_newtonBody_eq_cube {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈ FullMassClass B (euclideanUnitCube n) ↔
      projectiveProductToricNewtonBody u = euclideanUnitCube n := by
  constructor
  · rintro ⟨_hg, h | h⟩
    · exact ((cube_interior_nonempty n).ne_empty h).elim
    · rwa [← native_newton_eq_subgradient_closure hu hi] at h
  · intro h
    refine ⟨projectiveProductToricProfile_mem_growthClass hu hi, Or.inr ?_⟩
    rwa [← native_newton_eq_subgradient_closure hu hi]

/-- Actual original unnormalized native full mass is exactly the genuine Newton cube. -/
theorem projectiveProduct_mem_relativeFullMassPreceq_iff_newtonBody_eq_cube {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeFullMassPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      projectiveProductToricNewtonBody u = euclideanUnitCube n :=
  (projectiveProduct_mem_relativeFullMassPreceq_iff_fullMassClass hu hi).trans
    (projectiveProduct_mem_fullMassClass_iff_newtonBody_eq_cube hu hi)

/-- Actual native normalized E1 manufactures the convex full-mass clause before
the original convex energy-one class is assembled. -/
theorem projectiveProduct_mem_relativeFiniteEnergy_iff_energyOneClass {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈
        EnergyOneClass B (euclideanUnitCube n) volume := by
  rw [mem_energyOneClass_iff volume B (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n)]
  constructor
  · intro h
    exact ⟨(projectiveProduct_mem_relativeFullMassPreceq_iff_fullMassClass hu hi).mp
      (preceq_of_relativeFiniteEnergy h).1,
      (projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle).mp h⟩
  · intro h
    exact (projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle).mpr h.2

/-- Actual unnormalized native E1 equals the original convex energy-one class,
without assuming the target full-mass clause. -/
theorem projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_energyOneClass {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈
        EnergyOneClass B (euclideanUnitCube n) volume := by
  rw [mem_energyOneClass_iff volume B (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n)]
  constructor
  · intro h
    exact ⟨(projectiveProduct_mem_relativeFullMassPreceq_iff_fullMassClass hu hi).mp h.1,
      (projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi).mp h⟩
  · intro h
    exact (projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi).mpr h.2

end SGPT.Toric
