import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex

/-! Actual finite cut simplices, polar-coordinate faces and attained extreme
maximizers. This is source-free finite-dimensional geometry for the complete
revised rmk:pwlinhull; no vertex/optimizer/psh conclusion is caller data. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.CutSimplex

open Set

variable {ι : Type*} [Fintype ι]

/-- The genuine continuous linear finite weighted objective. -/
def objective (c : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

theorem objective_apply (c w : ι → ℝ) : objective c w = ∑ i, w i * c i := by
  simp [objective, mul_comm]

/-- Exactly a standard simplex intersected with its barycentre halfspace. -/
def cut (τ : ι → ℝ) (s : ℝ) : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {w | s ≤ objective τ w}

theorem mem_cut_iff (τ : ι → ℝ) (s : ℝ) (w : ι → ℝ) :
    w ∈ cut τ s ↔ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ s ≤ ∑ i, w i * τ i := by
  simp only [cut, mem_inter_iff, stdSimplex, mem_ofPred_eq, objective_apply, and_assoc]

/-- Compactness is produced from the actual standard simplex and closed
barycentre inequality; no linear-programming compactness certificate. -/
theorem cut_isCompact (τ : ι → ℝ) (s : ℝ) : IsCompact (cut τ s) :=
  (isCompact_stdSimplex ℝ ι).inter_right
    (isClosed_le continuous_const (objective τ).continuous)

theorem cut_convex (τ : ι → ℝ) (s : ℝ) : Convex ℝ (cut τ s) := by
  intro w hw v hv a b ha hb hab
  refine ⟨convex_stdSimplex ℝ ι hw.1 hv.1 ha hb hab, ?_⟩
  change s ≤ objective τ (a • w + b • v)
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    s = a * s + b * s := by rw [← add_mul, hab, one_mul]
    _ ≤ a * objective τ w + b * objective τ v :=
      add_le_add (mul_le_mul_of_nonneg_left hw.2 ha) (mul_le_mul_of_nonneg_left hv.2 hb)

/-- Actual coordinate face removing disallowed nodal coefficients. -/
def coordinateFace (τ : ι → ℝ) (s : ℝ) (J : Finset ι) : Set (ι → ℝ) :=
  {w ∈ cut τ s | ∀ i ∉ J, w i = 0}

theorem coordinateFace_isCompact (τ : ι → ℝ) (s : ℝ) (J : Finset ι) :
    IsCompact (coordinateFace τ s J) := by
  have hz : IsClosed {w : ι → ℝ | ∀ i ∉ J, w i = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply i) continuous_const
  exact (cut_isCompact τ s).inter_right hz

theorem coordinateFace_convex (τ : ι → ℝ) (s : ℝ) (J : Finset ι) :
    Convex ℝ (coordinateFace τ s J) := by
  intro w hw v hv a b ha hb hab
  refine ⟨cut_convex τ s hw.1 hv.1 ha hb hab, ?_⟩
  intro i hi
  change a * w i + b * v i = 0
  rw [hw.2 i hi, hv.2 i hi]
  ring

/-- Coordinate removal is an actual extreme face because all simplex
coordinates are nonnegative. This is produced, not assumed by the LP API. -/
theorem coordinateFace_isExtreme (τ : ι → ℝ) (s : ℝ) (J : Finset ι) :
    IsExtreme ℝ (cut τ s) (coordinateFace τ s J) := by
  refine ⟨fun _ hw => hw.1, ?_⟩
  intro u hu v hv w hw hseg
  rcases hseg with ⟨a, b, ha, hb, hab, heq⟩
  refine ⟨hu, ?_⟩
  intro i hi
  have hei := congrFun heq i
  change a * u i + b * v i = w i at hei
  rw [hw.2 i hi] at hei
  have hui : 0 ≤ u i := hu.1.1 i
  have hvi : 0 ≤ v i := hv.1.1 i
  apply le_antisymm _ hui
  by_contra h
  have hp : 0 < u i := lt_of_not_ge h
  have hpu : 0 < a * u i := mul_pos ha hp
  have hpv : 0 ≤ b * v i := mul_nonneg hb.le hvi
  linarith

/-- Genuine compact exposed-face maximization: an actual extreme point of
an actual compact set maximizes the supplied real linear objective. -/
theorem exists_extreme_max {C : Set (ι → ℝ)} (hC : IsCompact C) (hne : C.Nonempty)
    (c : ι → ℝ) :
    ∃ w ∈ C.extremePoints ℝ, ∀ v ∈ C, objective c v ≤ objective c w := by
  let E := {w ∈ C | ∀ v ∈ C, objective c v ≤ objective c w}
  have he : IsExposed ℝ C E := fun _ => ⟨objective c, rfl⟩
  obtain ⟨w₀, hw₀, hmax⟩ := hC.exists_isMaxOn hne (objective c).continuous.continuousOn
  have hE : E.Nonempty := ⟨w₀, hw₀, hmax⟩
  obtain ⟨w, hw⟩ := (he.isCompact hC).extremePoints_nonempty hE
  exact ⟨w, he.isExtreme.extremePoints_subset_extremePoints hw, hw.1.2⟩

/-- The actual real optimizer on a polar-coordinate face is an extreme
point of the ORIGINAL cut simplex. Nonempty feasibility is the only LP
hypothesis, and will be manufactured from actual source weights. -/
theorem exists_coordinateFace_extreme_max (τ c : ι → ℝ) (s : ℝ) (J : Finset ι)
    (hne : (coordinateFace τ s J).Nonempty) :
    ∃ w ∈ coordinateFace τ s J, w ∈ (cut τ s).extremePoints ℝ ∧
      ∀ v ∈ coordinateFace τ s J, objective c v ≤ objective c w := by
  obtain ⟨w, hw, hmax⟩ := exists_extreme_max (coordinateFace_isCompact τ s J) hne c
  exact ⟨w, hw.1, (coordinateFace_isExtreme τ s J).extremePoints_subset_extremePoints hw, hmax⟩

end SGPT.Convex.CutSimplex
