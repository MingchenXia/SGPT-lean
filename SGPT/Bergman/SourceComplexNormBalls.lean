import SGPT.Bergman.SourcePartialBergmanTrace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# ComplexNormBalls

Complex norms on a finite-dimensional complex vector space: compact unit balls of positive finite Haar volume and their scaling (used for source `def:Bergman:L942`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.QuantizationFrontier
open Set Metric MeasureTheory
open scoped Topology Pointwise

/-- The literal mathematical data of a complex norm: group norm and exact complex homogeneity.
No topology, compactness, volume or basis conclusion is a field. -/
structure ComplexNorm (E : Type*) [AddCommGroup E] [Module ℂ E] where
  toAddGroupNorm : AddGroupNorm E
  norm_smul : ∀ (c : ℂ) (x : E), toAddGroupNorm (c • x) = ‖c‖ * toAddGroupNorm x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A genuine vector wrapper carries the chosen norm without an inherited competing metric. -/
structure WithComplexNorm (_N : ComplexNorm E) where
  val : E

/-- BOTH true maps retain the whole original vector; no family or coordinate certificate. -/
def complexNormOriginalEquivRaw (N : ComplexNorm E) : WithComplexNorm N ≃ E where
  toFun := WithComplexNorm.val
  invFun := WithComplexNorm.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (N : ComplexNorm E) : AddCommGroup (WithComplexNorm N) :=
  (complexNormOriginalEquivRaw N).addCommGroup
instance (N : ComplexNorm E) : Module ℂ (WithComplexNorm N) :=
  Equiv.module ℂ (complexNormOriginalEquivRaw N)

/-- The actual chosen norm is pulled along the true whole-vector map, with definiteness proved. -/
def wrappedComplexNorm (N : ComplexNorm E) : AddGroupNorm (WithComplexNorm N) where
  toFun x := N.toAddGroupNorm x.val
  map_zero' := N.toAddGroupNorm.map_zero'
  add_le' x y := N.toAddGroupNorm.add_le' x.val y.val
  neg' x := N.toAddGroupNorm.neg' x.val
  eq_zero_of_map_eq_zero' x hx := by
    apply (complexNormOriginalEquivRaw N).injective
    exact N.toAddGroupNorm.eq_zero_of_map_eq_zero' x.val hx

instance (N : ComplexNorm E) : NormedAddCommGroup (WithComplexNorm N) :=
  (wrappedComplexNorm N).toNormedAddCommGroup

/-- Homogeneity PROVES the chosen vector wrapper's complex normed-space structure. -/
instance chosenComplexNormSpace (N : ComplexNorm E) : NormedSpace ℂ (WithComplexNorm N) where
  toModule := Equiv.module ℂ (complexNormOriginalEquivRaw N)
  norm_smul_le c x := (N.norm_smul c x.val).le

/-- Actual identity-on-vector linear maps in BOTH directions, with no basis selection. -/
def complexNormOriginalEquiv (N : ComplexNorm E) : WithComplexNorm N ≃ₗ[ℂ] E :=
  Equiv.linearEquiv ℂ (complexNormOriginalEquivRaw N)

variable [FiniteDimensional ℂ E]

instance (N : ComplexNorm E) : FiniteDimensional ℂ (WithComplexNorm N) :=
  FiniteDimensional.of_injective (complexNormOriginalEquiv N).toLinearMap
    (complexNormOriginalEquiv N).injective

/-- Native finite-dimensional continuity proves actual norm-topology equivalence in BOTH directions. -/
def complexNormOriginalContinuousEquiv (N : ComplexNorm E) : WithComplexNorm N ≃L[ℂ] E :=
  (complexNormOriginalEquiv N).toContinuousLinearEquiv

/-- The actual source norm sublevel, on ALL original vectors. -/
def normUnitBall (N : ComplexNorm E) : Set E := {x | N.toAddGroupNorm x ≤ 1}

/-- The image formula uses every actual vector and exact chosen norm, without an incoming ball dictionary. -/
theorem normUnitBall_eq_image (N : ComplexNorm E) :
    normUnitBall N = complexNormOriginalContinuousEquiv N '' closedBall (0 : WithComplexNorm N) 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x⟩, ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    exact (mem_closedBall_zero_iff.mp hy)

/-- Compactness is produced from true norm equivalence and finite dimension, including dimension zero. -/
theorem normUnitBall_isCompact (N : ComplexNorm E) : IsCompact (normUnitBall N) := by
  have : ProperSpace (WithComplexNorm N) := FiniteDimensional.proper ℂ (WithComplexNorm N)
  rw [normUnitBall_eq_image]
  exact (isCompact_closedBall (0 : WithComplexNorm N) 1).image
    (complexNormOriginalContinuousEquiv N).continuous

/-- A true open ball transports to an actual neighborhood of zero inside the chosen norm unit ball. -/
theorem normUnitBall_mem_nhds_zero (N : ComplexNorm E) : normUnitBall N ∈ 𝓝 0 := by
  have h := (complexNormOriginalContinuousEquiv N).toHomeomorph.isOpenMap _
    (isOpen_ball : IsOpen (ball (0 : WithComplexNorm N) 1))
  apply Filter.mem_of_superset (h.mem_nhds ?_) ?_
  · exact ⟨0, by simp, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_ball_zero_iff.mp hy).le

variable [MeasurableSpace E] [BorelSpace E] (vol : Measure E) [vol.IsAddHaarMeasure]

omit [BorelSpace E] in
/-- Every chosen genuine Haar normalization gives FINITE true norm-ball volume. -/
theorem normUnitBall_measure_ne_top (N : ComplexNorm E) : vol (normUnitBall N) ≠ ⊤ :=
  (normUnitBall_isCompact N).measure_ne_top

omit [BorelSpace E] in
/-- Actual nonempty interior proves POSITIVE volume, retaining dimension-zero spaces. -/
theorem normUnitBall_measure_pos (N : ComplexNorm E) : 0 < vol (normUnitBall N) :=
  vol.measure_pos_of_mem_nhds (normUnitBall_mem_nhds_zero N)

omit [BorelSpace E] in
/-- The exact real norm-ball volume is finite and strictly positive; no infinity-to-real fallback. -/
theorem normUnitBall_real_pos (N : ComplexNorm E) : 0 < vol.real (normUnitBall N) :=
  ENNReal.toReal_pos (normUnitBall_measure_pos vol N).ne' (normUnitBall_measure_ne_top vol N)

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- The native scalar-tower formula retains the exact complex factor, also at dimension zero. -/
theorem normSpace_real_dimension : Module.finrank ℝ E = 2 * Module.finrank ℂ E :=
  finrank_real_of_complex E

/-- Actual Haar dilation on ALL original vectors, with precisely twice complex dimension. -/
theorem normUnitBall_measure_smul (N : ComplexNorm E) {a : ℝ} (ha : 0 ≤ a) :
    vol (a • normUnitBall N) = ENNReal.ofReal (a ^ (2 * Module.finrank ℂ E)) * vol (normUnitBall N) := by
  rw [Measure.addHaar_smul_of_nonneg vol ha, finrank_real_of_complex E]

end SGPT.Bergman.QuantizationFrontier
