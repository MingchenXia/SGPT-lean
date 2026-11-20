import SGPT.Convex.RankOneLegendreEnergy
import SGPT.Convex.MixedAlexandrovPolynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter MeasureTheory SGPT.PSH
open scoped Topology NNReal ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "B" => innerₗ E

/-- The two original endpoint profiles in a genuine binary slot family. -/
def binaryConvexFamily (f g : RealConvexFunction E) (i : Fin 2) : RealConvexFunction E :=
  if i = 0 then f else g

/-- Midpoint domination gives finite mass for every actual binary mixed endpoint
measure, including dimension zero and lower-dimensional moment bodies. -/
theorem isFiniteMeasure_mixedEndpoint (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    (a : Fin n → Fin 2) :
    IsFiniteMeasure (mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (a i))) := by
  classical
  let c : Fin 2 → ℝ≥0 := fun _ => Real.toNNReal (1 / 2)
  let h := finiteConvexWeightedSum (binaryConvexFamily f g) c
  have hval : h.val = affineProfile f g (1 / 2) := by
    funext x
    norm_num [h, finiteConvexWeightedSum, Fin.sum_univ_two, binaryConvexFamily,
      c, affineProfile]
  have hh : (fun x => (h.val x : EReal)) ∈ BoundedGrowthClass B P := by
    rw [hval]
    exact boundedGrowthClass_affineProfile hf hg (by norm_num)
  have hfull := mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hh
  have hmass : alexandrovMeasure B μ (fun x => (h.val x : EReal)) univ < ⊤ := by
    rw [alexandrovMeasure_univ_eq_body_of_mem_fullMassClass B hP hne hconv hfull]
    exact ENNReal.mul_lt_top (by simp) hP.measure_lt_top
  have hdiag := alexandrovMeasure_finiteConvexWeightedSum μ b (binaryConvexFamily f g) c
  have hsum : (∑ k : Fin n → Fin 2, (∏ i, c (k i)) •
      mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (k i))) univ < ⊤ := by
    rw [← hdiag]
    exact hmass
  rw [Measure.finsetSum_apply] at hsum
  have hle : ((∏ i : Fin n, c (a i)) •
      mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (a i))) univ ≤
      ∑ k : Fin n → Fin 2, ((∏ i, c (k i)) •
        mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (k i))) univ :=
    Finset.single_le_sum (f := fun k : Fin n → Fin 2 =>
      ((∏ i, c (k i)) • mixedAlexandrovMeasure μ b
        (fun i => binaryConvexFamily f g (k i))) univ)
      (fun k _ => bot_le) (Finset.mem_univ a)
  have hterm := lt_of_le_of_lt hle hsum
  rw [Measure.coe_nnreal_smul_apply] at hterm
  have hcoef : (((∏ i : Fin n, c (a i)) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simp [c]
  refine ⟨?_⟩
  rcases ENNReal.mul_lt_top_iff.mp hterm with h | h | h
  · exact h.2
  · exact False.elim (hcoef h)
  · rw [h]; exact ENNReal.zero_lt_top

/-- The original bounded growth pair manufactures signed gap integrability on
all actual mixed endpoint measures. -/
theorem integrable_gap_mixedEndpoint (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    (a : Fin n → Fin 2) :
    Integrable (fun x => g.val x - f.val x)
      (mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (a i))) := by
  have hfinite := isFiniteMeasure_mixedEndpoint μ b hP hne hconv hf hg a
  obtain ⟨C, hC⟩ := boundedGrowthPair_exists_abs_sub_le hf hg
  have hh : Measurable (fun x => g.val x - f.val x) :=
    (continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).measurable.sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ)).measurable
  exact Integrable.of_bound hh.aestronglyMeasurable C
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))

/-- Literal actual finite mixed endpoint integrals supply the affine tangent
polynomial, with no polynomial or derivative certificate. -/
def affineTangentPolynomial (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E) (t : ℝ) : ℝ :=
  ∑ a : Fin n → Fin 2, (∏ i, if a i = 0 then 1 - t else t) *
    ∫ x, (g.val x - f.val x)
      ∂mixedAlexandrovMeasure μ b (fun i => binaryConvexFamily f g (a i))

/-- The manufactured finite tangent polynomial is continuous on all real time. -/
theorem continuous_affineTangentPolynomial (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E) :
    Continuous (affineTangentPolynomial μ b f g) := by
  classical
  unfold affineTangentPolynomial
  apply continuous_finsetSum
  intro a _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro i _
  split_ifs <;> fun_prop

/-- The actual pure Alexandrov tangent integral is the literal mixed endpoint
polynomial along the original finite affine profile. -/
theorem integral_gap_affineProfile_eq_tangentPolynomial (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, (g.val x - f.val x)
      ∂alexandrovMeasure B μ (fun x => (affineProfile f g t x : EReal))) =
      affineTangentPolynomial μ b f g t := by
  classical
  let c : Fin 2 → ℝ≥0 := fun i => Real.toNNReal (if i = 0 then 1 - t else t)
  have hc (i : Fin 2) : 0 ≤ if i = 0 then 1 - t else t := by
    split_ifs
    · exact sub_nonneg.mpr ht.2
    · exact ht.1
  have hval : (finiteConvexWeightedSum (binaryConvexFamily f g) c).val = affineProfile f g t := by
    funext x
    simp only [finiteConvexWeightedSum, Fin.sum_univ_two, c, Real.coe_toNNReal _ (hc _)]
    simp [binaryConvexFamily, affineProfile]
  rw [← hval, alexandrovMeasure_finiteConvexWeightedSum μ b]
  rw [integral_finsetSum_measure (fun a _ =>
    (integrable_gap_mixedEndpoint μ b hP hne hconv hf hg a).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, NNReal.coe_prod]
  unfold affineTangentPolynomial
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact Real.coe_toNNReal _ (hc _)
end SGPT.Convex
