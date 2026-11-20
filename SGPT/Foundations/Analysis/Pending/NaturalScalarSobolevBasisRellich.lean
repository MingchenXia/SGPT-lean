import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisBump
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-! # Genuine scalar value Rellich compactness for the original closed first-jet space

Five complete mathematical statements and ENTIRE proofs precede this source.
No weak-Sobolev identification or value-projection injectivity is assumed.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisRellich

open NaturalScalarSobolevJet NaturalScalarSobolevL2Smoothing
  NaturalScalarSobolevBasisGradient NaturalScalarSobolevBasisBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (K : Compacts E)
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)

/-- Actual arbitrarily small bump error and native smoothing nets yield original value total boundedness. -/
theorem native_value_totallyBounded (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K b f‖ ≤ R) :
    TotallyBounded (scalarStageL2 μ K '' A) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  let r : ℝ := ε / (8 * ((Real.sqrt (basisGradientConstant b) + 1) * (R + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  let ρ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hrr : r * Real.sqrt (basisGradientConstant b) * R < ε / 8 := by
    have heq : r * ((Real.sqrt (basisGradientConstant b) + 1) * (R + 1)) = ε / 8 := by
      dsimp [r]
      field_simp
    have hcomp : Real.sqrt (basisGradientConstant b) * R <
        (Real.sqrt (basisGradientConstant b) + 1) * (R + 1) := by
      nlinarith [Real.sqrt_nonneg (basisGradientConstant b)]
    have hprod := mul_lt_mul_of_pos_left hcomp hr
    nlinarith
  obtain ⟨F, hFA, hFfin, hF⟩ := finite_firstJet_smoothing_l2_approx μ K ρ b A R hR hA
    (ε / 2) (half_pos hε)
  have herr (f : 𝓓_{K}(E, ℝ)) (hf : f ∈ A) :
      dist (scalarStageL2 μ K f) (smoothingL2 μ K ρ f) ≤ r * Real.sqrt (basisGradientConstant b) * R := by
    rw [dist_comm, dist_eq_norm]
    exact (NaturalScalarSobolevBasisBump.norm_smoothingL2_error_le_firstJet μ ρ K b f).trans
      (mul_le_mul_of_nonneg_left (hA f hf)
        (mul_nonneg hr.le (Real.sqrt_nonneg _)))
  refine ⟨scalarStageL2 μ K '' F, hFfin.image _, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨g, hg, hfg⟩ := hF f hf
  refine mem_iUnion₂.mpr ⟨scalarStageL2 μ K g, ⟨g, hg, rfl⟩, ?_⟩
  change dist (scalarStageL2 μ K f) (scalarStageL2 μ K g) < ε
  have hsm : dist (smoothingL2 μ K ρ f) (smoothingL2 μ K ρ g) < ε / 2 := by
    simpa only [dist_eq_norm] using hfg
  calc
    _ ≤ dist (scalarStageL2 μ K f) (smoothingL2 μ K ρ f) +
        dist (smoothingL2 μ K ρ f) (scalarStageL2 μ K g) := dist_triangle _ _ _
    _ ≤ dist (scalarStageL2 μ K f) (smoothingL2 μ K ρ f) +
        (dist (smoothingL2 μ K ρ f) (smoothingL2 μ K ρ g) +
          dist (smoothingL2 μ K ρ g) (scalarStageL2 μ K g)) :=
      add_le_add (le_refl _) (dist_triangle _ _ _)
    _ < ε := by
      have hferr := herr f hf
      have hgerr := herr g (hFA hg)
      rw [dist_comm (scalarStageL2 μ K g)] at hgerr
      linarith

/-- The original real L² value closure is genuinely compact in its existing complete metric. -/
theorem isCompact_native_value_closure (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K b f‖ ≤ R) :
    IsCompact (closure (scalarStageL2 μ K '' A)) :=
  (native_value_totallyBounded μ K b A R hR hA).closure.isCompact_of_isClosed isClosed_closure

/-- Native approximation is internally produced from the literal actual first-jet range closure. -/
theorem exists_native_jet_approx (a : SobolevFirstJet μ K b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : 𝓓_{K}(E, ℝ), ‖a.val - firstJetLinear μ K b f‖ < δ ∧
      ‖firstJetLinear μ K b f‖ ≤ ‖a‖ + δ := by
  have ha : a.val ∈ closure ((firstJetLinear μ K b).range : Set (JetL2 μ ι)) := a.property
  obtain ⟨j, hj, haj⟩ := Metric.mem_closure_iff.mp ha δ hδ
  rcases hj with ⟨f, rfl⟩
  have hdist : ‖a.val - firstJetLinear μ K b f‖ < δ := by
    simpa only [dist_eq_norm] using haj
  refine ⟨f, hdist, ?_⟩
  have ht := norm_sub_norm_le (firstJetLinear μ K b f) a.val
  rw [norm_sub_rev] at ht
  change ‖firstJetLinear μ K b f‖ ≤ ‖a.val‖ + δ
  linarith

/-- Every completed value belongs to the closure of a genuinely native jet-bounded value family. -/
theorem value_image_closedBall_totallyBounded (R : ℝ) (hR : 0 ≤ R) :
    TotallyBounded (jetCoordinateCLM μ K b (Sum.inl ()) ''
      closedBall (0 : SobolevFirstJet μ K b) R) := by
  let A : Set 𝓓_{K}(E, ℝ) := {f | ‖firstJetLinear μ K b f‖ ≤ R + 1}
  have hA : TotallyBounded (scalarStageL2 μ K '' A) :=
    native_value_totallyBounded μ K b A (R + 1) (by linarith) (fun _ hf => hf)
  apply hA.closure.subset
  rintro _ ⟨a, ha, rfl⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min ε 1 / 2
  have hδ : 0 < δ := half_pos (lt_min hε (by norm_num))
  have hδ1 : δ ≤ 1 := by dsimp [δ]; have := min_le_right ε 1; linarith
  have hδε : δ ≤ ε := by
    dsimp [δ]
    have hmin : 0 < min ε 1 := lt_min hε (by norm_num)
    exact (half_le_self hmin.le).trans (min_le_left _ _)
  obtain ⟨f, haf, hfnorm⟩ := exists_native_jet_approx μ K b a δ hδ
  have haR : ‖a‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using ha
  have hf : f ∈ A := hfnorm.trans (by linarith)
  refine ⟨scalarStageL2 μ K f, ⟨f, hf, rfl⟩, ?_⟩
  have hp : ‖jetCoordinateCLM μ K b (Sum.inl ()) a -
      scalarStageL2 μ K f‖ ≤ ‖a.val - firstJetLinear μ K b f‖ := by
    rw [← firstJetLinear_value μ K b f,
      ← jetCoordinateCLM_apply_native μ K b (Sum.inl ()) f, ← map_sub]
    exact jetCoordinateCLM_norm_le μ K b (Sum.inl ()) (a - toSobolevFirstJet μ K b f)
  exact (by simpa only [dist_eq_norm] using hp.trans_lt (haf.trans_le hδε))

/-- Genuine compact closure of the completed first-jet value image, including zero radii. -/
theorem isCompact_value_image_closedBall_closure (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure (jetCoordinateCLM μ K b (Sum.inl ()) ''
      closedBall (0 : SobolevFirstJet μ K b) R)) :=
  (value_image_closedBall_totallyBounded μ K b R hR).closure.isCompact_of_isClosed isClosed_closure

/-- The literal original closed-first-jet value-coordinate continuous linear map is a compact operator. -/
theorem isCompactOperator_value :
    IsCompactOperator (jetCoordinateCLM μ K b (Sum.inl ())) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (jetCoordinateCLM μ K b (Sum.inl ())).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  exact isCompact_value_image_closedBall_closure μ K b 1 (by norm_num)

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisRellich
