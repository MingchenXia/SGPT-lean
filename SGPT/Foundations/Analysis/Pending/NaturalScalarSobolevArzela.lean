import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevSmoothingBounds
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Data.Set.Finite.Range

/-! # Genuine compact restrictions and fixed-smoothing Arzelà--Ascoli

Three entire mathematical statements and proofs precede this source. The
actual bounded continuous restriction retains every original smoothing value.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions Convolution Pointwise Topology BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevArzela

open NaturalScalarSobolevJet NaturalScalarSobolevBump NaturalScalarSobolevSmoothingBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (K : Compacts E) (ρ : ContDiffBump (0 : E))

/-- The actual original compact set enlarged by the genuine normalized-kernel outer radius. -/
def enlargedCompact : Compacts E :=
  ⟨(K : Set E) + closedBall 0 ρ.rOut, K.isCompact.add (isCompact_closedBall 0 _)⟩

/-- Literal original smoothing restricted to its own genuine common compact support domain. -/
def smoothingRestriction (f : 𝓓_{K}(E, ℝ)) :
    (enlargedCompact K ρ : Set E) →ᵇ ℝ := by
  letI : CompactSpace (enlargedCompact K ρ : Set E) :=
    isCompact_iff_compactSpace.mp (enlargedCompact K ρ).isCompact
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x.val,
      (normedBump_contDiff μ ρ K f).continuous.comp continuous_subtype_val⟩

/-- Actual restriction evaluation is the original whole-space convolution, with no extension convention. -/
theorem smoothingRestriction_apply (f : 𝓓_{K}(E, ℝ)) (x : (enlargedCompact K ρ : Set E)) :
    smoothingRestriction μ K ρ f x =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x.val := rfl

/-- Internally constructed whole-family bounds give actual uniform-metric compact closure. -/
theorem isCompact_smoothingRestriction_closure (A : Set 𝓓_{K}(E, ℝ))
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ f ∈ A, ‖scalarStageL2 μ K f‖ ≤ R) :
    IsCompact (closure (smoothingRestriction μ K ρ '' A)) := by
  let : CompactSpace (enlargedCompact K ρ : Set E) :=
    isCompact_iff_compactSpace.mp (enlargedCompact K ρ).isCompact
  obtain ⟨M, L, hM, _, hfamily⟩ := normedBump_family_bounds μ K ρ A R hR hA
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-M) M) isCompact_Icc
  · intro g x hg
    rcases hg with ⟨f, hf, rfl⟩
    exact abs_le.mp (by simpa only [smoothingRestriction_apply, Real.norm_eq_abs] using
      ((hfamily f hf).1 x.val))
  · have hm : Continuous (fun r : ℝ => L * r) := continuous_const.mul continuous_id
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => L * r)
      (by simpa only [mul_zero] using hm.tendsto (0 : ℝ))
    intro x y i
    rcases i.property with ⟨f, hf, hfi⟩
    rw [← hfi]
    simpa only [smoothingRestriction_apply, dist_eq_norm, Subtype.dist_eq] using
    ((hfamily f hf).2 x.val y.val)

/-- Uniform finite nets have genuine original native-test centers from the same family. -/
theorem finite_native_smoothing_uniform_approx (A : Set 𝓓_{K}(E, ℝ))
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ f ∈ A, ‖scalarStageL2 μ K f‖ ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set 𝓓_{K}(E, ℝ), F ⊆ A ∧ F.Finite ∧ ∀ f ∈ A, ∃ g ∈ F,
      ∀ x : (enlargedCompact K ρ : Set E),
        ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x.val -
          (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g : E → ℝ)) x.val‖ < ε := by
  have ht := (isCompact_smoothingRestriction_closure μ K ρ A R hR hA).totallyBounded.subset
    subset_closure
  obtain ⟨t, hts, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded ht ε hε
  obtain ⟨F, hFA, hFfin, himage⟩ := htfin.exists_subset_finite_image_eq hts
  refine ⟨F, hFA, hFfin, ?_⟩
  intro f hf
  obtain ⟨c, hct, hfc⟩ := mem_iUnion₂.mp (hcover ⟨f, hf, rfl⟩)
  rw [← himage] at hct
  rcases hct with ⟨g, hg, rfl⟩
  refine ⟨g, hg, fun x => ?_⟩
  have hc : dist (smoothingRestriction μ K ρ f) (smoothingRestriction μ K ρ g) < ε := hfc
  exact (by simpa only [smoothingRestriction_apply, dist_eq_norm] using
    (BoundedContinuousFunction.dist_coe_le_dist x).trans_lt hc)

/-- Actual finite native first-jet bounds internally supply the preceding value-L² finite net. -/
theorem finite_firstJet_smoothing_uniform_approx {ι : Type*} [Fintype ι] (v : ι → E)
    (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K v f‖ ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set 𝓓_{K}(E, ℝ), F ⊆ A ∧ F.Finite ∧ ∀ f ∈ A, ∃ g ∈ F,
      ∀ x : (enlargedCompact K ρ : Set E),
        ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x.val -
          (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g : E → ℝ)) x.val‖ < ε := by
  apply finite_native_smoothing_uniform_approx μ K ρ A R hR _ ε hε
  intro f hf
  exact (PiLp.norm_apply_le (firstJetLinear μ K v f) (Sum.inl ())).trans (hA f hf)

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevArzela
