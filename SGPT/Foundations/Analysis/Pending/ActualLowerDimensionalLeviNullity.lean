import SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviNullColumns
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

/-! # Actual lower-dimensional smooth images and directional Levi nullity

Open-domain C1 regularity produces actual local Lipschitz estimates and
Haar-null transverse images. No analytic singular-stratification theorem
or projection-nullity certificate is assumed.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLowerDimensionalLeviNullity

open FirstPass

variable {k m : ℕ}

/-- Actual open-domain C1 maps from a smaller complex coordinate dimension
have Haar outer-null images, with no image-measurability premise. -/
theorem volume_image_eq_zero_of_lower_dimensional_contDiffOn
    {D : Set (ComplexModel k)} (hD : IsOpen D) {g : ComplexModel k → ComplexModel m}
    (hg : ContDiffOn ℝ 1 g D) (hkm : k < m) : volume (g '' D) = 0 := by
  have hdim : dimH (g '' D) ≤ (Module.finrank ℝ (ComplexModel k) : ℝ≥0∞) := by
    calc
      dimH (g '' D) ≤ dimH D := by
        apply dimH_image_le_of_locally_lipschitzOn
        intro x hx
        obtain ⟨C, t, ht, hgt⟩ := ((hg x hx).contDiffAt (hD.mem_nhds hx)).exists_lipschitzOnWith
        exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hgt⟩
      _ ≤ dimH (univ : Set (ComplexModel k)) := dimH_mono (subset_univ _)
      _ = _ := Real.dimH_univ_eq_finrank _
  have hreal : Module.finrank ℝ (ComplexModel k) < Module.finrank ℝ (ComplexModel m) := by
    rw [FirstPass.complexModel_real_finrank, FirstPass.complexModel_real_finrank]
    omega
  have hdimlt : dimH (g '' D) < (Module.finrank ℝ (ComplexModel m) : ℝ≥0∞) :=
    hdim.trans_lt (by exact_mod_cast hreal)
  have hnull : Measure.hausdorffMeasure (Module.finrank ℝ (ComplexModel m)) (g '' D) = 0 :=
    hausdorffMeasure_of_dimH_lt (d := (Module.finrank ℝ (ComplexModel m) : ℝ≥0)) hdimlt
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (Module.finrank ℝ (ComplexModel m))) hnull

/-- Original unbounded psh produces the actual directional measure and its
nullity on every given C1 parameter image of complex codimension at least two. -/
theorem exists_directional_measure_null_lower_dimensional_image
    (U : Opens ℂ) (V : Opens (ComplexModel m)) (f : ℂ × ComplexModel m → EReal)
    (hf : PlurisubharmonicOn f ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hΩ : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hne : ∃ a ∈ ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))), f a ≠ ⊥)
    {D : Set (ComplexModel k)} (hD : IsOpen D)
    (g : ComplexModel k → ℂ × ComplexModel m) (hg : ContDiffOn ℝ 1 g D) (hkm : k < m) :
    let Ω : Opens (ℂ × ComplexModel m) :=
      ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      (∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) =
        distributionalLeviCLM (1, (0 : ComplexModel m))
          (pshRegularDistribution hf volume hΩ hne) φ) ∧
      ν {x : Ω | x.val ∈ g '' D} = 0 := by
  obtain ⟨ν, hreg, hloc, hrep, hnull⟩ :=
    ActualDirectionalLeviNullColumns.exists_directional_measure_with_null_columns U V f hf hΩ hne
  refine ⟨ν, hreg, hloc, hrep, ?_⟩
  have hE := volume_image_eq_zero_of_lower_dimensional_contDiffOn hD
    (contDiff_snd.comp_contDiffOn hg) hkm
  apply measure_mono_null _ (hnull _ hE)
  rintro x ⟨z, hz, hzx⟩
  exact ⟨z, hz, congrArg Prod.snd hzx⟩

end SGPT.Foundations.Analysis.Pending.ActualLowerDimensionalLeviNullity
