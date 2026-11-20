import SGPT.Toric.TropicalSmoothDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators

/-- The literal original head and tail have the genuine L2 product norm. -/
def tropicalCoordinateSplit (n : ℕ) :
    ComplexModel (n + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ComplexModel n) where
  toFun z := WithLp.toLp 2 (z 0, WithLp.toLp 2 (fun i => z i.succ))
  invFun w := WithLp.toLp 2 (Fin.cons w.fst (fun i => w.snd i))
  left_inv z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv w := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · ext i
      rfl
  map_add' z w := rfl
  map_smul' c z := rfl
  norm_map' z := by
    change ‖WithLp.toLp 2 (z 0, WithLp.toLp 2 (fun i : Fin n => z i.succ))‖ = ‖z‖
    have hsource := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (n + 1) => ℂ) z
    rw [Fin.sum_univ_succ] at hsource
    have htarget := WithLp.prod_norm_sq_eq_of_L2
      (WithLp.toLp 2 (z 0, WithLp.toLp 2 (fun i : Fin n => z i.succ)))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, PiLp.norm_sq_eq_of_L2] at htarget
    nlinarith [norm_nonneg z,
      norm_nonneg (WithLp.toLp 2 (z 0, WithLp.toLp 2 (fun i : Fin n => z i.succ)))]

theorem tropicalCoordinateSplit_apply {n : ℕ} (z : ComplexModel (n + 1)) :
    tropicalCoordinateSplit n z =
      WithLp.toLp 2 (z 0, WithLp.toLp 2 (fun i => z i.succ)) := rfl

theorem tropicalCoordinateSplit_symm_apply {n : ℕ}
    (w : WithLp 2 (ℂ × ComplexModel n)) :
    (tropicalCoordinateSplit n).symm w =
      WithLp.toLp 2 (Fin.cons w.fst (fun i => w.snd i)) := rfl

private def tropicalVolume_emptyIsometry :
    ComplexModel 0 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 0) where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  norm_map' z := by
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]

private theorem tropicalVolume_empty :
    (volume : Measure (ComplexModel 0)) = Measure.dirac 0 := by
  have h := tropicalVolume_emptyIsometry.symm.measurePreserving.map_eq
  rw [volume_euclideanSpace_eq_dirac, Measure.map_dirac] at h
  simpa using h.symm

/-- The original complex Euclidean volume is the actual product of plane volumes. -/
theorem volume_preserving_complexModel_coordinates (n : ℕ) :
    MeasurePreserving (fun z : ComplexModel n => (fun i => z i))
      volume (Measure.pi (fun _ : Fin n => (volume : Measure ℂ))) := by
  induction n with
  | zero =>
    refine ⟨(MeasurableEquiv.toLp 2 (Fin 0 → ℂ)).symm.measurable, ?_⟩
    rw [tropicalVolume_empty, Measure.map_dirac]
    exact (Measure.volume_pi_eq_dirac (0 : Fin 0 → ℂ)).symm
  | succ n ih =>
    have hsplit := (WithLp.volume_preserving_ofLp ℂ (ComplexModel n)).comp
      (tropicalCoordinateSplit n).measurePreserving
    have hprod := (MeasurePreserving.id (volume : Measure ℂ)).prod ih
    have hjoin := MeasurePreserving.symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0)
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0)
    convert hjoin.comp (hprod.comp hsplit) using 1
    calc
      _ = borel (ComplexModel (n + 1)) := BorelSpace.measurable_eq
      _ = _ := (@BorelSpace.measurable_eq (ComplexModel (n + 1)) inferInstance
        (WithLp.measurableSpace 2 (Fin (n + 1) → ℂ)) inferInstance).symm
    funext z
    change (fun i => z i) = Fin.insertNth 0 (z 0) (fun j => z j.succ)
    rw [Fin.insertNth_zero']
    exact (Fin.cons_self_tail (fun i => z i)).symm

/-- The actual inverse coordinate map preserves the same unchanged measures. -/
theorem volume_preserving_complexModel_toLp (n : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin n → ℂ) → ComplexModel n)
      (Measure.pi (fun _ : Fin n => (volume : Measure ℂ))) volume := by
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm
    (volume_preserving_complexModel_coordinates n)

/-- Exact signed original-volume integral readback, including the total convention. -/
theorem integral_complexModel_coordinates {n : ℕ} (f : (Fin n → ℂ) → ℝ) :
    (∫ z : ComplexModel n, f (fun i => z i)) =
      ∫ z, f z ∂Measure.pi (fun _ : Fin n => (volume : Measure ℂ)) := by
  exact (volume_preserving_complexModel_coordinates n).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm.measurableEmbedding f

/-- Genuine integrability uses the same actual measurable coordinate equivalence. -/
theorem integrable_complexModel_coordinates {n : ℕ} (f : (Fin n → ℂ) → ℝ) :
    Integrable (fun z : ComplexModel n => f (fun i => z i)) ↔
      Integrable f (Measure.pi (fun _ : Fin n => (volume : Measure ℂ))) := by
  exact (volume_preserving_complexModel_coordinates n).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm.measurableEmbedding

end SGPT.Toric
