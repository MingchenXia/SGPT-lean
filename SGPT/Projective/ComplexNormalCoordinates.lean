import SGPT.Projective.ComplexNormalForm

/-! ACTUAL complex unitary normal coordinates manufactured from the original conormal.
Blueprint: `complex-normal-coordinates.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalCoordinates

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms CoordinateWedgeAssoc
open ComplexNormalForm
open scoped ComplexConjugate InnerProductSpace

/-- The literal original first positive complex coordinate unit vector. -/
def firstVector (m : ℕ) : ComplexModel (m + 1) := EuclideanSpace.single 0 1

theorem firstVector_norm (m : ℕ) : ‖firstVector m‖ = 1 := by
  simp [firstVector]

/-- The actual first complex coordinate functional has its actual operator norm one. -/
theorem firstProjection_norm (m : ℕ) :
    ‖(EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (m + 1)))‖ = 1 := by
  have hp : InnerProductSpace.toDual ℂ (ComplexModel (m + 1)) (firstVector m) =
      EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (m + 1)) := by
    ext z
    simp [firstVector, EuclideanSpace.inner_single_left]
  rw [← hp, LinearIsometryEquiv.norm_map, firstVector_norm]

/-- An ACTUAL isometry of the original first coordinate line extends to an ACTUAL complex unitary. -/
theorem exists_unitary_first (m : ℕ) (u : ComplexModel (m + 1)) (hu : ‖u‖ = 1) :
    ∃ U : ComplexModel (m + 1) ≃ₗᵢ[ℂ] ComplexModel (m + 1), U (firstVector m) = u := by
  let S : Submodule ℂ (ComplexModel (m + 1)) := ℂ ∙ firstVector m
  let L : S →ₗᵢ[ℂ] ComplexModel (m + 1) :=
    { toLinearMap :=
        { toFun := fun x => ((x : ComplexModel (m + 1)) 0) • u
          map_add' := by
            intro x y
            change (((x : ComplexModel (m + 1)) + (y : ComplexModel (m + 1))) 0) • u = _
            simp [add_smul]
          map_smul' := by
            intro c x
            change ((c • (x : ComplexModel (m + 1))) 0) • u = _
            simp [smul_smul] }
      norm_map' := by
        intro x
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.property
        change ‖((x : ComplexModel (m + 1)) 0) • u‖ = ‖(x : ComplexModel (m + 1))‖
        rw [← hc]
        simp [firstVector, norm_smul, hu] }
  have hsurj : Function.Surjective L.extend :=
    (LinearMap.injective_iff_surjective (f := L.extend.toLinearMap)).mp L.extend.injective
  refine ⟨LinearIsometryEquiv.ofSurjective L.extend hsurj, ?_⟩
  change L.extend (firstVector m) = u
  have h := L.extend_apply ⟨firstVector m, Submodule.mem_span_singleton_self (firstVector m)⟩
  simpa [L, firstVector] using h

/-- The original covector internally manufactures its ACTUAL complex unitary normal coordinates. -/
def normalCoordinates {m : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    ComplexModel (m + 1) ≃ₗᵢ[ℂ] ComplexModel (m + 1) :=
  (exists_unitary_first m (normalVector ℓ) (normalVector_norm ℓ hℓ)).choose

theorem normalCoordinates_first {m : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    normalCoordinates ℓ hℓ (firstVector m) = normalVector ℓ :=
  (exists_unitary_first m (normalVector ℓ) (normalVector_norm ℓ hℓ)).choose_spec

/-- The SAME original covector in the manufactured ACTUAL normal coordinates is norm times z₀. -/
theorem normalCoordinates_value {m : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (z : ComplexModel (m + 1)) :
    ℓ (normalCoordinates ℓ hℓ z) = ((‖ℓ‖ : ℝ) : ℂ) * z 0 := by
  rw [covector_eq_norm_mul_inner_normalVector ℓ hℓ]
  have hi : ⟪normalVector ℓ, normalCoordinates ℓ hℓ z⟫_ℂ = z 0 := by
    rw [← normalCoordinates_first ℓ hℓ, LinearIsometryEquiv.inner_map_map]
    simp [firstVector, EuclideanSpace.inner_single_left]
  rw [hi]

/-- The ACTUAL original normalized conormal pulls back to the literal coordinate normal form. -/
theorem normalCoordinates_normalForm {m : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    (normalForm ℓ).compContinuousLinearMap
      ((normalCoordinates ℓ hℓ).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      normalForm (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (m + 1))) := by
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, normalForm_apply, normalForm_apply]
  change DivisorRegularLocus.lineForm ℓ (normalCoordinates ℓ hℓ (v 0))
    (normalCoordinates ℓ hℓ (v 1)) =
    DivisorRegularLocus.lineForm (EuclideanSpace.proj (𝕜 := ℂ) 0) (v 0) (v 1)
  let p : ComplexModel (m + 1) →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) 0
  have hp : ‖p‖ = 1 := firstProjection_norm m
  have hc : (((‖ℓ‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hℓ
  calc
    _ = DivisorRegularLocus.lineForm (((‖ℓ‖ : ℝ) : ℂ) • p) (v 0) (v 1) := by
      simp only [DivisorRegularLocus.lineForm, normalCoordinates_value,
        smul_apply, smul_eq_mul, norm_smul, Complex.norm_real, norm_norm,
        hp, mul_one]
      rfl
    _ = _ := DivisorRegularLocus.lineForm_smul p hc _ _

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalCoordinates
