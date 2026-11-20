import SGPT.Unibranch.HironakaG10CompactArtinianRelationLift
import SGPT.Foundations.Analysis.Pending.HironakaG10ArtinianFlatQuotient
import SGPT.Foundations.Analysis.Pending.HironakaG10OneParameterQuotientFlatness
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace SGPT.Unibranch.HironakaG10ScalarOneRowCokernel
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaG10OneParameterQuotientFlatness HironakaG10ArtinianParameterPullback
  HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient HironakaRelativeNormalIdeal

/-- The unique-output image of a one-row matrix is the whole entry ideal,
retaining the action of any original scalar algebra. -/
theorem scalar_one_row_image_eq_ideal {Q R : Type*} [CommRing Q] [CommRing R] [Algebra Q R]
    {b : ℕ} (M : Matrix (Fin 1) (Fin b) R) :
    (LinearMap.range (M.mulVecLin.restrictScalars Q)).map
      (LinearEquiv.funUnique (Fin 1) Q R).toLinearMap =
        (Ideal.span (Set.range fun j => M 0 j)).restrictScalars Q := by
  have h := one_row_image_eq_ideal M
  ext x
  have hx := congrArg (fun S : Submodule R R => x ∈ S) h
  exact iff_of_eq hx

/-- The entire one-row cokernel is the entry-ideal quotient as a module over
the original parameter ring. -/
def scalarOneRowCokernelEquiv {Q R : Type*} [CommRing Q] [CommRing R] [Algebra Q R]
    {b : ℕ} (M : Matrix (Fin 1) (Fin b) R) :
    ((Fin 1 → R) ⧸ LinearMap.range (M.mulVecLin.restrictScalars Q)) ≃ₗ[Q]
      (R ⧸ (Ideal.span (Set.range fun j => M 0 j)).restrictScalars Q) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.funUnique (Fin 1) Q R)
    (scalar_one_row_image_eq_ideal M)

/-- Mapping the original entry ideal gives exactly the ideal of all substituted
entries. -/
theorem map_entry_ideal {A R : Type*} [CommRing A] [CommRing R] {b : ℕ}
    (ψ : A →+* R) (f : Fin b → A) :
    Ideal.map ψ (Ideal.span (Set.range f)) = Ideal.span (Set.range (fun j => ψ (f j))) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨f j,⟨j,rfl⟩,rfl⟩
/-- Flatness of the whole entry-ideal quotient implies flatness of the
actual one-row cokernel over the original parameter ring. -/
theorem scalarOneRowCokernel_flat_of_ideal_flat {Q R : Type*}
    [CommRing Q] [CommRing R] [Algebra Q R] {b : ℕ} (M : Matrix (Fin 1) (Fin b) R)
    (hflat : Module.Flat Q (R ⧸ Ideal.span (Set.range fun j => M 0 j))) :
    Module.Flat Q ((Fin 1 → R) ⧸ LinearMap.range (M.mulVecLin.restrictScalars Q)) := by
  letI := hflat
  exact Module.Flat.of_linearEquiv ((scalarOneRowCokernelEquiv M).trans
    (Submodule.Quotient.restrictScalarsEquiv Q (Ideal.span (Set.range fun j => M 0 j))))
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- Native flatness of an original finite-generator quotient gives flatness of
the literal one-row substituted tensor-germ cokernel. -/
theorem original_flat_gives_substituted_cokernel_flat (d t q : ℕ) {b : ℕ}
    (I : Ideal (HolGerm (ComplexModel d))) (f : Fin b → HolGerm (ComplexModel (d+t)))
    (hflat : Module.Flat (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.span (Set.range f))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    let R := Q ⊗[ℂ] HolGerm (ComplexModel t)
    let ψ := actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
      (parameterQuotientMap_kills d q I)
    let M : Matrix (Fin 1) (Fin b) R := fun _ j => ψ (f j)
    Module.Flat Q ((Fin 1 → R) ⧸ LinearMap.range (M.mulVecLin.restrictScalars Q)) := by
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let R := Q ⊗[ℂ] HolGerm (ComplexModel t)
  let ψ := actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
    (parameterQuotientMap_kills d q I)
  let M : Matrix (Fin 1) (Fin b) R := fun _ j => ψ (f j)
  have hq := actualBaseChangedQuotient_flat d t q I (Ideal.span (Set.range f)) hflat
  rw [map_entry_ideal] at hq
  exact scalarOneRowCokernel_flat_of_ideal_flat M hq
end
end SGPT.Unibranch.HironakaG10ScalarOneRowCokernel
