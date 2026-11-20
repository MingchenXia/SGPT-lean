import SGPT.Toric.ToricSourceTraceNewtonFace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Lebesgue measure in the ACTUAL original annihilator, defined only from
its genuine integral-compatible character coordinates, never from I-volume. -/
def toricStratumNormalizedVolume (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Measure (toricStratumRealSpace (polytopeToricRay γ hs v '' J)) :=
  Measure.map (toricFaceRealCharacterCoordinates (hs := hs) v J).symm volume

/-- Literal original affine face, translated into the actual original annihilator. -/
def toricStratumTranslatedFace (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    Set (toricStratumRealSpace (polytopeToricRay γ hs v '' J)) :=
  {x | x.val + latticeVector mσ ∈ A ∩ toricDivisorFace D (polytopeToricRay γ hs v '' J)}

/-- Actual compact-set volume transport in the genuine lattice-compatible coordinates. -/
theorem toricStratumNormalizedVolume_image (v : latticePolytopeVertices γ) (J : Set (Fin n))
    {A : Set (EuclideanSpace ℝ (Fin (toricFaceDimension J)))} (hA : IsCompact A) :
    toricStratumNormalizedVolume (hs := hs) v J
      ((toricFaceRealCharacterCoordinates (hs := hs) v J).symm '' A) = volume A := by
  let C := toricFaceRealCharacterCoordinates (hs := hs) v J
  have hcompact : IsCompact (C.symm '' A) := hA.image C.symm.continuous
  rw [toricStratumNormalizedVolume, Measure.map_apply C.symm.continuous.measurable hcompact.measurableSet]
  congr 1
  exact Set.preimage_image_eq _ C.symm.injective

/-- A genuine integral basis of the original annihilator lattice. Its
construction uses only the original fan and the actual integral equivalence. -/
def toricStratumFiniteCharacterBasis (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Module.Basis (Fin (toricFaceDimension J)) ℤ
      (toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :=
  (Pi.basisFun ℤ _).map (toricFaceCharacterCoordinates (hs := hs) v J).symm

/-- The real vectors of the actual integral basis are exactly the inverse
images of the ordinary Euclidean unit basis. -/
theorem toricStratumFiniteCharacterBasis_real (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (j : Fin (toricFaceDimension J)) :
    (toricFaceRealCharacterCoordinates (hs := hs) v J).symm
        (EuclideanSpace.basisFun (Fin (toricFaceDimension J)) ℝ j) =
      ⟨latticeVector (toricStratumFiniteCharacterBasis (hs := hs) v J j).val,
        latticeVector_mem_toricStratumRealSpace
          (toricStratumFiniteCharacterBasis (hs := hs) v J j).property⟩ := by
  have hb : EuclideanSpace.basisFun (Fin (toricFaceDimension J)) ℝ j =
      latticeVector (Pi.single j (1 : ℤ)) := by
    ext i
    simp [EuclideanSpace.basisFun_apply,
      latticeVector, integerCast, Pi.single_apply]
  rw [hb, toricFaceRealCharacterCoordinates_inverse_latticeVector]
  simp only [toricStratumFiniteCharacterBasis, Module.Basis.map_apply, Pi.basisFun_apply]

/-- The measure is normalized by the ORIGINAL integral lattice: the closed
fundamental parallelepiped of a genuine integral basis has measure one. This
also retains the rank-zero annihilator's actual unit point mass. -/
theorem toricStratumNormalizedVolume_fundamentalParallelepiped
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricStratumNormalizedVolume (hs := hs) v J
      (parallelepiped (fun j : Fin (toricFaceDimension J) =>
        (⟨latticeVector (toricStratumFiniteCharacterBasis (hs := hs) v J j).val,
          latticeVector_mem_toricStratumRealSpace
            (toricStratumFiniteCharacterBasis (hs := hs) v J j).property⟩ :
          toricStratumRealSpace (polytopeToricRay γ hs v '' J)))) = 1 := by
  let B := EuclideanSpace.basisFun (Fin (toricFaceDimension J)) ℝ
  let C := toricFaceRealCharacterCoordinates (hs := hs) v J
  have hcompact : IsCompact (parallelepiped B) := B.toBasis.parallelepiped.isCompact
  have himage : C.symm '' parallelepiped B =
      parallelepiped (fun j : Fin (toricFaceDimension J) =>
        (⟨latticeVector (toricStratumFiniteCharacterBasis (hs := hs) v J j).val,
          latticeVector_mem_toricStratumRealSpace
            (toricStratumFiniteCharacterBasis (hs := hs) v J j).property⟩ :
          toricStratumRealSpace (polytopeToricRay γ hs v '' J))) := by
    calc
      C.symm '' parallelepiped B = parallelepiped (C.symm ∘ B) :=
        image_parallelepiped C.symm.toLinearMap B
      _ = _ := by
        congr 1
        funext j
        exact toricStratumFiniteCharacterBasis_real v J j
  rw [←himage, toricStratumNormalizedVolume_image v J hcompact]
  exact B.volume_parallelepiped

end SGPT.Toric
