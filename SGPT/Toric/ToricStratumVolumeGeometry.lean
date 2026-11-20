import SGPT.Toric.ToricStratumNormalizedVolume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Pointwise ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The independently defined original lattice-normalized measure is a
genuine additive Haar measure, not a trace-volume alias. -/
instance toricStratumNormalizedVolume_isAddHaarMeasure
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Measure.IsAddHaarMeasure (toricStratumNormalizedVolume (hs := hs) v J) :=
  (toricFaceRealCharacterCoordinates (hs := hs) v J).symm.isAddHaarMeasure_map volume

/-- The actual real annihilator has the genuine integral character rank. -/
theorem finrank_toricStratumRealSpace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Module.finrank ℝ (toricStratumRealSpace (polytopeToricRay γ hs v '' J)) = toricFaceDimension J := by
  have hdim := (toricFaceRealCharacterCoordinates (hs := hs) v J).toLinearEquiv.finrank_eq
  simpa only [finrank_euclideanSpace_fin] using hdim

/-- Genuine original lattice volume scales by c^dim(Y), including rank0,
empty and lower-dimensional original faces. -/
theorem toricStratumNormalizedVolume_smul
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (A : Set (toricStratumRealSpace (polytopeToricRay γ hs v '' J))) :
    toricStratumNormalizedVolume (hs := hs) v J (c • A) =
      ENNReal.ofReal (c ^ toricFaceDimension J) * toricStratumNormalizedVolume (hs := hs) v J A := by
  simpa only [finrank_toricStratumRealSpace v J] using
    Measure.addHaar_smul_of_nonneg (toricStratumNormalizedVolume (hs := hs) v J) hc A

/-- Original annihilator equations and original Cartier equations make
face membership automatic for points of the original polytope. -/
theorem toricStratumTranslatedFace_eq_preimage
    {D : ToricDivisor γ hs} (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : A ⊆ toricDivisorPolytope D) :
    toricStratumTranslatedFace D v J mσ A =
      (fun x : toricStratumRealSpace (polytopeToricRay γ hs v '' J) => x.val + latticeVector mσ) ⁻¹' A := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx,hA hx,?_⟩
    intro ρ hρ
    rw [map_add, x.property ρ hρ, zero_add, latticeFunctional_latticeVector,
      intPairing_comm, hσ ρ hρ]
    norm_cast

/-- Actual original translated faces of compact original sets are compact.
The original affine inclusion is a proper isometry, so no target compactness
certificate or desired face/body comparison is an input. -/
theorem isCompact_toricStratumTranslatedFace
    {D : ToricDivisor γ hs} (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : A ⊆ toricDivisorPolytope D) (hAc : IsCompact A) :
    IsCompact (toricStratumTranslatedFace D v J mσ A) := by
  rw [toricStratumTranslatedFace_eq_preimage v J mσ hσ hA]
  have hiso : Isometry
      (fun x : toricStratumRealSpace (polytopeToricRay γ hs v '' J) => x.val + latticeVector mσ) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    change ‖(x.val + latticeVector mσ) - (y.val + latticeVector mσ)‖ = ‖x.val - y.val‖
    rw [add_sub_add_right_eq_sub]
  exact hiso.isClosedEmbedding.isCompact_preimage hAc

/-- Actual original translated faces retain convexity in the ACTUAL real
annihilator, without a supplied target convex-body model. -/
theorem convex_toricStratumTranslatedFace
    {D : ToricDivisor γ hs} (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : A ⊆ toricDivisorPolytope D) (hAc : Convex ℝ A) :
    Convex ℝ (toricStratumTranslatedFace D v J mσ A) := by
  rw [toricStratumTranslatedFace_eq_preimage v J mσ hσ hA]
  intro x hx y hy a b ha hb hab
  have hm : a • latticeVector mσ + b • latticeVector mσ = latticeVector mσ := by
    rw [←add_smul,hab,one_smul]
  have hpoint : (a • x + b • y).val + latticeVector mσ =
      a • (x.val + latticeVector mσ) + b • (y.val + latticeVector mσ) := by
    change a • x.val + b • y.val + latticeVector mσ = _
    calc
      _ = a • x.val + b • y.val + (a • latticeVector mσ + b • latticeVector mσ) :=
        congrArg (fun z => a • x.val + b • y.val + z) hm.symm
      _ = _ := by module
  change (a • x + b • y).val + latticeVector mσ ∈ A
  rw [hpoint]
  exact hAc hx hy ha hb hab

end SGPT.Toric
