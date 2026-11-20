import SGPT.Toric.ToricStratumVolumeGeometry

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory
open scoped Topology Pointwise ENNReal Classical

/-- Literal Minkowski sums factor through the genuine nonzero real scalar,
with the empty set retained. -/
theorem set_smul_add_eq_smul_add_inv_smul
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A B : Set E) {c : ℝ} (hc : c ≠ 0) :
    c • A + B = c • (A + c⁻¹ • B) := by
  ext x
  constructor
  · rintro ⟨p,⟨a,ha,rfl⟩,b,hb,rfl⟩
    refine ⟨a + c⁻¹ • b,⟨a,ha,c⁻¹ • b,⟨b,hb,rfl⟩,rfl⟩,?_⟩
    change c • (a + c⁻¹ • b) = c • a + b
    rw [smul_add,smul_inv_smul₀ hc]
  · rintro ⟨p,⟨a,ha,q,⟨b,hb,rfl⟩,rfl⟩,rfl⟩
    refine ⟨c • a,⟨a,ha,rfl⟩,b,hb,?_⟩
    change c • a + b = c • (a + c⁻¹ • b)
    rw [smul_add,smul_inv_smul₀ hc]

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original lattice volume of c*A+B is c^dim(Y) times the
volume of the genuine rational thickening A+c^{-1}B, including rank0. -/
theorem toricStratumNormalizedVolume_smul_add
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {c : ℝ} (hc : 0 < c)
    (A B : Set (toricStratumRealSpace (polytopeToricRay γ hs v '' J))) :
    toricStratumNormalizedVolume (hs := hs) v J (c • A + B) =
      ENNReal.ofReal (c ^ toricFaceDimension J) *
        toricStratumNormalizedVolume (hs := hs) v J (A + c⁻¹ • B) := by
  rw [set_smul_add_eq_smul_add_inv_smul A B hc.ne',toricStratumNormalizedVolume_smul v J hc.le]

end SGPT.Toric
