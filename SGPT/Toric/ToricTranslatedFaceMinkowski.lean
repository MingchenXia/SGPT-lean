import SGPT.Toric.ToricFaceMinkowski

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Pointwise Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The literal ORIGINAL translated face of the genuine integral
perturbation is the actual Minkowski sum IN M(sigma)_R. All integral Cartier
and original supporting equations are proved; no face/body/model certificate
is input. Arbitrary original Cartier representatives and empty faces remain. -/
theorem toricStratumTranslatedFace_nsmul_add
    (D E : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ mH : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (hH : IsToricCartierDatumAlong E (polytopeToricRay γ hs v '' J) mH)
    (N : ℕ) (hN : 0 < N)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : A ⊆ toricDivisorPolytope D) (hB : B ⊆ toricDivisorPolytope E) :
    toricStratumTranslatedFace (N • D + E) v J (N • mσ + mH) ((N : ℝ) • A + B) =
      (N : ℝ) • toricStratumTranslatedFace D v J mσ A +
        toricStratumTranslatedFace E v J mH B := by
  have hface := toricDivisorFace_inter_nsmul_add D E (polytopeToricRay γ hs v '' J) N hN hA hB
  ext x
  constructor
  · intro hx
    change x.val + latticeVector (N • mσ + mH) ∈
      ((N : ℝ) • A + B) ∩ toricDivisorFace (N • D + E) (polytopeToricRay γ hs v '' J) at hx
    rw [hface] at hx
    obtain ⟨p,⟨a,ha,rfl⟩,b,hb,heq⟩ := hx
    let xa : toricStratumRealSpace (polytopeToricRay γ hs v '' J) :=
      ⟨a - latticeVector mσ,sub_Cartier_mem_toricStratumRealSpace_of_mem_face hσ ha.2⟩
    let xb : toricStratumRealSpace (polytopeToricRay γ hs v '' J) :=
      ⟨b - latticeVector mH,sub_Cartier_mem_toricStratumRealSpace_of_mem_face hH hb.2⟩
    have hxa : xa ∈ toricStratumTranslatedFace D v J mσ A := by
      change (a - latticeVector mσ) + latticeVector mσ ∈ A ∩ toricDivisorFace D _
      simpa only [sub_add_cancel] using ha
    have hxb : xb ∈ toricStratumTranslatedFace E v J mH B := by
      change (b - latticeVector mH) + latticeVector mH ∈ B ∩ toricDivisorFace E _
      simpa only [sub_add_cancel] using hb
    refine ⟨(N : ℝ) • xa,⟨xa,hxa,rfl⟩,xb,hxb,?_⟩
    apply Subtype.ext
    change (N : ℝ) • (a - latticeVector mσ) + (b - latticeVector mH) = x.val
    rw [latticeVector_nsmul_add] at heq
    change (N : ℝ) • a + b = x.val + ((N : ℝ) • latticeVector mσ + latticeVector mH) at heq
    calc
      _ = ((N : ℝ) • a + b) - ((N : ℝ) • latticeVector mσ + latticeVector mH) := by module
      _ = x.val := by rw [heq]; abel
  · rintro ⟨p,⟨a,ha,rfl⟩,b,hb,rfl⟩
    change ((N : ℝ) • a + b).val + latticeVector (N • mσ + mH) ∈
      ((N : ℝ) • A + B) ∩ toricDivisorFace (N • D + E) (polytopeToricRay γ hs v '' J)
    rw [hface]
    refine ⟨(N : ℝ) • (a.val + latticeVector mσ),⟨a.val + latticeVector mσ,ha,rfl⟩,
      b.val + latticeVector mH,hb,?_⟩
    rw [latticeVector_nsmul_add]
    change (N : ℝ) • (a.val + latticeVector mσ) + (b.val + latticeVector mH) =
      ((N : ℝ) • a.val + b.val) + ((N : ℝ) • latticeVector mσ + latticeVector mH)
    module

end SGPT.Toric
