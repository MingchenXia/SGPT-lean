import SGPT.Toric.ToricAugmentedBaseLocus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal real span of the ACTUAL original ray generators, so its
rank is the dimension of the actual original fan cone. -/
def toricFanConeRealSpan (R : Set (PolytopeToricRays γ hs)) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun ρ : R => latticeVector ρ.val.val))

theorem linearIndependent_toricVertexRay_vectors (v : latticePolytopeVertices γ) :
    LinearIndependent ℝ (fun j : Fin n => latticeVector (polytopeToricRayGenerator γ hs v j)) := by
  apply linearIndependent_iff'.mpr
  intro S g h i hi
  have hh := congrArg (fun x : E =>
    latticeFunctional (originalPolytopeNativeBasis γ hs v i) x) h
  simp only [map_sum, map_smul, smul_eq_mul, map_zero,
    latticeFunctional_latticeVector, intPairing_basis_rayGenerator] at hh
  simpa [hi] using hh

theorem finrank_toricFanConeRealSpan {R : Set (PolytopeToricRays γ hs)}
    (hR : IsToricFanCone R) : Module.finrank ℝ (toricFanConeRealSpan R) = Nat.card R := by
  obtain ⟨v, J, rfl⟩ := hR
  let f := polytopeToricRay γ hs v
  have hinj : Function.Injective f := by
    intro i j hij
    apply (linearIndependent_toricVertexRay_vectors (hs := hs) v).injective
    exact congrArg (fun ρ : PolytopeToricRays γ hs => latticeVector ρ.val) hij
  have hspan : toricFanConeRealSpan (f '' J) =
      Submodule.span ℝ (Set.range (fun j : J =>
        latticeVector (polytopeToricRayGenerator γ hs v j.val))) := by
    unfold toricFanConeRealSpan
    congr 1
    ext x
    constructor
    · rintro ⟨ρ, rfl⟩
      obtain ⟨j, hj, hjρ⟩ := ρ.property
      refine ⟨⟨j, hj⟩, ?_⟩
      exact congrArg (fun ρ : PolytopeToricRays γ hs => latticeVector ρ.val) hjρ
    · rintro ⟨j, rfl⟩
      exact ⟨⟨f j.val, ⟨j.val, j.property, rfl⟩⟩, rfl⟩
  have hli : LinearIndependent ℝ (fun j : J =>
      latticeVector (polytopeToricRayGenerator γ hs v j.val)) :=
    (linearIndependent_toricVertexRay_vectors (hs := hs) v).comp
      (fun j : J => j.val) Subtype.val_injective
  rw [hspan, finrank_span_eq_card hli]
  rw [Nat.card_congr (Equiv.Set.image f J hinj).symm, Nat.card_eq_fintype_card]

theorem toricDivisorFaceDeficient_iff_actual_cone_dimension (D : ToricDivisor γ hs)
    {R : Set (PolytopeToricRays γ hs)} (hR : IsToricFanCone R) :
    ToricDivisorFaceDeficient D R ↔ toricDivisorFace D R = ∅ ∨
      Module.finrank ℝ (vectorSpan ℝ (toricDivisorFace D R)) <
        n - Module.finrank ℝ (toricFanConeRealSpan R) := by
  rw [finrank_toricFanConeRealSpan hR]
  rfl

end SGPT.Toric
