import SGPT.Toric.ToricFacePrimeDivisors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Exact whole orbit-closure preimages for EVERY actual set of target
rays. The actual ambient σ equations hold on the full image, and actual
prime-divisor readback supplies every further original equation. -/
theorem toricFaceNativeEmbedding_mem_orbitClosure_iff
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (R : Set (PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)))
    (p : PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceNativeEmbedding (hs := hs) v J p ∈
        toricOrbitClosure ((polytopeToricRay γ hs v '' J) ∪ toricFaceRayLift v J '' R) ↔
      p ∈ toricOrbitClosure R := by
  have hbase := toricFaceNativeEmbedding_mem_orbitClosure (hs := hs) v J p
  simp only [toricOrbitClosure, mem_iInter] at hbase ⊢
  constructor
  · intro h ρ hρ
    exact (toricFaceNativeEmbedding_mem_primeDivisor_iff v J ρ p).mp
      (h (toricFaceRayLift v J ρ) (Or.inr ⟨ρ, hρ, rfl⟩))
  · intro h ρ hρ
    rcases hρ with hρ | ⟨ρ', hρ', rfl⟩
    · exact hbase ρ hρ
    · exact (toricFaceNativeEmbedding_mem_primeDivisor_iff v J ρ' p).mpr (h ρ' hρ')

end SGPT.Toric
