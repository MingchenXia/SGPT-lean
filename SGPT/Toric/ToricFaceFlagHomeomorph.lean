import SGPT.Toric.ToricFaceChartOrbits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The same actual closure map, with its codomain restricted to the SAME
original flag-stage carrier. Its membership is proved by the actual full
orbit-closure realization, not supplied by a face-model presentation. -/
def toricFaceFlagEmbedding (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i)) →
      (toricFlag hs v e i) :=
  fun p => ⟨toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i) p, by
    have hp := toricFaceNativeEmbedding_mem_orbitClosure v (toricFlagSelectedIndices e i) p
    rw [← toricFlagRays_eq_selectedIndices] at hp
    exact hp⟩

/-- Genuine continuity into the actual original orbit-closure subspace. -/
theorem continuous_toricFaceFlagEmbedding (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Continuous (toricFaceFlagEmbedding (hs := hs) v e i) :=
  (continuous_toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)).subtype_mk _

/-- The actual full image theorem gives surjectivity onto the SAME original
carrier, while literal projective injectivity gives the inverse uniqueness. -/
theorem toricFaceFlagEmbedding_bijective (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Function.Bijective (toricFaceFlagEmbedding (hs := hs) v e i) := by
  constructor
  · intro p q hpq
    exact toricFaceNativeEmbedding_injective v (toricFlagSelectedIndices e i) (congrArg Subtype.val hpq)
  · intro y
    have hy : y.val ∈ Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) := by
      rw [range_toricFaceNativeEmbedding_eq_toricFlag]
      exact y.property
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩

/-- The genuine actual face-model/orbit-closure HOMEOMORPHISM, with both
original topologies. Native holomorphy is proved separately; this definition
makes no unproved complex-geometric or restricted-divisor claim. -/
def toricFaceFlagHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i)) ≃ₜ
      (toricFlag hs v e i) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (toricFaceFlagEmbedding (hs := hs) v e i)
      (toricFaceFlagEmbedding_bijective (hs := hs) v e i))
    (continuous_toricFaceFlagEmbedding (hs := hs) v e i)

/-- Literal original point readback, retaining ALL boundary points. -/
theorem toricFaceFlagHomeomorph_val (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))) :
    (toricFaceFlagHomeomorph (hs := hs) v e i p).val =
      toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i) p := rfl

end SGPT.Toric
