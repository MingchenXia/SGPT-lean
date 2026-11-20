import SGPT.Toric.ToricFaceNativeDual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every actual ambient free native primitive is in literal Mσ, because
ALL σ rays lie in this SAME source vertex cone and the native bases are dual. -/
theorem toricFaceNativeFreePrimitive_annihilator (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin n)
    (hk : polytopeToricRay γ hs w.val k ∉ polytopeToricRay γ hs v '' J) :
    originalPolytopeNativeBasis γ hs w.val k ∈
      toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
  intro ρ hρ
  obtain ⟨j, hj⟩ := toricNativeFace_rays_in_vertexCone v J w ρ hρ
  have hkj : k ≠ j := by
    intro h
    subst j
    have hρeq : polytopeToricRay γ hs w.val k = ρ := Subtype.ext hj
    exact hk (hρeq.symm ▸ hρ)
  change intPairing (originalPolytopeNativeBasis γ hs w.val k) ρ.val = 0
  rw [← hj, intPairing_basis_rayGenerator, if_neg hkj]

/-- The actual native target factors exhaust ALL original free native
factors. This is proved from the true annihilator basis and literal duality,
without a rank equality or a supplied coordinate correspondence. -/
theorem toricFaceNativeFreeIndex_surjective (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin n)
    (hk : polytopeToricRay γ hs w.val k ∉ polytopeToricRay γ hs v '' J) :
    ∃ j, toricFaceNativeFreeIndex v J w j = k := by
  by_contra h
  let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨originalPolytopeNativeBasis γ hs w.val k, toricFaceNativeFreePrimitive_annihilator v J w k hk⟩
  have hz : toricFaceCharacterCoordinates (hs := hs) v J m = 0 := by
    apply eq_of_intPairing_rayGenerator_eq
      (toricFaceVertexEquiv (hs := hs) v J w)
    intro j
    rw [toricFaceNativeRay_pairing]
    have hkj : k ≠ toricFaceNativeFreeIndex v J w j := by
      intro heq
      exact h ⟨j, heq.symm⟩
    change intPairing (originalPolytopeNativeBasis γ hs w.val k) _ = intPairing 0 _
    rw [intPairing_basis_rayGenerator, if_neg hkj]
    simp [intPairing]
  have hm : m = 0 := (toricFaceCharacterCoordinates (hs := hs) v J).injective
    (hz.trans (map_zero _).symm)
  exact (originalPolytopeNativeBasis γ hs w.val).ne_zero k (congrArg Subtype.val hm)

/-- The actual quotient-model native coordinates are in genuine bijection
with EXACTLY the original vertex-cone rays outside σ. -/
def toricFaceNativeFreeEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    Fin (toricFaceDimension J) ≃
      {k : Fin n // polytopeToricRay γ hs w.val k ∉ polytopeToricRay γ hs v '' J} :=
  Equiv.ofBijective
    (fun j => ⟨toricFaceNativeFreeIndex v J w j, toricFaceNativeFreeIndex_ray_not_mem v J w j⟩)
    ⟨fun _ _ h => toricFaceNativeFreeIndex_injective v J w (congrArg Subtype.val h), by
      intro k
      obtain ⟨j, hj⟩ := toricFaceNativeFreeIndex_surjective v J w k.val k.property
      exact ⟨j, Subtype.ext hj⟩⟩

end SGPT.Toric
