import SGPT.Toric.ToricFaceQuotientFan
import SGPT.Toric.ToricFaceWholeChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal quotient-ray duality for EVERY actual fan ray and EVERY
annihilator character, independent of the native presentation. -/
theorem toricFaceRayLift_pairing (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    intPairing (toricFaceCharacterCoordinates v J m) ρ.val =
      intPairing m.val (toricFaceRayLift v J ρ).val := by
  obtain ⟨w, k, rfl⟩ := exists_toricFaceRay_native_presentation v J ρ
  rw [toricFaceRayLift_native]
  exact toricFaceNativeRay_pairing v J w k m

/-- The produced source lift retains distinct actual quotient-fan rays;
the entire actual annihilator lattice, rather than a supplied quotient-fan
certificate, proves injectivity. -/
theorem toricFaceRayLift_injective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Injective (toricFaceRayLift (hs := hs) v J) := by
  intro ρ ρ' hρ
  apply Subtype.ext
  funext i
  let m := (toricFaceCharacterCoordinates (hs := hs) v J).symm (Pi.single i (1 : ℤ))
  have h := toricFaceRayLift_pairing v J ρ m
  have h' := toricFaceRayLift_pairing v J ρ' m
  rw [hρ] at h
  have heq := h.trans h'.symm
  change intPairing (toricFaceCharacterCoordinates v J
    ((toricFaceCharacterCoordinates v J).symm (Pi.single i 1))) ρ.val =
    intPairing (toricFaceCharacterCoordinates v J
      ((toricFaceCharacterCoordinates v J).symm (Pi.single i 1))) ρ'.val at heq
  rw [LinearEquiv.apply_symm_apply] at heq
  simpa [intPairing, Pi.single_apply] using heq

/-- Every actual quotient ray lifts outside the ORIGINAL σ, with this
fact produced from every genuine native presentation. -/
theorem toricFaceRayLift_not_mem (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceRayLift v J ρ ∉ polytopeToricRay γ hs v '' J := by
  obtain ⟨w, k, rfl⟩ := exists_toricFaceRay_native_presentation v J ρ
  rw [toricFaceRayLift_native]
  exact toricFaceNativeFreeIndex_ray_not_mem v J w k

/-- EXACT original prime-divisor restriction: the actual target prime
divisor is the preimage of the SAME original lifted prime divisor on every
point, including all boundary intersections. Genuine native charts/free
duality prove both directions, with no divisor-presentation assumption. -/
theorem toricFaceNativeEmbedding_mem_primeDivisor_iff
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (p : PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceNativeEmbedding (hs := hs) v J p ∈ toricPrimeDivisor (toricFaceRayLift v J ρ) ↔
      p ∈ toricPrimeDivisor ρ := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  obtain ⟨q, hp⟩ := originalPolytopeNativeModelChart_cover γY hY p
  obtain ⟨w, rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q
  have hpPi := hp
  rw [originalPolytopeNativeModelChart_source] at hpPi
  have hq : toricFaceNativeEmbedding (hs := hs) v J p ∈
      (originalPolytopeNativeModelChart γ hs w.val).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact (toricFaceNativeEmbedding_mem_chart_source_iff v J w p).mpr hpPi
  rw [mem_toricPrimeDivisor_iff hq, mem_toricPrimeDivisor_iff hp]
  constructor
  · rintro ⟨k, hk, hz⟩
    have hkρ : polytopeToricRay γ hs w.val k = toricFaceRayLift v J ρ := Subtype.ext hk
    have hkfree : polytopeToricRay γ hs w.val k ∉ polytopeToricRay γ hs v '' J :=
      hkρ ▸ toricFaceRayLift_not_mem v J ρ
    obtain ⟨j, hj⟩ := toricFaceNativeFreeIndex_surjective v J w k hkfree
    have hjρ : polytopeToricRay γY hY (toricFaceVertexEquiv v J w) j = ρ := by
      apply toricFaceRayLift_injective v J
      rw [toricFaceRayLift_native, hj]
      exact hkρ
    refine ⟨j, congrArg Subtype.val hjρ, ?_⟩
    change originalPolytopeNativePiChart γY hY (toricFaceVertexEquiv v J w) p j = 0
    rw [toricFaceNativeEmbedding_chart_free_coordinate v J w p hpPi j, hj]
    exact hz
  · rintro ⟨j, hj, hz⟩
    have hjρ : polytopeToricRay γY hY (toricFaceVertexEquiv v J w) j = ρ := Subtype.ext hj
    refine ⟨toricFaceNativeFreeIndex v J w j, ?_, ?_⟩
    · have heq := toricFaceRayLift_native (hs := hs) v J w j
      rw [hjρ] at heq
      exact congrArg Subtype.val heq.symm
    · change originalPolytopeNativePiChart γ hs w.val (toricFaceNativeEmbedding v J p)
        (toricFaceNativeFreeIndex v J w j) = 0
      rw [← toricFaceNativeEmbedding_chart_free_coordinate v J w p hpPi j]
      exact hz

end SGPT.Toric
