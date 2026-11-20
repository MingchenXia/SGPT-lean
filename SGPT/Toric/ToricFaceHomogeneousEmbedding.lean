import SGPT.Toric.ToricFaceSmooth
import SGPT.Toric.MonomialProjectiveCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual homogeneous indices of the ORIGINAL ambient model lying on
the literal selected original face. The FULL lattice-point family is used. -/
def ToricFaceHomogeneousIndex (v : latticePolytopeVertices γ) (J : Set (Fin n)) :=
  {i : Fin (originalPolytopeFullIndexSize γ + 1) //
    integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J}

/-- The FULL homogeneous target index is matched with the FULL original
ambient face index using the previously proved actual lattice-point bijection. -/
def toricFaceHomogeneousIndexEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) ≃
      ToricFaceHomogeneousIndex (hs := hs) v J :=
  (originalPolytopeFullEnumeration (toricFaceProjectedFamily (hs := hs) v J)).trans
    ((toricFaceFullLatticePointEquiv (hs := hs) v J).symm.trans
      ((originalPolytopeFullEnumeration γ).subtypeEquiv (fun _ => Iff.rfl)).symm)

/-- The original source homogeneous exponent is literally reconstructed
from the target exponent and the original vertex; no desired toric-model
equality is stored in the index correspondence. -/
theorem toricFaceHomogeneousIndexEquiv_exponent (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (i : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1)) :
    originalPolytopeFullExponents γ (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val =
      toricFaceIntegralReconstruction (hs := hs) v J
        (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J) i) := by
  change ((originalPolytopeFullEnumeration γ)
    ((originalPolytopeFullEnumeration γ).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Literal homogeneous zero-coordinate extension. It is constructed from
the ACTUAL full face-index dictionary, before restricting any projective map
to a toric variety or claiming an orbit-closure identification. -/
def toricFaceHomogeneousZeroExtension (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ) →ₗ[ℂ]
      (Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) where
  toFun z i := if hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J then
    z ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm ⟨i, hi⟩) else 0
  map_add' := by
    intro x y
    funext i
    by_cases hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J
    · simp only [dif_pos hi, Pi.add_apply]
    · simp only [dif_neg hi, Pi.add_apply, add_zero]
  map_smul' := by
    intro c x
    funext i
    by_cases hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J
    · simp only [dif_pos hi, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg hi, Pi.smul_apply, RingHom.id_apply, smul_zero]

/-- Every actual target homogeneous coordinate is read back exactly at its
actual original ambient face coordinate. -/
theorem toricFaceHomogeneousZeroExtension_readback (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (z : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ)
    (i : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1)) :
    toricFaceHomogeneousZeroExtension (hs := hs) v J z
      (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val = z i := by
  change (if hi : integerCast (originalPolytopeFullExponents γ
      (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val) ∈ toricNativeVertexFace (hs := hs) v J then
      z ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm
        ⟨(toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val, hi⟩) else 0) = z i
  rw [dif_pos (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).property]
  change z ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm
    ((toricFaceHomogeneousIndexEquiv (hs := hs) v J) i)) = z i
  rw [Equiv.symm_apply_apply]

/-- Every ambient homogeneous coordinate outside the actual original face
is literally zero, without replacing the original full index family. -/
theorem toricFaceHomogeneousZeroExtension_off_face (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (z : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1))
    (hi : integerCast (originalPolytopeFullExponents γ i) ∉ toricNativeVertexFace (hs := hs) v J) :
    toricFaceHomogeneousZeroExtension (hs := hs) v J z i = 0 := dif_neg hi

/-- Genuine full-coordinate readback proves injectivity of zero extension. -/
theorem toricFaceHomogeneousZeroExtension_injective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Injective (toricFaceHomogeneousZeroExtension (hs := hs) v J) := by
  intro x y hxy
  funext i
  have heq := congrFun hxy (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val
  rwa [toricFaceHomogeneousZeroExtension_readback, toricFaceHomogeneousZeroExtension_readback] at heq

/-- The literal linear extension is continuous in the actual finite
homogeneous coordinate topology. -/
theorem continuous_toricFaceHomogeneousZeroExtension (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricFaceHomogeneousZeroExtension (hs := hs) v J) := by
  apply continuous_pi
  intro i
  by_cases hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J
  · simpa only [toricFaceHomogeneousZeroExtension, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hi] using
      (continuous_apply ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm ⟨i, hi⟩))
  · simpa only [toricFaceHomogeneousZeroExtension, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi] using
      (continuous_const : Continuous (fun _ :
        (Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ) => (0 : ℂ)))

/-- The ACTUAL ambient projective coordinate embedding. No orbit-closure or
holomorphy conclusion is included in this definition. -/
def toricFaceProjectiveEmbedding (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Projectivization ℂ
      (Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ) →
      Projectivization ℂ (Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) :=
  Projectivization.map (toricFaceHomogeneousZeroExtension (hs := hs) v J)
    (toricFaceHomogeneousZeroExtension_injective (hs := hs) v J)

/-- Projective injectivity comes from the proved actual linear injection. -/
theorem toricFaceProjectiveEmbedding_injective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Injective (toricFaceProjectiveEmbedding (hs := hs) v J) :=
  Projectivization.map_injective _ _

/-- Continuity is proved in the original native nonzero-vector quotient
projective topologies, before restricting to the original toric models. -/
theorem continuous_toricFaceProjectiveEmbedding (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricFaceProjectiveEmbedding (hs := hs) v J) := by
  have hsub : Continuous (fun z : {z :
      Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ // z ≠ 0} =>
      (⟨toricFaceHomogeneousZeroExtension (hs := hs) v J z.val, by
        simpa only [map_zero] using
          (toricFaceHomogeneousZeroExtension_injective (hs := hs) v J).ne z.property⟩ :
        {z : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ // z ≠ 0})) :=
    ((continuous_toricFaceHomogeneousZeroExtension (hs := hs) v J).comp continuous_subtype_val).subtype_mk _
  apply continuous_coinduced_dom.mpr
  exact continuous_quotient_mk'.comp hsub

end SGPT.Toric
