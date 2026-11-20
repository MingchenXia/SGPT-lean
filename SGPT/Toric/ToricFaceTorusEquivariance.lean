import SGPT.Toric.ToricFaceChartOrbits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original quotient torus map, in the SAME finite Mσ basis
used by the actual constructed face model. Every coordinate is an original
integral edge character. -/
def toricFaceTorusQuotient (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (Fin n → ℂˣ) →* (Fin (toricFaceDimension J) → ℂˣ) where
  toFun a j := toricStratumTorusQuotient (hs := hs) v J a
    ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j)
  map_one' := funext fun j => map_one (latticeCharacter (originalPolytopeNativeBasis γ hs v
    ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val))
  map_mul' a b := funext fun j => map_mul (latticeCharacter (originalPolytopeNativeBasis γ hs v
    ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val)) a b

/-- The actual quotient retains genuine continuity. -/
theorem continuous_toricFaceTorusQuotient (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricFaceTorusQuotient (hs := hs) v J) := by
  apply continuous_pi
  intro j
  exact continuous_latticeCharacter _

/-- The constructed actual quotient admits an explicit original torus lift. -/
def toricFaceTorusSection (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) : Fin n → ℂˣ :=
  toricStratumTorusSection (hs := hs) v J (fun j => a ((Fintype.equivFin {j : Fin n // j ∉ J}) j))

/-- Genuine exact quotient/lift inverse, including rank zero. -/
theorem toricFaceTorusQuotient_section (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    toricFaceTorusQuotient (hs := hs) v J (toricFaceTorusSection (hs := hs) v J a) = a := by
  funext j
  have h := congrFun (toricStratumTorusQuotient_section (hs := hs) v J
    (fun j => a ((Fintype.equivFin {j : Fin n // j ∉ J}) j)))
      ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- Every ACTUAL compact target element has a genuine compact original lift;
compactness is produced from the original character norm formula. -/
theorem toricFaceTorusSection_compact (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) (ha : IsCompactTorusElement a) :
    IsCompactTorusElement (toricFaceTorusSection (hs := hs) v J a) :=
  toricStratumTorusSection_compact v J _ (fun j => ha ((Fintype.equivFin {j : Fin n // j ∉ J}) j))

/-- On the ACTUAL dense boundary orbit, the actual face map intertwines the
ORIGINAL ambient torus and its ACTUAL quotient, on the same original points. -/
theorem toricFaceNativeEmbedding_equivariant_orbit
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (a : Fin n → ℂˣ)
    (t : Fin (toricFaceDimension J) → ℂˣ) :
    toricFaceNativeEmbedding (hs := hs) v J
      (originalPolytopeNativeAction (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceTorusQuotient (hs := hs) v J a)
        (originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J) t)) =
      originalPolytopeNativeAction γ a
        (toricFaceNativeEmbedding (hs := hs) v J
          (originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J) t)) := by
  rw [originalPolytopeNativeAction_orbit, toricFaceNativeEmbedding_orbit, toricFaceNativeEmbedding_orbit,
    nativePiChart_symm_eq_vertexPoint, nativePiChart_symm_eq_vertexPoint]
  change vertexPoint hs v (modelPoint (toricFaceBoundaryCoordinates J (toricFaceTorusQuotient v J a * t))) =
    polytopeToricAction γ hs a (vertexPoint hs v (modelPoint (toricFaceBoundaryCoordinates J t)))
  rw [toricAction_vertexPoint]
  apply congrArg (vertexPoint hs v)
  ext k
  rw [vertexAction_apply]
  simp only [modelPoint_apply]
  by_cases hk : k ∈ J
  · simp [toricFaceBoundaryCoordinates, hk]
  · simp only [toricFaceBoundaryCoordinates, dif_neg hk, Pi.mul_apply, Units.val_mul]
    change ((latticeCharacter (originalPolytopeNativeBasis γ hs v
        ((Fintype.equivFin {j : Fin n // j ∉ J}).symm
          ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩)).val) a : ℂ) * _) = _
    rw [Equiv.symm_apply_apply]

/-- The ACTUAL biholomorphic face realization is T-equivariant on EVERY
original point. The dense-orbit equality and genuine continuity prove all
boundary points, rather than assuming a toric presentation certificate. -/
theorem toricFaceNativeEmbedding_equivariant
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (a : Fin n → ℂˣ)
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceNativeEmbedding (hs := hs) v J
      (originalPolytopeNativeAction (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceTorusQuotient (hs := hs) v J a) p) =
      originalPolytopeNativeAction γ a (toricFaceNativeEmbedding (hs := hs) v J p) := by
  have hF : Continuous (fun p => toricFaceNativeEmbedding (hs := hs) v J
      (originalPolytopeNativeAction (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceTorusQuotient (hs := hs) v J a) p)) :=
    (continuous_toricFaceNativeEmbedding (hs := hs) v J).comp
      (originalPolytopeNativeAction (toricFaceProjectedFamily (hs := hs) v J) _).continuous
  have hG : Continuous (fun p => originalPolytopeNativeAction γ a
      (toricFaceNativeEmbedding (hs := hs) v J p)) :=
    (originalPolytopeNativeAction γ a).continuous.comp (continuous_toricFaceNativeEmbedding v J)
  have heq := hF.ext_on
    (denseRange_originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J)) hG
    (by rintro _ ⟨t, rfl⟩; exact toricFaceNativeEmbedding_equivariant_orbit v J a t)
  exact congrFun heq p

end SGPT.Toric
