import SGPT.Toric.ToricFaceNativeEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Equality of ACTUAL projective representatives under the proved literal
zero-extension embedding gives EXACT selected homogeneous ratios. The scalar
fiber is produced by original projectivization, not supplied separately. -/
theorem toricFaceProjectiveEmbedding_selected_ratio
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (u : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ)
    (hu : u ≠ 0) (z : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hz : z ≠ 0)
    (hrep : Projectivization.mk ℂ z hz = toricFaceProjectiveEmbedding (hs := hs) v J
      (Projectivization.mk ℂ u hu))
    (i j : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1)) :
    z (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val /
      z (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val = u i / u j := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hrep
  have hzi : z (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val = (c : ℂ) * u i := by
    rw [← hc]
    change (c : ℂ) * toricFaceHomogeneousZeroExtension (hs := hs) v J u
      (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val = _
    rw [toricFaceHomogeneousZeroExtension_readback]
  have hzj : z (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val = (c : ℂ) * u j := by
    rw [← hc]
    change (c : ℂ) * toricFaceHomogeneousZeroExtension (hs := hs) v J u
      (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val = _
    rw [toricFaceHomogeneousZeroExtension_readback]
  rw [hzi, hzj]
  exact mul_div_mul_left _ _ (Units.ne_zero c)

/-- The actual selected source coordinate is nonzero exactly when the
same original target homogeneous coordinate is nonzero. -/
theorem toricFaceProjectiveEmbedding_selected_ne_zero_iff
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (u : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1) → ℂ)
    (hu : u ≠ 0) (z : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hz : z ≠ 0)
    (hrep : Projectivization.mk ℂ z hz = toricFaceProjectiveEmbedding (hs := hs) v J
      (Projectivization.mk ℂ u hu))
    (j : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1)) :
    z (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val ≠ 0 ↔ u j ≠ 0 := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hrep
  rw [← hc]
  change (c : ℂ) * toricFaceHomogeneousZeroExtension (hs := hs) v J u
    (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val ≠ 0 ↔ _
  rw [toricFaceHomogeneousZeroExtension_readback]
  exact mul_ne_zero_iff.trans (and_iff_right (Units.ne_zero c))

/-- In every ACTUAL target native chart, the inverse native coordinate is
literally the ratio of corresponding selected ORIGINAL ambient homogeneous
coordinates. This is the genuine coordinate producer for inverse holomorphy. -/
theorem toricFaceNativeEmbedding_inverse_chart_ratios
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J))
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J))
    (hp : p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) w).source)
    (z : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hz : z ≠ 0)
    (hrep : (toricFaceNativeEmbedding (hs := hs) v J p).val = Projectivization.mk ℂ z hz) :
    z (toricFaceHomogeneousIndexEquiv (hs := hs) v J
      (originalPolytopeNativeVertexIndex (toricFaceProjectedFamily (hs := hs) v J) w)).val ≠ 0 ∧
    ∀ j, originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) w p j =
      z (toricFaceHomogeneousIndexEquiv (hs := hs) v J
        (originalPolytopeNativeNeighborIndex (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) w j)).val /
      z (toricFaceHomogeneousIndexEquiv (hs := hs) v J
        (originalPolytopeNativeVertexIndex (toricFaceProjectedFamily (hs := hs) v J) w)).val := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  have hprep : p.val = Projectivization.mk ℂ p.val.rep p.val.rep_nonzero := p.val.mk_rep.symm
  have hzrep : Projectivization.mk ℂ z hz = toricFaceProjectiveEmbedding (hs := hs) v J
      (Projectivization.mk ℂ p.val.rep p.val.rep_nonzero) := by
    rw [← hprep]
    exact hrep.symm
  have hr := (originalPolytopeNativePiChart_spec γY hY w).2.2.2.2.2
    p hp p.val.rep p.val.rep_nonzero hprep
  refine ⟨(toricFaceProjectiveEmbedding_selected_ne_zero_iff v J _ _ _ _ hzrep _).mpr hr.1, ?_⟩
  intro j
  exact (hr.2 j).trans (toricFaceProjectiveEmbedding_selected_ratio v J _ _ _ _ hzrep _ _).symm

end SGPT.Toric
