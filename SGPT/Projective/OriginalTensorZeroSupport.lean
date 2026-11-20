import SGPT.Projective.OriginalTensorSectionLength

/-! Actual ENTIRE original tensor zero support union and genuine original
ordinary nonzero tensor section; no analytic/period equality input.
Blueprint: original-tensor-zero-support.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
variable {X : Scheme.{0}} {L N : X.Modules}

/-- Genuine original affine principal-zero support calculation in ANY original frame. -/
theorem originalZero_support_iff_not_basicOpen (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (V : X.affineOpens) {U : X.Opens} (e : LocalBundleFrame L U) (j : V.val ⟶ U)
    (x : X) (hx : x ∈ V.val) :
    x ∈ (sectionZeroIdealSheaf a s).support ↔
      x ∉ X.basicOpen (e.coefficients j (L.val.map V.val.leTop.op s)) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hx]
  change x ∈ X.zeroLocus (U := V.val) (sectionZeroIdeal L s V.val : Set Γ(X, V.val)) ↔ _
  rw [sectionZeroIdeal_eq_span_frame s e j, X.zeroLocus_span, X.zeroLocus_singleton]
  rfl

/-- ENTIRE actual original zero supports union for literal actual original tensor section. -/
theorem originalTensorSection_zeroSupport_union
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (c : LineBundleAtlas (bundleTensor L N))
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) :
    ((sectionZeroIdealSheaf c (tensorSection L N ⊤ s t)).support : Set X) =
      ((sectionZeroIdealSheaf a s).support : Set X) ∪ ((sectionZeroIdealSheaf b t).support : Set X) := by
  ext x
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := b.covers x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ a.opens i ⊓ b.opens j from ⟨hi, hj⟩)
  let e : LocalBundleFrame L V := bundleHomRestrictionIso L
    (SheafOfModules.unit X.ringCatSheaf) (homOfLE (hVU.trans inf_le_left)) (a.frame i)
  let d : LocalBundleFrame N V := bundleHomRestrictionIso N
    (SheafOfModules.unit X.ringCatSheaf) (homOfLE (hVU.trans inf_le_right)) (b.frame j)
  let VV : X.affineOpens := ⟨V, hV⟩
  have hT := originalZero_support_iff_not_basicOpen (L := bundleTensor L N)
    c (tensorSection L N ⊤ s t) VV (e.tensor d) (𝟙 V) x hxV
  have hS := originalZero_support_iff_not_basicOpen a s VV e (𝟙 V) x hxV
  have hN := originalZero_support_iff_not_basicOpen b t VV d (𝟙 V) x hxV
  have hp : (e.tensor d).coefficients (𝟙 V)
      ((bundleTensor L N).val.map V.leTop.op (tensorSection L N ⊤ s t)) =
      e.coefficients (𝟙 V) (L.val.map V.leTop.op s) * d.coefficients (𝟙 V) (N.val.map V.leTop.op t) := by
    rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients]
  have hT' := hT.trans (Iff.of_eq (congrArg (fun r : Γ(X, V) => x ∉ X.basicOpen r) hp))
  have hbasic : x ∉ X.basicOpen
      (e.coefficients (𝟙 V) (L.val.map V.leTop.op s) * d.coefficients (𝟙 V) (N.val.map V.leTop.op t)) ↔
      x ∉ X.basicOpen (e.coefficients (𝟙 V) (L.val.map V.leTop.op s)) ∨
      x ∉ X.basicOpen (d.coefficients (𝟙 V) (N.val.map V.leTop.op t)) := by
    rw [X.basicOpen_mul]
    exact not_and_or
  exact hT'.trans (hbasic.trans (hS.symm.or hN.symm))

/-- Literal original ordinary tensor of TWO nonzero original sections is nonzero, by SAME original stalk. -/
theorem originalTensorSection_ne_zero [IsIntegral X]
    (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (t : Γ(N, ⊤)) (ht : t ≠ 0) :
    tensorSection L N ⊤ s t ≠ 0 := by
  classical
  let x : X := Classical.arbitrary X
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := b.covers x
  let U := a.opens i ⊓ b.opens j
  have hx : x ∈ U := ⟨hi, hj⟩
  let e : LocalBundleFrame L U := bundleHomRestrictionIso L
    (SheafOfModules.unit X.ringCatSheaf) (Opens.infLELeft _ _) (a.frame i)
  let d : LocalBundleFrame N U := bundleHomRestrictionIso N
    (SheafOfModules.unit X.ringCatSheaf) (Opens.infLERight _ _) (b.frame j)
  have hn := mul_ne_zero (originalSectionFrameGerm_ne_zero a e s hs x hx)
    (originalSectionFrameGerm_ne_zero b d t ht x hx)
  intro hzero
  apply hn
  rw [← originalTensorSectionFrameGerm_mul, hzero]
  simp only [originalSectionFrameGerm, map_zero]

end SGPT.Projective.NumEq.AlgebraicCurveDegree
