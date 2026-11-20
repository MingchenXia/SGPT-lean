import SGPT.Foundations.Schemes.UnframedRegularPowerExactness
import SGPT.Foundations.Schemes.TensorSectionZeroIdeals

/-! Actual original Cartier exactness with an arbitrary DISTINCT original
line twist, including all original opens and nonintegral schemes.
Blueprint: original-twisted-cartier-exact.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite

variable {X : Scheme.{0}} {L B : X.Modules}

/-- An actual regular original section injects tensor multiplication by an
ARBITRARY original test line on EVERY open; no frame on that open is required. -/
theorem originalTensorRightMap_injective (a : LineBundleAtlas L)
    (b : LineBundleAtlas B) (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    (V : X.Opens) : Function.Injective ((sectionTensorRightMap B L s).app V) := by
  let μ := sectionTensorRightMap B L s
  intro t v h
  apply TopCat.Presheaf.IsSheaf.section_ext B.isSheaf
  intro x hx
  obtain ⟨i, hxi⟩ := b.covers x
  obtain ⟨j, hxj⟩ := a.covers x
  let W := V ⊓ (b.opens i ⊓ a.opens j)
  let k : W ⟶ V := homOfLE inf_le_left
  let iB : W ⟶ b.opens i := homOfLE (inf_le_right.trans inf_le_left)
  let iL : W ⟶ a.opens j := homOfLE (inf_le_right.trans inf_le_right)
  let eB := bundleHomRestrictionIso B (SheafOfModules.unit X.ringCatSheaf) iB (b.frame i)
  let eL := bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) iL (a.frame j)
  refine ⟨W, inf_le_left, ⟨hx, hxi, hxj⟩, ?_⟩
  apply sectionTensorRightMap_injective_of_regular s eB eL (𝟙 W)
    (sectionCoefficient_regular_of_evaluation_injective s hinj eL (𝟙 W))
  change μ.app W (B.presheaf.map k.op t) = μ.app W (B.presheaf.map k.op v)
  have ht := PresheafOfModules.naturality_apply μ.val k.op t
  have hv := PresheafOfModules.naturality_apply μ.val k.op v
  exact ht.trans ((congrArg ((bundleTensor B L).presheaf.map k.op) h).trans hv.symm)

/-- The FULL original tensor-quotient kernel equals the actual original
tensor multiplication range on EVERY open. Original regularity makes the
actual affine local preimages unique, so genuine sheaf gluing applies. -/
theorem originalTwistedCartier_exact (a : LineBundleAtlas L) (b : LineBundleAtlas B)
    (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    (V : X.Opens) :
    Function.Exact ((sectionTensorRightMap B L s).app V)
      ((sectionZeroTensorRestriction a s (bundleTensor B L)).app V) := by
  classical
  let C := bundleTensor B L
  let Q := bundleTensor C (sectionZeroPushforwardStructure a s)
  let μ := sectionTensorRightMap B L s
  let α := sectionZeroTensorRestriction a s C
  let J := Σ ij : b.I × a.I,
    {U : X.affineOpens // U.val ≤ V ⊓ (b.opens ij.1 ⊓ a.opens ij.2)}
  let U (j : J) : X.Opens := j.2.val.val
  let k (j : J) : U j ⟶ V := homOfLE (j.2.property.trans inf_le_left)
  have hc : V ≤ iSup U := by
    intro x hx
    obtain ⟨i, hxi⟩ := b.covers x
    obtain ⟨j, hxj⟩ := a.covers x
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ V ⊓ (b.opens i ⊓ a.opens j) from ⟨hx, hxi, hxj⟩)
    exact Opens.mem_iSup.mpr ⟨⟨⟨i, j⟩, ⟨⟨W, hW⟩, hWV⟩⟩, hxW⟩
  have he (j : J) : Function.Exact (μ.app (U j)) (α.app (U j)) := by
    let iB : U j ⟶ b.opens j.1.1 :=
      homOfLE (j.2.property.trans (inf_le_right.trans inf_le_left))
    let iL : U j ⟶ a.opens j.1.2 :=
      homOfLE (j.2.property.trans (inf_le_right.trans inf_le_right))
    exact sectionZeroAffineTensor_exact a s j.2.val
      (bundleHomRestrictionIso B (SheafOfModules.unit X.ringCatSheaf) iB (b.frame j.1.1))
      (bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) iL (a.frame j.1.2))
      (𝟙 (U j))
  intro x
  constructor
  · intro hx
    have hl (j : J) : ∃ t : Γ(B, U j), μ.app (U j) t = C.presheaf.map (k j).op x := by
      apply (he j _).mp
      have hn := PresheafOfModules.naturality_apply α.val (k j).op x
      change α.app (U j) (C.presheaf.map (k j).op x) =
        Q.presheaf.map (k j).op (α.app V x) at hn
      rw [hx, map_zero] at hn
      exact hn
    choose t ht using hl
    have hcompat : TopCat.Presheaf.IsCompatible B.presheaf U t := by
      intro i j
      apply originalTensorRightMap_injective a b s hinj (U i ⊓ U j)
      change μ.val.app (.op (U i ⊓ U j))
        (B.val.map (Opens.infLELeft (U i) (U j)).op (t i)) =
        μ.val.app (.op (U i ⊓ U j))
          (B.val.map (Opens.infLERight (U i) (U j)).op (t j))
      rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
      change C.presheaf.map (Opens.infLELeft (U i) (U j)).op (μ.app (U i) (t i)) =
        C.presheaf.map (Opens.infLERight (U i) (U j)).op (μ.app (U j) (t j))
      rw [ht, ht]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    let S : TopCat.Sheaf AddCommGrpCat X := ⟨B.presheaf, B.isSheaf⟩
    obtain ⟨y, hy, _⟩ := S.existsUnique_gluing' U V k hc t hcompat
    refine ⟨y, ?_⟩
    apply TopCat.Presheaf.IsSheaf.section_ext C.isSheaf
    intro z hz
    obtain ⟨j, hzj⟩ := Opens.mem_iSup.mp (hc hz)
    refine ⟨U j, (k j).le, hzj, ?_⟩
    have hn := PresheafOfModules.naturality_apply μ.val (k j).op y
    change μ.app (U j) (B.presheaf.map (k j).op y) =
      C.presheaf.map (k j).op (μ.app V y) at hn
    rw [hy j, ht j] at hn
    exact hn.symm
  · rintro ⟨y, rfl⟩
    apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
    intro z hz
    obtain ⟨j, hzj⟩ := Opens.mem_iSup.mp (hc hz)
    refine ⟨U j, (k j).le, hzj, ?_⟩
    have hμ := PresheafOfModules.naturality_apply μ.val (k j).op y
    have hn := PresheafOfModules.naturality_apply α.val (k j).op (μ.app V y)
    change α.app (U j) (C.presheaf.map (k j).op (μ.app V y)) =
      Q.presheaf.map (k j).op (α.app V (μ.app V y)) at hn
    rw [map_zero]
    exact hn.symm.trans ((he j _).mpr ⟨B.presheaf.map (k j).op y, hμ⟩)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
