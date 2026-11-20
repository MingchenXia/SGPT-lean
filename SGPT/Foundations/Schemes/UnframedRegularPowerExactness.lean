import SGPT.Foundations.Schemes.UnframedCartierQuotientSurjectivity
import SGPT.Foundations.Schemes.RegularSectionCechEuler
import SGPT.Foundations.Schemes.RegularZeroEvaluationMono

/-! Regularity of the ORIGINAL evaluation gives injective power maps and
actual middle exactness on every open by unique gluing of local preimages. -/

universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {L : X.Modules}

/-- Injectivity of ORIGINAL dual evaluation gives actual nonzerodivisor
coefficients on every genuine subordinate frame, including zero rings. -/
theorem sectionCoefficient_regular_of_evaluation_injective (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    {U V : X.Opens} (e : LocalBundleFrame L U) (i : V ⟶ U) :
    e.coefficients i (L.presheaf.map V.leTop.op s) ∈ nonZeroDivisors Γ(X, V) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro r hr
  have he : sectionZeroEvaluation L s V ((e.dual.coefficients i).symm r) =
      sectionZeroEvaluation L s V ((e.dual.coefficients i).symm 0) := by
    rw [sectionZeroEvaluation_frame s e i, sectionZeroEvaluation_frame s e i,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, mul_zero]
    exact hr
  exact (e.dual.coefficients i).symm.injective (hinj V he)

/-- Genuine all-open evaluation injectivity produces injectivity of literal
successor-power multiplication on EVERY ORIGINAL open, without a frame there. -/
theorem sectionPowerMultiplication_injective_unframed (a : LineBundleAtlas L)
    (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    (m : ℕ) (V : X.Opens) :
    Function.Injective ((sectionPowerMultiplication L s m).app V) := by
  let μ := sectionPowerMultiplication L s m
  intro t v h
  apply TopCat.Presheaf.IsSheaf.section_ext (bundleTensorPower L m).isSheaf
  intro x hx
  obtain ⟨j, hxj⟩ := a.covers x
  let W := V ⊓ a.opens j
  let i : W ⟶ a.opens j := homOfLE inf_le_right
  let k : W ⟶ V := homOfLE inf_le_left
  refine ⟨W, inf_le_left, ⟨hx, hxj⟩, ?_⟩
  apply sectionTensorRightMap_injective_of_regular s ((a.frame j).tensorPower m)
    (a.frame j) i (sectionCoefficient_regular_of_evaluation_injective s hinj (a.frame j) i)
  change μ.app W ((bundleTensorPower L m).presheaf.map k.op t) =
    μ.app W ((bundleTensorPower L m).presheaf.map k.op v)
  have ht := PresheafOfModules.naturality_apply μ.val k.op t
  have hv := PresheafOfModules.naturality_apply μ.val k.op v
  exact ht.trans ((congrArg ((bundleTensorPower L (m + 1)).presheaf.map k.op) h).trans hv.symm)

/-- The actual middle kernel is the ORIGINAL power-map range on EVERY open.
Regularity makes local affine preimages unique, so genuine sheaf gluing applies. -/
theorem sectionZeroPower_exact_unframed (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (hinj : ∀ V : X.Opens, Function.Injective (sectionZeroEvaluation L s V))
    (m : ℕ) (V : X.Opens) :
    Function.Exact ((sectionPowerMultiplication L s m).app V)
      ((sectionZeroTensorRestriction a s (bundleTensorPower L (m + 1))).app V) := by
  classical
  let B := bundleTensorPower L m
  let C := bundleTensorPower L (m + 1)
  let Q := bundleTensor C (sectionZeroPushforwardStructure a s)
  let μ := sectionPowerMultiplication L s m
  let α := sectionZeroTensorRestriction a s C
  let J := Σ j : a.I, {U : X.affineOpens // U.val ≤ V ⊓ a.opens j}
  let U (j : J) : X.Opens := j.2.val.val
  let k (j : J) : U j ⟶ V := homOfLE (j.2.property.trans inf_le_left)
  have hc : V ≤ iSup U := by
    intro x hx
    obtain ⟨j, hxj⟩ := a.covers x
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ V ⊓ a.opens j from ⟨hx, hxj⟩)
    exact Opens.mem_iSup.mpr ⟨⟨j, ⟨⟨W, hW⟩, hWV⟩⟩, hxW⟩
  have he (j : J) : Function.Exact (μ.app (U j)) (α.app (U j)) :=
    sectionZeroAffineTensor_exact a s j.2.val ((a.frame j.1).tensorPower m)
      (a.frame j.1) (homOfLE (j.2.property.trans inf_le_right))
  intro x
  constructor
  · intro hx
    have hl (j : J) : ∃ t : Γ(B, U j),
        μ.app (U j) t = C.presheaf.map (k j).op x := by
      apply (he j _).mp
      have hn := PresheafOfModules.naturality_apply α.val (k j).op x
      change α.app (U j) (C.presheaf.map (k j).op x) =
        Q.presheaf.map (k j).op (α.app V x) at hn
      rw [hx, map_zero] at hn
      exact hn
    choose t ht using hl
    have hcompat : TopCat.Presheaf.IsCompatible B.presheaf U t := by
      intro i j
      apply sectionPowerMultiplication_injective_unframed a s hinj m (U i ⊓ U j)
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

end
end SGPT.Foundations.Schemes
