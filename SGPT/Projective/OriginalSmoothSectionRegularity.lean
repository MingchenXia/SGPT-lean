import SGPT.Projective.WholeCurveSectionGerms
import SGPT.Foundations.Schemes.RegularZeroEvaluationMono
import SGPT.Foundations.Schemes.TensorSectionZeroIdeals

/-! Actual original all-component section nonvanishing manufactures genuine
all-open regularity in every smooth original dimension.
Blueprint: original-smooth-section-regularity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {L : X.Modules}

/-- Ordinary SAME original section is nonzero on EVERY actual original
clopen irreducible component, in arbitrary original smooth dimension. -/
def OriginalSmoothSectionNonzeroOnComponents (s : Γ(L, ⊤)) : Prop :=
  ∀ C : ↥(irreducibleComponents X),
    originalPulledSection (smoothProjectiveComponentOpen f n E C.val C.property).ι s ≠ 0

/-- The actual ordinary original component condition forces SAME coefficient
germs to be nonzero at EVERY original point, including nonclosed points. -/
theorem originalSmoothSectionFrameGerm_ne_zero (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (hs : OriginalSmoothSectionNonzeroOnComponents f n E s)
    {U : X.Opens} (e : LocalBundleFrame L U) (x : X) (hx : x ∈ U) :
    originalSectionFrameGerm e s x hx ≠ 0 := by
  obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f n E x
  let V := smoothProjectiveComponentOpen f n E C.val C.property
  let := smoothProjective_component_isIntegral f n E C.val C.property
  let p : V := ⟨x, hC⟩
  have hn := originalSectionFrameGerm_ne_zero (matePullbackAtlas V.ι a) (matePullbackFrame V.ι e)
    (originalPulledSection V.ι s) (hs C) p hx
  have hg := originalSectionFrameGerm_pullback V.ι e s p hx
  intro hzero
  apply hn
  exact hg.trans ((congrArg (V.ι.stalkMap p) hzero).trans (map_zero _))

/-- Actual original local domains and SAME nonzero original germs make the
ordinary original coefficient a genuine nonzerodivisor on EVERY framed open. -/
theorem originalSmoothSectionCoefficient_regular (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (hs : OriginalSmoothSectionNonzeroOnComponents f n E s)
    {U V : X.Opens} (e : LocalBundleFrame L U) (i : V ⟶ U) :
    e.coefficients i (L.val.map V.leTop.op s) ∈ nonZeroDivisors Γ(X, V) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro r hr
  apply TopCat.Presheaf.section_ext X.sheaf V r 0
  intro x hx
  let := smoothProjective_allPointStalk_isDomain f n E x
  let d : LocalBundleFrame L V :=
    bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) i e
  have hn : X.presheaf.germ V x hx (e.coefficients i (L.val.map V.leTop.op s)) ≠ 0 := by
    have h := originalSmoothSectionFrameGerm_ne_zero f n E a s hs d x hx
    simpa only [originalSectionFrameGerm, d, bundleHomRestrictionIso_coefficients,
      Category.id_comp] using h
  have hg := congrArg (fun t : Γ(X, V) => X.presheaf.germ V x hx t) hr
  rw [map_mul, map_zero] at hg
  exact ((mul_eq_zero.mp hg).resolve_left hn).trans (map_zero _).symm

/-- Actual all-component section nonvanishing internally produces primitive
ORIGINAL dual-evaluation injectivity on EVERY open, with no regularity premise. -/
theorem originalSmoothSectionZeroEvaluation_injective
    (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (hs : OriginalSmoothSectionNonzeroOnComponents f n E s) (V : X.Opens) :
    Function.Injective (sectionZeroEvaluation L s V) := by
  intro α β h
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (bundleDual L).val.presheaf) (bundleDual L).isSheaf
  intro x hx
  obtain ⟨j, hj⟩ := a.covers x
  let W := V ⊓ a.opens j
  let i : W ⟶ a.opens j := homOfLE inf_le_right
  have hr := originalSmoothSectionCoefficient_regular f n E a s hs (a.frame j) i
  refine ⟨W, inf_le_left, ⟨hx, hj⟩, ?_⟩
  apply ((a.frame j).dual.coefficients i).injective
  apply (mul_cancel_left_mem_nonZeroDivisors hr).mp
  have hh := congrArg (X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op) h
  rw [← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left),
    ← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left)] at hh
  rw [sectionZeroEvaluation_frame s (a.frame j) i,
    sectionZeroEvaluation_frame s (a.frame j) i] at hh
  exact hh

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
