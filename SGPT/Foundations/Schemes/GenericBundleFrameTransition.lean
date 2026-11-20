import SGPT.Foundations.Schemes.SectionRingCenteredFrame

/-!
# Actual generic-frame transitions on arbitrary rational bundle vectors

An integral scheme and genuine local sheaf frames give coefficient readback
on every nonempty subordinate open and a transition formula for EVERY vector
of the actual generic module stalk. At an actual center the transition factor
is the image of the actual local-stalk unit. No global section or global
line-bundle atlas is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {X : Scheme} [IsIntegral X] {L : X.Modules}

/-- The actual generic germ retains the genuine frame coefficient on EVERY
nonempty subordinate open, using the SAME actual generic generator. -/
theorem bundleGenericGerm_subordinate_eq_coefficient_smul_generator
    {U W : X.Opens} [Nonempty U] [Nonempty W]
    (e : LocalBundleFrame L U) (i : W ⟶ U) (s : bundleSections L W) :
    bundleGenericGerm L W s =
      X.germToFunctionField W (e.coefficients i s) • genericFrameGenerator e := by
  let m₀ := (localFrameCoefficients e).symm 1
  have h₀ : e.coefficients (𝟙 U) m₀ = 1 :=
    (localFrameCoefficients e).apply_symm_apply 1
  have hi := e.coefficients_restrict (𝟙 U) i m₀
  rw [Category.comp_id, h₀, map_one] at hi
  have hs : s = e.coefficients i s • L.val.map i.op m₀ := by
    apply (e.coefficients i).injective
    rw [map_smul, hi]
    exact (mul_one _).symm
  have hg := congrArg (bundleGenericGerm L W) hs
  rw [(bundleGenericGerm L W).map_smulₛₗ] at hg
  have hr : bundleGenericGerm L W (L.val.map i.op m₀) = genericFrameGenerator e :=
    L.presheaf.germ_res_apply i (genericPoint X) (genericPoint_mem_nonempty_open W) m₀
  rw [hr] at hg
  exact hg

/-- Actual generic-frame coefficient readback on every nonempty open
subordinate to the genuine local frame. -/
theorem genericBundleFiberFrame_germ_subordinate
    {U W : X.Opens} [Nonempty U] [Nonempty W]
    (e : LocalBundleFrame L U) (i : W ⟶ U) (s : bundleSections L W) :
    genericBundleFiberFrame e (bundleGenericGerm L W s) =
      X.germToFunctionField W (e.coefficients i s) := by
  rw [bundleGenericGerm_subordinate_eq_coefficient_smul_generator e i s,
    ← genericBundleFiberFrame_symm_apply]
  exact (genericBundleFiberFrame e).apply_symm_apply _

private theorem genericBundleFiberFrame_generator_transition
    {U V W : X.Opens} [Nonempty U] [Nonempty V] [Nonempty W]
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) :
    genericBundleFiberFrame f (genericFrameGenerator e) =
      X.germToFunctionField W
        (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) := by
  let m₀ := (localFrameCoefficients e).symm 1
  have h₀ : e.coefficients (𝟙 U) m₀ = 1 :=
    (localFrameCoefficients e).apply_symm_apply 1
  have hi := e.coefficients_restrict (𝟙 U) i m₀
  rw [Category.comp_id, h₀, map_one] at hi
  have ht := localBundleFrameTransition_coefficients e f i j (L.val.map i.op m₀)
  rw [hi, mul_one] at ht
  have hr : bundleGenericGerm L W (L.val.map i.op m₀) = genericFrameGenerator e :=
    L.presheaf.germ_res_apply i (genericPoint X) (genericPoint_mem_nonempty_open W) m₀
  rw [← hr, genericBundleFiberFrame_germ_subordinate f j]
  exact congrArg (X.germToFunctionField W) ht

/-- Every vector in the ACTUAL generic module stalk has the actual frame
transition coefficient on a genuine common nonempty open. No global-section
representation of the vector is assumed. -/
theorem genericBundleFiberFrame_transition
    {U V W : X.Opens} [Nonempty U] [Nonempty V] [Nonempty W]
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    (τ : genericBundleFiber L) :
    genericBundleFiberFrame f τ =
      X.germToFunctionField W
        (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) *
        genericBundleFiberFrame e τ := by
  calc
    genericBundleFiberFrame f τ =
        genericBundleFiberFrame f
          ((genericBundleFiberFrame e).symm (genericBundleFiberFrame e τ)) :=
      congrArg (genericBundleFiberFrame f) ((genericBundleFiberFrame e).symm_apply_apply τ).symm
    _ = genericBundleFiberFrame e τ * genericBundleFiberFrame f (genericFrameGenerator e) := by
      rw [genericBundleFiberFrame_symm_apply, (genericBundleFiberFrame f).map_smul]
      rfl
    _ = _ := by
      rw [genericBundleFiberFrame_generator_transition e f i j]
      exact mul_comm _ _

/-- At an actual center, the transition coefficient for EVERY generic
vector is literally the image of the actual LOCAL-stalk transition unit. -/
theorem genericBundleFiberFrame_transitionAtCenter
    {U V : X.Opens} (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (x : X) (hx : x ∈ U) (hy : x ∈ V) (τ : genericBundleFiber L) :
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    letI : Nonempty V := ⟨⟨x, hy⟩⟩
    genericBundleFiberFrame f τ =
      algebraMap (X.presheaf.stalk x) X.functionField
        (localBundleFrameTransitionAtCenter e f x hx hy : X.presheaf.stalk x) *
        genericBundleFiberFrame e τ := by
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : Nonempty V := ⟨⟨x, hy⟩⟩
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
  have ht := genericBundleFiberFrame_transition e f
    (homOfLE inf_le_left : U ⊓ V ⟶ U) (homOfLE inf_le_right : U ⊓ V ⟶ V) τ
  rw [← localBundleFrameTransitionAtCenter_functionField e f x hx hy] at ht
  exact ht

end
end SGPT.Foundations.Schemes
