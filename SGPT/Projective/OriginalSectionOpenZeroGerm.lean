import SGPT.Projective.OriginalOpenSectionZero

/-! True zero original pulled sections force the SAME original parent
coefficient germs to be zero. Blueprint: original-section-open-zero-germ.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} {M : X.Modules}

/-- The actual original open-zero section, in ANY actual original frame, has SAME zero parent germ. -/
theorem originalSection_coefficientGerm_eq_zero_of_open_pull_zero
    (U : X.Opens) (s : Γ(M, ⊤)) (hs : originalPulledSection U.ι s = 0)
    {V : X.Opens} (α : LocalBundleFrame M V) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    X.presheaf.germ V x hxV (α.coefficients (𝟙 V) (M.val.map V.leTop.op s)) = 0 := by
  let W := U.ι ⁻¹ᵁ V
  let A := U.ι ''ᵁ W
  let j : A ⟶ V := homOfLE (show A ≤ V from by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hz)
  have hc := originalOpenPulledSection_coefficients s α W (𝟙 W)
  have hz : α.coefficients j (M.val.map A.leTop.op s) = 0 := by
    simpa only [hs, map_zero] using hc.symm
  have hr := α.coefficients_restrict (𝟙 V) j (M.val.map V.leTop.op s)
  have hres : M.val.map j.op (M.val.map V.leTop.op s) = M.val.map A.leTop.op s := by
    rw [← M.val.map_comp_apply]
    rfl
  rw [hres] at hr
  have hrzero : X.presheaf.map j.op (α.coefficients (𝟙 V) (M.val.map V.leTop.op s)) = 0 :=
    hr.symm.trans hz
  have hxA : x ∈ A := ⟨⟨x, hxU⟩, hxV, rfl⟩
  have hg := congrArg (fun r : Γ(X, A) => X.presheaf.germ A x hxA r) hrzero
  have he : X.presheaf.germ A x hxA
      (X.presheaf.map j.op (α.coefficients (𝟙 V) (M.val.map V.leTop.op s))) =
        X.presheaf.germ V x hxV (α.coefficients (𝟙 V) (M.val.map V.leTop.op s)) :=
    congrArg (fun k : Γ(X, V) ⟶ X.presheaf.stalk x =>
      k (α.coefficients (𝟙 V) (M.val.map V.leTop.op s))) (X.presheaf.germ_res j x hxA)
  exact he.symm.trans (hg.trans (map_zero _))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
