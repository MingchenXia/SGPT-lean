import SGPT.Foundations.Schemes.DiscreteSingletonStalkGeometry
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison

/-! Actual singleton frames and true matching-frame descent produce a global
trivialization of any genuine line atlas on a discrete scheme. -/

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual line atlas on a discrete scheme PRODUCES a global sheaf
isomorphism to the ORIGINAL structure module, including empty schemes. -/
def LineBundleAtlas.discreteTrivialization {X : Scheme.{u}} [DiscreteTopology X]
    {L : X.Modules} (a : LineBundleAtlas L) : L ≅ SheafOfModules.unit X.ringCatSheaf := by
  let U := discreteSingletonOpen X
  let k (x : X) : U x ≤ a.opens (a.covers x).choose := by
    intro z hz
    have hzx : z = x := hz
    simpa only [hzx] using (a.covers x).choose_spec
  let E (x : X) : LocalBundleFrame L (U x) :=
    bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
      (homOfLE (k x)) (a.frame (a.covers x).choose)
  let Q (x : X) : LocalBundleFrame (SheafOfModules.unit X.ringCatSheaf) (U x) := Iso.refl _
  apply nativeMatchingBundleFrameIso L (SheafOfModules.unit X.ringCatSheaf) U
    (fun x ↦ ⟨x, Set.mem_singleton x⟩) E Q
  intro x y W h j
  by_cases hxy : x = y
  · subst y
    have hj : j = h := Subsingleton.elim _ _
    subst j
    simp only [localBundleFrameTransition, sectionFrameTransition_self]
  · have hW : W = ⊥ := by
      apply bot_unique
      intro z hz
      have hzx : z = x := h.le hz
      have hzy : z = y := j.le hz
      exact (hxy (hzx.symm.trans hzy)).elim
    let hR : Subsingleton (X.sheaf.obj.obj (op W)) := CommRingCat.subsingleton_of_isTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty X.sheaf hW)
    apply Units.ext
    exact hR.elim _ _

end
end SGPT.Foundations.Schemes
