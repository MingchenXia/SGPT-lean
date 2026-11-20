import SGPT.Projective.OkounkovOriginalAmpleUnitSections
import SGPT.Foundations.Schemes.SectionPowerZeroIdeals
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison

/-! True original support units under actual sheaf isomorphisms and literal tensor powers.
Blueprint: okounkov-original-unit-powers.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalUnitPowers
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Opposite TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree SGPT.Okounkov.OriginalAmpleUnits

/-- Actual original sheaf isomorphism preserves the ENTIRE ordinary original zero-support. -/
theorem sectionZeroSupport_iso {X : Scheme.{0}} {P Q : X.Modules}
    (a : LineBundleAtlas P) (b : LineBundleAtlas Q) (e : P ≅ Q) (s : Γ(P,⊤)) :
    (sectionZeroIdealSheaf b (e.hom.val.app (.op ⊤) s)).support = (sectionZeroIdealSheaf a s).support := by
  ext c
  obtain ⟨i,hi⟩ := b.covers c
  obtain ⟨W,hW,hcW,hWi⟩ := exists_isAffineOpen_mem_and_subset hi
  let j : W ⟶ b.opens i := homOfLE hWi
  let d := b.frame i
  have hcoef : (transportFrame e d).coefficients j (P.val.map W.leTop.op s) =
      d.coefficients j (Q.val.map W.leTop.op (e.hom.val.app (.op ⊤) s)) := by
    rw [transportFrame_coefficients,PresheafOfModules.naturality_apply e.hom.val W.leTop.op s]
  have hS := originalZero_support_iff_not_basicOpen a s ⟨W,hW⟩ (transportFrame e d) j c hcW
  have hT := originalZero_support_iff_not_basicOpen b (e.hom.val.app (.op ⊤) s) ⟨W,hW⟩ d j c hcW
  exact hT.trans ((Iff.of_eq (congrArg (fun r : Γ(X,W) => c∉X.basicOpen r) hcoef.symm)).trans hS.symm)

/-- ALL genuine original section powers avoid the SAME actual original point, including the degree-zero unit. -/
theorem not_mem_zeroSupport_tensorPower {X : Scheme.{0}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L,⊤)) (c : X)
    (hc : c∉(sectionZeroIdealSheaf a s).support) (m : ℕ) :
    c∉(sectionZeroIdealSheaf (a.tensorPower m) (bundleGlobalSectionTensorPower L s m)).support := by
  rw [sectionZeroIdealSheaf_globalSectionTensorPower]
  cases m with
  | zero =>
    change c∉(∅:Set X)
    exact fun h => h
  | succ m => simpa only [Scheme.IdealSheafData.support_pow_succ] using hc

/-- ONE genuine ample power gives ordinary point-avoiding sections in EVERY literal original multiple power. -/
theorem exists_fixed_ample_power_units_all_multiples
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {A : X.Modules}
    (a : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A) :
    ∃ d : ℕ, 0<d ∧ ∀ c : X, ∀ m : ℕ, ∃ t : Γ(bundleTensorPower A (d*m),⊤),
      ∀ b : LineBundleAtlas (bundleTensorPower A (d*m)), c∉(sectionZeroIdealSheaf b t).support := by
  obtain ⟨d,hd,hunit⟩ := exists_fixed_positive_power_section_avoids_every_point f P
  refine ⟨d,hd,?_⟩
  intro c m
  obtain ⟨s,hs⟩ := hunit c
  let B := bundleTensorPower A d
  let aB := a.tensorPower d
  let σ := bundleGlobalSectionTensorPower B s m
  let e : bundleTensorPower A (d*m) ≅ bundleTensorPower B m := nativeLineTensorPowerMulIso a d m
  let t : Γ(bundleTensorPower A (d*m),⊤) := e.inv.val.app (.op ⊤) σ
  have hσ : c∉(sectionZeroIdealSheaf (aB.tensorPower m) σ).support :=
    not_mem_zeroSupport_tensorPower aB s c (hs aB) m
  refine ⟨t,?_⟩
  intro b
  have heq := sectionZeroSupport_iso (aB.tensorPower m) b e.symm σ
  exact heq.symm ▸ hσ
end SGPT.Okounkov.OriginalUnitPowers
