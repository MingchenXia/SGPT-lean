import SGPT.Projective.OkounkovOriginalSerrePointUnits

/-! The SAME actual polarization degree precedes ALL auxiliary original lines in genuine ordinary Serre point-unit production.
Blueprint: okounkov-original-uniform-serre-point-units.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalUniformSerrePointUnits
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Projective.NumEq.AlgebraicCurveDegree
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {A : X.Modules}
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)

include aA in
/-- The LITERAL original polarization degree, before ANY auxiliary line, works for EVERY high degree and scheme point. -/
theorem exists_original_ampleTwist_point_units_polarizationPower {R : X.Modules} (aR : LineBundleAtlas R) :
    ∃ B : ℕ, ∀ D : ℕ, B≤D → ∀ c : X,
      ∃ s : Γ(bundleTensor R (bundleTensorPower A (P.power*D)),⊤),
        ∀ b : LineBundleAtlas (bundleTensor R (bundleTensorPower A (P.power*D))),
          c∉(sectionZeroIdealSheaf b s).support := by
  obtain ⟨B,hB⟩ := exists_originalProjectiveTwist_generators P.map aR
  refine ⟨B,?_⟩
  intro D hD c
  obtain ⟨G,hG⟩ := hB D hD
  let Q := (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf
  let aQ := (nativePolynomialPullbackAtlas ℂ P.ambientDimension P.map).tensorPower D
  let aT := pairwiseTensorAtlas aQ aR
  obtain ⟨t,ht⟩ := exists_originalGeneratedSection_avoids_point aT G c
  let eP : bundleTensorPower A (P.power*D) ≅ bundleTensorPower Q D :=
    nativeLineTensorPowerMulIso aA P.power D ≪≫ nativeLineTensorPowerIso P.iso D
  let e : bundleTensor (bundleTensorPower Q D) R ≅ bundleTensor R (bundleTensorPower A (P.power*D)) :=
    bundleTensorIso eP.symm (Iso.refl R) ≪≫ OriginalSerrePointUnits.tensorSwapIso (aA.tensorPower (P.power*D)) aR
  let s := e.hom.val.app (.op ⊤) t
  refine ⟨s,?_⟩
  intro b
  exact (OriginalUnitPowers.sectionZeroSupport_iso aT b e t).symm ▸ ht

include aA P in
/-- ONE actual ample degree precedes ALL auxiliary original lines, then ALL high degrees and original scheme points. -/
theorem exists_uniform_ampleDegree_allLine_serre_point_units :
    ∃ d : ℕ, 0<d ∧ ∀ {R : X.Modules} (_aR : LineBundleAtlas R),
      ∃ B : ℕ, ∀ D : ℕ, B≤D → ∀ c : X,
        ∃ s : Γ(bundleTensor R (bundleTensorPower A (d*D)),⊤),
          ∀ b : LineBundleAtlas (bundleTensor R (bundleTensorPower A (d*D))),
            c∉(sectionZeroIdealSheaf b s).support :=
  ⟨P.power,P.power_pos,fun aR => exists_original_ampleTwist_point_units_polarizationPower f aA P aR⟩
end SGPT.Okounkov.OriginalUniformSerrePointUnits
