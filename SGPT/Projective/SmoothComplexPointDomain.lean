import SGPT.Okounkov.SchemeNativeStalkFlatness
import SGPT.NAPotential.GAGAMult2Faithful
import Mathlib.RingTheory.LocalProperties.Reduced

/-! Actual original smooth complex-point stalks and affine maximal localizations
are domains WITHOUT original whole-scheme integrality. Blueprint:
smooth-complex-point-domain.tex; whole route algebraic-curve-components-plan.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance componentPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance componentPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance componentPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

include n in
/-- Faithfully flat actual native stalk map descends the actual DOMAIN structure;
no whole original integrality or chosen component is input. -/
theorem smoothComplexPointStalk_isDomain (p : SchemeComplexPoint f) :
    IsDomain (X.presheaf.stalk (schemeComplexPointImage f p)) :=
  Function.Injective.isDomain (schemeNativeStalkGerm f n p)
    (schemeNativeStalkGerm_faithfullyFlat f n p).injective

include f n in
/-- EVERY actual maximal localization of the SAME original affine ring is a domain. -/
theorem smoothAffineMaximalLocalization_isDomain {U : X.Opens} (hU : IsAffineOpen U)
    (P : Ideal Γ(X, U)) (hP : P.IsMaximal) : IsDomain (Localization.AtPrime P) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : LocallyOfFiniteType f := inferInstance
  let : P.IsPrime := hP.isPrime
  obtain ⟨p, hp⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P hP
  have hdom : IsDomain (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) := by
    rw [← hp]
    exact smoothComplexPointStalk_isDomain f n p
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hU.fromSpec ⟨P, hP.isPrime⟩, fromSpec_mem hU _⟩ : U)
  let := hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (fromSpec_mem hU _)
  let e := IsLocalization.algEquiv P.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) (Localization.AtPrime P)
  exact Function.Injective.isDomain e.symm e.symm.injective

include f n in
/-- Every original affine smooth section ring is reduced, even when disconnected/empty. -/
theorem smoothAffineSections_isReduced {U : X.Opens} (hU : IsAffineOpen U) : _root_.IsReduced Γ(X, U) := by
  apply isReduced_ofLocalizationMaximal
  intro P hP
  let := smoothAffineMaximalLocalization_isDomain f n hU P hP
  infer_instance

include f n in
/-- The ENTIRE actual original smooth scheme is reduced, without selecting
or assuming any integral component, including the empty original scheme. -/
theorem smoothScheme_isReduced : AlgebraicGeometry.IsReduced X := by
  constructor
  intro U
  constructor
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  let i : V ⟶ U := homOfLE hVU
  let := smoothAffineSections_isReduced f n hV
  have hres : X.presheaf.map i.op s = 0 :=
    (hs.map (X.presheaf.map i.op).hom).eq_zero
  rw [← X.presheaf.germ_res i x hxV, CommRingCat.comp_apply, hres, map_zero]
  simp

end SGPT.Projective.NumEq.AlgebraicCurveDegree
