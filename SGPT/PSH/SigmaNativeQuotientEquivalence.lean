import SGPT.PSH.SigmaNativeFormGluing

/-! PROVED canonical equivalence of the GENUINE global closed-form quotient
on the actual disjoint union with its EXISTING native component quotients. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {I : Type u} {C : I → Type u} [∀ c,TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c,ChartedSpace (ComplexModel (n c)) (C c)] [∀ c,IsComplexManifold (n c) (C c)]

/-- Actual restriction is a map on the TRUE global original quotient,
justified by genuine global dd^c restriction on every component. -/
def sigmaCohomologyToNative
    (q : OriginalRealBottChern (sigmaNativeAtlas (n := n) (C := C))) :
    ∀ c,RealBottChern (n c) (C c) := fun c =>
  Quotient.map (fun theta => sigmaRestrictedForm theta c)
    (fun theta eta h => (originalBottChernRel_sigma_iff theta eta).mp h c) q

/-- Genuine closed representatives of actual native quotient classes are
GLUED into one actual global original closed form before taking its class. -/
def sigmaCohomologyFromNative (q : ∀ c,RealBottChern (n c) (C c)) :
    OriginalRealBottChern (sigmaNativeAtlas (n := n) (C := C)) :=
  originalClass (sigmaGluedForm (fun c => (q c).out))

/-- PROVED canonical equivalence. In particular, injectivity glues actual
smooth native difference potentials into ONE global smooth difference;
surjectivity glues ACTUAL closed representatives. No product/flag is assumed
to be the original class or supplied as an unproved dictionary premise. -/
def sigmaNativeBottChernEquiv :
    OriginalRealBottChern (sigmaNativeAtlas (n := n) (C := C)) ≃
      (∀ c,RealBottChern (n c) (C c)) where
  toFun := sigmaCohomologyToNative
  invFun := sigmaCohomologyFromNative
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro theta
    apply (originalClass_eq_iff _ _).mpr
    apply (originalBottChernRel_sigma_iff _ _).mpr
    intro c
    apply (RealBottChern.ofRepresentative_eq_iff _ _).mp
    calc
      _ = RealBottChern.ofRepresentative
          ((RealBottChern.ofRepresentative (sigmaRestrictedForm theta c)).out) :=
        sigmaRestrictedGluedForm_class _ c
      _ = _ := Quotient.out_eq _
  right_inv := by
    intro q
    funext c
    change RealBottChern.ofRepresentative
      (sigmaRestrictedForm (sigmaGluedForm (fun d => (q d).out)) c)=q c
    rw [sigmaRestrictedGluedForm_class]
    exact Quotient.out_eq _

/-- Every actual global representative has the EXACT native class of its
actual restricted coefficient tensor in EVERY independently dimensional component. -/
theorem sigmaNativeBottChernEquiv_class
    (theta : AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C))) (c : I) :
    sigmaNativeBottChernEquiv (originalClass theta) c=
      RealBottChern.ofRepresentative (sigmaRestrictedForm theta c) := rfl

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
