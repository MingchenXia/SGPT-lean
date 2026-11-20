import SGPT.PSH.AtlasNefPullback

/-! The literal actual global smooth-potential nef condition DESCENDS to
the genuine original Bott--Chern quotient; fixed-model convention is exact. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- A TRUE global smooth dd^c difference changes the actual nef epsilon
potential by the SAME global smooth difference; no positivity flag is added. -/
theorem originalNefWithRespectTo_of_relation {theta eta : AtlasClosedRealOneOneForm A}
    (omega : AtlasClosedRealOneOneForm A) (hrel : OriginalBottChernRel theta eta)
    (hnef : OriginalNefWithRespectTo omega theta) : OriginalNefWithRespectTo omega eta := by
  obtain ⟨g,hg,heq⟩ := hrel
  intro epsilon hepsilon
  obtain ⟨h,hh,hpos⟩ := hnef epsilon hepsilon
  refine ⟨fun x => h x-g x,fun i => (hh i).sub (hg i),?_⟩
  intro i z hz
  have hs : ContDiffOn ℝ ∞ (h ∘ (A.chart i).symm) (A.chart i).target := by
    simpa only [preimage_univ,inter_univ] using hh i
  have gs : ContDiffOn ℝ ∞ (g ∘ (A.chart i).symm) (A.chart i).target := by
    simpa only [preimage_univ,inter_univ] using hg i
  rw [heq i z hz]
  change CoefficientSemipositive ((theta.coeff i z+smoothDDC (g ∘ (A.chart i).symm) z)+
    smoothDDC (fun y => (h ∘ (A.chart i).symm) y-(g ∘ (A.chart i).symm) y) z+epsilon • omega.coeff i z)
  rw [smoothDDC_sub (A.chart i).open_target hs gs hz]
  convert hpos i z hz using 1
  congr 1
  abel

/-- EXACT independence of actual global smooth-dd^c representative. -/
theorem originalNefWithRespectTo_relation_iff {theta eta : AtlasClosedRealOneOneForm A}
    (omega : AtlasClosedRealOneOneForm A) (hrel : OriginalBottChernRel theta eta) :
    OriginalNefWithRespectTo omega theta ↔ OriginalNefWithRespectTo omega eta :=
  ⟨originalNefWithRespectTo_of_relation omega hrel,
    originalNefWithRespectTo_of_relation omega (originalBottChernRel_symm hrel)⟩

/-- GENUINE source class nefness on the ACTUAL global quotient, obtained
from the literal one-global-smooth-potential criterion by proved invariance. -/
def OriginalClassNefWithRespectTo (omega : AtlasClosedRealOneOneForm A)
    (alpha : OriginalRealBottChern A) : Prop :=
  Quotient.lift (s := originalBottChernSetoid A) (OriginalNefWithRespectTo omega)
    (fun _ _ h => propext (originalNefWithRespectTo_relation_iff omega h)) alpha

/-- Actual original representatives read the EXACT global nef criterion. -/
theorem originalClassNefWithRespectTo_originalClass (omega theta : AtlasClosedRealOneOneForm A) :
    OriginalClassNefWithRespectTo omega (originalClass theta) ↔ OriginalNefWithRespectTo omega theta := Iff.rfl

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original global nef criterion is EXACTLY the accepted native
smooth-potential convention, in every natural dimension and BOTH directions. -/
theorem originalNef_fixedModel_iff (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M) :
    OriginalNefWithRespectTo (nativeClosedFormToAtlas omega.form) (nativeClosedFormToAtlas theta) ↔
      NefWithRespectTo omega theta := by
  constructor
  · intro hnef epsilon hepsilon
    obtain ⟨h,hh,hpos⟩ := hnef epsilon hepsilon
    refine ⟨h,?_,hpos⟩
    intro e
    have hs := hh e
    change ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ univ) at hs
    rw [Set.inter_univ] at hs
    exact hs
  · intro hnef epsilon hepsilon
    obtain ⟨h,hh,hpos⟩ := hnef epsilon hepsilon
    refine ⟨h,?_,hpos⟩
    intro e
    change ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ univ)
    rw [Set.inter_univ]
    exact hh e

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
