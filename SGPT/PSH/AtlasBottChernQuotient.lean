import SGPT.PSH.AtlasNativeComponentInclusion
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.PSH.AtlasQPSHAddition

/-! The genuine original global Bott--Chern quotient of actual atlas closed
(1,1) forms, modulo ONE globally smooth real dd^c difference. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Exactly ONE globally original-chart-smooth real potential; the equality
holds on EVERY original chart target and uses the existing native dd^c. -/
def OriginalBottChernRel (theta eta : AtlasClosedRealOneOneForm A) : Prop :=
  ∃ h : X → ℝ,A.ChartSmoothOn h univ ∧
    ∀ i z,z∈(A.chart i).target →
      eta.coeff i z=theta.coeff i z+smoothDDC (h ∘ (A.chart i).symm) z

/-- The actual zero smooth potential gives reflexivity. -/
theorem originalBottChernRel_refl (theta : AtlasClosedRealOneOneForm A) :
    OriginalBottChernRel theta theta := by
  refine ⟨fun _ => 0,fun _ => contDiffOn_const,?_⟩
  intro i z hz
  rw [show ((fun _ : X => (0 : ℝ)) ∘ (A.chart i).symm)=(fun _ => 0) from rfl,
    smoothDDC_zero,add_zero]

/-- The SAME global smooth difference negates, as for the native convention. -/
theorem originalBottChernRel_symm {theta eta : AtlasClosedRealOneOneForm A}
    (hrel : OriginalBottChernRel theta eta) : OriginalBottChernRel eta theta := by
  obtain ⟨h,hh,heq⟩ := hrel
  refine ⟨fun x => -h x,fun i => (hh i).neg,?_⟩
  intro i z hz
  have hs : ContDiffOn ℝ ∞ (h ∘ (A.chart i).symm) (A.chart i).target := by
    simpa only [preimage_univ,inter_univ] using hh i
  rw [show ((fun x => -h x) ∘ (A.chart i).symm)=(fun y => -(h ∘ (A.chart i).symm) y) from rfl,
    smoothDDC_neg (A.chart i).open_target hs hz,heq i z hz,add_neg_cancel_right]

/-- Actual global smooth potentials ADD; no componentwise certificate is
substituted for the genuine original global difference. -/
theorem originalBottChernRel_trans {theta eta zeta : AtlasClosedRealOneOneForm A}
    (h1 : OriginalBottChernRel theta eta) (h2 : OriginalBottChernRel eta zeta) :
    OriginalBottChernRel theta zeta := by
  obtain ⟨h,hh,heq⟩ := h1
  obtain ⟨g,hg,geq⟩ := h2
  refine ⟨fun x => h x+g x,fun i => (hh i).add (hg i),?_⟩
  intro i z hz
  have hs : ContDiffOn ℝ ∞ (h ∘ (A.chart i).symm) (A.chart i).target := by
    simpa only [preimage_univ,inter_univ] using hh i
  have gs : ContDiffOn ℝ ∞ (g ∘ (A.chart i).symm) (A.chart i).target := by
    simpa only [preimage_univ,inter_univ] using hg i
  rw [show ((fun x => h x+g x) ∘ (A.chart i).symm)=
      (fun y => (h ∘ (A.chart i).symm) y+(g ∘ (A.chart i).symm) y) from rfl,
    smoothDDC_add (A.chart i).open_target hs gs hz,geq i z hz,heq i z hz,add_assoc]

/-- Actual original smooth dd^c equivalence, independent of any component
class product or positivity output. -/
def originalBottChernSetoid (A : VariableComplexAtlas X) : Setoid (AtlasClosedRealOneOneForm A) where
  r := OriginalBottChernRel
  iseqv := ⟨originalBottChernRel_refl,originalBottChernRel_symm,originalBottChernRel_trans⟩

/-- The genuine original GLOBAL quotient of actual closed smooth forms. -/
def OriginalRealBottChern (A : VariableComplexAtlas X) := Quotient (originalBottChernSetoid A)

/-- The class of an actual original smooth closed real (1,1) form. -/
def originalClass (theta : AtlasClosedRealOneOneForm A) : OriginalRealBottChern A :=
  Quotient.mk _ theta

/-- Exact global smooth dd^c equivalence, retaining the full actual source
meaning of class equality. -/
theorem originalClass_eq_iff (theta eta : AtlasClosedRealOneOneForm A) :
    originalClass theta=originalClass eta ↔ OriginalBottChernRel theta eta := Quotient.eq

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
