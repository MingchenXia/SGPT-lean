import SGPT.PSH.PrimeNov16OriginalPrimePresentation
import SGPT.PSH.PrimeNov16OriginalStrictComposition
import SGPT.PSH.PrimeNov16OriginalSmoothCommonResolution
import SGPT.PSH.PrimeNov16OriginalCancellation

/-! Genuine SINGLE intrinsic original common-resolution equivalence/quotient.
No native representative fields or generated relation. Full blueprint first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalPrimeQuotient
open SGPT.Unibranch SourceReducedComplexSpace
open PrimeNov16OriginalPrimePresentation PrimeNov16OriginalStrictTransform

variable {X : SourceReducedComplexSpace}

theorem commonResolutionRelation_trans {p q r : PrimePresentation X}
    (hpq : commonResolutionRelation p q) (hqr : commonResolutionRelation q r) :
    commonResolutionRelation p r := by
  obtain ⟨h₀⟩ := hpq
  obtain ⟨h₁⟩ := hqr
  obtain ⟨S, hS, K₀, K₁, hK₀, hK₁, hHsquare, hHres⟩ :=
    PrimeNov16OriginalSmoothCommonResolution.exists_actual_original_smooth_common_resolution
      h₀.smooth h₁.smooth (h₀.left ≫ p.projection) (h₁.left ≫ q.projection)
      h₀.resolution.2 h₁.resolution.2
  have ha : (K₀ ≫ h₀.right) ≫ q.projection = K₀ ≫ (h₀.left ≫ p.projection) :=
    (Category.assoc _ _ _).trans (congrArg (fun F : h₀.model ⟶ X => K₀ ≫ F) h₀.over_base.symm)
  have hb : (K₁ ≫ h₁.left) ≫ q.projection = K₁ ≫ (h₁.left ≫ q.projection) := Category.assoc _ _ _
  have hmidcomp : (K₀ ≫ h₀.right) ≫ q.projection = (K₁ ≫ h₁.left) ≫ q.projection :=
    ha.trans (hHsquare.trans hb.symm)
  have hmidactual : IsProperBimeromorphic ((K₀ ≫ h₀.right) ≫ q.projection) :=
    Eq.mp (congrArg IsProperBimeromorphic (ha.trans hHsquare).symm) hHres.2
  have hmiddle : K₀ ≫ h₀.right = K₁ ≫ h₁.left :=
    PrimeNov16OriginalCancellation.eq_of_actual_common_projection q.projection q.resolution.2
      (K₀ ≫ h₀.right) (K₁ ≫ h₁.left) hmidcomp hmidactual
  have hleft : IsProperBimeromorphic (K₀ ≫ h₀.left) :=
    PrimeNov16OriginalSmoothComposition.isProperBimeromorphic_comp hS h₀.smooth p.smooth
      K₀ h₀.left hK₀ h₀.left_modification
  have hright : IsProperBimeromorphic (K₁ ≫ h₁.right) :=
    PrimeNov16OriginalSmoothComposition.isProperBimeromorphic_comp hS h₁.smooth r.smooth
      K₁ h₁.right hK₁ h₁.right_modification
  have hleftH : (K₀ ≫ h₀.left) ≫ p.projection = K₁ ≫ (h₁.left ≫ q.projection) :=
    (Category.assoc _ _ _).trans hHsquare
  have hfull : (K₀ ≫ h₀.left) ≫ p.projection = (K₁ ≫ h₁.right) ≫ r.projection :=
    hleftH.trans ((congrArg (fun F : h₁.model ⟶ X => K₁ ≫ F) h₁.over_base).trans
      (Category.assoc _ _ _).symm)
  have hres : IsResolution ((K₀ ≫ h₀.left) ≫ p.projection) :=
    Eq.mp (congrArg IsResolution hleftH.symm) hHres
  obtain ⟨cp, hcp⟩ := exists_component_containing_divisor p
  obtain ⟨cq, hcq⟩ := exists_component_containing_divisor q
  obtain ⟨cr, hcr⟩ := exists_component_containing_divisor r
  have h₀p := PrimeNov16OriginalStrictComposition.original_strictTransform_comp_of_subset_component
    hS h₀.smooth p.smooth K₀ h₀.left hK₀ h₀.left_modification p.divisor cp hcp
  have h₀q := PrimeNov16OriginalStrictComposition.original_strictTransform_comp_of_subset_component
    hS h₀.smooth q.smooth K₀ h₀.right hK₀ h₀.right_modification q.divisor cq hcq
  have h₁q := PrimeNov16OriginalStrictComposition.original_strictTransform_comp_of_subset_component
    hS h₁.smooth q.smooth K₁ h₁.left hK₁ h₁.left_modification q.divisor cq hcq
  have h₁r := PrimeNov16OriginalStrictComposition.original_strictTransform_comp_of_subset_component
    hS h₁.smooth r.smooth K₁ h₁.right hK₁ h₁.right_modification r.divisor cr hcr
  refine ⟨⟨S, hS, K₀ ≫ h₀.left, K₁ ≫ h₁.right, hleft, hright, hfull, hres, ?_⟩⟩
  calc
    _ = originalStrictTransform K₀ (originalStrictTransform h₀.left p.divisor) := h₀p
    _ = originalStrictTransform K₀ (originalStrictTransform h₀.right q.divisor) :=
      congrArg (originalStrictTransform K₀) h₀.strict_equal
    _ = originalStrictTransform (K₀ ≫ h₀.right) q.divisor := h₀q.symm
    _ = originalStrictTransform (K₁ ≫ h₁.left) q.divisor :=
      congrArg (fun F : S ⟶ q.model => originalStrictTransform F q.divisor) hmiddle
    _ = originalStrictTransform K₁ (originalStrictTransform h₁.left q.divisor) := h₁q
    _ = originalStrictTransform K₁ (originalStrictTransform h₁.right r.divisor) :=
      congrArg (originalStrictTransform K₁) h₁.strict_equal
    _ = originalStrictTransform (K₁ ≫ h₁.right) r.divisor := h₁r.symm

def primeSetoid : Setoid (PrimePresentation X) where
  r := commonResolutionRelation
  iseqv := ⟨commonResolutionRelation_refl, commonResolutionRelation_symm, commonResolutionRelation_trans⟩

variable (X) in
def PrimeOver : Type 1 := Quotient (primeSetoid (X := X))

variable (X) in
def WeightedPrimeOver : Type 1 := {c : ℚ // 0 < c} × PrimeOver X

theorem mk_eq_iff (p q : PrimePresentation X) :
    (Quot.mk commonResolutionRelation p : PrimeOver X) = Quot.mk commonResolutionRelation q ↔
      commonResolutionRelation p q := by
  constructor
  · exact Quotient.exact (s := primeSetoid (X := X)) (a := p) (b := q)
  · exact Quotient.sound (s := primeSetoid (X := X)) (a := p) (b := q)

end SGPT.PSH.PrimeNov16OriginalPrimeQuotient
