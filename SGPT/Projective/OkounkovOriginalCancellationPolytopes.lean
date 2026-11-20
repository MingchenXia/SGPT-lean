import SGPT.Projective.OkounkovOriginalCancellationProduct
import SGPT.Projective.OkounkovOriginalUniformFlatSections
import SGPT.Okounkov.AlgebraicValuationBodies

/-! Literal ORIGINAL raw degree polytopes, actual sections manufactured before comparison.
Blueprint: okounkov-original-cancellation-polytopes.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalCancellation
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} [IsIntegral X] {L L' A : X.Modules}
  (a : LineBundleAtlas L) (b : LineBundleAtlas L') (d : LineBundleAtlas A)
  {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

include b d in
/-- Literal ORIGINAL polytope inclusion from an actual original support-avoiding factor. -/
theorem lineBundleDegreePolytope_subset_twisted_of_support_section (hc : IsNonnegAt v c) (m k : ℕ)
    (q : LineBundleAtlas (bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k)))
    (r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)))
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤))
    (ht : c ∉ (sectionZeroIdealSheaf q t).support) :
    lineBundleDegreePolytope v c a m ⊆ AlgebraicValuation.twistedDegreePolytope v c m r := by
  unfold lineBundleDegreePolytope degreePolytope AlgebraicValuation.twistedDegreePolytope
  apply convexHull_mono
  apply Set.image_mono
  intro x hx
  change (x,(m:ℤ)) ∈ sectionSemigroup v c a at hx
  obtain ⟨j,s,hs,heq⟩ := hx
  have hjZ : (j:ℤ)=(m:ℤ) := (congrArg Prod.snd heq).symm
  have hj : j=m := by exact_mod_cast hjZ
  subst j
  have hxvec : x = sectionVector v c a m s hs := congrArg Prod.fst heq
  obtain ⟨τ,hτ,hval⟩ := exists_original_value_preserving_cancellation a b d v hc m k q r t ht s hs
  have hvec : plainSectionVector v c r τ hτ = sectionVector v c a m s hs := by
    rw [plainSectionValue_eq_vector c r τ hτ,sectionValue_eq_vector c a m s hs] at hval
    exact toLex.injective (WithTop.coe_injective hval)
  exact ⟨τ,hτ,hxvec.trans hvec.symm⟩

variable (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance cancellationPolytopesTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance cancellationPolytopesCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance cancellationPolytopesManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

include b in
/-- ONE actual original positive twist gives ALL SAME raw degree-polytope inclusions, all valuations/points. -/
theorem exists_fixed_positive_twist_raw_polytope_inclusions
    (q : LineBundleAtlas (bundleTensor L' (bundleDual L)))
    (H : SchemeLineBundleMetric f n E (bundleTensor L' (bundleDual L)))
    (K : SchemeLineBundleMetric f n E A) (hK : (K.curvature d).val.IsKahler)
    (hzero : RealBottChern.ofRepresentative (H.curvature q) = 0) :
    ∃ k : ℕ, 0<k ∧ ∀ m : ℕ, 0<m →
      ∀ v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))), ∀ c : X, IsNonnegAt v c →
      ∀ r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)),
        lineBundleDegreePolytope v c a m ⊆ AlgebraicValuation.twistedDegreePolytope v c m r := by
  obtain ⟨k,hk,huniform⟩ := NativeFrames.exists_uniform_original_class_zero_sections f n E d K hK
  refine ⟨k,hk,?_⟩
  intro m hm v c hc r
  obtain ⟨t,ht⟩ := huniform k le_rfl q H hzero m hm c
  exact lineBundleDegreePolytope_subset_twisted_of_support_section a b d v hc m k
    (NativeFrames.originalMixedPowerAtlas q d m k) r t ht

end SGPT.Okounkov.OriginalCancellation
