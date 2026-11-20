import SGPT.Projective.OkounkovOriginalIdealProducts
import SGPT.Projective.OkounkovOriginalUniformFlatSections

/-! SAME original multiplier values embedded by ACTUAL original unit factors, with ONE fixed twist.
Blueprint: okounkov-original-multiplier-embeddings.tex. No raw partial-polytope limit is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalMultiplierEmbeddings
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.OriginalCancellation
open SGPT.AlmostSemigroup

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance multiplierEmbeddingTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance multiplierEmbeddingCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance multiplierEmbeddingManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {L L' A : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas L') (d : LineBundleAtlas A)

include b d in
/-- An actual original unit factor produces SAME-exponent multiplier values of the SAME genuine twist. -/
theorem multiplier_slice_subset_twisted_of_support_section
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (m k : ℕ) (hm : 0<m)
    (q : LineBundleAtlas (bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k)))
    (r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)))
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤))
    (ht : c ∉ (sectionZeroIdealSheaf q t).support) (φ : SchemeComplexPoint f → EReal) :
    slice (AlgebraicValuation.multiplierSectionSet f n E v c a φ) (m:ℤ) ⊆
      AlgebraicValuation.twistedMultiplierValues f n E v c m r φ := by
  intro x hx
  obtain ⟨j,s,hs,hideal,heq⟩ := hx
  have hjZ : (j:ℤ)=(m:ℤ) := (congrArg Prod.snd heq).symm
  have hj : j=m := by exact_mod_cast hjZ
  subst j
  have hsI : IsIdealSection f n E (multiplierIdeal (n:=n) (m:ℝ) φ) m s :=
    hideal.resolve_left (Nat.ne_of_gt hm)
  let τ := originalCancellationProduct a b d m k s t
  have hz := OriginalUnits.plainSectionValue_eq_zero_of_not_mem_zeroSupport v q t c hc ht
  have hval := originalCancellationProduct_value a b d v hc m k q r s t
  rw [hz,add_zero] at hval
  have hτ : τ ≠ 0 := by
    intro hzero
    have htop := (plainSectionValue_eq_top_iff (v:=v) c r τ).mpr hzero
    exact ((sectionValue_eq_top_iff (v:=v) c a m s).not.mpr hs) (hval.symm.trans htop)
  have hτI := OriginalIdealProducts.originalCancellationProduct_isPlainMultiplierIdealSection
    f n E a b d φ m k s hsI t
  have hvec : plainSectionVector v c r τ hτ = sectionVector v c a m s hs := by
    rw [plainSectionValue_eq_vector c r τ hτ,sectionValue_eq_vector c a m s hs] at hval
    exact toLex.injective (WithTop.coe_injective hval)
  exact ⟨τ,hτ,Or.inr hτI,(congrArg Prod.fst heq).trans hvec.symm⟩

include b in
/-- ONE fixed original positive twist, BEFORE ALL degrees/valuations/centers/potentials, with actual multiplier-value inclusions. -/
theorem exists_fixed_positive_twist_multiplier_slice_inclusions
    (q : LineBundleAtlas (bundleTensor L' (bundleDual L)))
    (H : SchemeLineBundleMetric f n E (bundleTensor L' (bundleDual L)))
    (K : SchemeLineBundleMetric f n E A) (hK : (K.curvature d).val.IsKahler)
    (hzero : RealBottChern.ofRepresentative (H.curvature q) = 0) :
    ∃ k : ℕ, 0<k ∧ ∀ m : ℕ, 0<m →
      ∀ v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))), ∀ c : X, IsNonnegAt v c →
      ∀ r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)),
      ∀ φ : SchemeComplexPoint f → EReal,
        slice (AlgebraicValuation.multiplierSectionSet f n E v c a φ) (m:ℤ) ⊆
          AlgebraicValuation.twistedMultiplierValues f n E v c m r φ := by
  obtain ⟨k,hk,huniform⟩ := NativeFrames.exists_uniform_original_class_zero_sections f n E d K hK
  refine ⟨k,hk,?_⟩
  intro m hm v c hc r φ
  obtain ⟨t,ht⟩ := huniform k le_rfl q H hzero m hm c
  exact multiplier_slice_subset_twisted_of_support_section f n E a b d v hc m k hm
    (NativeFrames.originalMixedPowerAtlas q d m k) r t ht φ

end SGPT.Okounkov.OriginalMultiplierEmbeddings
