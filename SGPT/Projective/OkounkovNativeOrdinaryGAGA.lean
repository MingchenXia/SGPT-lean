import SGPT.Projective.AlgebraicNativeRegularCut
import SGPT.Projective.OriginalSectionUnit

/-! Genuine ordinary ORIGINAL section algebraization with no tensor-unit identification.
Blueprint: okounkov-native-ordinary-gaga.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeFrames
open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]

local instance ordinaryGAGATopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance ordinaryGAGACharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance ordinaryGAGAManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- An ACTUAL ordinary original algebraic section with EVERY original native frame reader, as output. -/
theorem exists_algebraic_ordinary_section {B : X.Modules} (a : LineBundleAtlas B)
    (H : SchemeLineBundleMetric f n E B)
    (s : HolomorphicSections (n:=n) (schemeHermitianLineBundle f n E a H).Fiber) :
    ∃ σ : Γ(B,⊤), ∀ (i : a.I) (p : SchemeComplexPoint f),
      schemeComplexPointImage f p ∈ a.opens i →
      sectionCoefficient (schemeHermitianLineBundle f n E a H).Fiber
        (schemeHermitianAtlasFrame f n E a H (a.frame i)).val s p =
      schemeOpenRegularFunction f n E (a.opens i)
        ((a.frame i).coefficients (𝟙 _) (B.val.map (a.opens i).leTop.op σ)) p := by
  obtain ⟨σ₁,hread,_⟩ := exists_algebraic_positivePower_section f n E a H 0 s
  let σ : Γ(B,⊤) := (bundleTensorLeftUnitIso B).hom.val.app (.op ⊤) σ₁
  have hunit : originalSectionUnit σ = σ₁ := by
    change (bundleTensorLeftUnitIso B).inv.val.app (.op ⊤)
      ((bundleTensorLeftUnitIso B).hom.val.app (.op ⊤) σ₁) = σ₁
    exact congr($((bundleTensorLeftUnitIso B).hom_inv_id).val.app (.op ⊤) |>.hom σ₁)
  refine ⟨σ,?_⟩
  intro i p hp
  have hcoef := originalSectionUnit_coefficients σ (a.frame i) (𝟙 _)
  rw [hunit] at hcoef
  have halg : algCoef (a.frame i) 1 σ₁ =
      (a.frame i).coefficients (𝟙 _) (B.val.map (a.opens i).leTop.op σ) := hcoef
  have h := hread i p hp
  rw [halg] at h
  exact h

section Native
variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsComplexManifold d M]

/-- Actual physical nonzeroness implies a nonzero coordinate in EVERY genuine native frame at that point. -/
theorem native_section_coefficient_ne_zero (B : HermitianHolomorphicLineBundle.{0,0} d M)
    (s : HolomorphicSections (n:=d) B.Fiber) (e : AtlasFrame B) {p : M}
    (hp : p ∈ e.val.baseSet) (hs : s p ≠ 0) : sectionCoefficient B.Fiber e.val s p ≠ 0 := by
  intro hzero
  apply hs
  apply (e.val.linearEquivAt ℂ p hp).injective
  simpa only [Trivialization.linearEquivAt_apply,map_zero,sectionCoefficient] using hzero

end Native
end SGPT.Okounkov.NativeFrames
