import SGPT.Projective.AlgebraicNativeCoefficientGerm
import SGPT.Projective.AlgebraicCurveZeroArtinian
import SGPT.Projective.AlgebraicCurveZeroLength
import SGPT.Projective.AlgebraicNativeZeroTrace
import SGPT.Projective.NativeCurveZeroPresentation
import SGPT.Foundations.Schemes.SchemeAnalyticSeparation

/-! FULL original algebraic zero-stalk length is the SAME actual physical
native regular multiplicity. Blueprint: algebraic-curve-native-multiplicity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult
open SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder DivisorRegularLocus
open scoped Topology Manifold

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
local instance multiplicityPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance multiplicityPointCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance multiplicityPointManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

private theorem normalOrder_carrier_cast {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] {A B : Set M} {p : M}
    (h : A = B) (Ψ : DivisorFlattening (m := 0) A p) (g : HolGerm (ComplexModel 1)) :
    normalOrder (h ▸ Ψ) g = normalOrder Ψ g := by
  cases h
  rfl

/-- EVERY actual original zero-stalk length equals SAME physical native multiplicity,
with actual point/frame/presentation all manufactured from the original section. -/
theorem exists_algebraic_curve_native_multiplicity
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0)
    (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) :
    ∃ (p : SchemeComplexPoint f) (_hp : schemeComplexPointImage f p = sectionZeroι (a.tensorPower (k + 1)) σ z)
      (i : a.I) (_hi : schemeComplexPointImage f p ∈ a.opens i)
      (P : RegularPresentation
        (sectionCoefficient (positivePower (schemeHermitianLineBundle f 1 E a H) k).Fiber
          (positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame i)) k).val
          (nativeSectionOfAlgebraicPositivePower f 1 E a H k σ) ∘
            (complexChartAt (n := 1) p).val.symm) ((complexChartAt (n := 1) p).val p)),
      Module.length ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)
        ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z) = (P.m : ℕ∞) ∧
      ∀ w ∈ P.U,
        (sectionCoefficient (positivePower (schemeHermitianLineBundle f 1 E a H) k).Fiber
          (positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame i)) k).val
          (nativeSectionOfAlgebraicPositivePower f 1 E a H k σ) ∘
            (complexChartAt (n := 1) p).val.symm) w = 0 →
          w = (complexChartAt (n := 1) p).val p := by
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
  have hz := sectionZero_image_isClosed f E (a.tensorPower (k + 1)) σ hσ z
  obtain ⟨p, hp, Ψ, hlength⟩ := exists_zeroStalk_length_eq_normalOrder
    f E (a.tensorPower (k + 1)) σ hσ z hz
  have htrace : schemeNativeAlgebraicTrace f
      (closure {sectionZeroι (a.tensorPower (k + 1)) σ z}) = ({p} : Set (SchemeComplexPoint f)) := by
    rw [hz.closure_eq]
    ext q
    change schemeComplexPointImage f q ∈ ({sectionZeroι (a.tensorPower (k + 1)) σ z} : Set X) ↔ q ∈ ({p} : Set (SchemeComplexPoint f))
    simp only [Set.mem_singleton_iff, ← hp, (schemeComplexPointImage_injective f).eq_iff]
  let Ψp : DivisorFlattening (m := 0) ({p} : Set (SchemeComplexPoint f)) p := htrace ▸ Ψ
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  let B := positivePower (schemeHermitianLineBundle f 1 E a H) k
  let s := nativeSectionOfAlgebraicPositivePower f 1 E a H k σ
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  have hs : s p = 0 := by
    apply (sectionZero_support_iff_native_zero f 1 E a H k σ p).mp
    have hrange : Set.range (sectionZeroι (a.tensorPower (k + 1)) σ) =
        ((sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ).support : Set X) :=
      Scheme.IdealSheafData.range_subschemeι _
    exact Eq.mp (congrArg (fun S : Set X => schemeComplexPointImage f p ∈ S) hrange)
      (show schemeComplexPointImage f p ∈ Set.range (sectionZeroι (a.tensorPower (k + 1)) σ)
        from ⟨z, hp.symm⟩)
  have hcoef : NativeHolGerm.mk (sectionCoefficient B.Fiber e.val s)
      (nativeSectionCoefficient_holomorphicAt B s e he) ≠ 0 :=
    algebraicNativeCoefficientGerm_ne_zero f 1 E a H k σ hσ i p hi
  obtain ⟨P, hPm, hPzero⟩ := exists_native_curve_section_presentation B s e p he hs hcoef Ψp
  refine ⟨p, hp, i, hi, P, ?_, hPzero⟩
  have hi' : sectionZeroι (a.tensorPower (k + 1)) σ z ∈ a.opens i := hp ▸ hi
  have hlen := hlength i hi'
  change (P.m : ℕ∞) = normalOrder Ψp
    (NativeHolGerm.chartEquiv p (algebraicNativeCoefficientGerm f 1 E a H k σ i p hi)) at hPm
  rw [algebraicNativeCoefficientGerm_model, normalOrder_carrier_cast] at hPm
  exact hlen.trans hPm.symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
