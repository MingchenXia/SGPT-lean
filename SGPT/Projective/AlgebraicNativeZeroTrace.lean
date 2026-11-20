import SGPT.Projective.AlgebraicNativeSectionReadback
import SGPT.Foundations.Schemes.SchemeAnalyticClosedEmbedding

/-! The ACTUAL original algebraic section-zero closed subscheme maps to
its ENTIRE actual native zero set, with its genuine point map retained.
Blueprint: algebraic-native-zero-trace.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.GAGA.H0L SGPT.GAGA.H0S
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]

local instance zeroTracePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance zeroTracePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance zeroTracePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The ACTUAL original section-zero support is exactly original coefficient
vanishing in ANY genuine original frame. No support/value identity is input. -/
theorem sectionZero_support_iff_coefficient_zero
    {L : X.Modules} (a : LineBundleAtlas L) (σ : bundleSections L ⊤)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf a σ).support ↔
      schemeOpenRegularFunction f n E U
        (α.coefficients (𝟙 U) (L.val.map (homOfLE le_top).op σ)) p = 0 := by
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset hp
  let Vaff : X.affineOpens := ⟨V, hV⟩
  let j : V ⟶ U := homOfLE hVU
  let c : Γ(X, V) := α.coefficients j (L.val.map V.leTop.op σ)
  have hsupp : schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf a σ).support ↔
      schemeComplexPointImage f p ∉ X.basicOpen c := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := Vaff) hpV]
    change schemeComplexPointImage f p ∈ X.zeroLocus
      (U := V) (sectionZeroIdeal L σ V : Set Γ(X, V)) ↔ _
    rw [sectionZeroIdeal_eq_span_frame σ α j, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    rfl
  have hv := schemeOpenRegularFunction_ne_zero_iff f E n V c p hpV
  have hzero : schemeComplexPointImage f p ∉ X.basicOpen c ↔
      schemeOpenRegularFunction f n E V c p = 0 := by
    simpa only [ne_eq, not_not] using (not_congr hv).symm
  have hc : schemeOpenRegularFunction f n E V c p =
      schemeOpenRegularFunction f n E U
        (α.coefficients (𝟙 U) (L.val.map (homOfLE le_top).op σ)) p := by
    change schemeOpenRegularFunction f n E V
      (α.coefficients (homOfLE hVU) (L.val.map V.leTop.op σ)) p = _
    exact (congrArg (fun r : Γ(X, V) => schemeOpenRegularFunction f n E V r p)
      (coefficients_restrict_top α hVU σ)).trans
        (schemeOpenRegularFunction_restrict f n E V U hVU _ hpV)
  rw [hsupp, hzero, hc]

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

/-- EXACT original algebraic zero support equals the entire actual native
zero set of the SAME manufactured section, with no nonzero requirement. -/
theorem sectionZero_support_iff_native_zero (k : ℕ)
    (σ : bundlePowerGlobalSections L (k + 1)) (p : SchemeComplexPoint f) :
    schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ).support ↔
      nativeSectionOfAlgebraicPositivePower f n E a H k σ p = 0 := by
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have hsupp := sectionZero_support_iff_coefficient_zero f n E (a.tensorPower (k + 1)) σ
    ((a.frame i).tensorPower (k + 1)) p hi
  let B := positivePower (schemeHermitianLineBundle f n E a H) k
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  have hzero : sectionCoefficient B.Fiber e.val
      (nativeSectionOfAlgebraicPositivePower f n E a H k σ) p = 0 ↔
      nativeSectionOfAlgebraicPositivePower f n E a H k σ p = 0 :=
    (e.val.linearEquivAt ℂ p he).map_eq_zero_iff
  rw [nativeSectionOfAlgebraicPositivePower_frame f n E a H k σ i hi] at hzero
  exact hsupp.trans hzero

/-- The ACTUAL original closed-subscheme complex-point map has exactly the
ENTIRE native section zero set as its range. True point lifts are produced
by the genuine closed-immersion theorem, not assumed as a certificate. -/
theorem sectionZeroPoint_range_eq_native_zero (k : ℕ)
    (σ : bundlePowerGlobalSections L (k + 1)) :
    Set.range (schemeComplexPointMap
      (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f) f
      (sectionZeroι (a.tensorPower (k + 1)) σ) rfl) =
        {p : SchemeComplexPoint f | nativeSectionOfAlgebraicPositivePower f n E a H k σ p = 0} := by
  rw [closedImmersionComplexPointMap_range]
  change {p : SchemeComplexPoint f | schemeComplexPointImage f p ∈
    Set.range (sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ).subschemeι} = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  ext p
  exact sectionZero_support_iff_native_zero f n E a H k σ p

/-- The SAME original zero-subscheme point map is a genuine homeomorphism
onto the ENTIRE actual native zero set; every component is retained. -/
def sectionZeroPointHomeomorph (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) :
    letI : TopologicalSpace (SchemeComplexPoint (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f)) :=
      schemeAnalyticPointTopology (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f)
    SchemeComplexPoint (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f) ≃ₜ
      {p : SchemeComplexPoint f | nativeSectionOfAlgebraicPositivePower f n E a H k σ p = 0} := by
  let := schemeAnalyticPointTopology (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f)
  exact (closedImmersionComplexPointMap_isClosedEmbedding f
    (sectionZeroι (a.tensorPower (k + 1)) σ)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (sectionZeroPoint_range_eq_native_zero f n E a H k σ))

/-- The homeomorphism retains the ACTUAL original closed immersion point
map, rather than identifying an abstract substitute zero space. -/
theorem sectionZeroPointHomeomorph_val (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (q : SchemeComplexPoint (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f)) :
    (sectionZeroPointHomeomorph f n E a H k σ q).val =
      schemeComplexPointMap (sectionZeroι (a.tensorPower (k + 1)) σ ≫ f) f
        (sectionZeroι (a.tensorPower (k + 1)) σ) rfl q := rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
