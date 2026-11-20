import SGPT.Okounkov.SchemeSectionWeight
import SGPT.Projective.BDivNov16OriginalAnalytificationStalkImage
import SGPT.Projective.BDivNov16NativePrincipalGermSpan
import SGPT.NAPotential.GAGAMult2SectionIdeal
import SGPT.PSH.CartierMetricPrimeCurrentClass
import SGPT.BDivisor.DFAlgNeronSeveri

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult SGPT.PSH.IdealRestriction
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves InvertibleIdealQuotient
open scoped Topology Manifold ContDiff

namespace SGPT.Projective.BDivNov16

noncomputable section

private theorem span_singleton_nativeGerm_iff {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M] {p : M} {H : M → ℂ}
    (hH : HolomorphicAt d H p) (g : M → ℂ) :
    (∃ hg : HolomorphicAt d g p, NativeHolGerm.mk g hg ∈ Ideal.span {NativeHolGerm.mk H hH}) ↔
      IsInSpanAt (n := d) (· = H) p g := by
  constructor
  · rintro ⟨hg, hmem⟩
    exact (nativeGerm_principal_mem_iff_isInSpanAt p H hH g hg).mp hmem
  · intro h
    exact ⟨h.1, (nativeGerm_principal_mem_iff_isInSpanAt p H hH g h.1).mpr h⟩

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance primeSectionTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance primeSectionCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance primeSectionManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The full analytic divisor ideal made from a section's native germs is
its original algebraic zero ideal extended to the native stalks. -/
theorem schemeSectionAnalyticIdeal_eq_analytification_sectionZero
    {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ) (σ : bundlePowerGlobalSections L k) :
    schemeSectionAnalyticIdeal f (m + 1) E a k σ =
      analytificationIdeal f (m + 1) E (sectionZeroIdealSheaf (a.tensorPower k) σ) := by
  apply GermIdeal.ext
  funext p g
  apply propext
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  let H := schemeOpenRegularFunction f (m + 1) E (a.opens i) (algCoef (a.frame i) k σ)
  have hH : HolomorphicAt (m + 1) H p :=
    schemeOpenRegularFunction_holomorphicAt f (m + 1) E _ _ p hi
  have heq : schemeFramePowerSectionNativeGerm f (m + 1) p (a.frame i) hi k σ =
      NativeHolGerm.mk H hH :=
    (schemeOpenRegularFunction_germ f (m + 1) E _ _ p hi).symm
  rw [schemeSectionAnalyticIdeal_mem_frame f (m + 1) E a k σ p (a.frame i) hi g,
    heq, analytificationIdeal_sectionZeroIdealSheaf_iff f (m + 1) E a k σ i hi g]
  exact span_singleton_nativeGerm_iff hH g

/-- When the actual algebraic section-zero ideal extends to the reduced
prime ideal on every native stalk, the prime integration-current class is
the curvature class of that same algebraic line, for every original metric. -/
theorem primeClass_eq_originalCartierSection_chern [IsIntegral X] [CompactSpace (SchemeComplexPoint f)]
    (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint f))
    {L : X.Modules} (a : LineBundleAtlas L) (σ : bundlePowerGlobalSections L 1) (hσ : σ ≠ 0)
    (H : SchemeLineBundleMetric f (m + 1) E L)
    (hfull : ∀ p : SchemeComplexPoint f,
      Ideal.map (schemeNativeStalkGerm f (m + 1) p)
        ((sectionZeroIdealSheaf (a.tensorPower 1) σ).stalkIdeal (schemeComplexPointImage f p)) =
        stalkIdeal (vanishingIdeal (n := m + 1) P.val) p) :
    SGPT.BDivisor.DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P) =
      RealBottChern.ofRepresentative (H.curvature a) := by
  let D := schemeSectionAnalyticDivisor f (m + 1) E a 1 σ hσ
  have hideal : D.ideal = (SGPT.Siu.primeEffectiveDivisor P).ideal := by
    change schemeSectionAnalyticIdeal f (m + 1) E a 1 σ = _
    rw [schemeSectionAnalyticIdeal_eq_analytification_sectionZero,
      SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal P]
    apply GermIdeal.ext
    funext p g
    apply propext
    have hPcoh : (vanishingIdeal (n := m + 1) P.val).IsCoherent := by
      rw [← SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal P]
      exact DivisorMetric.isCoherent_of_isInvertible (SGPT.Siu.primeEffectiveDivisor P).isInvertible
    constructor
    · intro hg
      have hhol := hg.1
      have hmem := (originalAnalytification_mem_iff_native_stalkImage f (m + 1) E
        (sectionZeroIdealSheaf (a.tensorPower 1) σ) p g hhol).mp hg
      change NativeHolGerm.mk g hhol ∈ Ideal.map (schemeNativeStalkGerm f (m + 1) p)
        ((sectionZeroIdealSheaf (a.tensorPower 1) σ).stalkIdeal (schemeComplexPointImage f p)) at hmem
      rw [hfull p] at hmem
      exact GermIdealTotalTransform.mem_of_isInSpanAt_mem hPcoh
        (isInSpanAt_of_mk_mem_spanGerms hhol hmem)
    · intro hg
      have hhol := hg.1
      apply (originalAnalytification_mem_iff_native_stalkImage f (m + 1) E
        (sectionZeroIdealSheaf (a.tensorPower 1) σ) p g hhol).mpr
      change NativeHolGerm.mk g hhol ∈ Ideal.map (schemeNativeStalkGerm f (m + 1) p)
        ((sectionZeroIdealSheaf (a.tensorPower 1) σ).stalkIdeal (schemeComplexPointImage f p))
      rw [hfull p]
      exact mk_mem_stalkIdeal hhol hg
  have hD : D = SGPT.Siu.primeEffectiveDivisor P :=
    HironakaEffectiveDivisorSum.effectiveDivisor_eq_of_ideal_eq hideal
  have hmetric := H.sectionMeteredDivisor_isDivisorMetric a 1 σ hσ
  change DivisorMetric.IsDivisorMetric D (H.sectionMeteredDivisor a 1 σ hσ) at hmetric
  rw [hD] at hmetric
  rw [SGPT.BDivisor.DFAlg.cycleClass_eq_of_isDivisorMetric _ _ hmetric,
    RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (H.sectionMeteredDivisor_curvature a 1 σ hσ), Nat.cast_one, one_smul]

end

end SGPT.Projective.BDivNov16
