import SGPT.Projective.OkounkovOriginalNativeMixedFrames
import SGPT.Projective.OkounkovNativeOrdinaryGAGA
import SGPT.Projective.OkounkovBottChernZeroSections
import SGPT.Projective.AlgebraicNativeZeroTrace

/-! Actual original mixed GAGA and uniform original sections avoiding EVERY scheme point.
Blueprint: okounkov-original-uniform-flat-sections.tex. No whole numerical-invariance credit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeFrames
open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]

local instance originalUniformSectionsTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalUniformSectionsCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalUniformSectionsManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable {N A : X.Modules} (a : LineBundleAtlas N) (b : LineBundleAtlas A)
  (H : SchemeLineBundleMetric f n E N) (K : SchemeLineBundleMetric f n E A)

/-- Genuine ORIGINAL ordinary mixed-power section and literal every-frame coefficient as OUTPUT. -/
theorem exists_algebraic_original_mixed_section (m k : ℕ) (hk : 0<k)
    (s : HolomorphicSections (n:=n) (twistedPower (schemeHermitianLineBundle f n E a H)
      (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m).Fiber) :
    ∃ σ : Γ(bundleTensor (bundleTensorPower N m) (bundleTensorPower A k),⊤),
      ∀ (ij : a.I × b.I) (p : SchemeComplexPoint f),
        schemeComplexPointImage f p ∈ a.opens ij.1 ⊓ b.opens ij.2 →
      sectionCoefficient (twistedPower (schemeHermitianLineBundle f n E a H)
        (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m).Fiber
          (originalMixedNativeFrame f n E a b H K m k ij).val s p =
      schemeOpenRegularFunction f n E (a.opens ij.1 ⊓ b.opens ij.2)
        (((originalMixedPowerAtlas a b m k).frame ij).coefficients (𝟙 _)
          ((bundleTensor (bundleTensorPower N m) (bundleTensorPower A k)).val.map
            (a.opens ij.1 ⊓ b.opens ij.2).leTop.op σ)) p := by
  let c := originalMixedPowerAtlas a b m k
  let F := schemeLineBundleMetric f n E c
  let Φ := originalMixedNativeEquiv f n E a b H K m k hk F
  obtain ⟨σ,hread⟩ := exists_algebraic_ordinary_section f n E c F (Φ.sectionMap s)
  refine ⟨σ,?_⟩
  intro ij p hp
  have hframe := originalMixedNativeEquiv_frame f n E a b H K m k hk F ij hp (s p)
  exact hframe.symm.trans (hread ij p hp)

/-- Nonzero actual native value manufactures SAME original algebraic section with actual zero support avoiding p. -/
theorem exists_original_mixed_section_avoiding_complex_point (m k : ℕ) (hk : 0<k)
    (s : HolomorphicSections (n:=n) (twistedPower (schemeHermitianLineBundle f n E a H)
      (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m).Fiber)
    (p : SchemeComplexPoint f) (hs : s p ≠ 0) :
    ∃ σ : Γ(bundleTensor (bundleTensorPower N m) (bundleTensorPower A k),⊤),
      schemeComplexPointImage f p ∉ (sectionZeroIdealSheaf (originalMixedPowerAtlas a b m k) σ).support := by
  obtain ⟨σ,hread⟩ := exists_algebraic_original_mixed_section f n E a b H K m k hk s
  obtain ⟨ij,hij⟩ := (originalMixedPowerAtlas a b m k).covers (schemeComplexPointImage f p)
  let e := originalMixedNativeFrame f n E a b H K m k ij
  have he : p ∈ e.val.baseSet := twistedPowerAtlasFrame_mem _ _ hij
    (positivePowerAtlasFrame_mem _ hij (k-1)) m
  have hn := native_section_coefficient_ne_zero _ s e he hs
  refine ⟨σ,?_⟩
  intro hsup
  have hz := (sectionZero_support_iff_coefficient_zero f n E (originalMixedPowerAtlas a b m k) σ
    ((originalMixedPowerAtlas a b m k).frame ij) p hij).mp hsup
  exact hn ((hread ij p hij).trans hz)

/-- ONE original positive twist, BEFORE every original class-zero line/power/SCHEME point; actual sections as output. -/
theorem exists_uniform_original_class_zero_sections
    (hKah : (K.curvature b).val.IsKahler) :
    ∃ k₀ : ℕ, 0<k₀ ∧ ∀ k : ℕ, k₀≤k →
      ∀ {N : X.Modules} (a : LineBundleAtlas N) (H : SchemeLineBundleMetric f n E N),
      RealBottChern.ofRepresentative (H.curvature a) = 0 →
      ∀ m : ℕ, 0<m → ∀ c : X,
        ∃ σ : Γ(bundleTensor (bundleTensorPower N m) (bundleTensorPower A k),⊤),
          c ∉ (sectionZeroIdealSheaf (originalMixedPowerAtlas a b m k) σ).support := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  obtain ⟨k₀,hk₀,huniform⟩ := FlatTwist.exists_uniform_class_zero_twist_nonzero_sections
    (schemeHermitianLineBundle f n E b K)
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E b K)
    (K.curvature b) (isOwnFirstChernForm_schemeHermitianLineBundle f n E b K) hKah
  refine ⟨k₀,hk₀,?_⟩
  intro k hk N a H hclass m hm c
  obtain ⟨p,_,hsp⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint f (show c ∈ (⊤ : X.Opens) from Set.mem_univ c)
  obtain ⟨s,hs⟩ := huniform k hk (schemeHermitianLineBundle f n E a H)
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E a H)
    (H.curvature a) (isOwnFirstChernForm_schemeHermitianLineBundle f n E a H) hclass m hm p
  obtain ⟨σ,hσ⟩ := exists_original_mixed_section_avoiding_complex_point f n E a b H K m k
    (lt_of_lt_of_le hk₀ hk) s p hs
  exact ⟨σ,fun hc => hσ (hsp.mem_closed (sectionZeroIdealSheaf _ σ).support.isClosed hc)⟩

end SGPT.Okounkov.NativeFrames
