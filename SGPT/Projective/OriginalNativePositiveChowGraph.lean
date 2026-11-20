import SGPT.Projective.OriginalChowProjectiveScheme
import SGPT.Bergman.SiuNativeProjectiveNS
import SGPT.Bergman.SiuKodairaEmbedding

/-! The genuine actual positive-native-bundle Kodaira map supplies the
original chart-level embedding and SAME original algebraic Chow graph.
No projective map/embedding/Chow ideal or algebraic graph certificate.
Blueprint: original-native-positive-chow-graph.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.NativeKodairaPullback SGPT.PSH.GlobalL2
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

/-- Actual native holomorphy and injective native differential PRODUCE
all ORIGINAL affine-chart embedding fields for the SAME projective map. -/
theorem originalEmbedding_of_native_mfderiv {n N : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {Φ : M → ComplexProjectiveSpace N}
    (hΦ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel N) ∞ Φ)
    (hinj : Function.Injective Φ)
    (hder : ∀ p, Function.Injective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel N) Φ p)) :
    IsHolomorphicEmbedding (n := n) Φ := by
  refine ⟨hΦ.continuous,hinj,?_,?_⟩
  · intro p i hi
    let c := complexChartAt (n := n) p
    let d : ComplexChart N (ComplexProjectiveSpace N) := ⟨affineChart i,affineChart_mem_atlas i⟩
    have hp : c.val p∈coordinateDomain Φ c d := mem_coordinateDomain (mem_complexChartAt_source p) hi
    filter_upwards [(coordinateDomain_isOpen hΦ c d).mem_nhds hp] with z hz
    exact (coordinateMap_contDiffAt hΦ c d hz).differentiableAt (by simp)
  · intro p i hi
    let c := complexChartAt (n := n) p
    let d : ComplexChart N (ComplexProjectiveSpace N) := ⟨affineChart i,affineChart_mem_atlas i⟩
    have hp : c.val p∈coordinateDomain Φ c d := mem_coordinateDomain (mem_complexChartAt_source p) hi
    have hh := SGPT.BDivisor.NSKodaira.coordinateMap_fderiv_injective_of_native_mfderiv hΦ hder c d hp
    rw [coordinateMap_fderiv_restrictScalars hΦ c d hp] at hh
    exact hh

section Original
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)
local instance nativePositiveChowTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativePositiveChowCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance nativePositiveChowManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The SAME actual positive native bundle manufactures a positive power,
ordinary native H0 sections, actual chart embedding and TRUE original
whole Chow graph, in all dimensions and on empty/disconnected sources.
No chosen native embedding/map, Chow polynomial/ideal or graph input. -/
theorem exists_originalNativePositiveChowGraph
    (G : HermitianHolomorphicLineBundle.{0,0} n (SchemeComplexPoint f))
    (hG : IsSourceSmoothHermitianMetric G) (θG : ClosedRealOneOneForm n (SchemeComplexPoint f))
    (hθG : IsOwnFirstChernForm G θG) (hK : θG.val.IsKahler) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ d : ℕ, 0<d ∧ ∃ (N : ℕ)
      (s : Fin (N+1) → HolomorphicSections (n := n) (positivePower G (d-1)).Fiber)
      (hgen : ∀ x, ∃ j, s j x≠0),
      let Φ := sourceNativeFiniteSectionProjectiveMap (positivePower G (d-1)) s hgen
      IsHolomorphicEmbedding (n := n) Φ ∧
      ∃ (m : ℕ) (μ : Type) (_ : Fintype μ)
        (P : μ → MvPolynomial (Fin (segreDim E.ambientDimension N+1)) ℂ)
        (hP : ∀ k, (P k).IsHomogeneous m),
        (coneIdeal (range (fun x => segreMap (projectivePoint f E n x) (Φ x)))).GeneratedOn
          (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace (segreDim E.ambientDimension N)))
          (fun k => SGPT.GAGA.PN.polyTuple (P k)) ∧
        range (originalChowProjectivePoint P m hP) =
          range (fun x => segreMap (projectivePoint f E n x) (Φ x)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨d,hd,N,s,hgen,hΦ,hinj,hder⟩ := SGPT.Bergman.SiuKodaira.kodairaEmbedding G hG θG hθG hK
  have hΦold := originalEmbedding_of_native_mfderiv hΦ hinj.injective hder
  refine ⟨d,hd,N,s,hgen,hΦold,?_⟩
  exact exists_originalSegreGraph_algebraicScheme (isHolomorphicEmbedding_projectivePoint f E n) hΦold
end Original

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
