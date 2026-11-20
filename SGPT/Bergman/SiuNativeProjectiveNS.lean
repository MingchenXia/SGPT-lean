import SGPT.Bergman.SiuNativeSectionMetric
import SGPT.Bergman.SiuNativeSectionDense
import SGPT.Projective.SourceNativeCoordinateFamily
import SGPT.Projective.SourceHyperplaneChernClass
import SGPT.GAGA.TowerAlgKahler
import SGPT.Bergman.SiuKodairaChartDerivative

/-! Original projective immersions produce an actual NS_R Kähler class
via the independent actual hyperplane bundle and actual Cartier section divisor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.NativeKodairaPullback
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Projective.HyperplaneClassNext
open SGPT.Toric SGPT.Toric.F1IntersectionDraft

variable {n m : ℕ} {X Y : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- The actual chart-smooth composition along a genuine holomorphic map,
with arbitrary original source and target dimensions. -/
theorem chartSmooth_comp_any {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {h : Y → ℝ} (hh : ChartSmooth (n := m) h) :
    ChartSmooth (n := n) (fun p => h (f p)) := by
  intro c z hz
  let d := complexChartAt (n := m) (f (c.val.symm z))
  have hzd : z ∈ coordinateDomain f c d := ⟨hz, mem_complexChartAt_source _⟩
  have hs := ((hh d).contDiffAt
    (d.val.open_target.mem_nhds (coordinateMap_mem_target hzd))).comp z
      (coordinateMap_contDiffAt_real hf c d hzd)
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [(coordinateDomain_isOpen hf c d).mem_nhds hzd] with w hw
  exact congrArg h (d.val.left_inv hw.2).symm

/-- Bott--Chern equality pulls back along the actual original map in
arbitrary dimensions; the actual global smooth potential is composed. -/
theorem ofRepresentative_pullback_congr_any {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {θ η : ClosedRealOneOneForm m Y}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative η) :
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf θ) =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf η) := by
  obtain ⟨g, hg, heq⟩ := (RealBottChern.ofRepresentative_eq_iff θ η).mp h
  refine (RealBottChern.ofRepresentative_eq_iff _ _).mpr
    ⟨fun p => g (f p), chartSmooth_comp_any hf hg, fun c z hz => ?_⟩
  let d := complexChartAt (n := m) (f (c.val.symm z))
  have hzd : z ∈ coordinateDomain f c d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := coordinateDomain_isOpen hf c d
  have hddc : smoothDDC (fun w => g (f (c.val.symm w))) z =
      (smoothDDC (fun w => g (d.val.symm w)) (coordinateMap f c d z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f c d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (coordinateMap_contDiffOn hf c d) (hg d)
      (fun _ hw => coordinateMap_mem_target hw) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with w hw
    exact congrArg g (d.val.left_inv hw.2).symm
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hf _ c d hzd, SmoothRealForm.pullback_coeff hf _ c d hzd,
    hddc, heq d _ (coordinateMap_mem_target hzd)]
  ext v
  simp

/-- The original projective immersion manufactures its actual Kähler form
and original Cartier-span class. The target hyperplane bundle and all of
its coordinate sections are independent produced original native objects. -/
theorem exists_kahler_mem_neronSeveri_of_projective_immersion {N : ℕ}
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (hdf : ∀ (c : ComplexChart n X) (d : ComplexChart N (ComplexProjectiveSpace N))
      (z : ComplexModel n), z ∈ coordinateDomain f c d →
        Function.Injective (fderiv ℝ (coordinateMap f c d) z)) :
    ∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
      RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X := by
  let O := sourceProjectiveHyperplaneBundle N
  let hO := sourceProjectiveHyperplaneBundle_sourceSmooth N
  let P := nativeHolomorphicPullbackBundle O f
  let hP := nativeHolomorphicPullback_smooth O f hO
  let t := fun i : Fin (N + 1) =>
    sourceNativeHolomorphicSectionPullback O f (sourceProjectiveCoordinateNativeSection N i)
  have hgen := sourceNativeHolomorphicSectionPullback_generating O f
    (sourceProjectiveCoordinateNativeSection N) (sourceProjectiveCoordinateNativeSection_generating N)
  obtain ⟨s, hs⟩ := exists_dense_native_section_of_global_generation P t hgen
  have hNS := nativeSection_chern_mem_neronSeveri P hP s hs
  let θO := sourceNativeFirstChernForm O hO
  have hOFS : RealBottChern.ofRepresentative θO = RealBottChern.ofRepresentative (fsClosedForm (N := N)) :=
    nativeProjectiveHyperplaneOfMetric_class_eq_fs (simplex_edgeSmooth (N := N))
      (sourceSimplexHyperplaneMetric N)
  have hclass : RealBottChern.ofRepresentative (sourceNativeFirstChernForm P hP) =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback f.contMDiff (fsClosedForm (N := N))) :=
    (RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (nativeHolomorphicPullback_firstChern_geometrically O f hO θO
        (sourceNativeFirstChernForm_isOwn O hO))).trans
          (ofRepresentative_pullback_congr_any f.contMDiff hOFS)
  refine ⟨ClosedRealOneOneForm.pullback f.contMDiff (fsClosedForm (N := N)), ?_, hclass ▸ hNS⟩
  exact SmoothRealForm.IsKahler.pullback_of_injective f.contMDiff hdf fsForm_isKahler

/-- The actual native immersion differential gives injectivity of every
actual real coordinate derivative, with all original chart changes proved. -/
theorem coordinateMap_fderiv_injective_of_native_mfderiv {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hinj : ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f p))
    (c : ComplexChart n X) (d : ComplexChart m Y) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain f c d) :
    Function.Injective (fderiv ℝ (coordinateMap f c d) z) := by
  let p := c.val.symm z
  let c₀ := complexChartAt (n := n) p
  let d₀ := complexChartAt (n := m) (f p)
  have hp : p ∈ c₀.val.source := mem_complexChartAt_source p
  have hfp : f p ∈ d₀.val.source := mem_complexChartAt_source (f p)
  have hpdom : c₀.val p ∈ coordinateDomain f c₀ d₀ := mem_coordinateDomain hp hfp
  have hpreferred : Function.Injective (fderiv ℂ (coordinateMap f c₀ d₀) (c₀.val p)) := by
    have h := hinj p
    rw [SGPT.Bergman.SiuKodaira.mfderiv_eq_fderiv_complexChartAt
      ((hf p).mdifferentiableAt (by simp))] at h
    exact h
  have hpreferredR : Function.Injective (fderiv ℝ (coordinateMap f c₀ d₀) (c₀.val p)) := by
    rw [coordinateMap_fderiv_restrictScalars hf c₀ d₀ hpdom]
    exact hpreferred
  have hsource : z ∈ (chartTransition c c₀).source := ⟨hz.1, hp⟩
  have hz₀ : z ∈ coordinateDomain f c d₀ := ⟨hz.1, hfp⟩
  have hsourceR : Function.Injective (fderiv ℝ (coordinateMap f c d₀) z) := by
    rw [coordinateMap_fderiv_change_source hf c c₀ d₀ hsource hz₀]
    change Function.Injective ((fderiv ℝ (coordinateMap f c₀ d₀) (c₀.val p)).comp _)
    exact hpreferredR.comp (KahlerPerturbation.chartTransitionDerivative_injective c c₀ hsource)
  rw [coordinateMap_fderiv_change_target hf c d₀ d hz₀ hz]
  exact (KahlerPerturbation.chartTransitionDerivative_injective d₀ d
    (coordinateMap_mem_transition_source hz₀ hz)).comp hsourceR

/-- A genuine native projective immersion, specified by its actual
original mfderiv, gives an actual Kähler class in the original Cartier span. -/
theorem exists_kahler_mem_neronSeveri_of_native_projective_immersion {N : ℕ}
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (hinj : ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) f p)) :
    ∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
      RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X :=
  exists_kahler_mem_neronSeveri_of_projective_immersion f
    (fun c d _ hz => coordinateMap_fderiv_injective_of_native_mfderiv f.contMDiff hinj c d hz)

/-- In particular every actual original holomorphic projective embedding
in the existing coordinate definition has an actual NS_R Kähler class. -/
theorem exists_kahler_mem_neronSeveri_of_holomorphic_projective_embedding {N : ℕ}
    {f : X → ComplexProjectiveSpace N} (hf : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) f) :
    ∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
      RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X :=
  exists_kahler_mem_neronSeveri_of_projective_immersion
    ⟨f, SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hf⟩
      (SGPT.GAGA.TowerAlg.injective_fderiv_coordinateMap_of_isHolomorphicEmbedding hf)

end SGPT.BDivisor.NSKodaira
