import SGPT.Projective.CurvePointNormalOrder
import SGPT.Bergman.SiuNativeSectionCartier

/-! Actual physical native section zero produces a genuine original chart
regular presentation with its SAME full point normal order.
Blueprint: native-curve-zero-presentation.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder DivisorRegularLocus
variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
  [IsComplexManifold 1 M]

/-- The SAME physical original chart coefficient produces its exact point
normal multiplicity, genuine regular presentation, and actual isolated zero. -/
theorem exists_native_curve_section_presentation
    (L : HermitianHolomorphicLineBundle.{0,0} 1 M) (s : HolomorphicSections (n := 1) L.Fiber)
    (e : AtlasFrame L) (p : M) (he : p ∈ e.val.baseSet) (hs : s p = 0)
    (hcoef : NativeHolGerm.mk (sectionCoefficient L.Fiber e.val s)
      (nativeSectionCoefficient_holomorphicAt L s e he) ≠ 0)
    (Ψ : DivisorFlattening (m := 0) ({p} : Set M) p) :
    let c := complexChartAt (n := 1) p
    ∃ P : RegularPresentation (sectionCoefficient L.Fiber e.val s ∘ c.val.symm) (c.val p),
      (P.m : ℕ∞) = normalOrder Ψ (NativeHolGerm.chartEquiv p
        (NativeHolGerm.mk (sectionCoefficient L.Fiber e.val s)
          (nativeSectionCoefficient_holomorphicAt L s e he))) ∧
      ∀ z ∈ P.U, (sectionCoefficient L.Fiber e.val s ∘ c.val.symm) z = 0 → z = c.val p := by
  let c := complexChartAt (n := 1) p
  let g := sectionCoefficient L.Fiber e.val s ∘ c.val.symm
  let x := c.val p
  have hpc : p ∈ c.val.source := mem_complexChartAt_source p
  let U := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hxU : x ∈ U := by
    refine ⟨c.val.map_source hpc, ?_⟩
    change c.val.symm (c.val p) ∈ e.val.baseSet
    rwa [c.val.left_inv hpc]
  have hgD : DifferentiableOn ℂ g U :=
    SGPT.Bergman.NativeHermitianMetric.sourceSectionCoefficient_chart_holomorphic L s c e
  have hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hgD z hz).differentiableAt (hU.mem_nhds hz)
  have hgz : g x = 0 := by
    change sectionCoefficient L.Fiber e.val s (c.val.symm (c.val p)) = 0
    rw [c.val.left_inv hpc]
    change e.val.linearEquivAt ℂ p he (s p) = 0
    rw [hs, map_zero]
  have hfreq : ∃ᶠ z in 𝓝 x, g z ≠ 0 := by
    by_contra h
    have hh : ∀ᶠ z in 𝓝 x, g z = 0 := by simpa only [Filter.not_frequently, not_ne_iff] using h
    apply hcoef
    change NativeHolGerm.mk _ _ = NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0)
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    filter_upwards [(c.val.continuousAt hpc).tendsto.eventually hh,
      c.val.open_source.mem_nhds hpc] with y hy hys
    simpa only [g, Function.comp_apply, c.val.left_inv hys] using hy
  obtain ⟨P, hPm, hPzero⟩ := exists_curve_regularPresentation g x hg hfreq hgz
  let G : ComplexModel 1 → ℂ := fun z => g (z + x)
  have hGt : Tendsto (fun z : ComplexModel 1 => z + x) (𝓝 0) (𝓝 x) := by
    simpa only [zero_add] using (continuous_add_const x).tendsto (0 : ComplexModel 1)
  have hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z := by
    filter_upwards [hGt.eventually hg] with z hz
    exact DifferentiableAt.comp (g := g) (f := fun y : ComplexModel 1 => y + x) z hz
      (differentiableAt_id.add_const x)
  have hmodel : NativeHolGerm.chartEquiv p (NativeHolGerm.mk
      (sectionCoefficient L.Fiber e.val s) (nativeSectionCoefficient_holomorphicAt L s e he)) =
      HolGerm.mk G hG := by
    apply Subtype.ext
    rfl
  have hGne : HolGerm.mk G hG ≠ 0 := by
    rw [← hmodel]
    exact (map_ne_zero_iff _ (NativeHolGerm.chartEquiv p).injective).mpr hcoef
  have horder := curvePoint_normalOrder_eq_analyticOrder p Ψ G hG hGne
  let F : ℂ → ℂ := fun z => g (curveScalarCoordinate.symm z)
  have htrans : (fun z : ℂ => G (curveScalarCoordinate.symm z)) =
      F ∘ (fun z : ℂ => z + curveScalarCoordinate x) := by
    funext z
    dsimp only [G, F, Function.comp_apply]
    rw [map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hshift : analyticOrderAt (F ∘ (fun z : ℂ => z + curveScalarCoordinate x)) 0 =
      analyticOrderAt F (curveScalarCoordinate x) := by
    simpa only [zero_add] using analyticOrderAt_comp_of_deriv_ne_zero
      (f := F) (g := fun z : ℂ => z + curveScalarCoordinate x)
      (z₀ := 0) (by fun_prop) (by simp)
  refine ⟨P, ?_, hPzero⟩
  rw [hmodel, horder, htrans, hshift]
  exact hPm.symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
