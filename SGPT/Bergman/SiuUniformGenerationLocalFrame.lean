import SGPT.Bergman.SiuUniformGenerationHolomorphicFrame
import SGPT.Bergman.SiuUniformGenerationGeometry
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.PSH.GlobalL2Correction

/-!
# Native coefficients, norms and curvature of the actual fixed-ball frames

The coefficient of a fibre vector is derived by normalizing any original
atlas coordinate of the actual nonzero frame section.  Reconstruction and
frame independence are proved.  The actual smooth Hermitian metric supplies
the smooth frame weight and its full first-Chern identity.

Blueprint: `siu-uniform-correction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {L : HermitianHolomorphicLineBundle.{0, 0} n X}

theorem atlasCoefficient_ne_zero_of_section_ne_zero
    (s : (x : X) → L.Fiber x) (e : AtlasFrame L) {x : X}
    (hx : x ∈ e.val.baseSet) (hs : s x ≠ 0) :
    e.val.continuousLinearMapAt ℂ x (s x) ≠ 0 := by
  let := e.property
  intro hzero
  have h := trivialization_eq_coef_smul_frame e.val hx (s x)
  rw [hzero, zero_smul] at h
  exact hs h

/-- The actual continuous linear coordinate of a nonzero local section.
Values outside its nonzero locus are harmless zero junk. -/
def sectionCoordinate (s : (x : X) → L.Fiber x) (x : X) : L.Fiber x →L[ℂ] ℂ :=
  ((prefFrame L x).val.continuousLinearMapAt ℂ x (s x))⁻¹ •
    (prefFrame L x).val.continuousLinearMapAt ℂ x

theorem sectionCoordinate_section (s : (x : X) → L.Fiber x) {x : X} (hs : s x ≠ 0) :
    sectionCoordinate s x (s x) = 1 := by
  have hd := atlasCoefficient_ne_zero_of_section_ne_zero s (prefFrame L x) (mem_prefFrame L x) hs
  simp only [sectionCoordinate, smul_apply, smul_eq_mul, inv_mul_cancel₀ hd]

theorem eq_sectionCoordinate_smul (s : (x : X) → L.Fiber x) {x : X} (hs : s x ≠ 0)
    (u : L.Fiber x) : u = sectionCoordinate s x u • s x := by
  let e := prefFrame L x
  let := e.property
  have he : x ∈ e.val.baseSet := mem_prefFrame L x
  have hd := atlasCoefficient_ne_zero_of_section_ne_zero s e he hs
  have hsu := trivialization_eq_coef_smul_frame e.val he u
  have hss := trivialization_eq_coef_smul_frame e.val he (s x)
  calc u = e.val.continuousLinearMapAt ℂ x u • e.val.symm x 1 := hsu
    _ = ((e.val.continuousLinearMapAt ℂ x (s x))⁻¹ * e.val.continuousLinearMapAt ℂ x u) • s x := by
        symm
        calc ((e.val.continuousLinearMapAt ℂ x (s x))⁻¹ * e.val.continuousLinearMapAt ℂ x u) • s x
            = ((e.val.continuousLinearMapAt ℂ x (s x))⁻¹ * e.val.continuousLinearMapAt ℂ x u) •
              (e.val.continuousLinearMapAt ℂ x (s x) • e.val.symm x 1) :=
                congrArg (fun v : L.Fiber x =>
                  ((e.val.continuousLinearMapAt ℂ x (s x))⁻¹ * e.val.continuousLinearMapAt ℂ x u) • v) hss
          _ = e.val.continuousLinearMapAt ℂ x u • e.val.symm x 1 := by
              rw [smul_smul]
              congr 1
              field_simp
    _ = sectionCoordinate s x u • s x := rfl

/-- Comparison with every original atlas coordinate, including frames outside
the chosen fixed cover. -/
theorem sectionCoordinate_eq_inFrame (s : (x : X) → L.Fiber x) (e : AtlasFrame L)
    {x : X} (he : x ∈ e.val.baseSet) (hs : s x ≠ 0) (u : L.Fiber x) :
    sectionCoordinate s x u = e.val.continuousLinearMapAt ℂ x u /
      e.val.continuousLinearMapAt ℂ x (s x) := by
  have hd := atlasCoefficient_ne_zero_of_section_ne_zero s e he hs
  apply (eq_div_iff hd).mpr
  have h := congrArg (e.val.continuousLinearMapAt ℂ x) (eq_sectionCoordinate_smul s hs u)
  simpa only [map_smul, smul_eq_mul] using h.symm

theorem norm_eq_sectionCoordinate_mul (s : (x : X) → L.Fiber x) {x : X} (hs : s x ≠ 0)
    (u : L.Fiber x) : ‖u‖ = ‖sectionCoordinate s x u‖ * ‖s x‖ := by
  conv_lhs => rw [eq_sectionCoordinate_smul s hs u]
  exact norm_smul _ _

/-- A genuine holomorphic local frame has holomorphic scalar coordinates for
every genuine holomorphic section on its domain. -/
theorem differentiableOn_sectionCoordinate_chart
    (c : ComplexChart n X) {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (s S : (x : X) → L.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) L.Fiber s U) (hs0 : ∀ x ∈ U, s x ≠ 0)
    (hS : IsHolomorphicSectionOn (n := n) L.Fiber S V) :
    DifferentiableOn ℂ (fun z => sectionCoordinate s (c.val.symm z) (S (c.val.symm z)))
      (c.val.target ∩ c.val.symm ⁻¹' (U ∩ V)) := by
  intro z hz
  let e := prefFrame L (c.val.symm z)
  let := e.property
  have he : c.val.symm z ∈ e.val.baseSet := mem_prefFrame L _
  have hsd : DifferentiableAt ℂ (fun w => e.val.continuousLinearMapAt ℂ (c.val.symm w)
      (s (c.val.symm w))) z :=
    (differentiableOn_coord_of_holomorphicSectionOn (F := s) e.val c hU hs).differentiableAt
    ((c.val.isOpen_inter_preimage_symm (hU.inter e.val.open_baseSet)).mem_nhds ⟨hz.1, hz.2.1, he⟩)
  have hSd : DifferentiableAt ℂ (fun w => e.val.continuousLinearMapAt ℂ (c.val.symm w)
      (S (c.val.symm w))) z :=
    (differentiableOn_coord_of_holomorphicSectionOn (F := S) e.val c hV hS).differentiableAt
    ((c.val.isOpen_inter_preimage_symm (hV.inter e.val.open_baseSet)).mem_nhds ⟨hz.1, hz.2.2, he⟩)
  have hden := atlasCoefficient_ne_zero_of_section_ne_zero s e he (hs0 _ hz.2.1)
  have hdiff : DifferentiableAt ℂ (fun w =>
      e.val.continuousLinearMapAt ℂ (c.val.symm w) (S (c.val.symm w)) /
        e.val.continuousLinearMapAt ℂ (c.val.symm w) (s (c.val.symm w))) z := by
    simpa only [div_eq_mul_inv] using hSd.fun_mul (hsd.fun_inv hden)
  have hev : (fun w => sectionCoordinate s (c.val.symm w) (S (c.val.symm w))) =ᶠ[𝓝 z]
      fun w => e.val.continuousLinearMapAt ℂ (c.val.symm w) (S (c.val.symm w)) /
        e.val.continuousLinearMapAt ℂ (c.val.symm w) (s (c.val.symm w)) := by
    filter_upwards [(c.val.isOpen_inter_preimage_symm
      (hU.inter e.val.open_baseSet)).mem_nhds ⟨hz.1, hz.2.1, he⟩] with w hw
    exact sectionCoordinate_eq_inFrame s e hw.2.2 (hs0 _ hw.2.1) _
  exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt

/-- The physical frame weight of an actual section. -/
def sectionWeight (s : (x : X) → L.Fiber x) (c : ComplexChart n X) (z : ComplexModel n) : ℝ :=
  -Real.log (‖s (c.val.symm z)‖ ^ 2)

theorem isSmoothLocalPotential_sectionWeight
    (hL : IsSourceSmoothHermitianMetric L) {θ : ClosedRealOneOneForm n X}
    (hθ : IsOwnFirstChernForm L θ)
    {U : Set X} (hU : IsOpen U) (s : (x : X) → L.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) L.Fiber s U) (hs0 : ∀ x ∈ U, s x ≠ 0)
    (c : ComplexChart n X) :
    IsSmoothLocalPotential θ.val c (c.val.target ∩ c.val.symm ⁻¹' U) (sectionWeight s c) := by
  have hsm : ContDiffOn ℝ ∞ (fun z => ‖s (c.val.symm z)‖ ^ 2)
      (c.val.target ∩ c.val.symm ⁻¹' U) := by
    simpa only [sourceNativeHermitianMetric_normSq] using
      (sourceNativeHermitianMetric L hL).smooth s U hU hs c
  have hweight : localWeight (sourceNativeHermitianMetric L hL) s c = sectionWeight s c := by
    funext z
    simp only [localWeight, sectionWeight, sourceNativeHermitianMetric_normSq]
  refine ⟨c.val.isOpen_inter_preimage_symm hU, inter_subset_left,
    (hsm.log fun z hz => (sq_pos_of_pos (norm_pos_iff.mpr (hs0 _ hz.2))).ne').neg, ?_⟩
  intro z hz
  have hd := isFirstChernForm_firstChernForm (sourceNativeHermitianMetric L hL)
    s U hU hs hs0 c z hz.1 hz.2
  rw [hweight] at hd
  exact hd.symm.trans (sourceNativeFirstChernForm_geometricallyEq L hL hθ c hz.1)

variable [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- The finite family consists of actual sections of the original target
bundle on the preselected geometric balls. -/
theorem exists_fixedCover_holomorphicFrames [CompactSpace X]
    {μ : Measure X} {G : HermitianHolomorphicLineBundle.{0, 0} n X}
    (D : SiuCover μ G G) (E : HermitianHolomorphicLineBundle.{0, 0} n X) :
    ∃ s : Fin D.m → (x : X) → E.Fiber x,
      ∀ a, IsHolomorphicSectionOn (n := n) E.Fiber (s a)
          ((D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
            ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2)) ∧
        ∀ x ∈ (D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
          ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2), s a x ≠ 0 := by
  have hframe := fun a : Fin D.m => exists_holomorphic_nonzero_frame_on_chartBall E
    (D.chartX a) (ctr (n := n) (D.pt a))
    (show 0 < 3 * D.R a / 2 by linarith [D.R_pos a])
    (show 3 * D.R a / 2 < 2 * D.R a by linarith [D.R_pos a])
    (show ball (ctr (n := n) (D.pt a)) (2 * D.R a) ⊆ (D.chartX a).val.target from
      fun z hz => (D.hball a hz).1)
  choose s hs hs0 using hframe
  exact ⟨s, fun a => ⟨hs a, hs0 a⟩⟩

end SGPT.Bergman.SiuUniformGeneration
