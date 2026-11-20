import SGPT.Okounkov.TranscendentalRelGenWeight
import SGPT.Bergman.SourceTensorDictionary
import SGPT.NAPotential.GAGAMultSiuGerms
import SGPT.NAPotential.NAGagaDisc

/-!
# The native pencil incidence domain for optimal extension

Domain producers for E2 of `thm:Bert`: proper holomorphic maps to a disc have
an actual smooth psh exhaustion, including maps whose source has larger
complex dimension than the disc. The pencil incidence retains the native
bundle equation rather than discarding its base locus.

Blueprint: `work/sgpt-resume-20261114/bert-e2/blueprint/bert-e2-incidence-tube.tex`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.IncidenceTubeExhaustion

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalRelGen

variable {n m : ℕ} {Z B : Type*}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  [TopologicalSpace B] [ChartedSpace (ComplexModel m) B] [IsComplexManifold m B]

/-- The proper-map exhaustion has no equal-dimension restriction; in
particular a native incidence manifold can map to a one-dimensional disc. -/
theorem isWeaklyPseudoconvexOpen_preimage_ball_of_proper_holomorphic {π : Z → B}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ π) (hπp : IsProperMap π)
    (d : ComplexChart m B) {p : ComplexModel m} {r : ℝ} (hball : closedBall p r ⊆ d.val.target) :
    IsWeaklyPseudoconvexOpen (n := n) (π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) := by
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hVdef
  have hVo : IsOpen V := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.continuous
  let ψ : Z → ℝ := fun y => ballExhaustion p r (d.val (π y))
  have hdom : ∀ e : ComplexChart n Z, e.val.target ∩ e.val.symm ⁻¹' V ⊆
      coordinateDomain π e d ∩ coordinateMap π e d ⁻¹' ball p r := by
    intro e w hw
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  refine ⟨hVo, ψ, ?_, ?_, ?_⟩
  · intro e
    refine ((contDiffOn_ballExhaustion p r).comp
      ((coordinateMap_contDiffOn_real hπ e d).mono fun w hw => (hdom e hw).1)
      fun w hw => (hdom e hw).2).congr fun w _ => rfl
  · intro e
    have hU : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hVo
    have hF : DifferentiableOn ℂ (coordinateMap π e d) (e.val.target ∩ e.val.symm ⁻¹' V) :=
      ((coordinateMap_contDiffOn hπ e d).differentiableOn (by simp)).mono fun w hw =>
        (hdom e hw).1
    have hpsh := plurisubharmonicOn_of_convexOn isOpen_ball (convexOn_ballExhaustion p r)
      (contDiffOn_ballExhaustion p r).continuousOn
    exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU hF
      (fun w hw => (hdom e hw).2) hpsh
  · intro t
    by_cases hr : 0 < r
    swap
    · convert isCompact_empty
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hy
      have h1 : dist (d.val (π y)) p < r := hy.2
      exact absurd (lt_of_le_of_lt dist_nonneg h1) hr
    by_cases ht : 0 < t
    · set s := Real.sqrt (max (r ^ 2 - t⁻¹) 0) with hs
      have hsr : s < r := by
        rw [hs, Real.sqrt_lt' hr]
        exact max_lt (by linarith [inv_pos.mpr ht]) (by positivity)
      have hsub : closedBall p s ⊆ d.val.target :=
        (closedBall_subset_closedBall hsr.le).trans hball
      have hsubb : closedBall p s ⊆ ball p r := closedBall_subset_ball hsr
      set K := π ⁻¹' (d.val.symm '' closedBall p s) with hK
      have hKc : IsCompact K := hπp.isCompact_preimage
        ((isCompact_closedBall p s).image_of_continuousOn (d.val.continuousOn_symm.mono hsub))
      have hKV : K ⊆ V := by
        rintro y ⟨v, hv, hvy⟩
        have hvt : v ∈ d.val.target := hsub hv
        refine ⟨?_, ?_⟩
        · rw [← hvy]; exact d.val.map_target hvt
        · change d.val (π y) ∈ ball p r
          rw [← hvy, d.val.right_inv hvt]
          exact hsubb hv
      have hψc : ContinuousOn ψ V := by
        refine (contDiffOn_ballExhaustion p r).continuousOn.comp ?_ fun y hy => hy.2
        exact (d.val.continuousOn.comp hπ.continuous.continuousOn fun y hy => hy.1)
      have hset : {y | y ∈ V ∧ ψ y ≤ t} = K ∩ ψ ⁻¹' Iic t := by
        ext y
        constructor
        · rintro ⟨hyV, hyt⟩
          refine ⟨⟨d.val (π y), ?_, d.val.left_inv hyV.1⟩, hyt⟩
          have hpos := ballExhaustion_pos hyV.2
          have h1 : t⁻¹ ≤ r ^ 2 - ‖d.val (π y) - p‖ ^ 2 := by
            have := (inv_le_inv₀ ht hpos).mpr hyt
            simpa [ballExhaustion, inv_inv] using this
          rw [mem_closedBall, dist_eq_norm, hs]
          refine Real.le_sqrt_of_sq_le ?_
          exact le_max_of_le_left (by linarith)
        · rintro ⟨hyK, hyt⟩
          exact ⟨hKV hyK, hyt⟩
      rw [hset]
      exact hKc.of_isClosed_subset
        ((hψc.mono hKV).preimage_isClosed_of_isClosed hKc.isClosed isClosed_Iic)
        inter_subset_left
    · -- no point of `V` has `ψ ≤ t ≤ 0`
      convert isCompact_empty
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      exact lt_of_le_of_lt (not_lt.mp ht) (ballExhaustion_pos hy.2)

open Bundle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle

section Pencil

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (A : HermitianHolomorphicLineBundle.{0, 0} n X)
  (s₀ s₁ : HolomorphicSections (n := n) A.Fiber)

/-- The original native pencil equation retains all base-locus points. -/
def pencilIncidence : Set (ComplexModel 1 × X) :=
  {q | s₀ q.2 = q.1 0 • s₁ q.2}

/-- The original pencil parameter on the actual incidence subtype. -/
def pencilProjection : pencilIncidence A s₀ s₁ → ComplexModel 1 := fun q => q.val.1

/-- A genuine atlas frame detects equality in the same original fibre. -/
theorem frameCoefficient_injective (e : AtlasFrame A) {x : X} (hx : x ∈ e.val.baseSet) :
    Function.Injective (e.val.continuousLinearMapAt ℂ x) := by
  let := e.property
  rw [← e.val.coe_continuousLinearEquivAt_eq hx]
  exact (e.val.continuousLinearEquivAt ℂ x hx).injective

/-- Closedness is proved from actual holomorphic bundle coefficients, not
from a chosen projective representative. -/
theorem isClosed_pencilIncidence : IsClosed (pencilIncidence A s₀ s₁) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro q hq
  let e : AtlasFrame A := ⟨trivializationAt ℂ A.Fiber q.2, inferInstance⟩
  let := e.property
  have hx : q.2 ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ A.Fiber q.2
  let f : ComplexModel 1 × X → ℂ := fun z =>
    e.val.continuousLinearMapAt ℂ z.2 (s₀ z.2) -
      z.1 0 * e.val.continuousLinearMapAt ℂ z.2 (s₁ z.2)
  have h₀ := SGPT.NAPotential.GAGAMult.holomorphicAt_coef_of_contMDiff e.val s₀.contMDiff hx
  have h₁ := SGPT.NAPotential.GAGAMult.holomorphicAt_coef_of_contMDiff e.val s₁.contMDiff hx
  have hf : ContinuousAt f q :=
    (h₀.self_of_nhds.continuousAt.comp continuous_snd.continuousAt).sub
      (((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous.comp continuous_fst).continuousAt.mul
        (h₁.self_of_nhds.continuousAt.comp continuous_snd.continuousAt))
  have hfne : f q ≠ 0 := by
    intro h
    apply hq
    apply frameCoefficient_injective A e hx
    rw [map_smul, smul_eq_mul]
    exact sub_eq_zero.mp h
  filter_upwards [hf.eventually_ne hfne] with z hz
  intro hinc
  apply hz
  change e.val.continuousLinearMapAt ℂ z.2 (s₀ z.2) -
    z.1 0 * e.val.continuousLinearMapAt ℂ z.2 (s₁ z.2) = 0
  rw [hinc, map_smul, smul_eq_mul, sub_self]

/-- Compactness of the original X makes the actual pencil projection
proper, including over its base locus. -/
theorem isProperMap_pencilProjection [CompactSpace X] :
    IsProperMap (pencilProjection A s₀ s₁) := by
  exact isProperMap_fst_of_compactSpace.comp
    ((isClosed_pencilIncidence A s₀ s₁).isClosedEmbedding_subtypeVal.isProperMap)

/-- Away from the denominator divisor the original pencil equation is
exactly the quotient in every actual frame. -/
theorem mem_pencilIncidence_iff_frame_ratio (e : AtlasFrame A) {x : X}
    (hx : x ∈ e.val.baseSet) (hs₁ : s₁ x ≠ 0) (t : ComplexModel 1) :
    (t, x) ∈ pencilIncidence A s₀ s₁ ↔
      t 0 = e.val.continuousLinearMapAt ℂ x (s₀ x) /
        e.val.continuousLinearMapAt ℂ x (s₁ x) := by
  let := e.property
  have hinj := frameCoefficient_injective A e hx
  have hden : e.val.continuousLinearMapAt ℂ x (s₁ x) ≠ 0 := by
    intro h
    apply hs₁
    apply hinj
    simpa only [map_zero] using h
  change s₀ x = t 0 • s₁ x ↔ _
  rw [eq_div_iff hden]
  constructor
  · intro h
    rw [h, map_smul, smul_eq_mul]
  · intro h
    apply hinj
    rw [map_smul, smul_eq_mul]
    exact h.symm

/-- The original ratio tube, expressed by the native pencil equation so
that no choice of frame enters its definition. -/
def pencilRatioTube (ρ : ℝ) : Set X :=
  {x | s₁ x ≠ 0 ∧ ∃ t ∈ ball (0 : ComplexModel 1) ρ, (t, x) ∈ pencilIncidence A s₀ s₁}

/-- In every actual frame the intrinsic tube is exactly
`|s₀/s₁| < ρ`, with its actual denominator divisor removed. -/
theorem mem_pencilRatioTube_iff (e : AtlasFrame A) {x : X} (hx : x ∈ e.val.baseSet) (ρ : ℝ) :
    x ∈ pencilRatioTube A s₀ s₁ ρ ↔ s₁ x ≠ 0 ∧
      ‖e.val.continuousLinearMapAt ℂ x (s₀ x) /
        e.val.continuousLinearMapAt ℂ x (s₁ x)‖ < ρ := by
  constructor
  · rintro ⟨hs₁, t, ht, hinc⟩
    have hratio := (mem_pencilIncidence_iff_frame_ratio A s₀ s₁ e hx hs₁ t).mp hinc
    refine ⟨hs₁, ?_⟩
    rw [← hratio, SGPT.NAPotential.NAGaga.norm_apply_zero]
    exact mem_ball_zero_iff.mp ht
  · rintro ⟨hs₁, hratio⟩
    let z := e.val.continuousLinearMapAt ℂ x (s₀ x) /
      e.val.continuousLinearMapAt ℂ x (s₁ x)
    let t : ComplexModel 1 := EuclideanSpace.single 0 z
    refine ⟨hs₁, t, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      simpa only [t, PiLp.norm_single] using hratio
    · apply (mem_pencilIncidence_iff_frame_ratio A s₀ s₁ e hx hs₁ t).mpr
      simp [t, z]

/-- Incidence over an actual open parameter region, before choosing a
native smooth incidence atlas on its regular locus. -/
def pencilIncidenceOver (U : TopologicalSpace.Opens (ComplexModel 1)) : Set (U × X) :=
  {q | (q.1.val, q.2) ∈ pencilIncidence A s₀ s₁}

/-- The original parameter projection on the restricted incidence family. -/
def pencilProjectionOver (U : TopologicalSpace.Opens (ComplexModel 1)) :
    pencilIncidenceOver A s₀ s₁ U → U := fun q => q.val.1

/-- Closedness survives restriction of the parameter region, including
all actual common zeros of the pencil sections. -/
theorem isClosed_pencilIncidenceOver (U : TopologicalSpace.Opens (ComplexModel 1)) :
    IsClosed (pencilIncidenceOver A s₀ s₁ U) :=
  (isClosed_pencilIncidence A s₀ s₁).preimage
    (continuous_subtype_val.prodMap continuous_id)

/-- The actual smooth-member parameter restriction is still proper. -/
theorem isProperMap_pencilProjectionOver [CompactSpace X]
    (U : TopologicalSpace.Opens (ComplexModel 1)) :
    IsProperMap (pencilProjectionOver A s₀ s₁ U) :=
  isProperMap_fst_of_compactSpace.comp
    ((isClosed_pencilIncidenceOver A s₀ s₁ U).isClosedEmbedding_subtypeVal.isProperMap)

/-- For any native smooth incidence structure whose actual projection is
holomorphic, a smaller parameter disc has the proved smooth psh exhaustion.
The only geometric input left visible is holomorphy of that projection. -/
theorem isWeaklyPseudoconvexOpen_pencilIncidenceTube [CompactSpace X]
    (U : TopologicalSpace.Opens (ComplexModel 1)) {k : ℕ}
    [ChartedSpace (ComplexModel k) (pencilIncidenceOver A s₀ s₁ U)]
    [IsComplexManifold k (pencilIncidenceOver A s₀ s₁ U)]
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel 1) ∞
      (pencilProjectionOver A s₀ s₁ U)) {ρ : ℝ} (hρ : 0 < ρ)
    (hdisc : closedBall (0 : ComplexModel 1) ρ ⊆ (U : Set (ComplexModel 1))) :
    IsWeaklyPseudoconvexOpen (n := k)
      {q : pencilIncidenceOver A s₀ s₁ U | q.val.1.val ∈ ball (0 : ComplexModel 1) ρ} := by
  let u₀ : U := ⟨0, hdisc (mem_closedBall_self hρ.le)⟩
  let d := complexChartAt (n := 1) u₀
  have hdsource : d.val.source = univ := by
    simp [d, complexChartAt, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq]
  have hdapply : ∀ u : U, d.val u = u.val := fun _ => rfl
  have hdtgt : d.val.target = (U : Set (ComplexModel 1)) := by
    simp [d, complexChartAt, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def, chartAt_self_eq]
  have h := isWeaklyPseudoconvexOpen_preimage_ball_of_proper_holomorphic hπ
    (isProperMap_pencilProjectionOver A s₀ s₁ U) d (by rwa [hdtgt])
  simpa only [hdsource, univ_inter, Set.preimage, Set.mem_ofPred_eq, hdapply, pencilProjectionOver] using h

end Pencil

end SGPT.Trace.IncidenceTubeExhaustion
