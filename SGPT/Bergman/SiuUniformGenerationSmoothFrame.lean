import SGPT.Bergman.SiuUniformGenerationBundleProjection

/-!
# Actual smooth nonzero frames on prescribed coordinate balls

The finite atlas-frame embedding and its actual smooth projector feed the
finite radial projection product.  Its vectors retract to the original line
bundle fibres.  Smoothness is read through every original atlas coefficient in
the prescribed coordinate chart; no uniform frame domain is assumed.

Blueprint: `siu-uniform-generation.tex`, node `siu-uniform:smooth-frame`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : HermitianHolomorphicLineBundle.{0, 0} n X}

namespace FrameEmbedding

variable (P : FramePartition n L.Fiber)

/-- A smooth ambient function retracts to the actual original fibres. -/
def retractedSection (c : ComplexChart n X) (v : ComplexModel n → Fin P.card → ℂ)
    (x : X) : L.Fiber x := retract P x (v (c.val x))

theorem contDiffOn_retractedSection_coefficient
    (c : ComplexChart n X) {p : ComplexModel n} {r : ℝ}
    (hball : ball p r ⊆ c.val.target)
    (v : ComplexModel n → Fin P.card → ℂ) (hv : ContDiffOn ℝ ∞ v (ball p r))
    (e : AtlasFrame L) :
    ContDiffOn ℝ ∞ (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z)
      (retractedSection P c v (c.val.symm z)))
      (ball p r ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let U : Set (ComplexModel n) := ball p r ∩ c.val.symm ⁻¹' e.val.baseSet
  have hUt : U ⊆ c.val.target := fun z hz => hball hz.1
  have hUe : U ⊆ c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet :=
    fun z hz => ⟨hball hz.1, hz.2⟩
  have hd : ContDiffOn ℝ ∞ (fun z => (denominator P (c.val.symm z) : ℂ)⁻¹) U :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_denominator P c)).inv
      (fun z _ => Complex.ofReal_ne_zero.mpr (denominator_pos P _).ne')).mono hUt
  have hsum : ContDiffOn ℝ ∞
      (fun z => ∑ b, v z b * ((P.part b (c.val.symm z) : ℂ) *
        e.val.continuousLinearMapAt ℂ (c.val.symm z) ((P.frame b).symm (c.val.symm z) 1))) U := by
    refine ContDiffOn.sum fun b _ => ?_
    have hvb : ContDiffOn ℝ ∞ (fun z => v z b) (ball p r) :=
      ((ContinuousLinearMap.proj b : (Fin P.card → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hv
    exact (hvb.mono inter_subset_left).mul
      ((contDiffOn_cutoff_frameCoefficient c e ⟨P.frame b, P.mem b⟩ (P.smooth b)
        (P.support b)).mono hUe)
  refine (hd.mul hsum).congr fun z hz => ?_
  have hcz : c.val (c.val.symm z) = z := c.val.right_inv (hball hz.1)
  simp only [retractedSection, hcz, retract, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end FrameEmbedding

/-- Every original line bundle on a compact base has an actual nonzero smooth
frame on every strictly smaller prescribed chart ball.  The conclusion retains
the original fibres, and smoothness is proved for every original atlas-frame
coefficient in that chart.  The finite subdivision may depend on `L`. -/
theorem exists_chartSmooth_nonzero_frame [CompactSpace X]
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (p : ComplexModel n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hball : ball p R ⊆ c.val.target) :
    ∃ s : (x : X) → L.Fiber x,
      (∀ e : AtlasFrame L, ContDiffOn ℝ ∞
        (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z)))
        (ball p r ∩ c.val.symm ⁻¹' e.val.baseSet)) ∧
      ∀ x ∈ c.val.source ∩ c.val ⁻¹' ball p r, s x ≠ 0 := by
  obtain ⟨P⟩ := exists_framePartition (n := n) L.Fiber
  let e₀ := prefFrame L (c.val.symm p)
  let u₀ : L.Fiber (c.val.symm p) := e₀.val.symm (c.val.symm p) 1
  have hu₀ : u₀ ≠ 0 := norm_pos_iff.mp
    (SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_pos L.Fiber e₀.val (mem_prefFrame L _))
  let v₀ : Fin P.card → ℂ := FrameEmbedding.embed P (c.val.symm p) u₀
  have hv₀ : v₀ ≠ 0 := FrameEmbedding.embed_ne_zero P _ hu₀
  have hfix₀ : FrameEmbedding.projectionCLM P (c.val.symm p) v₀ = v₀ := by
    rw [FrameEmbedding.projectionCLM_apply]
    exact FrameEmbedding.projection_embed P _ u₀
  obtain ⟨v, hv, hvfix⟩ := exists_smooth_nonzero_fixedVector_on_ball
    (fun z => FrameEmbedding.projectionCLM P (c.val.symm z)) p hr hrR
    ((FrameEmbedding.contDiffOn_projectionCLM P c).mono hball)
    (fun z _ w => FrameEmbedding.projectionCLM_idempotent P _ w) v₀ hv₀ hfix₀
  let s : (x : X) → L.Fiber x := FrameEmbedding.retractedSection P c v
  have hsmall : ball p r ⊆ c.val.target := (ball_subset_ball hrR.le).trans hball
  refine ⟨s, fun e => FrameEmbedding.contDiffOn_retractedSection_coefficient P c hsmall v hv e, ?_⟩
  intro x hx
  have h := hvfix (c.val x) hx.2
  have hfixed : FrameEmbedding.projection P x (v (c.val x)) = v (c.val x) := by
    have hh := h.2
    rw [FrameEmbedding.projectionCLM_apply, c.val.left_inv hx.1] at hh
    exact hh
  exact FrameEmbedding.retract_ne_zero_of_projection_fixed P x h.1 hfixed

end SGPT.Bergman.SiuUniformGeneration
