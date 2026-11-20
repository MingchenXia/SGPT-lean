import SGPT.Bergman.SiuUniformGenerationProjection
import SGPT.LineBundle.TMetricBare
import SGPT.PSH.GlobalL2CoverSystem

/-!
# The actual finite-frame embedding and retraction of a line bundle

Given the existing finite atlas-frame partition of the original line bundle,
the embedding has components `χ_a e_a(u)`.  Its explicit left inverse is
`(Σ χ_a²)⁻¹ Σ χ_a w_a e_a⁻¹(1)`.  Thus the finite ambient projection is
constructed from the original bundle; its idempotence is proved rather than
assumed as a desired output.

Blueprint: `siu-uniform-generation.tex`, node `siu-uniform:smooth-frame`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter
open scoped Topology Manifold ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- A smooth cutoff supported in one frame domain makes its scalar transition
to a fixed frame smooth across the boundary of the first domain. -/
theorem contDiffOn_cutoff_frameTransition
    (c : ComplexChart n X) (e f : AtlasFrame L)
    {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hsupp : tsupport χ ⊆ f.val.baseSet) :
    ContDiffOn ℝ ∞ (fun z => (χ (c.val.symm z) : ℂ) * frameTransition f e (c.val.symm z))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have hχr := (hχ c).contDiffAt (c.val.open_target.mem_nhds hz.1)
  have hχc : ContDiffAt ℝ ∞ (fun w => (χ (c.val.symm w) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hχr
  by_cases hs : c.val.symm z ∈ tsupport χ
  · have hz' := hsupp hs
    let W := c.val.target ∩ c.val.symm ⁻¹' (f.val.baseSet ∩ e.val.baseSet)
    have hWo : IsOpen W := c.val.isOpen_inter_preimage_symm
      (f.val.open_baseSet.inter e.val.open_baseSet)
    have hzW : z ∈ W := ⟨hz.1, hz', hz.2⟩
    have hd : DifferentiableOn ℂ (fun w => frameTransition f e (c.val.symm w)) W := by
      intro w hw
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm c hw.1
        (frameTransition_mdifferentiableAt f e hw.2)).differentiableWithinAt
    exact hχc.mul (contDiffAt_real_of_differentiableOn_complex hd hWo hzW)
  · have heq : (fun w => (χ (c.val.symm w) : ℂ) * frameTransition f e (c.val.symm w))
        =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(c.val.isOpen_inter_preimage_symm
        (isClosed_tsupport χ).isOpen_compl).mem_nhds ⟨hz.1, hs⟩] with w hw
      simp only [image_eq_zero_of_notMem_tsupport hw.2, Complex.ofReal_zero, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The same cutoff estimate for the literal coordinate of the actual frame
vector, without replacing that vector by a proxy transition. -/
theorem contDiffOn_cutoff_frameCoefficient
    (c : ComplexChart n X) (e f : AtlasFrame L)
    {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hsupp : tsupport χ ⊆ f.val.baseSet) :
    ContDiffOn ℝ ∞ (fun z => (χ (c.val.symm z) : ℂ) *
      e.val.continuousLinearMapAt ℂ (c.val.symm z) (f.val.symm (c.val.symm z) 1))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let := e.property
  let := f.property
  refine (contDiffOn_cutoff_frameTransition c e f hχ hsupp).congr fun z hz => ?_
  by_cases hχ0 : χ (c.val.symm z) = 0
  · simp only [hχ0, Complex.ofReal_zero, zero_mul]
  · have hzf : c.val.symm z ∈ f.val.baseSet := hsupp (subset_tsupport _ hχ0)
    congr 1
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz.2]
    exact (Trivialization.coordChangeL_apply f.val e.val ⟨hzf, hz.2⟩ 1).symm

namespace FrameEmbedding

variable (P : FramePartition n L.Fiber)

/-- The positive scalar used to normalize the explicit retraction. -/
def denominator (x : X) : ℝ := ∑ a, P.part a x ^ 2

theorem denominator_pos (x : X) : 0 < denominator P x := by
  obtain ⟨a, ha⟩ := P.exists_part_pos x
  have hle : P.part a x ^ 2 ≤ denominator P x :=
    Finset.single_le_sum (fun b _ => sq_nonneg (P.part b x)) (Finset.mem_univ a)
  exact (sq_pos_of_pos ha).trans_le hle

/-- The literal original fibre embedded in one finite trivial ambient space. -/
def embed (x : X) (u : L.Fiber x) : Fin P.card → ℂ :=
  fun a => (P.part a x : ℂ) * P.coord a x u

/-- The actual fibre-valued left inverse, using the same finite atlas frames. -/
def retract (x : X) (w : Fin P.card → ℂ) : L.Fiber x :=
  (denominator P x : ℂ)⁻¹ •
    ∑ a, ((P.part a x : ℂ) * w a) • (P.frame a).symm x 1

theorem frame_term (x : X) (u : L.Fiber x) (a : Fin P.card) :
    ((P.part a x : ℂ) * embed P x u a) • (P.frame a).symm x 1 =
      (P.part a x ^ 2 : ℝ) • u := by
  let := P.mem a
  by_cases ha : P.part a x = 0
  · simp only [ha, Complex.ofReal_zero, zero_mul, zero_smul, zero_pow two_ne_zero]
  · have hx : x ∈ (P.frame a).baseSet := P.support a (subset_tsupport _ ha)
    have hrepr := SGPT.PSH.GlobalL2.trivialization_eq_coef_smul_frame (P.frame a) hx u
    change ((P.part a x : ℂ) * ((P.part a x : ℂ) * P.coord a x u)) •
      (P.frame a).symm x 1 = (P.part a x ^ 2 : ℝ) • u
    calc ((P.part a x : ℂ) * ((P.part a x : ℂ) * P.coord a x u)) •
          (P.frame a).symm x 1 = (P.part a x ^ 2 : ℝ) •
            (P.coord a x u • (P.frame a).symm x 1) := by
          change _ = ((P.part a x ^ 2 : ℝ) : ℂ) •
            (P.coord a x u • (P.frame a).symm x 1)
          rw [smul_smul, Complex.ofReal_pow]
          congr 1
          ring
      _ = (P.part a x ^ 2 : ℝ) • u :=
        congrArg (fun w : L.Fiber x => (P.part a x ^ 2 : ℝ) • w) hrepr.symm

/-- The finite-frame retraction is a genuine left inverse on every original
fibre, including points outside some of the individual frame domains. -/
theorem retract_embed (x : X) (u : L.Fiber x) : retract P x (embed P x u) = u := by
  have hd : (denominator P x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (denominator_pos P x).ne'
  unfold retract
  simp_rw [frame_term P x u]
  rw [← Finset.sum_smul]
  change (denominator P x : ℂ)⁻¹ • ((denominator P x : ℝ) • u) = u
  change (denominator P x : ℂ)⁻¹ • ((denominator P x : ℂ) • u) = u
  rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem embed_injective (x : X) : Function.Injective (embed P x) :=
  Function.LeftInverse.injective (retract_embed P x)

theorem embed_zero (x : X) : embed P x (0 : L.Fiber x) = 0 := by
  funext a
  simp [embed]

theorem embed_ne_zero (x : X) {u : L.Fiber x} (hu : u ≠ 0) : embed P x u ≠ 0 := by
  intro hzero
  exact hu (embed_injective P x (hzero.trans (embed_zero P x).symm))

/-- The actual finite ambient projection, before bundling its linear map. -/
def projection (x : X) (w : Fin P.card → ℂ) : Fin P.card → ℂ :=
  embed P x (retract P x w)

theorem projection_idempotent (x : X) (w : Fin P.card → ℂ) :
    projection P x (projection P x w) = projection P x w := by
  unfold projection
  rw [retract_embed]

theorem projection_embed (x : X) (u : L.Fiber x) :
    projection P x (embed P x u) = embed P x u := by
  unfold projection
  rw [retract_embed]

/-- A nonzero vector fixed by the actual projector retracts to a nonzero
vector of the original fibre, with no surrogate fibre or model identification. -/
theorem retract_ne_zero_of_projection_fixed (x : X) {w : Fin P.card → ℂ}
    (hw : w ≠ 0) (hfixed : projection P x w = w) : retract P x w ≠ 0 := by
  intro hzero
  apply hw
  rw [← hfixed, projection, hzero, embed_zero]

/-- Literal matrix entries of the original finite-frame projection. -/
def projectionCoefficient (a b : Fin P.card) (x : X) : ℂ :=
  (denominator P x : ℂ)⁻¹ * (P.part a x : ℂ) *
    ((P.part b x : ℂ) * P.coord a x ((P.frame b).symm x 1))

theorem contDiffOn_denominator (c : ComplexChart n X) :
    ContDiffOn ℝ ∞ (fun z => denominator P (c.val.symm z)) c.val.target :=
  ContDiffOn.sum fun a _ => (P.smooth a c).pow 2

theorem contDiffOn_projectionCoefficient (c : ComplexChart n X) (a b : Fin P.card) :
    ContDiffOn ℝ ∞ (fun z => projectionCoefficient P a b (c.val.symm z)) c.val.target := by
  let e : AtlasFrame L := ⟨P.frame a, P.mem a⟩
  let f : AtlasFrame L := ⟨P.frame b, P.mem b⟩
  intro z hz
  have hd : ContDiffAt ℝ ∞ (fun w => (denominator P (c.val.symm w) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((contDiffOn_denominator P c).contDiffAt (c.val.open_target.mem_nhds hz))
  have hd0 : (denominator P (c.val.symm z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (denominator_pos P _).ne'
  have hχ : ContDiffAt ℝ ∞ (fun w => (P.part a (c.val.symm w) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((P.smooth a c).contDiffAt (c.val.open_target.mem_nhds hz))
  by_cases hs : c.val.symm z ∈ tsupport (P.part a)
  · have he := P.support a hs
    have hco := (contDiffOn_cutoff_frameCoefficient c e f (P.smooth b) (P.support b)).contDiffAt
      ((c.val.isOpen_inter_preimage_symm e.val.open_baseSet).mem_nhds ⟨hz, he⟩)
    exact ((hd.inv hd0).mul hχ |>.mul hco).contDiffWithinAt
  · have heq : (fun w => projectionCoefficient P a b (c.val.symm w))
        =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(c.val.isOpen_inter_preimage_symm
        (isClosed_tsupport (P.part a)).isOpen_compl).mem_nhds ⟨hz, hs⟩] with w hw
      simp [projectionCoefficient, image_eq_zero_of_notMem_tsupport hw.2]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- A fixed coordinate matrix unit on the actual finite ambient space. -/
def coordinateOperator (a b : Fin P.card) :
    (Fin P.card → ℂ) →L[ℝ] (Fin P.card → ℂ) :=
  ((ContinuousLinearMap.proj b : (Fin P.card → ℂ) →L[ℂ] ℂ).smulRight
    (Pi.single a (1 : ℂ))).restrictScalars ℝ

/-- The original finite-frame projection bundled as a real continuous linear
endomorphism, for the finite projection-product theorem. -/
def projectionCLM (x : X) : (Fin P.card → ℂ) →L[ℝ] (Fin P.card → ℂ) :=
  ∑ a, ∑ b, projectionCoefficient P a b x • coordinateOperator P a b

theorem projectionCLM_apply (x : X) (w : Fin P.card → ℂ) :
    projectionCLM P x w = projection P x w := by
  classical
  ext a
  simp only [projectionCLM, sum_apply, smul_apply,
    coordinateOperator, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ∑ b, projectionCoefficient P a b x * w b =
    (P.part a x : ℂ) * P.coord a x
      ((denominator P x : ℂ)⁻¹ • ∑ b, ((P.part b x : ℂ) * w b) • (P.frame b).symm x 1)
  simp only [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp [projectionCoefficient]
  ring

theorem projectionCLM_idempotent (x : X) (w : Fin P.card → ℂ) :
    projectionCLM P x (projectionCLM P x w) = projectionCLM P x w := by
  simp only [projectionCLM_apply, projection_idempotent]

theorem contDiffOn_projectionCLM (c : ComplexChart n X) :
    ContDiffOn ℝ ∞ (fun z => projectionCLM P (c.val.symm z)) c.val.target :=
  ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
    (contDiffOn_projectionCoefficient P c a b).smul contDiffOn_const

end FrameEmbedding

end SGPT.Bergman.SiuUniformGeneration
