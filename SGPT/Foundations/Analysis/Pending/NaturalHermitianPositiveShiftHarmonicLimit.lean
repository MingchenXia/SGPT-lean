import SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftResolvent
import SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakResolvent

set_option autoImplicit false

/-! # Actual strong positive-shift harmonic limit in the original Hilbert norm
All five entire mathematical proofs precede SOURCE. The actual dense
reduced-defect range and uniform contractions will produce the limit.
No compactness, spectral-gap or unshifted inverse certificate is used.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftHarmonicLimit

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianWeakResolvent NaturalHermitianWeakLaplacian
  NaturalHermitianWeakHarmonicKernel NaturalHermitianReducedWeakResolvent
  NaturalHermitianPositiveShiftResolvent

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (harmonicKernel w q) :=
  harmonicKernel_complete w q

/-- Literal scaled original positive-shift resolvent. -/
def scaledResolvent (w : KahlerBackground n M) (q : ℕ) (t : ℝ) (ht : 0 < t) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q :=
  t • positiveShiftResolvent w q t ht

theorem scaledResolvent_apply (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    scaledResolvent w q t ht f = t • positiveShiftResolvent w q t ht f := rfl

/-- Actual uniform contraction, derived from the genuine sharp inverse bound. -/
theorem scaledResolvent_norm_le (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ‖scaledResolvent w q t ht f‖ ≤ ‖f‖ := by
  have hnorm := norm_smul t (positiveShiftResolvent w q t ht f)
  have habs : ‖t‖ = t := Real.norm_of_nonneg ht.le
  calc
    ‖scaledResolvent w q t ht f‖ = ‖t‖ * ‖positiveShiftResolvent w q t ht f‖ := hnorm
    _ = t * ‖positiveShiftResolvent w q t ht f‖ :=
      congrArg (fun c => c * ‖positiveShiftResolvent w q t ht f‖) habs
    _ ≤ t * (t⁻¹ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (positiveShiftResolvent_norm_le w t ht f) ht.le
    _ = ‖f‖ := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem scaledResolvent_opNorm_le_one (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : ‖scaledResolvent w q t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  exact (scaledResolvent_norm_le w t ht f).trans_eq (one_mul ‖f‖).symm

theorem scaledResolvent_inner_symm (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (scaledResolvent w q t ht f) g = inner ℝ f (scaledResolvent w q t ht g) :=
  (real_inner_smul_left (positiveShiftResolvent w q t ht f) g t).trans
    ((congrArg (fun a => t * a) (positiveShiftResolvent_inner_symm w t ht f g)).trans
      (real_inner_smul_right f (positiveShiftResolvent w q t ht g) t).symm)

/-- Both true native inverse identities yield the literal original factor intertwining. -/
theorem positiveShiftResolvent_factor (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftResolvent w q t ht (positiveShiftFactor w q t f) = shiftedWeakResolvent w q f := by
  let e := positiveShiftFactorEquiv w q t ht
  have hi : e.symm (positiveShiftFactor w q t f) = f :=
    (congrArg e.symm (positiveShiftFactorEquiv_apply w t ht f).symm).trans
      (e.symm_apply_apply f)
  exact congrArg (shiftedWeakResolvent w q) hi

/-- Actual harmonic vectors are fixed by every original scaled resolvent. -/
theorem scaledResolvent_of_mem_harmonicKernel (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q)
    (hf : f ∈ harmonicKernel w q) : scaledResolvent w q t ht f = f := by
  have hr : shiftedWeakResolvent w q f = f := (mem_harmonicKernel_iff w f).mp hf
  have hb : positiveShiftFactor w q t f = t • f := by
    rw [positiveShiftFactor_apply, hr, sub_smul, one_smul]
    abel
  exact (map_smul (positiveShiftResolvent w q t ht) t f).symm.trans
    ((congrArg (positiveShiftResolvent w q t ht) hb.symm).trans
      ((positiveShiftResolvent_factor w t ht f).trans hr))

/-- Genuine original adjoint equality, obtained from the actual inner symmetry. -/
theorem scaledResolvent_adjoint (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.adjoint (scaledResolvent w q t ht) = scaledResolvent w q t ht :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    (fun f g => scaledResolvent_inner_symm w t ht f g)).symm

theorem scaledResolvent_mem_harmonic_orthogonal (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q)
    (hf : f ∈ (harmonicKernel w q)ᗮ) :
    scaledResolvent w q t ht f ∈ (harmonicKernel w q)ᗮ := by
  intro k hk
  exact (scaledResolvent_inner_symm w t ht k f).symm.trans
    ((congrArg (fun a => inner ℝ a f)
      (scaledResolvent_of_mem_harmonicKernel w t ht k hk)).trans (hf k hk))

theorem scaledResolvent_harmonicProjection (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    scaledResolvent w q t ht (harmonicProjection w q f) = harmonicProjection w q f :=
  scaledResolvent_of_mem_harmonicKernel w t ht _ (harmonicProjection_mem w f)

theorem harmonicProjection_scaledResolvent (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q (scaledResolvent w q t ht f) = harmonicProjection w q f := by
  have hp := harmonicProjection_mem w f
  have hr := scaledResolvent_mem_harmonic_orthogonal w t ht
    (f - harmonicProjection w q f) (sub_harmonicProjection_mem_orthogonal w f)
  have heq : scaledResolvent w q t ht (f - harmonicProjection w q f) =
      scaledResolvent w q t ht f - harmonicProjection w q f :=
    (map_sub (scaledResolvent w q t ht) f (harmonicProjection w q f)).trans
      (congrArg (fun a => scaledResolvent w q t ht f - a)
        (scaledResolvent_harmonicProjection w t ht f))
  exact Submodule.eq_starProjection_of_mem_orthogonal hp (heq ▸ hr)

theorem scaledResolvent_comp_harmonicProjection (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    (scaledResolvent w q t ht).comp (harmonicProjection w q) = harmonicProjection w q := by
  ext f
  exact scaledResolvent_harmonicProjection w t ht f

theorem harmonicProjection_comp_scaledResolvent (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    (harmonicProjection w q).comp (scaledResolvent w q t ht) = harmonicProjection w q := by
  ext f
  exact harmonicProjection_scaledResolvent w t ht f

/-- The actual intertwining gives decay on the dense original defect range. -/
theorem scaledResolvent_defect (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    scaledResolvent w q t ht (f - shiftedWeakResolvent w q f) =
      t • shiftedWeakResolvent w q f - t • scaledResolvent w q t ht
        (shiftedWeakResolvent w q f) := by
  have hb : positiveShiftFactor w q t f =
      (f - shiftedWeakResolvent w q f) + t • shiftedWeakResolvent w q f := by
    rw [positiveShiftFactor_apply, sub_smul, one_smul]
    abel
  have hj : positiveShiftResolvent w q t ht (f - shiftedWeakResolvent w q f) +
      t • positiveShiftResolvent w q t ht (shiftedWeakResolvent w q f) =
        shiftedWeakResolvent w q f := by
    exact ((map_add (positiveShiftResolvent w q t ht)
      (f - shiftedWeakResolvent w q f) (t • shiftedWeakResolvent w q f)).trans
      (congrArg (fun a => positiveShiftResolvent w q t ht
        (f - shiftedWeakResolvent w q f) + a)
        (map_smul (positiveShiftResolvent w q t ht) t (shiftedWeakResolvent w q f)))).symm.trans
          ((congrArg (positiveShiftResolvent w q t ht) hb.symm).trans
            (positiveShiftResolvent_factor w t ht f))
  exact (congrArg (fun a => t • a) (eq_sub_of_add_eq hj)).trans
    (smul_sub t _ _)

theorem scaledResolvent_defect_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ‖scaledResolvent w q t ht (f - shiftedWeakResolvent w q f)‖ ≤ 2 * t * ‖f‖ := by
  rw [scaledResolvent_defect]
  calc
    ‖t • shiftedWeakResolvent w q f - t • scaledResolvent w q t ht
        (shiftedWeakResolvent w q f)‖ ≤
        ‖t • shiftedWeakResolvent w q f‖ +
          ‖t • scaledResolvent w q t ht (shiftedWeakResolvent w q f)‖ := norm_sub_le _ _
    _ = t * ‖shiftedWeakResolvent w q f‖ +
        t * ‖scaledResolvent w q t ht (shiftedWeakResolvent w q f)‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le]
    _ ≤ t * ‖f‖ + t * ‖f‖ := add_le_add
      (mul_le_mul_of_nonneg_left (shiftedWeakResolvent_norm_le w f) ht.le)
      (mul_le_mul_of_nonneg_left
        ((scaledResolvent_norm_le w t ht _).trans (shiftedWeakResolvent_norm_le w f)) ht.le)
    _ = 2 * t * ‖f‖ := by ring

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup ((harmonicKernel w q)ᗮ) :=
  Submodule.normedAddCommGroup ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ ((harmonicKernel w q)ᗮ) :=
  Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := harmonicComplement_complete w q

theorem scaledResolvent_reducedDefect (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    scaledResolvent w q t ht (reducedDefect w q f).val =
      t • shiftedWeakResolvent w q f.val - t • scaledResolvent w q t ht
        (shiftedWeakResolvent w q f.val) :=
  scaledResolvent_defect w t ht f.val

theorem scaledResolvent_reducedDefect_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    ‖scaledResolvent w q t ht (reducedDefect w q f).val‖ ≤ 2 * t * ‖f‖ :=
  scaledResolvent_defect_norm_le w t ht f.val

/-- The true original dense defect range and uniform contraction produce the whole strong limit. -/
theorem scaledResolvent_tendsto_zero_on_orthogonal (w : KahlerBackground n M)
    {ι : Type*} (F : Filter ι) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (ht0 : Tendsto t F (𝓝 0)) (f : (harmonicKernel w q)ᗮ) :
    Tendsto (fun i => scaledResolvent w q (t i) (ht i) f.val) F (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := (reducedDefect_denseRange w q).exists_dist_lt f (half_pos hε)
  have happrox : ‖f.val - (reducedDefect w q y).val‖ < ε / 2 := by
    simpa only [dist_eq_norm, ← Submodule.coe_sub, Submodule.norm_coe] using hy
  have hb : Tendsto (fun i => 2 * t i * ‖y‖) F (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds.mul ht0).mul_const ‖y‖)
  have hev : ∀ᶠ i in F, 2 * t i * ‖y‖ < ε / 2 :=
    hb.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with i hi
  have hadd : scaledResolvent w q (t i) (ht i) f.val =
      scaledResolvent w q (t i) (ht i) (f.val - (reducedDefect w q y).val) +
        scaledResolvent w q (t i) (ht i) (reducedDefect w q y).val := by
    rw [map_sub]
    abel
  rw [dist_zero_right, hadd]
  calc
    ‖scaledResolvent w q (t i) (ht i) (f.val - (reducedDefect w q y).val) +
        scaledResolvent w q (t i) (ht i) (reducedDefect w q y).val‖ ≤
        ‖scaledResolvent w q (t i) (ht i) (f.val - (reducedDefect w q y).val)‖ +
          ‖scaledResolvent w q (t i) (ht i) (reducedDefect w q y).val‖ := norm_add_le _ _
    _ ≤ ‖f.val - (reducedDefect w q y).val‖ + 2 * t i * ‖y‖ := add_le_add
      (scaledResolvent_norm_le w (t i) (ht i) _)
      (scaledResolvent_reducedDefect_norm_le w (t i) (ht i) y)
    _ < ε / 2 + ε / 2 := add_lt_add happrox hi
    _ = ε := add_halves ε

/-- Original pointwise strong convergence to the actual native harmonic projection. -/
theorem scaledResolvent_tendsto_harmonicProjection (w : KahlerBackground n M)
    {ι : Type*} (F : Filter ι) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (ht0 : Tendsto t F (𝓝 0)) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    Tendsto (fun i => scaledResolvent w q (t i) (ht i) f) F
      (𝓝 (harmonicProjection w q f)) := by
  let g : (harmonicKernel w q)ᗮ :=
    ⟨f - harmonicProjection w q f, sub_harmonicProjection_mem_orthogonal w f⟩
  have hzero := scaledResolvent_tendsto_zero_on_orthogonal w F t ht ht0 g
  have hadd : ∀ i, scaledResolvent w q (t i) (ht i) f =
      harmonicProjection w q f + scaledResolvent w q (t i) (ht i) g.val := by
    intro i
    rw [map_sub, scaledResolvent_harmonicProjection]
    abel
  have hsum : Tendsto (fun i => harmonicProjection w q f +
      scaledResolvent w q (t i) (ht i) g.val) F (𝓝 (harmonicProjection w q f + 0)) :=
    tendsto_const_nhds.add hzero
  simpa only [add_zero, ← hadd] using hsum

/-- Exact original harmonic component of every positive-shift solution. -/
theorem harmonicProjection_positiveShiftResolvent (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q (positiveShiftResolvent w q t ht f) =
      t⁻¹ • harmonicProjection w q f := by
  have h : t • harmonicProjection w q (positiveShiftResolvent w q t ht f) =
      harmonicProjection w q f :=
    (map_smul (harmonicProjection w q) t (positiveShiftResolvent w q t ht f)).symm.trans
      (harmonicProjection_scaledResolvent w t ht f)
  calc
    harmonicProjection w q (positiveShiftResolvent w q t ht f) =
        t⁻¹ • (t • harmonicProjection w q (positiveShiftResolvent w q t ht f)) := by
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = t⁻¹ • harmonicProjection w q f := congrArg (fun a => t⁻¹ • a) h

theorem positiveShiftResolvent_mem_orthogonal_iff (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftResolvent w q t ht f ∈ (harmonicKernel w q)ᗮ ↔
      f ∈ (harmonicKernel w q)ᗮ := by
  constructor
  · intro h
    have hz := (harmonicProjection_eq_zero_iff w _).mpr h
    have hscale : t • harmonicProjection w q (positiveShiftResolvent w q t ht f) =
        harmonicProjection w q f :=
      (map_smul (harmonicProjection w q) t (positiveShiftResolvent w q t ht f)).symm.trans
        (harmonicProjection_scaledResolvent w t ht f)
    apply (harmonicProjection_eq_zero_iff w f).mp
    exact hscale.symm.trans ((congrArg (fun a => t • a) hz).trans (smul_zero t))
  · intro h
    apply (harmonicProjection_eq_zero_iff w _).mp
    exact (harmonicProjection_positiveShiftResolvent w t ht f).trans
      ((congrArg (fun a => t⁻¹ • a) ((harmonicProjection_eq_zero_iff w f).mpr h)).trans
        (smul_zero t⁻¹))

/-- The exact harmonic projection gives the genuine forcing norm lower bound. -/
theorem positiveShiftResolvent_harmonic_norm_lower (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    t⁻¹ * ‖harmonicProjection w q f‖ ≤ ‖positiveShiftResolvent w q t ht f‖ := by
  have hn : ‖harmonicProjection w q (positiveShiftResolvent w q t ht f)‖ =
      t⁻¹ * ‖harmonicProjection w q f‖ := by
    rw [harmonicProjection_positiveShiftResolvent, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  exact hn.symm.trans_le (harmonicProjection_apply_norm_le w _)

/-- Necessary unshifted forcing compatibility produces the actual strong zero limit. -/
theorem scaledResolvent_tendsto_zero_of_unshifted_solution (w : KahlerBackground n M)
    {ι : Type*} (F : Filter ι) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (ht0 : Tendsto t F (𝓝 0)) (f : HilbertFormL2 w.form.val w.isKahler.1 q)
    (a : weakDomain w q) (ha : weakLaplacian w q a = f) :
    harmonicProjection w q f = 0 ∧
      Tendsto (fun i => scaledResolvent w q (t i) (ht i) f) F (𝓝 0) := by
  have hp := unshifted_solution_forcing_orthogonal w f a ha
  exact ⟨hp, hp ▸ scaledResolvent_tendsto_harmonicProjection w F t ht ht0 f⟩

end SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftHarmonicLimit
