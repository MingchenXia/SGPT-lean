import SGPT.Envelopes.LapClass3Measure

/-!
# Quasi-plurisubharmonic functions with bounded `ω`-Laplacian have bounded complex Hessian

Lane CZ-LP (`claude-cz-lp`, node `czlp:psh-hessian`).  If `g` is `θ'`-plurisubharmonic and has
bounded `ω`-Laplacian, then `g` has a bounded complex Hessian (`DNTC11.HasBoundedComplexHessian`):
`hasBoundedComplexHessian_of_isThetaPshPotential`.

*Proof.*  In a chart, `g ∘ e⁻¹` has an `L¹_loc` Hessian density `H` (`LapClass3Density`), the almost
everywhere limit of the complex Hessians of the strong approximations, so
`|Re tr(N⁻¹H)| ≤ K` almost everywhere (`N` the coefficient matrix of `ω`).  With a local potential
`ψ` of `θ'`, `g ∘ e⁻¹ + ψ` is plurisubharmonic, so `P = H + ∂∂̄ψ` is positive semidefinite almost
everywhere (`CZLp.IsHessianDensityOn.ae_hermQuad_nonneg_of_psh`).  For such `P`,
`⟨Pv, v⟩ ≤ tr P ‖v‖² ≤ (tr N) Re tr(N⁻¹P) ‖v‖²` (`re_dotProduct_mulVec_le`,
`re_trace_le_re_trace_mul`), and polarization bounds the entries.

This is the step `g = P_{θ + Aω}(f) ∈ C^{1,1̄} ∩ PSH ⇒ bounded complex Hessian` of the reduction of
`thm:DNTcontact` for `f ∈ C^{1,1̄}(X)` to the bounded-Hessian case (`LapClass3Contact`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix ComplexOrder ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11

/-! ### Algebra of semipositive Hermitian matrices -/

section Algebra

variable {n : ℕ}

theorem sesqForm_eq_dotProduct (P : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    sesqForm P v v = star (fun i => star (v i)) ⬝ᵥ (P *ᵥ fun i => star (v i)) := by
  simp only [sesqForm, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem posSemidef_of_hermQuad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hPh : P.IsHermitian)
    (hP : ∀ v, 0 ≤ hermQuad P v) : P.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hPh fun x => ?_
  set v : ComplexModel n := WithLp.toLp 2 (fun i => star (x i)) with hv
  have hx : (fun i => star (v i)) = x := by
    funext i
    simp [hv]
  have h1 := sesqForm_eq_dotProduct P v
  rw [hx] at h1
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · have := hP v
    rwa [hermQuad, h1] at this
  · exact (hPh.im_star_dotProduct_mulVec_self x).symm

theorem hermQuad_le_trace_mul {P : Matrix (Fin n) (Fin n) ℂ} (hPh : P.IsHermitian)
    (hP : ∀ v, 0 ≤ hermQuad P v) (v : ComplexModel n) :
    hermQuad P v ≤ P.trace.re * ‖v‖ ^ 2 := by
  have hpsd := posSemidef_of_hermQuad_nonneg hPh hP
  have h := re_dotProduct_mulVec_le hpsd (fun i => star (v i))
  rw [hermQuad, sesqForm_eq_dotProduct]
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- **Entries of a semipositive matrix with a trace bound.** -/
theorem norm_apply_le_of_trace {N S H : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef)
    (hP : ∀ v, 0 ≤ hermQuad (H + S) v) (hPh : (H + S).IsHermitian) {K c₁ c₃ T : ℝ}
    (hH : (N⁻¹ * H).trace.re ≤ K) (hS : (N⁻¹ * S).trace.re ≤ c₁) (hT : N.trace.re ≤ T)
    (hSb : ∀ i j, ‖S i j‖ ≤ c₃) (i j : Fin n) :
    ‖H i j‖ ≤ 4 * (T * (K + c₁)) + c₃ := by
  have hpsd := posSemidef_of_hermQuad_nonneg hPh hP
  have htr := re_trace_le_re_trace_mul hN hpsd
  have hNtr : 0 ≤ N.trace.re := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [Matrix.trace]
    · have : Nonempty (Fin n) := ⟨⟨0, h0⟩⟩
      exact (Complex.pos_iff.mp hN.trace_pos).1.le
  have hsum : (N⁻¹ * (H + S)).trace.re ≤ K + c₁ := by
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    linarith
  have hpsd0 : 0 ≤ (H + S).trace.re := by
    have : 0 ≤ (H + S).trace := hpsd.trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  have hKc : 0 ≤ K + c₁ := by
    by_contra hneg
    push Not at hneg
    have : (N⁻¹ * (H + S)).trace.re < 0 := lt_of_le_of_lt hsum hneg
    have h2 : N.trace.re * (N⁻¹ * (H + S)).trace.re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hNtr this.le
    by_cases hNz : N.trace.re = 0
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [Matrix.trace] at this
      · have : Nonempty (Fin n) := ⟨⟨0, h0⟩⟩
        exact absurd hNz (Complex.pos_iff.mp hN.trace_pos).1.ne'
    · have : N.trace.re * (N⁻¹ * (H + S)).trace.re < 0 :=
        mul_neg_of_pos_of_neg (lt_of_le_of_ne hNtr (Ne.symm hNz)) this
      linarith
  have htrP : (H + S).trace.re ≤ T * (K + c₁) :=
    htr.trans ((mul_le_mul_of_nonneg_left hsum hNtr).trans (mul_le_mul_of_nonneg_right hT hKc))
  have hq : ∀ v, |hermQuad (H + S) v| ≤ T * (K + c₁) * ‖v‖ ^ 2 := fun v => by
    rw [abs_of_nonneg (hP v)]
    exact (hermQuad_le_trace_mul hPh hP v).trans
      (mul_le_mul_of_nonneg_right htrP (sq_nonneg _))
  have hent := norm_polarize_le hq i j
  rw [polarize_hermQuad hPh] at hent
  have : H i j = (H + S) i j - S i j := by simp
  rw [this]
  exact (norm_sub_le _ _).trans (add_le_add hent (hSb i j))

end Algebra

/-! ### The manifold statement -/

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
theorem continuousOn_inv_coeff (w : KahlerBackground (m + 1) Y) (e : ComplexChart (m + 1) Y) :
    ContinuousOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z))⁻¹) e.val.target := by
  have hN : ContinuousOn (fun z => normalizedHermitianMatrix (w.form.val.coeff e z))
      e.val.target := by
    have hlin : Continuous fun A : CoordinateRealTwoForm (m + 1) => normalizedHermitianMatrix A := by
      unfold normalizedHermitianMatrix
      fun_prop
    exact hlin.comp_continuousOn (w.form.val.smooth e).continuousOn
  have hdet : ContinuousOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z)).det)
      e.val.target := (continuous_id.matrix_det).comp_continuousOn hN
  have hadj : ContinuousOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z)).adjugate)
      e.val.target := (continuous_id.matrix_adjugate).comp_continuousOn hN
  have hne : ∀ z ∈ e.val.target, (normalizedHermitianMatrix (w.form.val.coeff e z)).det ≠ 0 :=
    fun z hz => (posDef_coeff w.isKahler.1 hz).det_pos.ne'
  have heq : EqOn (fun z => (normalizedHermitianMatrix (w.form.val.coeff e z))⁻¹)
      (fun z => ((normalizedHermitianMatrix (w.form.val.coeff e z)).det)⁻¹ •
        (normalizedHermitianMatrix (w.form.val.coeff e z)).adjugate) e.val.target := by
    intro z hz
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((hdet.inv₀ hne).smul hadj).congr heq

/-- **A `θ'`-psh function with bounded `ω`-Laplacian has a bounded complex Hessian.** -/
theorem hasBoundedComplexHessian_of_isThetaPshPotential (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {g : Y → ℝ} (hg : HasBoundedMetricLaplacian w g)
    (hpsh : IsThetaPshPotential θ.val (fun x => (g x : EReal))) :
    HasBoundedComplexHessian (n := m + 1) g := by
  classical
  refine ⟨hg.1, fun e => ?_⟩
  obtain ⟨A⟩ := nonempty_lapApprox w hg
  obtain ⟨H, hH, hHt⟩ := A.exists_density hg.1 e
  set N : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    fun z => normalizedHermitianMatrix (w.form.val.coeff e z) with hNdef
  -- the trace bound
  have htr : ∀ᵐ z, z ∈ e.val.target → ((N z)⁻¹ * H z).trace.re ≤ A.K := by
    filter_upwards [hHt] with z hz hzt
    have hcont : Continuous fun B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ =>
        ((N z)⁻¹ * B).trace.re := by fun_prop
    have hlim := (hcont.tendsto _).comp (hz hzt)
    refine le_of_tendsto' hlim fun k => ?_
    have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hk := laplacian_eq w.isKahler.1 (chartSmooth_two_of _ (A.smooth k)) hx
    rw [e.val.right_inv hzt, chartLaplacian] at hk
    simp only [Function.comp_apply]
    rw [← hk]
    exact (le_abs_self _).trans (A.lap_le k _)
  -- local bounds
  have hloc : ∀ z₀ ∈ e.val.target, ∃ r > 0, ∃ C : ℝ,
      ∀ᵐ z, z ∈ ball z₀ r → ∀ i j, ‖H z i j‖ ≤ C := by
    intro z₀ hz₀
    obtain ⟨W, ψ, hz₀W, hψ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z₀ hz₀
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hψ.1 z₀ hz₀W
    set r := ε / 2 with hr
    have hr0 : 0 < r := by positivity
    have hBW : closedBall z₀ r ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
    have hBt : closedBall z₀ r ⊆ e.val.target := hBW.trans hψ.2.1
    have hBc : IsCompact (closedBall z₀ r) := isCompact_closedBall _ _
    -- continuous data on the ball
    have hHψ : ∀ i j, ContinuousOn (fun z => complexHessian ψ z i j) W := fun i j =>
      continuousOn_complexHessian_apply hψ.1 hψ.2.2.1 i j
    have hHψm : ContinuousOn (fun z => complexHessian ψ z) W :=
      continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hHψ i j
    have hinv := continuousOn_inv_coeff w e
    have hc1 : ContinuousOn (fun z => ((N z)⁻¹ * complexHessian ψ z).trace.re) (closedBall z₀ r) :=
      (Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_trace).comp_continuousOn
        ((hinv.mono hBt).mul (hHψm.mono hBW))))
    have hT : ContinuousOn (fun z => (N z).trace.re) (closedBall z₀ r) := by
      have hlin : Continuous fun A : CoordinateRealTwoForm (m + 1) =>
          (normalizedHermitianMatrix A).trace.re := by
        simp only [normalizedHermitianMatrix, Matrix.trace, Matrix.diag]
        fun_prop
      exact hlin.comp_continuousOn ((w.form.val.smooth e).continuousOn.mono hBt)
    obtain ⟨c₁, hc₁⟩ := hBc.exists_bound_of_continuousOn hc1
    obtain ⟨T, hTb⟩ := hBc.exists_bound_of_continuousOn hT
    have hc3 : ∀ i j, ∃ c, ∀ z ∈ closedBall z₀ r, ‖complexHessian ψ z i j‖ ≤ c := fun i j => by
      obtain ⟨c, hc⟩ := hBc.exists_bound_of_continuousOn ((hHψ i j).mono hBW)
      exact ⟨c, fun z hz => by simpa using hc z hz⟩
    choose c₃ hc₃ using hc3
    set C₃ : ℝ := ∑ i, ∑ j, |c₃ i j| with hC₃
    have hC₃b : ∀ z ∈ closedBall z₀ r, ∀ i j, ‖complexHessian ψ z i j‖ ≤ C₃ := fun z hz i j =>
      (hc₃ i j z hz).trans ((le_abs_self _).trans
        ((Finset.single_le_sum (f := fun j => |c₃ i j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans (Finset.single_le_sum
            (f := fun i => ∑ j, |c₃ i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ i))))
    -- plurisubharmonicity
    have hV : IsLocallyBoundedPshOn ⟨W, hψ.1⟩ (fun z => g (e.val.symm z) + ψ z) :=
      isLocallyBoundedPshOn_chart hpsh hψ
        ((hg.1.comp_continuousOn (e.val.continuousOn_symm.mono hψ.2.1)).add hψ.2.2.1.continuousOn)
    have hdens : IsHessianDensityOn (fun z => g (e.val.symm z) + ψ z)
        (fun z => H z + smoothHess W ψ z) W := (hH.mono hψ.1 hψ.2.1).add_contDiffOn hψ.2.2.1
    have hpsd := hdens.ae_hermQuad_nonneg_of_psh hV
    refine ⟨r, hr0, 4 * (|T| * (A.K + |c₁|)) + C₃, ?_⟩
    filter_upwards [hpsd, htr] with z hz1 hz2 hzB i j
    have hzB' : z ∈ closedBall z₀ r := ball_subset_closedBall hzB
    have hzW : z ∈ W := hBW hzB'
    have hzt : z ∈ e.val.target := hBt hzB'
    have hsm : smoothHess W ψ z = complexHessian ψ z := by simp [smoothHess, hzW]
    have hP := hz1 hzW
    rw [hsm] at hP
    have hPh : (H z + complexHessian ψ z).IsHermitian := by
      have := hdens.isHermitian z
      rwa [hsm] at this
    have hc1z : ((N z)⁻¹ * complexHessian ψ z).trace.re ≤ |c₁| := by
      have := hc₁ z hzB'
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    have hTz : (N z).trace.re ≤ |T| := by
      have := hTb z hzB'
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact norm_apply_le_of_trace (posDef_coeff w.isKahler.1 hzt) hP hPh (hz2 hzt) hc1z hTz
      (hC₃b z hzB') i j
  -- assemble
  refine ⟨H, ⟨e.val.open_target, hg.1.comp_continuousOn e.val.continuousOn_symm, hH.isHermitian,
    hH.measurable, fun K hK hKt => ?_, hH.levi⟩⟩
  choose! r hr C hC using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ComplexModel (m + 1)) (r z))
    (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr z (hKt hz))⟩)
  refine ⟨∑ z ∈ t, |C z|, ?_⟩
  have hall : ∀ᵐ z, ∀ y ∈ t, z ∈ ball (y : ComplexModel (m + 1)) (r y) →
      ∀ i j, ‖H z i j‖ ≤ C y := by
    exact (Filter.eventually_all_finset t).mpr fun y _ => hC y (hKt y.2)
  filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae hall] with z hzK hz i j
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (ht hzK)
  exact (hz y hy hzy i j).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun y : K => |C y|) (fun _ _ => abs_nonneg _) hy))

end SGPT.Envelopes.LapClass3
