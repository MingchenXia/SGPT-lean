import SGPT.Trace.TwistedL2XSigma
import SGPT.Trace.TwistedL2SingularCompact

/-!
# The `S`-form on a manifold and the reduction to the density lemma

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:defect`,
`claude-tl2-man:sigma-reduction`).

* `TwistedDatum.FSX`: the `S`-form `⟨(gA_u)ᵀ - gA_u, (gA_w)ᵀ - gA_w⟩_σ |e|² e^{-φ}` with `g = σᵀ` and
  `A_u = ∂̄u` in the chart (by Kähler lowering, `claude-twisted-l2:kahler-lowering`, the `(0,2)`-form
  `(gA_u)ᵀ - gA_u` is `∂̄(σ^♭u)`); it is a gauge form (`isGaugeFormX_S`).
* `XFam.defect_le`: the `∂̄`-defect `Q(τ)` is at most `(sup a) · ‖S τ‖²` (pointwise Kähler identity
  `neg_re_traceMulConj_le`).
* `SigmaGraphDensityX` and `twistedL2CorrectionStatement_of_sigmaGraphDensityX`,
  `compactTwistedL2CorrectionStatement_of_sigmaGraphDensityX`: the main estimate on a manifold `X`
  (and its compact singular version) follows from the density of test families in
  `Dom T* ∩ ker S` for every datum on `X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### The matrix `A_u = ∂̄u` -/

theorem Amat_congr {u u' : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] u') : Amat u z = Amat u' z := by
  ext j k
  simp only [Amat, of_apply]
  exact dbarDir_congr (hu.mono fun y hy => by simp [hy])

theorem Amat_eq_zero {u : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] 0) : Amat u z = 0 := by
  rw [Amat_congr hu]
  ext j _
  simp [Amat, dbarDir_const]

theorem Amat_sum {ι : Type*} (s : Finset ι) {w : ι → ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hw : ∀ i ∈ s, DifferentiableAt ℝ (w i) z) :
    Amat (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, Amat (w i) z := by
  ext j k
  simp only [Amat, of_apply, Matrix.sum_apply, euclid_sum_apply]
  exact dbarDir_finset_sum_fun s fun i hi => differentiableAt_coord (hw i hi) j

theorem kahlerAntisym_sum (g : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    kahlerAntisym g (∑ i ∈ s, A i) = ∑ i ∈ s, kahlerAntisym g (A i) := by
  simp only [kahlerAntisym, Matrix.mul_sum, transpose_sum, Finset.sum_sub_distrib]

theorem kahlerAntisym_zero' (g : Matrix (Fin n) (Fin n) ℂ) : kahlerAntisym g 0 = 0 := by
  simp [kahlerAntisym]

theorem trS_self_eq (W : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    trS W W z = traceMulConj (Amat W z) := by
  rw [trS_eq_trace, traceMulConj, map_conj_eq_conjTranspose_transpose]

theorem continuousOn_Amat {D : Set (ComplexModel n)} (hD : IsOpen D)
    {u : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u D) :
    ContinuousOn (Amat u) D :=
  continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun _ =>
    (contDiffOn_dbarDir hD (contDiffOn_coord hu j) _).continuousOn

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The `S`-form `⟨∂̄σ^♭u, ∂̄σ^♭w⟩_σ |e|² e^{-φ}`, with `∂̄σ^♭u = (gA_u)ᵀ - gA_u`. -/
def FSX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  zeroTwoPair (gX T.omega T.r c z)⁻¹ (kahlerAntisym (gX T.omega T.r c z) (Amat u z))
    (kahlerAntisym (gX T.omega T.r c z) (Amat w z)) * ((T.wX c e z : ℝ) : ℂ)

variable {T}

theorem continuousOn_gXinv (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (fun z => (gX T.omega T.r c z)⁻¹) (T.pieceDomain c e) := by
  intro z hz
  have hσ := continuousOn_gX T.isOpen_U T.kahler c
  have hdet : (gX T.omega T.r c z).det ≠ 0 :=
    (posDef_gX T.isOpen_U T.kahler hz.1.1 hz.2).det_pos.ne'
  have hinv : ContinuousAt Ring.inverse (gX T.omega T.r c z).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' T.U) :=
    c.val.isOpen_inter_preimage_symm T.isOpen_U
  exact (ContinuousAt.comp (f := fun y => gX T.omega T.r c y)
    (continuousAt_matrix_inv _ hinv) (hσ.continuousAt (hO.mem_nhds ⟨hz.1.1, hz.2⟩)))
      |>.continuousWithinAt

theorem continuousOn_kahlerAntisym {D : Set (ComplexModel n)}
    {g A : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} (hg : ContinuousOn g D)
    (hA : ContinuousOn A D) : ContinuousOn (fun z => kahlerAntisym (g z) (A z)) D := by
  have hgc : ∀ a b : Fin n, ContinuousOn (fun z => g z a b) D := fun a b =>
    continuousOn_pi.mp (continuousOn_pi.mp hg a) b
  have hAc : ∀ a b : Fin n, ContinuousOn (fun z => A z a b) D := fun a b =>
    continuousOn_pi.mp (continuousOn_pi.mp hA a) b
  refine continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => ?_
  simp only [kahlerAntisym, Matrix.sub_apply, transpose_apply, mul_apply]
  exact (continuousOn_finsetSum Finset.univ fun l _ => (hgc k l).mul (hAc l j)).sub
    (continuousOn_finsetSum Finset.univ fun l _ => (hgc j l).mul (hAc l k))

theorem isGaugeFormX_S : T.IsGaugeFormX T.FSX where
  congr c e u u' w w' z hu hw := by simp only [FSX, Amat_congr hu, Amat_congr hw]
  zero c e u w z hw := by simp [FSX, Amat_eq_zero hw, kahlerAntisym_zero', zeroTwoPair_zero]
  add c e u ι s w z _ _ hw := by
    simp only [FSX]
    rw [Amat_sum s fun i hi => (hw i hi).differentiableAt (by simp), kahlerAntisym_sum,
      zeroTwoPair_sum, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' hu hw hu' hw' hru hrw := by
    obtain ⟨hzo, hzD, hW⟩ := gauge_setup hz hz'
    have hzd' := chg_mem_pieceDomain hz hz'
    set S := T.ovlD c c' e e'
    have hSo : IsOpen S := T.isOpen_ovlD c c' e e'
    have hψ : DifferentiableOn ℂ (chg c c') S :=
      (differentiableOn_chg c c').mono fun y hy => hy.1.2
    have ht : DifferentiableOn ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) S :=
      (differentiableOn_frameTrans c e e').mono fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.2⟩
    have hO := T.isOpen_pieceDomain c e
    have hO' := T.isOpen_pieceDomain c' e'
    have hAu := Amat_transport hSo hψ ht hzD
      ((hu.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
      ((hu'.contDiffAt (hO'.mem_nhds hzd')).differentiableAt (by simp)) hru
    have hAw := Amat_transport hSo hψ ht hzD
      ((hw.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
      ((hw'.contDiffAt (hO'.mem_nhds hzd')).differentiableAt (by simp)) hrw
    have hM : IsUnit (linMat (fderiv ℂ (chg c c') z)).det :=
      (isUnit_iff_isUnit_det _).mp (isUnit_linMat_fderiv_chg hzo)
    have hg : IsUnit (gX T.omega T.r c z).det :=
      isUnit_iff_ne_zero.mpr (posDef_gX T.isOpen_U T.kahler hz.1.1 hz.2).det_pos.ne'
    have hgg := gX_chg T.isOpen_U T.kahler hzo hz.2
    simp only [FSX]
    rw [kahlerAntisym_zeroTwoPair_transport hM hg hgg hAu hAw, ← hW]
    ring
  contOn c e u w hu hw := by
    have hO := T.isOpen_pieceDomain c e
    have hg : ContinuousOn (gX T.omega T.r c) (T.pieceDomain c e) :=
      (continuousOn_gX T.isOpen_U T.kahler c).mono fun z hz => ⟨hz.1.1, hz.2⟩
    exact (continuousOn_zeroTwoPair (continuousOn_gXinv c e)
      (continuousOn_kahlerAntisym hg (continuousOn_Amat hO hu))
      (continuousOn_kahlerAntisym hg (continuousOn_Amat hO hw))).mul (continuousOn_wXc c e)

namespace XFam

variable (F : T.XFam)

/-- The `S`-energy `‖∂̄(σ^♭ W_τ)‖²_σ` of a family (weight `|e|² e^{-φ}`). -/
def senergy : ℝ := ∫ x, (F.Φ T.FSX x).re ∂T.μ

theorem neg_FTX_le {Ma : ℝ} (hMa : ∀ x ∈ T.U, T.a x ≤ Ma) (x : X) :
    -(F.Φ T.FTX x).re ≤ Ma * (F.Φ T.FSX x).re := by
  by_cases hx : x ∈ T.U
  · set c := chartX (n := n) x
    set e := atlasFrameAt T.L x
    have hxs : x ∈ c.val.source ∩ e.val.baseSet := mem_ref
    have hz : c.val x ∈ T.pieceDomain c e := mem_pd_of_chart hx hxs
    rw [F.Φ_eq_diag isGaugeFormX_tr hx hxs, F.Φ_eq_diag isGaugeFormX_S hx hxs]
    simp only [FTX, FSX]
    have hT : (trS (F.tot c e) (F.tot c e) (c.val x) *
        ((T.aC c (c.val x) * T.wX c e (c.val x) : ℝ) : ℂ)).re =
        (traceMulConj (Amat (F.tot c e) (c.val x))).re *
          (T.aC c (c.val x) * T.wX c e (c.val x)) := by
      rw [trS_self_eq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hS : (zeroTwoPair (gX T.omega T.r c (c.val x))⁻¹
        (kahlerAntisym (gX T.omega T.r c (c.val x)) (Amat (F.tot c e) (c.val x)))
        (kahlerAntisym (gX T.omega T.r c (c.val x)) (Amat (F.tot c e) (c.val x))) *
        ((T.wX c e (c.val x) : ℝ) : ℂ)).re =
        zeroTwoNormSq (gX T.omega T.r c (c.val x))⁻¹
          (kahlerAntisym (gX T.omega T.r c (c.val x)) (Amat (F.tot c e) (c.val x))) *
          T.wX c e (c.val x) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        zeroTwoPair_re]
    rw [hT, hS]
    have hgpd : (gX T.omega T.r c (c.val x)).PosDef := posDef_gX T.isOpen_U T.kahler hz.1.1 hz.2
    have hdef := neg_re_traceMulConj_le hgpd (Amat (F.tot c e) (c.val x))
    have hZ := zeroTwoNormSq_nonneg hgpd
      (kahlerAntisym (gX T.omega T.r c (c.val x)) (Amat (F.tot c e) (c.val x)))
    have ha := aC_pos hz
    have haM : T.aC c (c.val x) ≤ Ma := hMa _ hz.2
    have hE := wX_pos (T := T) hz.1
    have k1 := mul_le_mul_of_nonneg_right hdef (mul_nonneg ha.le hE.le)
    have k2 := mul_le_mul_of_nonneg_right haM (mul_nonneg hZ hE.le)
    nlinarith [k1, k2]
  · simp [F.Φ_eq_zero isGaugeFormX_tr hx, F.Φ_eq_zero isGaugeFormX_S hx]

/-- **The `∂̄`-defect is controlled by the `S`-energy** (`claude-tl2-man:defect`). -/
theorem defect_le {Ma : ℝ} (hMa : ∀ x ∈ T.U, T.a x ≤ Ma) : F.defect ≤ Ma * F.senergy := by
  have iT := F.integrable_Φ (G := T.FTX) isGaugeFormX_tr
  have iS : Integrable (fun x => (F.Φ T.FSX x).re) T.μ :=
    (F.integrable_Φ (G := T.FSX) isGaugeFormX_S).re
  have iTr : Integrable (fun x => (F.Φ T.FTX x).re) T.μ := iT.re
  have hre : (∫ x, F.Φ T.FTX x ∂T.μ).re = ∫ x, (F.Φ T.FTX x).re ∂T.μ := (integral_re iT).symm
  unfold defect senergy
  rw [hre, ← integral_neg, ← integral_const_mul]
  exact integral_mono iTr.neg (iS.const_mul Ma) (F.neg_FTX_le hMa)

end XFam

/-- **Density of test families in `Dom T* ∩ ker S` on `X`** (FPT `lem:cutoff-mollifier-density`,
read on finite families of local pieces): every family can be approximated in the data pairing and
in the `T*`-energy by families of arbitrarily small `S`-energy. -/
def SigmaGraphDensityX (T : TwistedDatum n X) : Prop :=
  ∀ F : T.XFam, ∀ ε : ℝ, 0 < ε → ∃ F' : T.XFam,
    ‖F'.data - F.data‖ ≤ ε ∧ F'.energy ≤ F.energy + ε ∧ F'.senergy ≤ ε

theorem graphDensityX_of_sigmaGraphDensityX (h : T.SigmaGraphDensityX) : T.GraphDensityX := by
  intro F ε hε
  obtain ⟨m, Ma, hm, hb⟩ := T.bounds
  have hMa : ∀ x ∈ T.U, T.a x ≤ Ma := fun x hx => (hb x hx).2.1
  set M' := max Ma 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMa' : ∀ x ∈ T.U, T.a x ≤ M' := fun x hx => (hMa x hx).trans (le_max_left _ _)
  obtain ⟨F', h1, h2, h3⟩ := h F (min ε (ε / M')) (lt_min hε (div_pos hε hM'pos))
  refine ⟨F', h1.trans (min_le_left _ _), h2.trans (by linarith [min_le_left ε (ε / M')]), ?_⟩
  have hd := F'.defect_le hMa'
  have h3' : F'.senergy ≤ ε / M' := h3.trans (min_le_right _ _)
  calc F'.defect ≤ M' * F'.senergy := hd
    _ ≤ M' * (ε / M') := mul_le_mul_of_nonneg_left h3' hM'pos.le
    _ = ε := by field_simp

end TwistedDatum

variable (n X)

/-- **The main twisted estimate on a complex manifold from the density lemma**
(`claude-tl2-man:sigma-reduction`). -/
theorem twistedL2CorrectionStatement_of_sigmaGraphDensityX
    (hdens : ∀ T : TwistedDatum n X, T.SigmaGraphDensityX) : TwistedL2CorrectionStatement n X :=
  twistedL2CorrectionStatement_of_graphDensityX n X fun T =>
    TwistedDatum.graphDensityX_of_sigmaGraphDensityX (hdens T)

/-- The compact singular twisted estimate (`claude-twisted-l2:compact`) on `X` from the density
lemma on `X`. -/
theorem compactTwistedL2CorrectionStatement_of_sigmaGraphDensityX
    (hdens : ∀ T : TwistedDatum n X, T.SigmaGraphDensityX) :
    CompactTwistedL2CorrectionStatement n X :=
  compactTwistedL2CorrectionStatement_of_main n X
    (twistedL2CorrectionStatement_of_sigmaGraphDensityX n X hdens)

end SGPT.Trace.TwistedL2
