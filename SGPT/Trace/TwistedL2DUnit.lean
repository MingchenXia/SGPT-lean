import SGPT.Trace.TwistedL2DMatrix

/-!
# Families of local pieces read in the measurable unit frame

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:unit`).  Fix a twisted datum `T` on `ℂⁿ` and
the density `ρ` of its volume.  The measurable unit frame `ε` of `L` (`unitFrame`) has the
coefficient `uc e` in an atlas frame `e` (`ε = uc e · e`).  A local piece `h ⊗ e` is the vector
field `(h / uc e) ⊗ ε`; reading all pieces in `ε` turns a finite family into honest functions on
`ℂⁿ`, at the price of losing smoothness (`ε` is only measurable).

* `IsCovariant Q`: a frame-indexed local operator on coefficient fields which transforms like
  the coefficients under a change of frame; then `Q_{e₀}(W_{e₀}) = uc e₀ · ∑_i Q_{e_i}(h_i)/uc e_i`
  (`cov_sum`).  `ϑ_p`, `∂̄σ^♭` and the identity are covariant.
* `gam`: the unit-frame coefficient vector of `∂̄G` (measurable, frame independent).
* The three quantities of `SigmaGraphDensity` as integrals of unit-frame functions:
  `energy_eq` (`‖T*τ‖² = ∫ (a+b) s² |∑_i ϑ h_i / uc e_i|²`), `senergy_eq`
  (`∫ s² |∑_i ∂̄σ^♭h_i / uc e_i|²_σ`) and `localDataPairing_eq` (`∫ s² ⟪h / uc e, gam⟫`), with
  `s² = e^{-φ} ρ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)}

/-! ### The unit coefficient -/

/-- The coefficient of the unit frame in the frame `e` (zero off the base set). -/
def uc (e : AtlasFrame T.L) (z : ComplexModel n) : ℂ := e.val.baseSet.indicator (unitCoeff e) z

theorem measurable_uc (e : AtlasFrame T.L) : Measurable (uc e) :=
  measurable_indicator_unitCoeff e

theorem uc_of_mem {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e.val.baseSet) :
    uc e z = unitCoeff e z := indicator_of_mem hz _

theorem norm_uc_sq_mul {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e.val.baseSet) :
    ‖uc e z‖ ^ 2 * frameNormSq T.L e z = 1 := by
  rw [uc_of_mem hz]; exact norm_unitCoeff_mul e hz

theorem uc_ne_zero {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e.val.baseSet) :
    uc e z ≠ 0 := by
  rw [uc_of_mem hz]; exact unitCoeff_ne_zero e hz

/-- `uc e' = t_{e e'} uc e`. -/
theorem uc_trans {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    uc e' z = frameTrans T.L e e' z * uc e z := by
  rw [uc_of_mem hz.1, uc_of_mem hz.2]
  exact frameCoeff_eq_frameTrans_mul e e' (unitFrame T.L) hz

theorem inv_uc_trans {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet ∩ e'.val.baseSet) (c : ℂ) :
    (uc e' z)⁻¹ * (frameTrans T.L e e' z * c) = (uc e z)⁻¹ * c := by
  rw [uc_trans hz]
  have h1 := frameTrans_ne_zero e e' hz
  have h2 := uc_ne_zero (T := T) hz.1
  field_simp

theorem norm_uc_pos {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e.val.baseSet) :
    0 < ‖uc e z‖ := norm_pos_iff.mpr (uc_ne_zero hz)

theorem norm_inv_uc {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e.val.baseSet) :
    ‖(uc e z)⁻¹‖ = Real.sqrt (frameNormSq T.L e z) := by
  have h := norm_uc_sq_mul (T := T) hz
  have hp := norm_uc_pos (T := T) hz
  have hf : frameNormSq T.L e z = (‖uc e z‖⁻¹) ^ 2 := by
    field_simp; linarith
  rw [hf, Real.sqrt_sq (by positivity), norm_inv]

theorem continuousOn_frameNormSq (e : AtlasFrame T.L) :
    ContinuousOn (frameNormSq T.L e) e.val.baseSet := by
  have h := (T.metric_smooth chart0 e).continuousOn
  simp only [chart0_target, chart0_symm_apply, univ_inter] at h
  exact h

/-! ### The weight `s = √(e^{-φ} ρ)` -/

variable (T) in
/-- `s = √(e^{-φ} ρ)`, so that `s² dλ = e^{-φ} dμ`. -/
def sw (ρ : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ := Real.sqrt (Real.exp (-T.φ z) * ρ z)

variable {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ chart0 ρ)
include hρ

theorem sw_sq (z : ComplexModel n) : T.sw ρ z ^ 2 = Real.exp (-T.φ z) * ρ z :=
  Real.sq_sqrt (mul_nonneg (Real.exp_pos _).le (pos_of_isChartDensity hρ z).le)

theorem sw_pos (z : ComplexModel n) : 0 < T.sw ρ z :=
  Real.sqrt_pos.mpr (mul_pos (Real.exp_pos _) (pos_of_isChartDensity hρ z))

theorem continuousOn_sw : ContinuousOn (T.sw ρ) T.U := by
  have hφ := (T.contDiffOn_U T.φ_smooth).continuousOn
  exact ((Real.continuous_exp.comp_continuousOn hφ.neg).mul
    (continuous_of_isChartDensity hρ).continuousOn).sqrt

theorem exp_neg_pW_mul_norm_uc {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet) :
    Real.exp (-T.pW ρ e z) * ‖uc e z‖ ^ 2 = T.sw ρ z ^ 2 := by
  have h := T.exp_neg_localWeight e hρ (c := chart0) (z := z) ⟨mem_univ z, hz⟩
  simp only [chart0_symm_apply] at h
  rw [pW, h, sw_sq hρ]
  have := norm_uc_sq_mul (T := T) hz
  calc frameNormSq T.L e z * Real.exp (-T.φ z) * ρ z * ‖uc e z‖ ^ 2
      = (‖uc e z‖ ^ 2 * frameNormSq T.L e z) * (Real.exp (-T.φ z) * ρ z) := by ring
    _ = _ := by rw [this, one_mul]

omit hρ

/-! ### Covariant operators -/

/-- A frame-indexed local operator on coefficient fields, transforming like the coefficients. -/
structure IsCovariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q : AtlasFrame T.L → (ComplexModel n → ComplexModel n) → ComplexModel n → V) : Prop where
  congr : ∀ e u u' z, u =ᶠ[𝓝 z] u' → Q e u z = Q e u' z
  zero : ∀ e u z, u =ᶠ[𝓝 z] 0 → Q e u z = 0
  add : ∀ e {ι : Type} (s : Finset ι) (w : ι → ComplexModel n → ComplexModel n) z, z ∈ T.dom e →
    (∀ i ∈ s, ContDiffAt ℝ ∞ (w i) z) → Q e (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, Q e (w i) z
  gauge : ∀ e e' u z, z ∈ T.dom e → z ∈ T.dom e' → ContDiffAt ℝ ∞ u z →
    Q e' (fun y => frameTrans T.L e e' y • u y) z = frameTrans T.L e e' z • Q e u z

section Cov

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {Q : AtlasFrame T.L → (ComplexModel n → ComplexModel n) → ComplexModel n → V}
  {ι : Type} {s : Finset ι} {e : ι → AtlasFrame T.L} {h : ι → ComplexModel n → ComplexModel n}

theorem cov_piece (hQ : IsCovariant Q) (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))
    {e₀ : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e₀) (i : ι) :
    Q e₀ (transp T.L (e i) e₀ (h i)) z = uc e₀ z • (uc (e i) z)⁻¹ • Q (e i) (h i) z := by
  have hz' := (T.mem_dom).mp hz
  by_cases hzi : z ∈ (e i).val.baseSet
  · have hzdi : z ∈ T.dom (e i) := (T.mem_dom).mpr ⟨hzi, hz'.2⟩
    rw [hQ.congr _ _ _ z (transp_eventuallyEq_smul (h i) hzi),
      hQ.gauge (e i) e₀ (h i) z hzdi hz ((hh i).1.contDiffAt), smul_smul]
    congr 1
    rw [uc_trans ⟨hzi, hz'.1⟩]
    have h2 := uc_ne_zero (T := T) hzi
    field_simp
  · have hzs : z ∉ tsupport (h i) := fun h' => hzi (T.tsupport_subset_base hh i h')
    rw [hQ.zero _ _ z (transp_eventuallyEq_zero hzs),
      hQ.zero _ _ z (eventuallyEq_zero_of_notMem_tsupport hzs), smul_zero, smul_zero]

/-- **A covariant operator applied to the global field of a family.** -/
theorem cov_sum (hQ : IsCovariant Q) (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))
    {e₀ : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e₀) :
    Q e₀ (T.tot s e h e₀) z = uc e₀ z • ∑ i ∈ s, (uc (e i) z)⁻¹ • Q (e i) (h i) z := by
  have hz' := (T.mem_dom).mp hz
  change Q e₀ (fun y => ∑ i ∈ s, transp T.L (e i) e₀ (h i) y) z = _
  rw [hQ.add e₀ s _ z hz fun i _ => T.contDiffAt_transp hh i hz'.1, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => cov_piece hQ hh hz i

theorem cov_eq_zero (hQ : IsCovariant Q) (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))
    (i : ι) {z : ComplexModel n} (hz : z ∉ T.dom (e i)) : Q (e i) (h i) z = 0 :=
  hQ.zero _ _ z (eventuallyEq_zero_of_notMem_tsupport fun h' => hz (T.tsupport_subset_dom hh i h'))

end Cov

theorem isCovariant_theta {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ chart0 ρ) :
    IsCovariant (V := ℂ) fun e u z => chartTheta (T.pW ρ e) u z where
  congr e u u' z hu := chartTheta_congr hu
  zero e u z hu := chartTheta_eq_zero_of_eventuallyEq hu
  add e ι s w z _ hw := chartTheta_finset_sum s fun i hi => (hw i hi).differentiableAt (by simp)
  gauge e e' u z hz hz' hu := by
    rw [smul_eq_mul]
    exact chartTheta_gauge (T.gaugeData_pW (ρ := ρ) e e') ⟨hz, hz'⟩
      ((pW_contDiffAt hρ hz).differentiableAt (by simp)) (hu.differentiableAt (by simp))

theorem isCovariant_sigmaDbar :
    IsCovariant (T := T) (V := Matrix (Fin n) (Fin n) ℂ) fun _ u z => sigmaDbar T.omega T.r u z where
  congr _e _u _u' _z hu := sigmaDbar_congr hu
  zero _e _u _z hu := sigmaDbar_zero hu
  add e _ι s _w _z hz hw := sigmaDbar_sum s (dom_subset_U e hz) hw
  gauge e e' _u _z hz hz' hu :=
    sigmaDbar_smul (dom_subset_U e hz)
      ((T.gaugeData_pW (ρ := fun _ => 1) e e').differentiableAt ⟨hz, hz'⟩) hu

theorem isCovariant_id :
    IsCovariant (T := T) (V := ComplexModel n) fun _ u z => u z where
  congr e u u' z hu := hu.self_of_nhds
  zero e u z hu := by simpa using hu.self_of_nhds
  add e ι s w z _ _ := by simp
  gauge e e' u z _ _ _ := rfl

/-! ### The unit-frame coefficient of `∂̄G` -/

/-- The vector `(∂_{z̄_l} f)_l`. -/
def dbarV (f : ComplexModel n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun l => dbarDir (coordVec l) f z

variable (T) in
/-- `∂̄G` read in the unit frame through the frame `e`. -/
def gamE (e : AtlasFrame T.L) (z : ComplexModel n) : ComplexModel n :=
  (T.dom e).indicator (fun z => (uc e z)⁻¹ • dbarV (chartCoeff T.L chart0 e T.G) z) z

variable (T) in
/-- `∂̄G` in the unit frame. -/
def gam (z : ComplexModel n) : ComplexModel n := T.gamE (unitFrameTriv T.L z) z

theorem dbarV_G_trans {e e' : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e)
    (hz' : z ∈ T.dom e') :
    dbarV (chartCoeff T.L chart0 e' T.G) z =
      frameTrans T.L e e' z • dbarV (chartCoeff T.L chart0 e T.G) z := by
  have hzb : z ∈ e.val.baseSet ∩ e'.val.baseSet :=
    ⟨((T.mem_dom).mp hz).1, ((T.mem_dom).mp hz').1⟩
  have hG : DifferentiableAt ℝ (chartCoeff T.L chart0 e T.G) z :=
    ((T.contDiffOn_G e).contDiffAt ((T.isOpen_dom e).mem_nhds hz)).differentiableAt (by simp)
  have ht := (T.gaugeData_pW (ρ := fun _ => 1) e e').differentiableAt ⟨hz, hz'⟩
  ext l
  simp only [dbarV, PiLp.smul_apply, smul_eq_mul]
  rw [dbarDir_congr_of_eventuallyEq (T.chartCoeff_eventuallyEq e e' hzb), dbarDir_holo_mul ht hG]

theorem gamE_eq {e e' : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e)
    (hz' : z ∈ T.dom e') : T.gamE e' z = T.gamE e z := by
  have hzb : z ∈ e.val.baseSet ∩ e'.val.baseSet :=
    ⟨((T.mem_dom).mp hz).1, ((T.mem_dom).mp hz').1⟩
  rw [gamE, gamE, indicator_of_mem hz', indicator_of_mem hz, dbarV_G_trans hz hz', smul_smul,
    uc_trans hzb]
  have h1 := frameTrans_ne_zero e e' hzb
  have h2 := uc_ne_zero (T := T) hzb.1
  congr 1
  field_simp

theorem gam_eq {e : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e) :
    T.gam z = T.gamE e z := by
  have hz' : z ∈ T.dom (unitFrameTriv T.L z) :=
    (T.mem_dom).mpr ⟨mem_unitFrameTriv_baseSet T.L z, ((T.mem_dom).mp hz).2⟩
  rw [gam]
  exact gamE_eq hz hz'

theorem gam_eq_zero {z : ComplexModel n} (hz : z ∉ T.U) : T.gam z = 0 := by
  rw [gam, gamE, indicator_of_notMem]
  exact fun h => hz ((T.mem_dom).mp h).2

theorem measurable_gamE (e : AtlasFrame T.L) : Measurable (T.gamE e) := by
  classical
  have hc : ContinuousOn (dbarV (chartCoeff T.L chart0 e T.G)) (T.dom e) := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun l => ?_)
    exact (contDiffOn_dbarDir (T.isOpen_dom e) (T.contDiffOn_G e) _).continuousOn
  have hm : Measurable ((T.dom e).indicator (dbarV (chartCoeff T.L chart0 e T.G))) := by
    have := hc.measurable_piecewise (g := fun _ => (0 : ComplexModel n)) continuousOn_const
      (T.isOpen_dom e).measurableSet
    convert this using 1
    funext z
    by_cases hz : z ∈ T.dom e <;> simp [hz]
  have h2 : T.gamE e = fun z => (uc e z)⁻¹ • (T.dom e).indicator
      (dbarV (chartCoeff T.L chart0 e T.G)) z := by
    funext z
    by_cases hz : z ∈ T.dom e
    · simp [gamE, indicator_of_mem hz]
    · simp [gamE, indicator_of_notMem hz]
  rw [h2]
  exact ((measurable_uc e).inv).smul hm

open Classical in
theorem measurable_gam : Measurable T.gam := by
  have hX : Nonempty (ComplexModel n) := ⟨0⟩
  set E : ℕ → AtlasFrame T.L := fun k => atlasFrameAt T.L (frameSeq T.L hX k) with hE
  have hm := Measurable.find (f := fun k => T.gamE (E k))
    (p := fun k z => z ∈ (E k).val.baseSet) (fun k => measurable_gamE (E k))
    (fun k => (E k).val.open_baseSet.measurableSet) (frameSeq_spec T.L hX)
  convert hm using 1
  funext x
  have hfi : Nat.find (frameSeq_spec T.L hX x) = frameIndex T.L x := rfl
  rw [hfi]
  rfl

/-! ### The three quantities in the unit frame -/

theorem inner_dbarV (f : ComplexModel n → ℂ) (z v : ComplexModel n) :
    ⟪v, dbarV f z⟫_ℂ = dbarPairing f z v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dbarV, dotProduct, dbarPairing,
    Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem zeroTwoNormSq_smul (N β : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    zeroTwoNormSq N (c • β) = ‖c‖ ^ 2 * zeroTwoNormSq N β := by
  rw [← zeroTwoPair_re, ← zeroTwoPair_re, zeroTwoPair_smul, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]

section Quantities

include hρ

/-- **The `T*`-energy density in the unit frame.** -/
theorem FA_re_eq (F : T.FrameFamily) {z : ComplexModel n} (hz : z ∈ T.U) :
    (T.Φ (T.FA ρ) F.s F.e F.h z).re = (T.a z + T.b z) * T.sw ρ z ^ 2 *
      ‖∑ i ∈ F.s, (uc (F.e i) z)⁻¹ * chartTheta (T.pW ρ (F.e i)) (F.h i) z‖ ^ 2 := by
  have hz₀ : z ∈ T.dom (atlasFrameAt T.L z) := frameAt_mem_dom hz
  rw [Φ_eq_diag F.spec (isGaugeForm_tstar hρ) hz, FA_diag_re]
  have hc := cov_sum (isCovariant_theta hρ) F.spec (s := F.s) hz₀
  simp only [smul_eq_mul] at hc
  rw [hc, norm_mul, mul_pow]
  have hw := exp_neg_pW_mul_norm_uc hρ ((T.mem_dom).mp hz₀).1
  rw [← hw]
  ring

/-- **The `S`-energy density in the unit frame.** -/
theorem FS_re_eq (F : T.FrameFamily) {z : ComplexModel n} (hz : z ∈ T.U) :
    (T.Φ (T.FS ρ) F.s F.e F.h z).re = T.sw ρ z ^ 2 *
      zeroTwoNormSq (sigmaInv T.omega T.r z)
        (∑ i ∈ F.s, (uc (F.e i) z)⁻¹ • sigmaDbar T.omega T.r (F.h i) z) := by
  have hz₀ : z ∈ T.dom (atlasFrameAt T.L z) := frameAt_mem_dom hz
  rw [Φ_eq_diag F.spec (isGaugeForm_S hρ) hz]
  have hc := cov_sum (isCovariant_sigmaDbar (T := T)) F.spec (s := F.s) hz₀
  simp only [FS, cweight]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    zeroTwoPair_re, zeroTwoNormSq_smul]
  have hw := exp_neg_pW_mul_norm_uc hρ ((T.mem_dom).mp hz₀).1
  rw [← hw]
  ring

/-- **The data density in the unit frame.** -/
theorem FD_eq {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hz : z ∈ T.dom e) :
    dbarPairing (chartCoeff T.L chart0 e T.G) z (h z) * cweight (T.pW ρ e) z =
      ((T.sw ρ z ^ 2 : ℝ) : ℂ) * ⟪(uc e z)⁻¹ • h z, T.gam z⟫_ℂ := by
  have hzb := ((T.mem_dom).mp hz).1
  rw [gam_eq hz, gamE, indicator_of_mem hz, inner_smul_left, inner_smul_right, inner_dbarV,
    ← exp_neg_pW_mul_norm_uc hρ hzb, cweight]
  have hu := uc_ne_zero (T := T) hzb
  rw [map_inv₀, ← mul_assoc, ← mul_assoc]
  have this : (starRingEnd ℂ) (uc e z) * uc e z = ((‖uc e z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hn : (‖uc e z‖ : ℂ) ≠ 0 := by
    have := norm_uc_pos (T := T) hzb
    exact_mod_cast this.ne'
  have key : ((Real.exp (-T.pW ρ e z) * ‖uc e z‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (uc e z))⁻¹ *
      (uc e z)⁻¹ = ((Real.exp (-T.pW ρ e z) : ℝ) : ℂ) := by
    rw [mul_assoc, ← mul_inv, this]
    push_cast
    field_simp
  rw [key]
  ring

end Quantities

end TwistedDatum

end SGPT.Trace.TwistedL2
