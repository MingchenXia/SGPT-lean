import SGPT.Trace.TwistedL2XTheta

/-!
# The integrands of the twisted Bochner--Kodaira argument on a manifold

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:levi`, `claude-tl2-man:forms`).

* `TwistedDatum.dDir_pX_transport`, `TwistedDatum.leviS_pX_transport`: the Levi form of the local
  weight `p = -log |e|²_h + φ - log ρ` is chart invariant.  The weights of two chart-frames differ by
  `log |t|² + log(ρ_c / ρ_{c'} ∘ ψ)`; instead of computing the Jacobian of `ψ` we read off from the
  chart invariance of `ϑ` (`chartTheta_transport`), applied to a constant field, that the
  `(1,0)`-derivative of the difference is holomorphic, so its Levi form vanishes.
* `TwistedDatum.IsGaugeFormX`: chart-frame-indexed local sesquilinear integrands (densities with
  respect to `μ`, read in chart coordinates) which are invariant under change of chart and frame.
* The six integrands `FθX` (twisted adjoint), `FLX` (twisted Levi form), `FTX` (`tr(A Ā)`), `FAX`
  (`T*`), `FHX` (twisted curvature), `FDX` (data) are gauge forms (`isGaugeFormX_theta`, …).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### Flat preliminaries -/

/-- The holomorphic divergence `∑_j ∂_j w_j`. -/
def hdiv (w : ComplexModel n → ComplexModel n) (y : ComplexModel n) : ℂ :=
  ∑ j, dDir (coordVec j) (fun x => w x j) y

theorem dDir_vec_eq_sum (f : ComplexModel n → ℂ) (y v : ComplexModel n) :
    dDir v f y = ∑ j, v j * dDir (coordVec j) f y := by
  conv_lhs => rw [← eq_sum_coordVec v]
  rw [dDir_sum_dir]

theorem chartTheta_eq_hdiv (p : ComplexModel n → ℝ) (w : ComplexModel n → ComplexModel n)
    (y : ComplexModel n) :
    chartTheta p w y = -hdiv w y + dDir (w y) (fun x => (p x : ℂ)) y := by
  have h : ∑ j, dDir (coordVec j) (fun x => (p x : ℂ)) y * w y j =
      dDir (w y) (fun x => (p x : ℂ)) y := by
    rw [dDir_vec_eq_sum]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [chartTheta, deltaDir, hdiv, Finset.sum_sub_distrib, h]
  ring

theorem hdiv_const (v y : ComplexModel n) : hdiv (fun _ => v) y = 0 := by
  simp [hdiv, dDir]

theorem differentiableOn_hdiv {w : ComplexModel n → ComplexModel n} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hw : DifferentiableOn ℂ w Ω) : DifferentiableOn ℂ (hdiv w) Ω := by
  have hj : ∀ j : Fin n, DifferentiableOn ℂ (fun x => w x j) Ω := fun j =>
    (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiable.comp_differentiableOn hw
  have h : DifferentiableOn ℂ (fun y => ∑ j, fderiv ℂ (fun x => w x j) y (coordVec j)) Ω :=
    DifferentiableOn.fun_sum fun j _ => differentiableOn_fderiv_apply_of_isOpen (hj j) hΩ _
  refine h.congr fun y hy => ?_
  simp only [hdiv]
  exact Finset.sum_congr rfl fun j _ =>
    dDir_eq_fderiv_complex ((hj j).differentiableAt (hΩ.mem_nhds hy)) _

theorem dDir_ofReal_sub {f g : ComplexModel n → ℝ} {y v : ComplexModel n}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dDir v (fun x => ((f x - g x : ℝ) : ℂ)) y =
      dDir v (fun x => (f x : ℂ)) y - dDir v (fun x => (g x : ℂ)) y := by
  push_cast
  exact dDir_sub (differentiableAt_ofReal_comp hf) (differentiableAt_ofReal_comp hg)

/-- The twisted weight shifts `ϑ` by `∂f`. -/
theorem chartTheta_sub_weight {p f : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : DifferentiableAt ℝ p y) (hf : DifferentiableAt ℝ f y)
    (w : ComplexModel n → ComplexModel n) :
    chartTheta (fun x => p x - f x) w y =
      chartTheta p w y - dDir (w y) (fun x => (f x : ℂ)) y := by
  rw [chartTheta_eq_hdiv, chartTheta_eq_hdiv, dDir_ofReal_sub hp hf]
  ring

/-- If the `(1,0)`-derivatives of two weights differ by holomorphic functions near `z`, their Levi
forms agree at `z`. -/
theorem leviS_eq_of_dDir_eq_add_holo {q₁ q₂ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hq₂ : ContDiffAt ℝ 2 q₂ z)
    (h : ∀ j : Fin n, ∃ g : ComplexModel n → ℂ, DifferentiableAt ℂ g z ∧
      dDir (coordVec j) (fun y => (q₁ y : ℂ)) =ᶠ[𝓝 z]
        fun y => dDir (coordVec j) (fun y => (q₂ y : ℂ)) y + g y)
    (u w : ComplexModel n) : leviS q₁ z u w = leviS q₂ z u w := by
  have hq₂c : ContDiffAt ℝ 2 (fun y => (q₂ y : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp z hq₂
  have hk : ∀ j k : Fin n, dbarDir (coordVec k) (dDir (coordVec j) fun y => (q₁ y : ℂ)) z =
      dbarDir (coordVec k) (dDir (coordVec j) fun y => (q₂ y : ℂ)) z := by
    intro j k
    obtain ⟨g, hg, hev⟩ := h j
    rw [dbarDir_congr hev, dbarDir_add (differentiableAt_dDir hq₂c) (hg.restrictScalars ℝ),
      dbarDir_holomorphic hg, add_zero]
  simp only [leviS, hk]

theorem leviS_smul_eq (p : ComplexModel n → ℝ) (z u w : ComplexModel n) (c : ℂ) :
    leviS p z (c • u) (c • w) = (c * conj c) * leviS p z u w :=
  leviS_smul p z u w c

/-! ### Manifold objects -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section ConstTransport

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The transport into `(c', e')` of the constant field `v` written in `(c, e)`. -/
def constTr (c c' : ComplexChart n X) (e e' : AtlasFrame L) (v : ComplexModel n)
    (y : ComplexModel n) : ComplexModel n :=
  frameTrans L e e' (c'.val.symm y) • fderiv ℂ (chg c c') (chg c' c y) v

variable {L}

/-- The domain `c'(c'.source ∩ c.source ∩ base e ∩ base e')` of `constTr`. -/
def ctDom (L : HermitianHolomorphicLineBundle.{0, 0} n X) (c c' : ComplexChart n X)
    (e e' : AtlasFrame L) : Set (ComplexModel n) :=
  ovl c' c ∩ c'.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet)

theorem isOpen_ctDom (c c' : ComplexChart n X) (e e' : AtlasFrame L) :
    IsOpen (ctDom L c c' e e') :=
  (c'.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage (isOpen_ovl c' c)
    (e.val.open_baseSet.inter e'.val.open_baseSet)

theorem differentiableOn_constTr (c c' : ComplexChart n X) (e e' : AtlasFrame L)
    (v : ComplexModel n) : DifferentiableOn ℂ (constTr L c c' e e' v) (ctDom L c c' e e') := by
  have h1 : DifferentiableOn ℂ (fun y => frameTrans L e e' (c'.val.symm y)) (ctDom L c c' e e') :=
    (differentiableOn_frameTrans c' e e').mono fun y hy => ⟨hy.1.1, hy.2⟩
  have h2 : DifferentiableOn ℂ (fun y => fderiv ℂ (chg c c') (chg c' c y) v) (ctDom L c c' e e') :=
    (differentiableOn_fderiv_chg_comp c c' v).mono fun y hy => hy.1
  exact h1.smul h2

theorem constTr_chg {c c' : ComplexChart n X} {e e' : AtlasFrame L} (v : ComplexModel n)
    {y : ComplexModel n} (hy : y ∈ ovl c c') :
    constTr L c c' e e' v (chg c c' y) =
      frameTrans L e e' (c.val.symm y) • fderiv ℂ (chg c c') y v := by
  simp only [constTr, symm_chg hy, chg_chg hy]

theorem isTransp_const {c c' : ComplexChart n X} {e e' : AtlasFrame L} (v : ComplexModel n)
    {z : ComplexModel n} (hz : z ∈ ovl c c') :
    IsTransp L c e c' e' (fun _ => v) (constTr L c c' e e' v) z := by
  filter_upwards [(isOpen_ovl c c').mem_nhds hz] with y hy
  exact constTr_chg v hy

end ConstTransport

namespace TwistedDatum

variable [MeasurableSpace X] [BorelSpace X] {T : TwistedDatum n X}

theorem contDiffAt_pX {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) : ContDiffAt ℝ ∞ (T.pX c e) z :=
  (T.contDiffOn_pX c e).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)

theorem chg_mem_pieceDomain {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {y : ComplexModel n} (hy : y ∈ T.pieceDomain c e)
    (hy' : c.val.symm y ∈ c'.val.source ∩ e'.val.baseSet) :
    chg c c' y ∈ T.pieceDomain c' e' := by
  have hyo : y ∈ ovl c c' := ⟨hy.1.1, hy'.1⟩
  refine ⟨⟨c'.val.map_source hy'.1, ?_⟩, ?_⟩
  · simp only [mem_preimage]; rw [symm_chg hyo]; exact hy'.2
  · simp only [mem_preimage]; rw [symm_chg hyo]; exact hy.2

/-- The overlap domain of two chart-frames, in the coordinates of the first. -/
def ovlD (T : TwistedDatum n X) (c c' : ComplexChart n X) (e e' : AtlasFrame T.L) :
    Set (ComplexModel n) :=
  T.pieceDomain c e ∩ ovl c c' ∩ c.val.symm ⁻¹' e'.val.baseSet

theorem isOpen_ovlD (c c' : ComplexChart n X) (e e' : AtlasFrame T.L) :
    IsOpen (T.ovlD c c' e e') :=
  (c.val.continuousOn_symm.mono fun _ hy => hy.2.1).isOpen_inter_preimage
    ((T.isOpen_pieceDomain c e).inter (isOpen_ovl c c')) e'.val.open_baseSet

theorem mem_ovlD {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet) :
    z ∈ T.ovlD c c' e e' :=
  ⟨⟨hz, hz.1.1, hz'.1⟩, hz'.2⟩

theorem ovlD_spec {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {y : ComplexModel n}
    (hy : y ∈ T.ovlD c c' e e') :
    y ∈ T.pieceDomain c e ∧ c.val.symm y ∈ c'.val.source ∩ e'.val.baseSet :=
  ⟨hy.1.1, hy.1.2.2, hy.2⟩

theorem differentiableAt_frameTrans_chart {c : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hb : c.val.symm z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    DifferentiableAt ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) z :=
  (differentiableOn_frameTrans c e e').differentiableAt
    ((c.val.continuousOn_symm.isOpen_inter_preimage c.val.open_target
      (e.val.open_baseSet.inter e'.val.open_baseSet)).mem_nhds ⟨hz, hb⟩)

/-- **The `(1,0)`-derivatives of the weights of two chart-frames differ by a holomorphic
function.** -/
theorem dDir_pX_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.ovlD c c' e e') (v : ComplexModel n) :
    ∃ g : ComplexModel n → ℂ, DifferentiableAt ℂ g z ∧
      dDir v (fun y => (T.pX c' e' (chg c c' y) : ℂ)) =ᶠ[𝓝 z]
        fun y => dDir v (fun y => (T.pX c e y : ℂ)) y + g y := by
  set t : ComplexModel n → ℂ := fun y => frameTrans T.L e e' (c.val.symm y) with ht
  set w := constTr T.L c c' e e' v with hw
  refine ⟨fun y => hdiv w (chg c c' y) / t y, ?_, ?_⟩
  · obtain ⟨hzd, hz'⟩ := ovlD_spec hz
    have hzo : z ∈ ovl c c' := ⟨hzd.1.1, hz'.1⟩
    have hct : chg c c' z ∈ ctDom T.L c c' e e' :=
      ⟨chg_mem_ovl hzo, by rw [mem_preimage, symm_chg hzo]; exact ⟨hzd.1.2, hz'.2⟩⟩
    have h1 : DifferentiableAt ℂ (hdiv w) (chg c c' z) :=
      (differentiableOn_hdiv (isOpen_ctDom c c' e e') (differentiableOn_constTr c c' e e' v))
        |>.differentiableAt ((isOpen_ctDom c c' e e').mem_nhds hct)
    have h2 : DifferentiableAt ℂ t z :=
      differentiableAt_frameTrans_chart hzd.1.1 ⟨hzd.1.2, hz'.2⟩
    have h3 : DifferentiableAt ℂ (fun y => hdiv w (chg c c' y)) z :=
      h1.comp z (differentiableAt_chg hzo)
    have h5 : t z ≠ 0 := frameTrans_ne_zero e e' ⟨hzd.1.2, hz'.2⟩
    have h4 := h3.mul (h2.inv h5)
    have e : (fun y => hdiv w (chg c c' y) / t y) = (fun y => hdiv w (chg c c' y)) * t⁻¹ := by
      funext y; simp [div_eq_mul_inv]
    rw [e]; exact h4
  · filter_upwards [(T.isOpen_ovlD c c' e e').mem_nhds hz] with y hy
    obtain ⟨hyd, hy'⟩ := ovlD_spec hy
    have hyo : y ∈ ovl c c' := ⟨hyd.1.1, hy'.1⟩
    have hb : c.val.symm y ∈ e.val.baseSet ∩ e'.val.baseSet := ⟨hyd.1.2, hy'.2⟩
    have hct : chg c c' y ∈ ctDom T.L c c' e e' :=
      ⟨chg_mem_ovl hyo, by rw [mem_preimage, symm_chg hyo]; exact hb⟩
    have hA' : IsOpen (T.pieceDomain c' e' ∩ ctDom T.L c c' e e') :=
      (T.isOpen_pieceDomain c' e').inter (isOpen_ctDom c c' e e')
    have hθ := T.chartTheta_transport (T.isOpen_pieceDomain c e) hA' subset_rfl
      inter_subset_left contDiffOn_const
      ((contDiffOn_real_of_differentiableOn_complex (differentiableOn_constTr c c' e e' v)
        (isOpen_ctDom c c' e e')).mono inter_subset_right)
      hyd hy' ⟨chg_mem_pieceDomain hyd hy', hct⟩ (isTransp_const v hyo)
    have ht0 : t y ≠ 0 := frameTrans_ne_zero e e' hb
    have hp' : DifferentiableAt ℝ (fun x => (T.pX c' e' x : ℂ)) (chg c c' y) :=
      differentiableAt_ofReal_comp ((contDiffAt_pX (chg_mem_pieceDomain hyd hy')).differentiableAt
        (by simp))
    rw [chartTheta_eq_hdiv, chartTheta_eq_hdiv, hdiv_const, constTr_chg v hyo, dDir_smul_dir,
      ← dDir_comp_holo (differentiableAt_chg hyo) hp'] at hθ
    change _ = _ + hdiv w (chg c c' y) / t y
    field_simp
    linear_combination hθ

/-- **Chart invariance of the Levi form of the local weight.** -/
theorem leviS_pX_comp {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.ovlD c c' e e') (a b : ComplexModel n) :
    leviS (fun y => T.pX c' e' (chg c c' y)) z a b = leviS (T.pX c e) z a b :=
  leviS_eq_of_dDir_eq_add_holo
    ((contDiffAt_pX (ovlD_spec hz).1).of_le (WithTop.coe_le_coe.mpr le_top))
    (fun j => dDir_pX_transport hz (coordVec j)) a b

theorem leviS_transport_of_smooth {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.ovlD c c' e e') {q : ComplexModel n → ℝ}
    (hq : ContDiffOn ℝ ∞ q (T.pieceDomain c' e')) (a b : ComplexModel n) :
    leviS q (chg c c' z) (fderiv ℂ (chg c c') z a) (fderiv ℂ (chg c c') z b) =
      leviS (fun y => q (chg c c' y)) z a b := by
  have hS : IsOpen (T.ovlD c c' e e') := T.isOpen_ovlD c c' e e'
  exact leviS_comp_holo hS (T.isOpen_pieceDomain c' e')
    ((differentiableOn_chg c c').mono fun y hy => hy.1.2)
    hq (fun y hy => chg_mem_pieceDomain (ovlD_spec hy).1 (ovlD_spec hy).2) hz a b

/-- `Levi(p')(ψ z)(Dψ a, Dψ b) = Levi(p)(z)(a, b)`. -/
theorem leviS_pX_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.ovlD c c' e e') (a b : ComplexModel n) :
    leviS (T.pX c' e') (chg c c' z) (fderiv ℂ (chg c c') z a) (fderiv ℂ (chg c c') z b) =
      leviS (T.pX c e) z a b := by
  rw [leviS_transport_of_smooth hz (T.contDiffOn_pX c' e'), leviS_pX_comp hz]

end TwistedDatum

end SGPT.Trace.TwistedL2
