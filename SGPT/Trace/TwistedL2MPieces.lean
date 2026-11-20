import SGPT.Trace.TwistedL2MMKH

/-!
# Finite families of local pieces on `ℂⁿ` as global vector fields

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:pieces`).  Fix a twisted datum `T` on
`X = ℂⁿ` and the (unique) density `ρ` of its volume.  A finite family of local test pieces
`h_i ⊗ e_i` (each `h_i` the coefficient vector of an `L`-valued `(1,0)`-vector field in the frame
`e_i`) is one global field `W = ∑_i h_i ⊗ e_i`; its coefficient vector in a frame `e` is
`tot e = ∑_i transp e_i e h_i`.

A *gauge form* (`IsGaugeForm`) is a frame-indexed local sesquilinear integrand `F e u w z`
which is invariant under change of frame.  The key lemma `sum_gauge` says that the sum over the
pieces of `F e_i (tot e_i) h_i`, each computed in the frame of its own piece, is the diagonal value
`F e (tot e) (tot e)` in any frame `e` at the point.  The integrands of the twisted
Bochner--Kodaira--Nakano argument are gauge forms (`isGaugeForm_theta`, `isGaugeForm_levi`,
`isGaugeForm_tr`, `isGaugeForm_tstar`, `isGaugeForm_curv`, `isGaugeForm_data`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### Smoothness of Wirtinger derivatives on open sets -/

theorem contDiffOn_dDir {f : ComplexModel n → ℂ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (v : ComplexModel n) : ContDiffOn ℝ ∞ (dDir v f) D := by
  have hD' : ContDiffOn ℝ ∞ (fderiv ℝ f) D := hf.fderiv_of_isOpen hD (by simp)
  have hfun : dDir v f = fun y => (2 : ℂ)⁻¹ *
      (fderiv ℝ f y v - Complex.I * fderiv ℝ f y (Complex.I • v)) := by
    funext y; simp only [dDir]; ring
  rw [hfun]
  exact contDiffOn_const.mul ((hD'.clm_apply contDiffOn_const).sub
    (contDiffOn_const.mul (hD'.clm_apply contDiffOn_const)))

theorem contDiffOn_dbarDir {f : ComplexModel n → ℂ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (v : ComplexModel n) : ContDiffOn ℝ ∞ (dbarDir v f) D := by
  have hD' : ContDiffOn ℝ ∞ (fderiv ℝ f) D := hf.fderiv_of_isOpen hD (by simp)
  have hfun : dbarDir v f = fun y => (2 : ℂ)⁻¹ *
      (fderiv ℝ f y v + Complex.I * fderiv ℝ f y (Complex.I • v)) := by
    funext y; simp only [dbarDir]; ring
  rw [hfun]
  exact contDiffOn_const.mul ((hD'.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (hD'.clm_apply contDiffOn_const)))

theorem contDiffOn_ofReal' {p : ComplexModel n → ℝ} {D : Set (ComplexModel n)}
    (hp : ContDiffOn ℝ ∞ p D) : ContDiffOn ℝ ∞ (fun y => (p y : ℂ)) D :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hp

theorem contDiffOn_coord {u : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hu : ContDiffOn ℝ ∞ u D) (j : Fin n) : ContDiffOn ℝ ∞ (fun y => u y j) D :=
  ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hu

theorem continuousOn_chartTheta' {p : ComplexModel n → ℝ} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hp : ContDiffOn ℝ ∞ p D) {u : ComplexModel n → ComplexModel n}
    (hu : ContDiffOn ℝ ∞ u D) : ContinuousOn (chartTheta p u) D := by
  unfold chartTheta deltaDir
  refine ContinuousOn.neg (continuousOn_finsetSum _ fun j _ => ?_)
  exact (contDiffOn_dDir hD (contDiffOn_coord hu j) _).continuousOn.sub
    ((contDiffOn_dDir hD (contDiffOn_ofReal' hp) _).continuousOn.mul
      (contDiffOn_coord hu j).continuousOn)

theorem continuousOn_cweight {p : ComplexModel n → ℝ} {D : Set (ComplexModel n)}
    (hp : ContDiffOn ℝ ∞ p D) : ContinuousOn (cweight p) D := by
  unfold cweight
  exact Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
    hp.continuousOn.neg)

theorem continuousOn_leviS {p : ComplexModel n → ℝ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hp : ContDiffOn ℝ ∞ p D) {u w : ComplexModel n → ComplexModel n}
    (hu : ContinuousOn u D) (hw : ContinuousOn w D) :
    ContinuousOn (fun z => leviS p z (u z) (w z)) D := by
  unfold leviS
  refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
  have h1 : ContinuousOn (dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ))) D :=
    (contDiffOn_dbarDir hD (contDiffOn_dDir hD (contDiffOn_ofReal' hp) _) _).continuousOn
  have hu' : ContinuousOn (fun z => u z j) D :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn hu)
  have hw' : ContinuousOn (fun z => w z k) D :=
    ((EuclideanSpace.proj k : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn hw)
  exact (h1.mul hu').mul (Complex.continuous_conj.comp_continuousOn hw')

theorem continuousOn_trS {D : Set (ComplexModel n)} (hD : IsOpen D)
    {u w : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u D)
    (hw : ContDiffOn ℝ ∞ w D) : ContinuousOn (trS u w) D := by
  unfold trS
  refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
  exact (contDiffOn_dbarDir hD (contDiffOn_coord hu j) _).continuousOn.mul
    (Complex.continuous_conj.comp_continuousOn
      (contDiffOn_dbarDir hD (contDiffOn_coord hw k) _).continuousOn)

/-! ### The datum on `ℂⁿ` -/

namespace TwistedDatum

variable (T : TwistedDatum n (ComplexModel n)) (ρ : ComplexModel n → ℝ)

/-- The local weight `p_e = -log |e|² + φ - log ρ` in the frame `e`. -/
def pW (e : AtlasFrame T.L) : ComplexModel n → ℝ := localWeight T.L chart0 e ρ T.φ

/-- The twisted local weight `p_e - log a` (the weight of the metric `a h e^{-φ}`). -/
def pT (e : AtlasFrame T.L) : ComplexModel n → ℝ := fun z => T.pW ρ e z - Real.log (T.a z)

/-- The domain `base e ∩ U` of the frame `e`. -/
abbrev dom (e : AtlasFrame T.L) : Set (ComplexModel n) := T.pieceDomain chart0 e

theorem mem_dom {e : AtlasFrame T.L} {z : ComplexModel n} :
    z ∈ T.dom e ↔ z ∈ e.val.baseSet ∧ z ∈ T.U := by
  simp [dom, TwistedDatum.pieceDomain, chartFrameDomain]

theorem isOpen_dom (e : AtlasFrame T.L) : IsOpen (T.dom e) := T.isOpen_pieceDomain chart0 e

theorem contDiffOn_U {f : ComplexModel n → ℝ}
    (hf : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) f T.U) : ContDiffOn ℝ ∞ f T.U := by
  have h := hf chart0
  simp only [chart0_target, chart0_symm_apply] at h
  exact h.mono fun z hz => ⟨mem_univ z, hz⟩

theorem a_pos {z : ComplexModel n} (hz : z ∈ T.U) : 0 < T.a z := by
  obtain ⟨m, M, hm, hb⟩ := T.bounds
  exact hm.trans_le (hb z hz).1

theorem b_pos {z : ComplexModel n} (hz : z ∈ T.U) : 0 < T.b z := by
  obtain ⟨m, M, hm, hb⟩ := T.bounds
  exact hm.trans_le (hb z hz).2.2.1

variable {ρ} (hρ : IsChartDensity T.μ chart0 ρ)

include hρ in
theorem contDiffOn_pW (e : AtlasFrame T.L) : ContDiffOn ℝ ∞ (T.pW ρ e) (T.dom e) :=
  T.contDiffOn_localWeight e hρ

include hρ in
theorem contDiffOn_pT (e : AtlasFrame T.L) : ContDiffOn ℝ ∞ (T.pT ρ e) (T.dom e) := by
  have ha : ContDiffOn ℝ ∞ T.a (T.dom e) := (T.contDiffOn_U T.a_smooth).mono fun z hz =>
    ((T.mem_dom).mp hz).2
  exact (T.contDiffOn_pW hρ e).sub (ha.log fun z hz => (T.a_pos ((T.mem_dom).mp hz).2).ne')

theorem pW_eq (e e' : AtlasFrame T.L) {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    T.pW ρ e' z = T.pW ρ e z + Real.log (‖frameTrans T.L e e' z‖ ^ 2) := by
  have h := frameNormSq_eq_frameTrans e e' hz
  have h1 := frameNormSq_pos e hz.1
  have h2 := frameNormSq_pos e' hz.2
  have ht : 0 < ‖frameTrans T.L e e' z‖ ^ 2 := by
    have := frameTrans_ne_zero e e' hz; positivity
  simp only [pW, localWeight, chart0_symm_apply]
  rw [h, Real.log_mul ht.ne' h2.ne']
  ring

/-- The gauge data of a change of frame, for the local weights. -/
theorem gaugeData_pW (e e' : AtlasFrame T.L) :
    GaugeData (T.dom e ∩ T.dom e') (frameTrans T.L e e') (T.pW ρ e) (T.pW ρ e') where
  isOpen := (T.isOpen_dom e).inter (T.isOpen_dom e')
  holo := (differentiableOn_frameTrans_model e e').mono fun _z hz =>
    ⟨((T.mem_dom).mp hz.1).1, ((T.mem_dom).mp hz.2).1⟩
  ne_zero := fun _z hz => frameTrans_ne_zero e e' ⟨((T.mem_dom).mp hz.1).1, ((T.mem_dom).mp hz.2).1⟩
  weight := fun _z hz => T.pW_eq e e' ⟨((T.mem_dom).mp hz.1).1, ((T.mem_dom).mp hz.2).1⟩

/-- The gauge data of a change of frame, for the twisted local weights. -/
theorem gaugeData_pT (e e' : AtlasFrame T.L) :
    GaugeData (T.dom e ∩ T.dom e') (frameTrans T.L e e') (T.pT ρ e) (T.pT ρ e') where
  isOpen := (T.gaugeData_pW (ρ := ρ) e e').isOpen
  holo := (T.gaugeData_pW (ρ := ρ) e e').holo
  ne_zero := (T.gaugeData_pW (ρ := ρ) e e').ne_zero
  weight := fun z hz => by
    simp only [pT, (T.gaugeData_pW (ρ := ρ) e e').weight z hz]
    ring

/-! ### Gauge forms -/

/-- A frame-indexed local sesquilinear integrand, invariant under change of frame. -/
structure IsGaugeForm
    (F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) → (ComplexModel n → ComplexModel n) →
      ComplexModel n → ℂ) : Prop where
  congr : ∀ e u u' w w' z, u =ᶠ[𝓝 z] u' → w =ᶠ[𝓝 z] w' → F e u w z = F e u' w' z
  zero : ∀ e u w z, w =ᶠ[𝓝 z] 0 → F e u w z = 0
  add : ∀ e (u : ComplexModel n → ComplexModel n) {ι : Type} (s : Finset ι)
    (w : ι → ComplexModel n → ComplexModel n) z, z ∈ T.dom e → ContDiffAt ℝ ∞ u z →
    (∀ i ∈ s, ContDiffAt ℝ ∞ (w i) z) →
    F e u (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, F e u (w i) z
  gauge : ∀ e e' u w z, z ∈ T.dom e → z ∈ T.dom e' → ContDiffAt ℝ ∞ u z →
    ContDiffAt ℝ ∞ w z →
    F e' (fun y => frameTrans T.L e e' y • u y) (fun y => frameTrans T.L e e' y • w y) z = F e u w z
  contOn : ∀ e u w, ContDiffOn ℝ ∞ u (T.dom e) → ContDiffOn ℝ ∞ w (T.dom e) →
    ContinuousOn (F e u w) (T.dom e)

/-! ### Families of pieces -/

section Family

variable {ι : Type} (s : Finset ι) (e : ι → AtlasFrame T.L) (h : ι → ComplexModel n → ComplexModel n)

/-- The coefficient vector, in the frame `e₀`, of the global field `∑_i h_i ⊗ e_i`. -/
def tot (e₀ : AtlasFrame T.L) (z : ComplexModel n) : ComplexModel n :=
  ∑ i ∈ s, transp T.L (e i) e₀ (h i) z

variable {s e h}
variable (hh : ∀ i, IsLocalTestField T.L T.U chart0 (e i) (h i))

include hh in
theorem tsupport_subset_dom (i : ι) : tsupport (h i) ⊆ T.dom (e i) := by
  intro z hz
  have := (hh i).2.2 hz
  exact this

include hh in
theorem tsupport_subset_base (i : ι) : tsupport (h i) ⊆ (e i).val.baseSet := fun _z hz =>
  ((T.mem_dom).mp (T.tsupport_subset_dom hh i hz)).1

include hh in
theorem contDiffOn_tot (e₀ : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (T.tot s e h e₀) e₀.val.baseSet := by
  unfold tot
  exact ContDiffOn.sum fun i _ => contDiffOn_transp (hh i).1 (T.tsupport_subset_base hh i)

include hh in
theorem contDiffAt_tot {e₀ : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ e₀.val.baseSet) :
    ContDiffAt ℝ ∞ (T.tot s e h e₀) z :=
  (T.contDiffOn_tot hh e₀).contDiffAt (e₀.val.open_baseSet.mem_nhds hz)

include hh in
theorem contDiffAt_transp {e₀ : AtlasFrame T.L} (i : ι) {z : ComplexModel n}
    (hz : z ∈ e₀.val.baseSet) : ContDiffAt ℝ ∞ (transp T.L (e i) e₀ (h i)) z :=
  (contDiffOn_transp (hh i).1 (T.tsupport_subset_base hh i)).contDiffAt
    (e₀.val.open_baseSet.mem_nhds hz)

theorem tot_eventuallyEq {e₀ e₁ : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ e₀.val.baseSet ∩ e₁.val.baseSet) :
    T.tot s e h e₁ =ᶠ[𝓝 z] fun y => frameTrans T.L e₀ e₁ y • T.tot s e h e₀ y := by
  have hall : ∀ᶠ y in 𝓝 z, ∀ i ∈ s,
      transp T.L (e i) e₁ (h i) y = frameTrans T.L e₀ e₁ y • transp T.L (e i) e₀ (h i) y :=
    (s.eventually_all).mpr fun i _ => transp_eventuallyEq (e i) e₀ e₁ (h i) hz
  filter_upwards [hall] with y hy
  simp only [tot, Finset.smul_sum]
  exact Finset.sum_congr rfl hy

include hh in
/-- **Pieces computed in their own frames add up to the diagonal value in any frame.** -/
theorem sum_gauge {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) {e₀ : AtlasFrame T.L} {z : ComplexModel n} (hz : z ∈ T.dom e₀) :
    ∑ i ∈ s, F (e i) (T.tot s e h (e i)) (h i) z = F e₀ (T.tot s e h e₀) (T.tot s e h e₀) z := by
  have hz' := (T.mem_dom).mp hz
  have hterm : ∀ i ∈ s, F (e i) (T.tot s e h (e i)) (h i) z =
      F e₀ (T.tot s e h e₀) (transp T.L (e i) e₀ (h i)) z := by
    intro i _
    by_cases hzi : z ∈ (e i).val.baseSet
    · have hzdi : z ∈ T.dom (e i) := (T.mem_dom).mpr ⟨hzi, hz'.2⟩
      rw [hF.congr (e i) _ _ _ _ z (T.tot_eventuallyEq ⟨hz'.1, hzi⟩)
        (eventuallyEq_frameTrans_smul_transp (T.tsupport_subset_base hh i) ⟨hz'.1, hzi⟩)]
      exact hF.gauge e₀ (e i) _ _ z hz hzdi (T.contDiffAt_tot hh hz'.1)
        (T.contDiffAt_transp hh i hz'.1)
    · have hzs : z ∉ tsupport (h i) := fun h' => hzi (T.tsupport_subset_base hh i h')
      rw [hF.zero _ _ _ z (eventuallyEq_zero_of_notMem_tsupport hzs),
        hF.zero _ _ _ z (transp_eventuallyEq_zero hzs)]
  rw [Finset.sum_congr rfl hterm, ← hF.add e₀ _ s _ z hz (T.contDiffAt_tot hh hz'.1)
    fun i _ => T.contDiffAt_transp hh i hz'.1]
  rfl

omit hh in
theorem piece_eq_zero {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) (i : ι) {z : ComplexModel n} (hz : z ∉ tsupport (h i)) :
    F (e i) (T.tot s e h (e i)) (h i) z = 0 :=
  hF.zero _ _ _ z (eventuallyEq_zero_of_notMem_tsupport hz)

include hh in
theorem continuous_piece {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) (i : ι) :
    Continuous fun z => F (e i) (T.tot s e h (e i)) (h i) z := by
  refine continuous_of_continuousOn_of_eq_zero (T.isOpen_dom (e i)) ?_ (isClosed_tsupport (h i))
    (T.tsupport_subset_dom hh i) fun z hz => T.piece_eq_zero hF i hz
  exact hF.contOn (e i) _ _ ((T.contDiffOn_tot hh (e i)).mono fun z hz => ((T.mem_dom).mp hz).1)
    (hh i).1.contDiffOn

include hh in
theorem integrable_piece {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) (i : ι) :
    Integrable (fun z => F (e i) (T.tot s e h (e i)) (h i) z) := by
  refine (T.continuous_piece hh hF i).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hh i).2.1 fun z hz => T.piece_eq_zero hF i ?_
  exact hz

include hh in
theorem integrable_sum_pieces {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) :
    Integrable (fun z => ∑ i ∈ s, F (e i) (T.tot s e h (e i)) (h i) z) :=
  integrable_finsetSum _ fun i _ => T.integrable_piece hh hF i

include hh in
theorem sum_pieces_eq_zero_of_notMem_U {F : AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
      (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ}
    (hF : T.IsGaugeForm F) {z : ComplexModel n} (hz : z ∉ T.U) :
    ∑ i ∈ s, F (e i) (T.tot s e h (e i)) (h i) z = 0 := by
  refine Finset.sum_eq_zero fun i _ => T.piece_eq_zero hF i fun h' => hz ?_
  exact ((T.mem_dom).mp (T.tsupport_subset_dom hh i h')).2

end Family

end TwistedDatum

end SGPT.Trace.TwistedL2
