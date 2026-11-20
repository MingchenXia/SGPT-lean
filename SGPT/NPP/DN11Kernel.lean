import SGPT.NPP.DN11ParamLimit
import SGPT.NPP.DN5LocalKernel

/-!
# The chart smoothing as a parametric integral against a normalized kernel; limits

Lane DN11 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 6, the passage from smooth
to arbitrary local plurisubharmonic potentials).

Lane DN5 represents the chart smoothing near `(z₀, 0)` as a ratio
`localSmoothing Φ α f z t = (∫ f K((z, t), ·)) / ∫ K((z, t), ·)`
(`SGPT.NPP.DN5.exists_localSmoothing_kernel`).  Dividing the kernel by its (smooth, positive) mass
gives one smooth kernel `K̃`, supported in a fixed compact `C`, with
`localSmoothing Φ α f z t = ∫ f(y) K̃((z, t), y) dy` for **every** `f`
(`exists_localSmoothing_normKernel`).  With `SGPT.NPP.DN11ParamLimit`, if `f_j → g` weakly on an
open set containing `C`, then at every `(z, t)` of the patch (`0 < t < δ`):

* the values `S_{f_j}(z, t)` converge (`tendsto_localSmoothing`);
* the `t`-derivatives converge (`tendsto_deriv_localSmoothing`);
* the first and second derivatives of `s ↦ S_{f_j}(z, eˢ)` converge
  (`tendsto_deriv_localSmoothing_exp`, `tendsto_deriv_deriv_localSmoothing_exp`);
* the Levi forms of `(z, w) ↦ S_{f_j}(z, |w|)` at `w ≠ 0` converge
  (`tendsto_leviForm_localSmoothing`).

Also: `S_f` is smooth on the patch for `f` integrable on `C` (`contDiffOn_localSmoothing`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.NPP.DN11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NPP.DN5

variable {N : ℕ}

local notation "E" => ComplexModel N

/-- Equal germs have equal Levi forms. -/
theorem leviForm_congr_nhds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedSpace ℝ F] {u v : F → ℝ} {x : F} (h : u =ᶠ[𝓝 x] v) (a : F) :
    leviForm u x a = leviForm v x a := by
  have h1 : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ v := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ v) x := h1.fderiv_eq
  simp only [leviForm, realHessian_eq_fderiv, h2]

/-- **Normalized kernel representation of the chart smoothing**: near `(z₀, 0)`, for `0 < t < δ`,
`localSmoothing Φ α f z t = ∫ f(y) K̃((z, t), y) dy` for every `f`, with `K̃` smooth in
`((z, t), y)` and vanishing off a compact `C ⊆ W`. -/
theorem exists_localSmoothing_normKernel {Φ : E → E → E} {O : Set (E × E)}
    (hΦ : IsLocalFibreMap Φ O) {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hα : ContDiffOn ℝ ∞ α U) (h11 : ∀ z ∈ U, IsOneOne (α z))
    (hpos : ∀ z ∈ U, IsStrictlyPositive (α z)) {z₀ : E} (hz₀U : z₀ ∈ U)
    (hz₀O : (z₀, (0 : E)) ∈ O) {W : Set E} (hW : W ∈ 𝓝 z₀) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ C : Set E, IsCompact C ∧ C ⊆ W ∧
      ∃ K : E × ℝ → E → ℝ,
        ContDiffOn ℝ ∞ (fun q : (E × ℝ) × E => K q.1 q.2) ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ) ∧
        (∀ p y, y ∉ C → K p y = 0) ∧ ball z₀ ε ⊆ U ∧
        ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ f : E → ℝ,
          localSmoothing Φ α f z t = ∫ y, f y * K (z, t) y := by
  obtain ⟨ε, δ, hε, hδ, C, hC, hCW, K, hK, hKC, -, hεU, -, hpos', hrep⟩ :=
    exists_localSmoothing_kernel hΦ hU hα h11 hpos hz₀U hz₀O hW
  set S : Set (E × ℝ) := ball z₀ ε ×ˢ Ioo 0 δ with hS
  have hSo : IsOpen S := isOpen_ball.prod isOpen_Ioo
  have hD : ContDiffOn ℝ ∞ (fun p : E × ℝ => ∫ y, (fun _ => (1 : ℝ)) y * K p y) S :=
    contDiffOn_integral_mul_kernel hSo hK hC hKC
      (integrableOn_const (μ := volume) hC.measure_lt_top.ne)
  simp only [one_mul] at hD
  have hDpos : ∀ p ∈ S, 0 < ∫ y, K p y := fun p hp => hpos' p.1 hp.1 p.2 hp.2
  refine ⟨ε, δ, hε, hδ, C, hC, hCW, fun p y => K p y / ∫ y, K p y, ?_, ?_, hεU, ?_⟩
  · refine hK.div ((hD.comp contDiffOn_fst (fun q hq => hq.1))) ?_
    intro q hq
    exact (hDpos q.1 hq.1).ne'
  · intro p y hy
    simp only [hKC p y hy, zero_div]
  · intro z hz t ht f
    rw [hrep z hz t ht f, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring

/-- Data of a normalized kernel patch at `z₀` (the conclusion of
`exists_localSmoothing_normKernel`). -/
structure NormKernelPatch (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z₀ : E) (ε δ : ℝ)
    (C : Set E) (K : E × ℝ → E → ℝ) : Prop where
  ε_pos : 0 < ε
  δ_pos : 0 < δ
  compact : IsCompact C
  smooth : ContDiffOn ℝ ∞ (fun q : (E × ℝ) × E => K q.1 q.2) ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ)
  vanish : ∀ p y, y ∉ C → K p y = 0
  rep : ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ f : E → ℝ,
    localSmoothing Φ α f z t = ∫ y, f y * K (z, t) y

variable {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
  {α : ComplexModel N → ComplexModel N [⋀^Fin 2]→L[ℝ] ℝ} {z₀ : ComplexModel N} {ε δ : ℝ}
  {C : Set (ComplexModel N)} {K : ComplexModel N × ℝ → ComplexModel N → ℝ}

/-- The open set `{(z, w) : z ∈ B(z₀, ε), 0 < |w| < δ}`. -/
def jointPatch (z₀ : E) (ε δ : ℝ) : Set (E × ℂ) :=
  {q | q.1 ∈ ball z₀ ε ∧ q.2 ≠ 0 ∧ ‖q.2‖ < δ}

theorem isOpen_jointPatch (z₀ : E) (ε δ : ℝ) : IsOpen (jointPatch z₀ ε δ) := by
  have h1 : IsOpen {q : E × ℂ | q.1 ∈ ball z₀ ε} := isOpen_ball.preimage continuous_fst
  have h2 : IsOpen {q : E × ℂ | q.2 ≠ 0} := isOpen_ne.preimage continuous_snd
  have h3 : IsOpen {q : E × ℂ | ‖q.2‖ < δ} :=
    isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  exact h1.inter (h2.inter h3)

namespace NormKernelPatch

theorem isOpen_patch (_hP : NormKernelPatch Φ α z₀ ε δ C K) :
    IsOpen (ball z₀ ε ×ˢ Ioo (0 : ℝ) δ) :=
  isOpen_ball.prod isOpen_Ioo

/-- `S_f` agrees near `(z, t)` with the parametric integral. -/
theorem eventuallyEq (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε) {t : ℝ}
    (ht : t ∈ Ioo 0 δ) (f : E → ℝ) :
    (fun p : E × ℝ => localSmoothing Φ α f p.1 p.2) =ᶠ[𝓝 (z, t)]
      fun p => ∫ y, f y * K p y := by
  filter_upwards [hP.isOpen_patch.mem_nhds ⟨hz, ht⟩] with p hp
  exact hP.rep p.1 hp.1 p.2 hp.2 f

/-- **Smoothness of the chart smoothing on the patch**, for `f` integrable on `C`. -/
theorem contDiffOn (hP : NormKernelPatch Φ α z₀ ε δ C K) {f : E → ℝ} (hf : IntegrableOn f C) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => localSmoothing Φ α f p.1 p.2) (ball z₀ ε ×ˢ Ioo 0 δ) :=
  (contDiffOn_integral_mul_kernel hP.isOpen_patch hP.smooth hP.compact hP.vanish hf).congr
    fun p hp => hP.rep p.1 hp.1 p.2 hp.2 f

/-! #### The `t`-slices -/

/-- The kernel of the `t`-slice at `z`. -/
theorem smooth_tslice (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => K (z, q.1) q.2) (Ioo 0 δ ×ˢ univ) := by
  refine hP.smooth.comp (((contDiffOn_const.prodMk contDiffOn_fst)).prodMk contDiffOn_snd) ?_
  intro q hq
  exact ⟨⟨hz, hq.1⟩, mem_univ _⟩

theorem eventuallyEq_tslice (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε) {t : ℝ}
    (ht : t ∈ Ioo 0 δ)
    (f : E → ℝ) :
    localSmoothing Φ α f z =ᶠ[𝓝 t] fun s => ∫ y, f y * K (z, s) y := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact hP.rep z hz s hs f

/-- The kernel of the `log`-slice `s ↦ S(z, eˢ)` at `z`. -/
theorem smooth_logslice (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => K (z, Real.exp q.1) q.2) (Iio (Real.log δ) ×ˢ univ) := by
  refine hP.smooth.comp (((contDiffOn_const.prodMk
    (Real.contDiff_exp.comp_contDiffOn contDiffOn_fst))).prodMk contDiffOn_snd) ?_
  intro q hq
  refine ⟨⟨hz, Real.exp_pos _, ?_⟩, mem_univ _⟩
  have h := hq.1
  simp only [mem_Iio] at h
  calc Real.exp q.1 < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr h
    _ = δ := Real.exp_log hP.δ_pos

theorem eventuallyEq_logslice (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε) {s : ℝ}
    (hs : s < Real.log δ)
    (f : E → ℝ) :
    (fun s => localSmoothing Φ α f z (Real.exp s)) =ᶠ[𝓝 s]
      fun s => ∫ y, f y * K (z, Real.exp s) y := by
  filter_upwards [isOpen_Iio.mem_nhds (show s ∈ Iio (Real.log δ) from hs)] with s' hs'
  refine hP.rep z hz _ ⟨Real.exp_pos _, ?_⟩ f
  calc Real.exp s' < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr hs'
    _ = δ := Real.exp_log hP.δ_pos

/-! #### The joint `(z, w)` kernel -/

theorem smooth_joint (hP : NormKernelPatch Φ α z₀ ε δ C K) :
    ContDiffOn ℝ ∞ (fun q : (E × ℂ) × E => K (q.1.1, ‖q.1.2‖) q.2)
      (jointPatch z₀ ε δ ×ˢ univ) := by
  have hmap : ContDiffOn ℝ ∞ (fun q : (E × ℂ) × E => (((q.1.1, ‖q.1.2‖) : E × ℝ), q.2))
      (jointPatch z₀ ε δ ×ˢ univ) := by
    refine ContDiffOn.prodMk (ContDiffOn.prodMk (contDiff_fst.comp contDiff_fst).contDiffOn ?_)
      contDiffOn_snd
    intro q hq
    have hq2 : q.1.2 ≠ 0 := hq.1.2.1
    exact ((contDiffAt_norm ℝ hq2).comp q (contDiff_snd.comp contDiff_fst).contDiffAt)
      |>.contDiffWithinAt
  refine hP.smooth.comp hmap ?_
  intro q hq
  exact ⟨⟨hq.1.1, norm_pos_iff.mpr hq.1.2.1, hq.1.2.2⟩, mem_univ _⟩

theorem eventuallyEq_joint (hP : NormKernelPatch Φ α z₀ ε δ C K) {q : E × ℂ}
    (hq : q ∈ jointPatch z₀ ε δ) (f : E → ℝ) :
    (fun p : E × ℂ => localSmoothing Φ α f p.1 ‖p.2‖) =ᶠ[𝓝 q]
      fun p => ∫ y, f y * K (p.1, ‖p.2‖) y := by
  filter_upwards [(isOpen_jointPatch z₀ ε δ).mem_nhds hq] with p hp
  exact hP.rep p.1 hp.1 ‖p.2‖ ⟨norm_pos_iff.mpr hp.2.1, hp.2.2⟩ f

/-! #### Limits under weak convergence -/

variable {U : Opens (ComplexModel N)} {f : ℕ → ComplexModel N → ℝ} {g : ComplexModel N → ℝ}

/-- **Values converge.** -/
theorem tendsto_localSmoothing (hP : NormKernelPatch Φ α z₀ ε δ C K) (hCU : C ⊆ U)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop (𝓝 (∫ x, φ x * g x)))
    {z : E} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    Tendsto (fun j => localSmoothing Φ α (f j) z t) atTop (𝓝 (localSmoothing Φ α g z t)) := by
  simp_rw [hP.rep z hz t ht]
  exact tendsto_integral_mul_kernel hP.smooth hP.compact hCU hP.vanish hweak
    (show (z, t) ∈ ball z₀ ε ×ˢ Ioo 0 δ from ⟨hz, ht⟩)

/-- **The `t`-derivatives converge.** -/
theorem tendsto_deriv_localSmoothing (hP : NormKernelPatch Φ α z₀ ε δ C K) (hCU : C ⊆ U)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop (𝓝 (∫ x, φ x * g x)))
    (hf : ∀ j, IntegrableOn (f j) C) (hg : IntegrableOn g C)
    {z : E} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    Tendsto (fun j => deriv (localSmoothing Φ α (f j) z) t) atTop
      (𝓝 (deriv (localSmoothing Φ α g z) t)) := by
  simp_rw [(hP.eventuallyEq_tslice hz ht _).deriv_eq, ← fderiv_apply_one_eq_deriv]
  exact tendsto_fderiv_integral_mul_kernel (K := fun s y => K (z, s) y) isOpen_Ioo
    (hP.smooth_tslice hz) hP.compact hCU (fun s y hy => hP.vanish _ y hy) hweak hf hg ht 1

/-- **The first derivatives of `s ↦ S(z, eˢ)` converge.** -/
theorem tendsto_deriv_localSmoothing_exp (hP : NormKernelPatch Φ α z₀ ε δ C K) (hCU : C ⊆ U)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop (𝓝 (∫ x, φ x * g x)))
    (hf : ∀ j, IntegrableOn (f j) C) (hg : IntegrableOn g C)
    {z : E} (hz : z ∈ ball z₀ ε) {s : ℝ}
    (hs : s < Real.log δ) :
    Tendsto (fun j => deriv (fun s => localSmoothing Φ α (f j) z (Real.exp s)) s) atTop
      (𝓝 (deriv (fun s => localSmoothing Φ α g z (Real.exp s)) s)) := by
  simp_rw [(hP.eventuallyEq_logslice hz hs _).deriv_eq, ← fderiv_apply_one_eq_deriv]
  exact tendsto_fderiv_integral_mul_kernel (K := fun s y => K (z, Real.exp s) y) isOpen_Iio
    (hP.smooth_logslice hz) hP.compact hCU (fun s y hy => hP.vanish _ y hy) hweak hf hg
    (show s ∈ Iio (Real.log δ) from hs) 1

/-- `d/ds S(z, eˢ) = ∫ f(y) ∂_s K((z, eˢ), y) dy` near `s`. -/
theorem eventuallyEq_deriv_logslice (hP : NormKernelPatch Φ α z₀ ε δ C K) {z : E} (hz : z ∈ ball z₀ ε)
    {s : ℝ} (hs : s < Real.log δ)
    {f : E → ℝ} (hf : IntegrableOn f C) :
    deriv (fun s => localSmoothing Φ α f z (Real.exp s)) =ᶠ[𝓝 s]
      fun s => ∫ y, f y * fderiv ℝ (fun s => K (z, Real.exp s) y) s 1 := by
  filter_upwards [(hP.eventuallyEq_logslice hz hs f).eventuallyEq_nhds,
    isOpen_Iio.mem_nhds (show s ∈ Iio (Real.log δ) from hs)] with s' hs' hs''
  rw [hs'.deriv_eq, ← fderiv_apply_one_eq_deriv]
  exact fderiv_integral_mul_kernel_apply (K := fun s y => K (z, Real.exp s) y) isOpen_Iio
    ((hP.smooth_logslice hz).of_le (by norm_cast)) hP.compact (fun s y hy => hP.vanish _ y hy) hf
    hs'' 1

/-- **The second derivatives of `s ↦ S(z, eˢ)` converge.** -/
theorem tendsto_deriv_deriv_localSmoothing_exp (hP : NormKernelPatch Φ α z₀ ε δ C K) (hCU : C ⊆ U)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop (𝓝 (∫ x, φ x * g x)))
    (hf : ∀ j, IntegrableOn (f j) C) (hg : IntegrableOn g C)
    {z : E} (hz : z ∈ ball z₀ ε) {s : ℝ}
    (hs : s < Real.log δ) :
    Tendsto (fun j => deriv (deriv (fun s => localSmoothing Φ α (f j) z (Real.exp s))) s) atTop
      (𝓝 (deriv (deriv (fun s => localSmoothing Φ α g z (Real.exp s))) s)) := by
  simp_rw [(hP.eventuallyEq_deriv_logslice hz hs (hf _)).deriv_eq,
    (hP.eventuallyEq_deriv_logslice hz hs hg).deriv_eq, ← fderiv_apply_one_eq_deriv]
  have hK1 : ContDiffOn ℝ ∞ (fun q : ℝ × E =>
      fderiv ℝ (fun s => K (z, Real.exp s) q.2) q.1 1) (Iio (Real.log δ) ×ˢ univ) := by
    refine contDiffOn_infty.mpr fun m => ?_
    exact (SGPT.NPP.DN3.contDiffOn_fderiv_param (F := fun s y => K (z, Real.exp s) y) (m := m)
      isOpen_Iio ((hP.smooth_logslice hz).of_le (natCast_add_one_le_infty m))).clm_apply
      contDiffOn_const
  refine tendsto_fderiv_integral_mul_kernel
    (K := fun s y => fderiv ℝ (fun s => K (z, Real.exp s) y) s 1) isOpen_Iio hK1 hP.compact hCU
    (fun s y hy => ?_) hweak hf hg (show s ∈ Iio (Real.log δ) from hs) 1
  rw [fderiv_param_eq_zero_of_notMem (K := fun s y => K (z, Real.exp s) y)
    (fun s y hy => hP.vanish _ y hy) hy s]
  rfl

/-- **The Levi forms of `(z, w) ↦ S(z, |w|)` converge** at `w ≠ 0`. -/
theorem tendsto_leviForm_localSmoothing (hP : NormKernelPatch Φ α z₀ ε δ C K) (hCU : C ⊆ U)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop (𝓝 (∫ x, φ x * g x)))
    (hf : ∀ j, IntegrableOn (f j) C) (hg : IntegrableOn g C)
    {z : E} (hz : z ∈ ball z₀ ε) {w : ℂ} (hw0 : w ≠ 0)
    (hw : ‖w‖ < δ) (V : E × ℂ) :
    Tendsto (fun j => leviForm (fun p : E × ℂ => localSmoothing Φ α (f j) p.1 ‖p.2‖) (z, w) V)
      atTop (𝓝 (leviForm (fun p : E × ℂ => localSmoothing Φ α g p.1 ‖p.2‖) (z, w) V)) := by
  have hq : (z, w) ∈ jointPatch z₀ ε δ := ⟨hz, hw0, hw⟩
  simp_rw [leviForm_congr_nhds (hP.eventuallyEq_joint hq _)]
  exact tendsto_leviForm_integral_mul_kernel (K := fun p y => K (p.1, ‖p.2‖) y)
    (isOpen_jointPatch z₀ ε δ) hP.smooth_joint hP.compact hCU (fun p y hy => hP.vanish _ y hy)
    hweak hf hg
    hq V

end NormKernelPatch

end SGPT.NPP.DN11
