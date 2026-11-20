import SGPT.NPP.DN11Kernel
import SGPT.Foundations.Analysis.Pending.DistributionRegularizationFinal
import SGPT.Foundations.Analysis.GermPshLeviPositivity
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability

/-!
# The joint Levi estimate for plurisubharmonic potentials with poles

Lane DN11 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`,
`chapters/inputs/q10-big-envelope-regularity.tex`, Step 6: "If `p` is merely plurisubharmonic, we
apply the estimate to the convolutions `p_ε ↓ p` and let `ε → 0`; the smoothings of `p_ε` converge
to that of `p` in `C²` on compact subsets of `{t > 0}`, since the kernel is smooth").

Let `Φ` be a local fibre map (`SGPT.NPP.DN5.IsLocalFibreMap`), `α` a smooth strictly positive
`(1,1)` coefficient, `K` compact, and `u : ℂⁿ → [-∞, ∞)` plurisubharmonic on an open `W ⊇ K` and
*nondegenerate* (`u ≢ -∞` on every open subset of `W`).  Write
`S_f(z, t) = localSmoothing Φ α f z t` and `S = S_{toReal ∘ u}`.

* `exists_localPatch`: near every `z₀ ∈ K` there are a normalized kernel patch
  (`SGPT.NPP.DN11.NormKernelPatch`), whose kernel is supported in a compact `C`, and a sequence of
  globally smooth functions `f_j`, plurisubharmonic on an open `Ω ⊇ C` containing a fixed ball
  around each centre of the patch, with `f_j → toReal ∘ u` weakly on `Ω` (the local decreasing
  regularization `SGPT.Foundations.Analysis.Pending.exists_local_decreasing_psh_regularization` of the
  regular distribution of `u`, `SGPT.Foundations.Analysis.pshRegularDistribution`).
* **`jointBound_of_smooth`** (the deliverable for lane DN9, FPT Step 6): any lower bound
  `B(S_p'(z, |w|), S_p'(z, 2|w|)) ≤ L[(z, w) ↦ S_p(z, |w|)](z, w)(v, η)`, with `B` continuous in the
  two `t`-derivatives, that holds for **every smooth** `p` plurisubharmonic on `B(z, c|w|)`
  (uniformly for `z ∈ K`, `0 < |w| < r₁`), holds for `toReal ∘ u` for `0 < |w| < r₂`.
* `contDiffOn_localSmoothing_toReal` (export (X) for DN9/DN10): `S` is smooth on `V × (0, r₂)`,
  `V ⊇ K` open.
* `localSmoothing_toReal_split` (export (Y) for DN9/DN10): if `f + g = u` on `W` with `g`
  continuous, then `S_{toReal ∘ u} = S_{toReal ∘ f} + S_g` on `V × (0, r₂)` (the polar set of `u` is
  null and `toReal ∘ u` is integrable on the support of the kernel).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.NPP.DN11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NPP.DN5

variable {N : ℕ}

/-- A positive lower bound for finitely many positive numbers. -/
theorem exists_pos_le_finset {ι : Type*} (t : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ t, 0 < r i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i ∈ t, m ≤ r i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t ha ih =>
    obtain ⟨m, hm, hle⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    refine ⟨min m (r a), lt_min hm (hr a (Finset.mem_insert_self a t)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with h | h
    · rw [h]; exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle i h)

/-- Shrinking the base radius of a kernel patch. -/
theorem NormKernelPatch.mono_ε {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
    {α : ComplexModel N → ComplexModel N [⋀^Fin 2]→L[ℝ] ℝ} {z₀ : ComplexModel N} {ε δ : ℝ}
    {C : Set (ComplexModel N)} {K : ComplexModel N × ℝ → ComplexModel N → ℝ}
    (hP : NormKernelPatch Φ α z₀ ε δ C K) {ε' : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) :
    NormKernelPatch Φ α z₀ ε' δ C K where
  ε_pos := hε'
  δ_pos := hP.δ_pos
  compact := hP.compact
  smooth := hP.smooth.mono (prod_mono (prod_mono (ball_subset_ball hle) le_rfl) le_rfl)
  vanish := hP.vanish
  rep := fun z hz t ht f => hP.rep z (ball_subset_ball hle hz) t ht f

/-- **Local data near a centre**: a normalized kernel patch at `z₀`, supported in a compact `C`
inside an open `Ω ⊆ W`, smooth functions `f_j` plurisubharmonic on `Ω` (which contains the ball of
radius `ρ` around every centre of the patch) converging weakly to `toReal ∘ u` on `Ω`, and the
integrability and a.e. finiteness of `u` on `C`. -/
theorem exists_localPatch {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
    {O : Set (ComplexModel N × ComplexModel N)} (hΦ : IsLocalFibreMap Φ O)
    {α : ComplexModel N → ComplexModel N [⋀^Fin 2]→L[ℝ] ℝ} {U : Set (ComplexModel N)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (hαpos : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z))
    {W : Set (ComplexModel N)} (hW : IsOpen W) {u : ComplexModel N → EReal}
    (hu : PlurisubharmonicOn u W)
    (hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥)
    {z₀ : ComplexModel N} (hz₀U : z₀ ∈ U) (hz₀W : z₀ ∈ W) (hz₀O : (z₀, (0 : ComplexModel N)) ∈ O) :
    ∃ ε δ ρ : ℝ, 0 < ρ ∧ ∃ (C : Set (ComplexModel N)) (K : ComplexModel N × ℝ → ComplexModel N → ℝ)
      (Ω : Opens (ComplexModel N)) (f : ℕ → ComplexModel N → ℝ),
      NormKernelPatch Φ α z₀ ε δ C K ∧ C ⊆ Ω ∧ (Ω : Set (ComplexModel N)) ⊆ W ∧
      (∀ z ∈ ball z₀ ε, ball z ρ ⊆ Ω) ∧
      (∀ j, ContDiff ℝ ∞ (f j)) ∧ (∀ j, ∀ y ∈ Ω, ∀ v, 0 ≤ leviForm (f j) y v) ∧
      (∀ φ : 𝓓(Ω, ℝ), Tendsto (fun j => ∫ x, φ x * f j x) atTop
        (𝓝 (∫ x, φ x * (u x).toReal))) ∧
      IntegrableOn (fun y => (u y).toReal) C ∧
      (∀ᵐ y ∂(volume.restrict C), u y ≠ ⊤ ∧ u y ≠ ⊥) := by
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW z₀ hz₀W
  let B : Opens (ComplexModel N) := ⟨ball z₀ r, isOpen_ball⟩
  have hBc : IsPreconnected (B : Set (ComplexModel N)) := (convex_ball z₀ r).isPreconnected
  have huB : PlurisubharmonicOn u B := hu.mono hrW
  have hneB : ∃ a ∈ (B : Set (ComplexModel N)), u a ≠ ⊥ :=
    hne z₀ hz₀W (ball z₀ r) isOpen_ball (mem_ball_self hr)
  have hT := huB.pshRegularDistribution_hasNonnegativeDistributionalLevi (μ := volume) hBc hneB
  obtain ⟨Ω, hΩB, f, hz₀Ω, hsm, hdisc, -, hconv⟩ :=
    Pending.exists_local_decreasing_psh_regularization volume hT z₀ (mem_ball_self hr)
  have hΩB' : (Ω : Set (ComplexModel N)) ⊆ ball z₀ r := hΩB
  obtain ⟨ρ', hρ', hρ'Ω⟩ := Metric.isOpen_iff.mp Ω.isOpen z₀ hz₀Ω
  obtain ⟨ε₀, δ, hε₀, hδ, C, hC, hCb, K, hK, hKC, -, hrep⟩ :=
    exists_localSmoothing_normKernel hΦ hU hα (fun z hz => (hαpos z hz).1)
      (fun z hz => (hαpos z hz).2) hz₀U hz₀O (ball_mem_nhds z₀ (half_pos hρ'))
  have hP : NormKernelPatch Φ α z₀ ε₀ δ C K := ⟨hε₀, hδ, hC, hK, hKC, hrep⟩
  have hCΩ : C ⊆ Ω := hCb.trans ((ball_subset_ball (half_le_self hρ'.le)).trans hρ'Ω)
  have hCB : C ⊆ ball z₀ r := hCΩ.trans hΩB'
  refine ⟨min ε₀ (ρ' / 2), δ, ρ' / 2, half_pos hρ', C, K, Ω, f,
    hP.mono_ε (lt_min hε₀ (half_pos hρ')) (min_le_left _ _), hCΩ, hΩB'.trans hrW, ?_,
    hsm, ?_, ?_, ?_, ?_⟩
  · intro z hz y hy
    apply hρ'Ω
    rw [mem_ball] at hy hz ⊢
    have := dist_triangle y z z₀
    have h2 : dist z z₀ < ρ' / 2 := hz.trans_le (min_le_right _ _)
    linarith
  · intro j y hy v
    exact leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := Ω) (hsm j).contDiffOn
      ((hdisc j).plurisubharmonicOn Ω.isOpen) hy v
  · intro φ
    have h := hconv φ
    rw [restrictDistribution_apply, pshRegularDistribution_apply] at h
    have he : ∀ x, ((TestFunction.monoCLM ℝ φ : 𝓓(B, ℝ)) : ComplexModel N → ℝ) x = φ x :=
      fun x => congrFun (testFunction_inclusion_coe hΩB φ) x
    simp only [he] at h
    exact h
  · exact (huB.locallyIntegrableOn_toReal volume hBc hneB).integrableOn_compact_subset hCB hC
  · exact ae_restrict_of_ae_restrict_of_subset hCB (huB.ae_finite volume hBc hneB)

section Main

variable {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
  {O : Set (ComplexModel N × ComplexModel N)}
  {α : ComplexModel N → ComplexModel N [⋀^Fin 2]→L[ℝ] ℝ} {U : Set (ComplexModel N)}
  {K W : Set (ComplexModel N)} {u : ComplexModel N → EReal}

/-- **The joint estimate near one centre** (local form of `jointBound_of_smooth`). -/
theorem jointBound_local (hΦ : IsLocalFibreMap Φ O) (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (hαpos : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z))
    (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O)
    (hW : IsOpen W) (hKW : K ⊆ W) (hu : PlurisubharmonicOn u W)
    (hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥)
    (B : ComplexModel N → ℂ → ComplexModel N → ℂ → ℝ → ℝ → ℝ)
    (hB : ∀ z w v η, Continuous fun x : ℝ × ℝ => B z w v η x.1 x.2) {r₁ c : ℝ} (hr₁ : 0 < r₁)
    (hsmooth : ∀ z ∈ K, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₁ → ∀ p : ComplexModel N → ℝ,
      ContDiff ℝ ∞ p → (∀ y ∈ ball z (c * ‖w‖), ∀ v, 0 ≤ leviForm p y v) →
      ∀ (v : ComplexModel N) (η : ℂ),
        B z w v η (deriv (localSmoothing Φ α p z) ‖w‖) (deriv (localSmoothing Φ α p z) (2 * ‖w‖))
          ≤ leviForm (fun q : ComplexModel N × ℂ => localSmoothing Φ α p q.1 ‖q.2‖) (z, w) (v, η))
    {z₀ : ComplexModel N} (hz₀ : z₀ ∈ K) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ z ∈ ball z₀ ε, z ∈ K → ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r →
      ∀ (v : ComplexModel N) (η : ℂ),
        B z w v η (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) ‖w‖)
            (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) (2 * ‖w‖)) ≤
          leviForm (fun q : ComplexModel N × ℂ =>
            localSmoothing Φ α (fun y => (u y).toReal) q.1 ‖q.2‖) (z, w) (v, η) := by
  obtain ⟨ε, δ, ρ, hρ, C, Kn, Ω, f, hP, hCΩ, -, hball, hsm, hpsh, hweak, hint, -⟩ :=
    exists_localPatch hΦ hU hα hαpos hW hu hne (hKU hz₀) (hKW hz₀) (hKO z₀ hz₀)
  have hδ := hP.δ_pos
  have hfint : ∀ j, IntegrableOn (f j) C := fun j =>
    (hsm j).continuous.continuousOn.integrableOn_compact hP.compact
  set r : ℝ := min r₁ (min (δ / 2) (ρ / (|c| + 1))) with hr
  have hc1 : 0 < |c| + 1 := by positivity
  refine ⟨ε, r, hP.ε_pos, ?_, ?_⟩
  · exact lt_min hr₁ (lt_min (half_pos hδ) (div_pos hρ hc1))
  · intro z hz hzK w hw0 hwr v η
    have hwr₁ : ‖w‖ < r₁ := hwr.trans_le (min_le_left _ _)
    have hwδ : ‖w‖ < δ / 2 := hwr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hwρ : ‖w‖ < ρ / (|c| + 1) := hwr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hcw : c * ‖w‖ ≤ ρ := by
      have h1 : c * ‖w‖ ≤ |c| * ‖w‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
      have h2 : (|c| + 1) * ‖w‖ < ρ := by
        rw [lt_div_iff₀ hc1] at hwρ; linarith
      nlinarith [norm_nonneg w]
    have hj : ∀ j, B z w v η (deriv (localSmoothing Φ α (f j) z) ‖w‖)
        (deriv (localSmoothing Φ α (f j) z) (2 * ‖w‖)) ≤
        leviForm (fun q : ComplexModel N × ℂ => localSmoothing Φ α (f j) q.1 ‖q.2‖) (z, w) (v, η) :=
      fun j => hsmooth z hzK w hw0 hwr₁ (f j) (hsm j)
        (fun y hy v => hpsh j y (hball z hz (ball_subset_ball hcw hy)) v) v η
    have ht1 : ‖w‖ ∈ Ioo 0 δ := ⟨hw0, by linarith⟩
    have ht2 : 2 * ‖w‖ ∈ Ioo 0 δ := ⟨by linarith, by linarith⟩
    have hd1 := hP.tendsto_deriv_localSmoothing hCΩ hweak hfint hint hz ht1
    have hd2 := hP.tendsto_deriv_localSmoothing hCΩ hweak hfint hint hz ht2
    have hL := hP.tendsto_leviForm_localSmoothing hCΩ hweak hfint hint hz (norm_pos_iff.mp hw0)
      (by linarith) (v, η)
    have hBlim : Tendsto (fun j => B z w v η (deriv (localSmoothing Φ α (f j) z) ‖w‖)
        (deriv (localSmoothing Φ α (f j) z) (2 * ‖w‖))) atTop
        (𝓝 (B z w v η (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) ‖w‖)
          (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) (2 * ‖w‖)))) :=
      ((hB z w v η).tendsto _).comp (hd1.prodMk_nhds hd2)
    exact le_of_tendsto_of_tendsto' hBlim hL hj

/-- **The joint Levi estimate for plurisubharmonic potentials with poles** (FPT
`lem:chern-joint-smoothing`, Step 6).  Let `B` be any lower bound, continuous in the two
`t`-derivatives `S'(z, |w|)`, `S'(z, 2|w|)`, that holds for the chart smoothing of **every smooth**
function plurisubharmonic on `B(z, c|w|)`, for `z ∈ K` and `0 < |w| < r₁`.  Then it holds for the
chart smoothing of `toReal ∘ u`, `u` plurisubharmonic and nondegenerate on `W ⊇ K`, for
`0 < |w| < r₂` (some `0 < r₂ ≤ r₁`).  Proof: near each centre, `u` is the weak limit of smooth
plurisubharmonic `f_j` (`exists_localPatch`); the `t`-derivatives and the Levi forms of the
smoothings converge (`SGPT.NPP.DN11.NormKernelPatch`); compactness of `K`. -/
theorem jointBound_of_smooth (hΦ : IsLocalFibreMap Φ O) (hU : IsOpen U)
    (hα : ContDiffOn ℝ ∞ α U) (hαpos : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z))
    (hK : IsCompact K) (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O)
    (hW : IsOpen W) (hKW : K ⊆ W) (hu : PlurisubharmonicOn u W)
    (hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥)
    (B : ComplexModel N → ℂ → ComplexModel N → ℂ → ℝ → ℝ → ℝ)
    (hB : ∀ z w v η, Continuous fun x : ℝ × ℝ => B z w v η x.1 x.2) {r₁ c : ℝ} (hr₁ : 0 < r₁)
    (hsmooth : ∀ z ∈ K, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₁ → ∀ p : ComplexModel N → ℝ,
      ContDiff ℝ ∞ p → (∀ y ∈ ball z (c * ‖w‖), ∀ v, 0 ≤ leviForm p y v) →
      ∀ (v : ComplexModel N) (η : ℂ),
        B z w v η (deriv (localSmoothing Φ α p z) ‖w‖) (deriv (localSmoothing Φ α p z) (2 * ‖w‖))
          ≤ leviForm (fun q : ComplexModel N × ℂ => localSmoothing Φ α p q.1 ‖q.2‖) (z, w) (v, η)) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ r₂ ≤ r₁ ∧ ∀ z ∈ K, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₂ →
      ∀ (v : ComplexModel N) (η : ℂ),
        B z w v η (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) ‖w‖)
            (deriv (localSmoothing Φ α (fun y => (u y).toReal) z) (2 * ‖w‖)) ≤
          leviForm (fun q : ComplexModel N × ℂ =>
            localSmoothing Φ α (fun y => (u y).toReal) q.1 ‖q.2‖) (z, w) (v, η) := by
  have hloc := fun z₀ (hz₀ : z₀ ∈ K) =>
    jointBound_local hΦ hU hα hαpos hKU hKO hW hKW hu hne B hB hr₁ hsmooth hz₀
  choose! ε r hε hr hP using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (ε x))
    (fun x hx => ball_mem_nhds x (hε x hx))
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_finset t r (fun i hi => hr i (htK i hi))
  refine ⟨min r₁ m, lt_min hr₁ hm, min_le_left _ _, fun z hz w hw0 hw v η => ?_⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (hcover hz)
  exact hP x (htK x hxt) z hzx hz w hw0 (hw.trans_le ((min_le_right _ _).trans (hmle x hxt))) v η

/-- Gluing local `C^∞` statements on patches `B(x, ε(x)) × (0, δ(x))` along a finite cover of the
compact `K`. -/
theorem exists_cover_patches (hK : IsCompact K) (ε δ : ComplexModel N → ℝ)
    (hε : ∀ x ∈ K, 0 < ε x) (hδ : ∀ x ∈ K, 0 < δ x) :
    ∃ V : Set (ComplexModel N), ∃ r₂ : ℝ, IsOpen V ∧ K ⊆ V ∧ 0 < r₂ ∧
      ∀ z ∈ V, ∃ x ∈ K, z ∈ ball x (ε x) ∧ r₂ ≤ δ x := by
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (ε x))
    (fun x hx => ball_mem_nhds x (hε x hx))
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_finset t δ (fun i hi => hδ i (htK i hi))
  refine ⟨⋃ x ∈ t, ball x (ε x), m, isOpen_biUnion fun _ _ => isOpen_ball, hcover, hm,
    fun z hz => ?_⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp hz
  exact ⟨x, htK x hxt, hzx, hmle x hxt⟩

/-- **Export (X)**: the chart smoothing of `toReal ∘ u` (`u` plurisubharmonic and nondegenerate on
`W ⊇ K`) is `C^∞` in `(z, t)` on `V × (0, r₂)`, `V ⊇ K` open. -/
theorem contDiffOn_localSmoothing_toReal (hΦ : IsLocalFibreMap Φ O) (hU : IsOpen U)
    (hα : ContDiffOn ℝ ∞ α U) (hαpos : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z))
    (hK : IsCompact K) (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O)
    (hW : IsOpen W) (hKW : K ⊆ W) (hu : PlurisubharmonicOn u W)
    (hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥) :
    ∃ V : Set (ComplexModel N), ∃ r₂ : ℝ, IsOpen V ∧ K ⊆ V ∧ 0 < r₂ ∧
      ContDiffOn ℝ ∞ (fun x : ComplexModel N × ℝ =>
        localSmoothing Φ α (fun y => (u y).toReal) x.1 x.2) (V ×ˢ Ioo 0 r₂) := by
  have hloc : ∀ z₀ ∈ K, ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ (fun x : ComplexModel N × ℝ =>
        localSmoothing Φ α (fun y => (u y).toReal) x.1 x.2) (ball z₀ ε ×ˢ Ioo 0 δ) := by
    intro z₀ hz₀
    obtain ⟨ε, δ, -, -, C, Kn, Ω, -, hP, -, -, -, -, -, -, hint, -⟩ :=
      exists_localPatch hΦ hU hα hαpos hW hu hne (hKU hz₀) (hKW hz₀) (hKO z₀ hz₀)
    exact ⟨ε, δ, hP.ε_pos, hP.δ_pos, hP.contDiffOn hint⟩
  choose! ε δ hε hδ hcd using hloc
  obtain ⟨V, r₂, hV, hKV, hr₂, hVc⟩ := exists_cover_patches hK ε δ hε hδ
  refine ⟨V, r₂, hV, hKV, hr₂, contDiffOn_of_locally_contDiffOn fun q hq => ?_⟩
  obtain ⟨x, hxK, hzx, hle⟩ := hVc q.1 hq.1
  refine ⟨ball x (ε x) ×ˢ Ioo 0 (δ x), isOpen_ball.prod isOpen_Ioo,
    ⟨hzx, hq.2.1, hq.2.2.trans_le hle⟩, (hcd x hxK).mono inter_subset_right⟩

/-- `u = f + g` with `u` finite and `g` real gives `toReal u = toReal f + g`. -/
theorem toReal_eq_toReal_add {a v : EReal} {b : ℝ} (h : a + (b : EReal) = v) (hv : v ≠ ⊤)
    (hv' : v ≠ ⊥) : v.toReal = a.toReal + b := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add] at h; exact absurd h.symm hv'
  | coe a => rw [← h, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
  | top => rw [EReal.top_add_coe] at h; exact absurd h.symm hv

/-- **Export (Y)**: splitting.  If `f + g = u` on `W` (`g` continuous, `u` plurisubharmonic and
nondegenerate on `W ⊇ K`), then `S_{toReal ∘ u} = S_{toReal ∘ f} + S_g` on `V × (0, r₂)`,
`V ⊇ K` open. -/
theorem localSmoothing_toReal_split (hΦ : IsLocalFibreMap Φ O) (hU : IsOpen U)
    (hα : ContDiffOn ℝ ∞ α U) (hαpos : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z))
    (hK : IsCompact K) (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : ComplexModel N)) ∈ O)
    (hW : IsOpen W) (hKW : K ⊆ W) (hu : PlurisubharmonicOn u W)
    (hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥)
    {g : ComplexModel N → ℝ} (hg : ContinuousOn g W) {f : ComplexModel N → EReal}
    (hfg : ∀ y ∈ W, f y + (g y : EReal) = u y) :
    ∃ V : Set (ComplexModel N), ∃ r₂ : ℝ, IsOpen V ∧ K ⊆ V ∧ 0 < r₂ ∧
      ∀ z ∈ V, ∀ t ∈ Ioo 0 r₂,
        localSmoothing Φ α (fun y => (u y).toReal) z t =
          localSmoothing Φ α (fun y => (f y).toReal) z t + localSmoothing Φ α g z t := by
  have hloc : ∀ z₀ ∈ K, ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ,
      localSmoothing Φ α (fun y => (u y).toReal) z t =
        localSmoothing Φ α (fun y => (f y).toReal) z t + localSmoothing Φ α g z t := by
    intro z₀ hz₀
    obtain ⟨ε, δ, -, -, C, Kn, Ω, -, hP, hCΩ, hΩW, -, -, -, -, hint, hfin⟩ :=
      exists_localPatch hΦ hU hα hαpos hW hu hne (hKU hz₀) (hKW hz₀) (hKO z₀ hz₀)
    refine ⟨ε, δ, hP.ε_pos, hP.δ_pos, fun z hz t ht => ?_⟩
    have hCW : C ⊆ W := hCΩ.trans hΩW
    have hgC : IntegrableOn g C := (hg.mono hCW).integrableOn_compact hP.compact
    have hCm : MeasurableSet C := hP.compact.isClosed.measurableSet
    have hae : ∀ᵐ y ∂(volume.restrict C), (u y).toReal = (f y).toReal + g y := by
      filter_upwards [hfin, ae_restrict_mem hCm] with y hy hyC
      exact toReal_eq_toReal_add (hfg y (hCW hyC)) hy.1 hy.2
    have hfC : IntegrableOn (fun y => (f y).toReal) C :=
      (hint.sub hgC).congr_fun_ae (by
        filter_upwards [hae] with y hy
        simp only [Pi.sub_apply, hy]; ring)
    have hk : Continuous fun y => Kn (z, t) y :=
      (contDiff_slice hP.smooth (show (z, t) ∈ ball z₀ ε ×ˢ Ioo 0 δ from ⟨hz, ht⟩)).continuous
    have hkC : ∀ y, y ∉ C → Kn (z, t) y = 0 := fun y hy => hP.vanish _ y hy
    have I1 := integrable_smul_kernel hk hP.compact hkC hfC
    have I2 := integrable_smul_kernel hk hP.compact hkC hgC
    simp only [smul_eq_mul] at I1 I2
    rw [hP.rep z hz t ht, hP.rep z hz t ht, hP.rep z hz t ht, ← integral_add I1 I2]
    have hae' := (ae_restrict_iff' hCm).mp hae
    refine integral_congr_ae ?_
    filter_upwards [hae'] with y hy
    by_cases hyC : y ∈ C
    · rw [hy hyC]; ring
    · simp only [hkC y hyC, mul_zero, add_zero]
  choose! ε δ hε hδ hsplit using hloc
  obtain ⟨V, r₂, hV, hKV, hr₂, hVc⟩ := exists_cover_patches hK ε δ hε hδ
  refine ⟨V, r₂, hV, hKV, hr₂, fun z hz t ht => ?_⟩
  obtain ⟨x, hxK, hzx, hle⟩ := hVc z hz
  exact hsplit x hxK z hzx t ⟨ht.1, ht.2.trans_le hle⟩

end Main

end SGPT.NPP.DN11
