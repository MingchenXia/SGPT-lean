import SGPT.Envelopes.DNTC11LocalContact
import SGPT.Okounkov.TranscendentalWNRegContact
import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

/-!
# `C^{1,1̄}` obstacles on a compact Kähler manifold and their Monge–Ampère densities

Lane S53 (`claude-dnt-c11`).

## The class of obstacles

The book (`chapter_npp`, before `thm:Tos_C11`) uses `C^{1,1̄}(X)` without a definition; its
sources (Darvas–Rubinstein, *J. Math. Soc. Japan* 68 (2016), eq. (CooEq); Di Nezza–Trapani,
*Ann. Sci. ÉNS* 57 (2024), §1) define it as the bounded functions with bounded Laplacian
`Δ_ω f ∈ L^∞`.  Darvas–Rubinstein remark that for a function `f` with `C f ∈ PSH(X, ω)` for some
`C > 0` this is equivalent to `i∂∂̄ f` having bounded coefficients.  The class formalized here,
`HasBoundedComplexHessian f`, is the latter: `f` is continuous and in every holomorphic chart the
distributional complex Hessian of `f` has a locally bounded density
(`IsBoundedHessianDensityOn`).  It is therefore `C^{1,1̄}(X) ∩ QPSH(X)` (every such `f` is
`Aω`-psh for some `A`, `exists_isThetaPshPotential_add_smul`); it contains all smooth (and all
`C^{1,1}`) functions and is the class `IsCOneOneBar` of WN-REG with an explicit density.  For
`n ≥ 2` it is strictly smaller than the bounded-Laplacian class (FPT,
`ex:metric-laplacian-unbounded-hessian`).

## Main results of this file

* `HasBoundedComplexHessian`, `HasBoundedComplexHessian.of_chartSmooth`.
* `plurisubharmonicOn_chartFunction_add_potential`: a `θ`-psh function plus *any* smooth local
  potential of `θ` is plurisubharmonic.
* `diagonalPotentialMeasure_image_eq_truncation`: the non-pluripolar measure on a chart patch
  is the local non-pluripolar measure of the corrected potential.
* `diagonalPotentialMeasure_image_eq_density` (**density formula** for `θ`-psh obstacles): if
  `f ∈ PSH(X, θ)` has a bounded complex Hessian, then `θ_fⁿ = (n!/πⁿ) det(ρ + f)_{j k̄} dV` in every
  chart, for every local potential `ρ` of `θ`.
* `exists_isThetaPshPotential_add_smul`: `f` is `(θ + tω)`-psh for all large `t`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ}

/-! ### Measures that agree locally on an open set -/

theorem restrict_eq_of_forall_mem_nhds {μ ν : Measure (ComplexModel n)}
    {W : Set (ComplexModel n)}
    (h : ∀ z ∈ W, ∃ N : Set (ComplexModel n), IsOpen N ∧ z ∈ N ∧
      μ.restrict N = ν.restrict N) :
    μ.restrict W = ν.restrict W := by
  classical
  choose N hNo hzN hN using h
  set S : W → Set (ComplexModel n) := fun z => N z.1 z.2 with hS
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S fun z => hNo z.1 z.2
  have : Countable T := hTc.to_subtype
  have hWsub : W ⊆ ⋃ i : T, S i := by
    intro z hz
    have : z ∈ ⋃ i, S i := mem_iUnion.mpr ⟨⟨z, hz⟩, hzN z hz⟩
    rw [← hTU] at this
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp this
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  have hall : μ.restrict (⋃ i : T, S i) = ν.restrict (⋃ i : T, S i) :=
    Measure.restrict_iUnion_congr.mpr fun i => hN i.1.1 i.1.2
  have := congrArg (fun m : Measure (ComplexModel n) => m.restrict W) hall
  simpa only [Measure.restrict_restrict_of_subset hWsub] using this

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The class of obstacles -/

/-- **Continuous functions with a locally bounded complex Hessian** (`C^{1,1̄} ∩ QPSH`, see the module
docstring): `f` is continuous and in every holomorphic chart `e` the function `f ∘ e⁻¹` has a
bounded density of its distributional complex Hessian on the chart target. -/
def HasBoundedComplexHessian (f : M → ℝ) : Prop :=
  Continuous f ∧ ∀ e : ComplexChart n M, ∃ h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ,
    IsBoundedHessianDensityOn (fun z => f (e.val.symm z)) h e.val.target

/-- Chart-smooth functions have a bounded complex Hessian (their classical one). -/
theorem HasBoundedComplexHessian.of_chartSmooth {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    HasBoundedComplexHessian (n := n) f :=
  ⟨ProductTestForms.ChartSmooth.continuous hf, fun e =>
    ⟨_, isBoundedHessianDensityOn_of_contDiffOn e.val.open_target (hf e)⟩⟩

omit [IsComplexManifold n M] in
/-- In a chart, `f ∘ e⁻¹ + ρ` has a bounded density on the domain `W` of a smooth function `ρ`. -/
theorem HasBoundedComplexHessian.exists_density_add {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (e : ComplexChart n M) {W : Set (ComplexModel n)}
    (hW : IsOpen W) (hWe : W ⊆ e.val.target) {ρ : ComplexModel n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ W) :
    ∃ h, IsBoundedHessianDensityOn (fun z => f (e.val.symm z) + ρ z) h W := by
  obtain ⟨h, hh⟩ := hf.2 e
  exact ⟨_, (hh.mono hW hWe).add_contDiffOn hρ⟩

/-! ### Local potentials -/

/-- A `θ`-psh function plus an arbitrary smooth local potential of `θ` is plurisubharmonic. -/
theorem plurisubharmonicOn_chartFunction_add_potential {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ e W ρ) :
    PlurisubharmonicOn (fun z => chartFunction u e z + (ρ z : EReal)) W := by
  intro z hz
  obtain ⟨W', ρ', hzW', hρ', hpsh'⟩ := hu e z (hρ.2.1 hz)
  have hV : IsOpen (W ∩ W') := hρ.1.inter hρ'.1
  have h1 := (FirstPass.smoothLocalPotential_psh_iff θ e (W ∩ W') ρ' ρ
    (hρ'.mono hV inter_subset_right) (hρ.mono hV inter_subset_left) (chartFunction u e)).mp
    (hpsh'.mono inter_subset_right)
  exact h1 z ⟨hz, hzW'⟩

/-! ### Patches of the non-pluripolar measure -/

section Patches

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The non-pluripolar measure on a chart patch** is the local non-pluripolar measure of the
corrected potential `u ∘ e⁻¹ + ρ`, for any smooth local potential `ρ` of `θ`. -/
theorem diagonalPotentialMeasure_image_eq_truncation (hn : 0 < n) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ.val e W ρ)
    {T : Set (ComplexModel n)} (hTW : T ⊆ W) :
    diagonalPotentialMeasure θ u hu (e.val.symm '' T) =
      truncationLimitMeasure ⟨W, hρ.1⟩ (fun z => chartFunction u e z + (ρ z : EReal))
        (plurisubharmonicOn_chartFunction_add_potential hu.1 hρ) T := by
  have hpsh := plurisubharmonicOn_chartFunction_add_potential hu.1 hρ
  let P : Patch (fun _ : Fin n => θ) (fun _ => u) :=
    { chart := e
      domain := ⟨W, hρ.1⟩
      domain_le_target := hρ.2.1
      potential := fun _ => ρ
      localPotential := fun _ => hρ
      plurisubharmonic := fun _ => hpsh }
  have hTt : T ⊆ e.val.target := hTW.trans hρ.2.1
  have hSP : e.val.symm '' T ⊆ (P.source : Set M) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨e.val.map_target (hTt hz), ?_⟩
    show e.val (e.val.symm z) ∈ W
    rw [e.val.right_inv (hTt hz)]
    exact hTW hz
  have h1 : diagonalPotentialMeasure θ u hu (e.val.symm '' T) =
      (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1)).restrict
        (P.source : Set M) (e.val.symm '' T) := (Measure.restrict_eq_self _ hSP).symm
  rw [h1, globalMixedMeasure_restrict_patch, patchMeasure, Patch.pushMeasure_apply_image,
    inter_eq_left.mpr hSP]
  have himg : e.val '' (e.val.symm '' T) = T := by
    rw [← image_comp]
    conv_rhs => rw [← image_id T]
    exact image_congr fun z hz => e.val.right_inv (hTt hz)
  change MixedNonPluripolar.mixedTruncationLimitMeasure P.domain (fun _ => _) (fun _ => hpsh)
    (P.chart.val '' (e.val.symm '' T)) = _
  rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hpsh]
  exact congrArg _ himg

theorem truncationLimitMeasure_congr_fun {Ω : Opens (ComplexModel n)}
    {U U' : ComplexModel n → EReal} (h : U = U') (hU : PlurisubharmonicOn U Ω)
    (hU' : PlurisubharmonicOn U' Ω) :
    truncationLimitMeasure Ω U hU = truncationLimitMeasure Ω U' hU' := by
  subst h
  rfl

/-- **The density formula for `θ`-psh obstacles.**  If `f ∈ PSH(X, θ)` has a bounded complex
Hessian, then in every chart `e`, for every smooth local potential `ρ` of `θ` on `W` and every bounded
density `h` of the complex Hessian of `f ∘ e⁻¹ + ρ` on `W`,
`θ_fⁿ(e⁻¹(K)) = ∫_K (n!/πⁿ) det h` for measurable `K ⊆ W`. -/
theorem diagonalPotentialMeasure_image_eq_density (hn : 0 < n) (θ : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal)))
    {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ.val e W ρ)
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hh : IsBoundedHessianDensityOn (fun z => f (e.val.symm z) + ρ z) h W)
    {K : Set (ComplexModel n)} (hKW : K ⊆ W) :
    diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh (e.val.symm '' K) =
      ∫⁻ z in K, ENNReal.ofReal (hessDensity h z) := by
  set Ω : Opens (ComplexModel n) := ⟨W, hρ.1⟩ with hΩ
  set Q : ComplexModel n → ℝ := fun z => f (e.val.symm z) + ρ z with hQ
  have hpsh := plurisubharmonicOn_chartFunction_add_potential hfpsh.1 hρ
  have hfun : (fun z => chartFunction (fun x => (f x : EReal)) e z + (ρ z : EReal)) =
      fun z => ((Q z : ℝ) : EReal) := by
    funext z
    simp only [hQ, chartFunction, EReal.coe_add]
  have hQpsh : PlurisubharmonicOn (fun z => ((Q z : ℝ) : EReal)) Ω := hfun ▸ hpsh
  have hQb : IsLocallyBoundedPshOn Ω Q := by
    refine ⟨hQpsh, fun z hz => ?_⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 z hz
    have hcb : closedBall z (ε / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
    obtain ⟨C, hC⟩ := (isCompact_closedBall z (ε / 2)).exists_bound_of_continuousOn
      (hh.continuousOn.mono hcb)
    refine ⟨⟨ball z (ε / 2), isOpen_ball⟩, mem_ball_self (by linarith),
      ball_subset_closedBall.trans hcb, C, fun w hw => ?_⟩
    have := hC w (ball_subset_closedBall hw)
    rwa [Real.norm_eq_abs] at this
  rw [diagonalPotentialMeasure_image_eq_truncation hn θ hfpsh hρ hKW,
    truncationLimitMeasure_congr_fun hfun hpsh hQpsh,
    truncationLimitMeasure_eq_canonical hQb]
  -- the local density formula on small balls, globalized over `W`
  have hloc : (canonicalBedfordTaylorMeasure Ω Q hQb).restrict W =
      (volume.withDensity fun z => ENNReal.ofReal (hessDensity h z)).restrict W := by
    refine restrict_eq_of_forall_mem_nhds fun z hz => ?_
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 z hz
    set R := ε / 5 with hR
    have hR0 : 0 < R := by positivity
    have hball : closedBall z (4 * R) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεW
    refine ⟨ball z R, isOpen_ball, mem_ball_self hR0, ?_⟩
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT,
      canonicalBedfordTaylorMeasure_eq_density hn hQb hh hR0 hball inter_subset_right,
      withDensity_apply _ (hT.inter measurableSet_ball)]
  have := congrArg (fun m : Measure (ComplexModel n) => m K) hloc
  rw [Measure.restrict_eq_self _ hKW, Measure.restrict_eq_self _ hKW] at this
  rw [this, withDensity_apply']

end Patches


/-! ### Quasi-plurisubharmonicity -/

/-- The Levi form of a smooth local potential is `π` times the form on complex lines. -/
theorem hermQuad_smoothHess_eq {α : SmoothRealForm n M 2} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential α e W ρ)
    {z : ComplexModel n} (hz : z ∈ W) (v : ComplexModel n) :
    hermQuad (smoothHess W ρ z) v = Real.pi * α.coeff e z ![v, Complex.I • v] := by
  have h2 : ContDiffAt ℝ 2 ρ z :=
    ((hρ.2.2.1 z hz).contDiffAt (hρ.1.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  simp only [smoothHess, hz, if_true]
  rw [hermQuad_complexHessian h2, ← hρ.2.2.2 hz,
    FirstPass.smoothDDC_complexDiagonal_eq_leviForm h2]
  field_simp

/-- **Local threshold.**  Near every point `x`, in the preferred chart at `x`, there are a ball and
`T` such that for every `t ≥ T` the function `f` is `(θ + tω)`-psh there, with an explicit
potential. -/
theorem exists_local_threshold (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f) (x : M) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ⊆ (complexChartAt (n := n) x).val.source ∧ ∃ T : ℝ,
      ∀ t : ℝ, T ≤ t → ∀ y ∈ N, ∃ W ρ, (complexChartAt (n := n) x).val y ∈ W ∧
        IsSmoothLocalPotential (θ + t • w.form).val (complexChartAt (n := n) x) W ρ ∧
        PlurisubharmonicOn (fun z => chartFunction (fun x => (f x : EReal))
          (complexChartAt (n := n) x) z + (ρ z : EReal)) W := by
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hxe
  obtain ⟨Wθ, ρθ, hz₀θ, hρθ⟩ := Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z₀ hz₀
  obtain ⟨Wω, ρω, hz₀ω, hρω⟩ :=
    Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials w.form e z₀ hz₀
  -- a lower bound for `ω` and an upper bound for `θ` near `z₀`
  obtain ⟨m, hm, hmle⟩ := KahlerDomination.exists_lineValue_lower_bound (w.isKahler.1 e z₀ hz₀).2
  have hωc : ContinuousAt (w.form.val.coeff e) z₀ :=
    ((w.form.val.smooth e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz₀)
  have hθc : ContinuousAt (θ.val.coeff e) z₀ :=
    ((θ.val.smooth e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz₀)
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.continuousAt_iff.mp hωc (m / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Metric.continuousAt_iff.mp hθc 1 one_pos
  have hO : IsOpen (Wθ ∩ Wω ∩ e.val.target) := (hρθ.1.inter hρω.1).inter e.val.open_target
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO z₀ ⟨⟨hz₀θ, hz₀ω⟩, hz₀⟩
  set r := min (ε / 2) (min (δ₁ / 2) (δ₂ / 2)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hrε : closedBall z₀ r ⊆ Wθ ∩ Wω ∩ e.val.target :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hεO
  have hrδ₁ : ∀ z ∈ closedBall z₀ r, dist z z₀ < δ₁ := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.mp hz)
      (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith))
  have hrδ₂ : ∀ z ∈ closedBall z₀ r, dist z z₀ < δ₂ := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.mp hz)
      (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith))
  have hωlow : ∀ z ∈ closedBall z₀ r, ∀ v : ComplexModel n,
      m / 2 * ‖v‖ ^ 2 ≤ w.form.val.coeff e z ![v, Complex.I • v] := by
    intro z hz v
    have hd := hδ₁b (hrδ₁ z hz)
    rw [dist_eq_norm] at hd
    have hsplit : w.form.val.coeff e z ![v, Complex.I • v] = w.form.val.coeff e z₀ ![v, Complex.I • v] +
        (w.form.val.coeff e z - w.form.val.coeff e z₀) ![v, Complex.I • v] := by simp
    have h1 := KahlerDomination.neg_norm_mul_le_lineValue
      (w.form.val.coeff e z - w.form.val.coeff e z₀) v
    have h2 := hmle v
    have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hd.le hv2]
  set Bθ := ‖θ.val.coeff e z₀‖ + 1 with hBθ
  have hθup : ∀ z ∈ closedBall z₀ r, ∀ v : ComplexModel n,
      -(Bθ * ‖v‖ ^ 2) ≤ θ.val.coeff e z ![v, Complex.I • v] := by
    intro z hz v
    have hd := hδ₂b (hrδ₂ z hz)
    rw [dist_eq_norm] at hd
    have hn : ‖θ.val.coeff e z‖ ≤ Bθ := by
      have := norm_le_insert' (θ.val.coeff e z) (θ.val.coeff e z₀)
      linarith
    have h1 := KahlerDomination.neg_norm_mul_le_lineValue (θ.val.coeff e z) v
    have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hn hv2]
  -- a bound for the density of `f`
  obtain ⟨h, hh⟩ := hf.2 e
  obtain ⟨C, hC0, hC⟩ := hh.exists_ae_abs_hermQuad_le (isCompact_closedBall z₀ r)
    (hrε.trans inter_subset_right)
  set T : ℝ := (C + Real.pi * Bθ) / (Real.pi * (m / 2)) with hT
  refine ⟨e.val.source ∩ e.val ⁻¹' ball z₀ r, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hxe, mem_ball_self hr0⟩, inter_subset_left, T, fun t ht y hy => ?_⟩
  set W := ball z₀ r with hW
  have hWθ : W ⊆ Wθ := fun z hz => (hrε (ball_subset_closedBall hz)).1.1
  have hWω : W ⊆ Wω := fun z hz => (hrε (ball_subset_closedBall hz)).1.2
  have hWt : W ⊆ e.val.target := fun z hz => (hrε (ball_subset_closedBall hz)).2
  have hρθW := hρθ.mono isOpen_ball hWθ
  have hρωW := hρω.mono isOpen_ball hWω
  set ρ : ComplexModel n → ℝ := fun z => ρθ z + t * ρω z with hρdef
  have hρs : ContDiffOn ℝ ∞ ρ W := hρθW.2.2.1.add ((contDiffOn_const (c := t)).mul hρωW.2.2.1)
  have hpot : IsSmoothLocalPotential (θ + t • w.form).val e W ρ := by
    refine ⟨isOpen_ball, hWt, hρs, fun z hz => ?_⟩
    have h1 := FirstPass.smoothDDC_add isOpen_ball hρθW.2.2.1
      ((contDiffOn_const (c := t)).mul hρωW.2.2.1) hz
    have h2 := FirstPass.smoothDDC_smul isOpen_ball hρωW.2.2.1 t hz
    simp only [smul_eq_mul] at h2
    rw [h1, h2, hρθW.2.2.2 hz, hρωW.2.2.2 hz, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul]
  refine ⟨W, ρ, hy.2, hpot, ?_⟩
  -- the corrected potential has semipositive density
  have hd := (hh.mono isOpen_ball hWt).add_contDiffOn hρs
  have hpsh := plurisubharmonicOn_of_hermQuad_nonneg hd fun v => by
    have hCW : ∀ᵐ z ∂(volume.restrict W), ∀ v, |hermQuad (h z) v| ≤ C * ‖v‖ ^ 2 :=
      ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hC
    filter_upwards [hCW, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzW
    rw [hermQuad_add, hermQuad_smoothHess_eq hpot hzW v, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul]
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    have e1 := hz v
    have e2 := hωlow z (ball_subset_closedBall hzW) v
    have e3 := hθup z (ball_subset_closedBall hzW) v
    have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
    have hpi := Real.pi_pos
    have hTt : (C + Real.pi * Bθ) ≤ t * (Real.pi * (m / 2)) := by
      rwa [hT, div_le_iff₀ (by positivity)] at ht
    have hab := neg_abs_le (hermQuad (h z) v)
    have k1 : Real.pi * (t * (m / 2 * ‖v‖ ^ 2)) ≤
        Real.pi * (t * w.form.val.coeff e z ![v, Complex.I • v]) := by
      have ht0 : 0 ≤ t := by
        have : 0 ≤ (C + Real.pi * Bθ) / (Real.pi * (m / 2)) := by positivity
        linarith
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 ht0) hpi.le
    nlinarith [mul_le_mul_of_nonneg_right hTt hv2]
  intro z hz
  refine (hpsh z hz).congr (Eventually.of_forall fun z' => ?_)
  simp only [chartFunction, EReal.coe_add]

/-- **`f` is quasi-plurisubharmonic**: there is `T ≥ 1` such that `f` is `(θ + tω)`-psh for every
`t ≥ T`. -/
theorem exists_isThetaPshPotential_add_smul [CompactSpace M] (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      IsThetaPshPotential (θ + t • w.form).val (fun x => (f x : EReal)) := by
  classical
  choose N hNo hxN hNs T hT using exists_local_threshold w θ hf
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  refine ⟨1 + ∑ x ∈ s, |T x|, by linarith [Finset.sum_nonneg fun x (_ : x ∈ s) => abs_nonneg (T x)],
    fun t ht => ⟨?_, fun x U _ hx => ⟨x, hx, EReal.coe_ne_bot _⟩⟩⟩
  intro e z hz
  set y := e.val.symm z with hy
  have hye : y ∈ e.val.source := e.val.map_target hz
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  have hTx : T x ≤ t := by
    have h1 : T x ≤ |T x| := le_abs_self _
    have h2 : |T x| ≤ ∑ x ∈ s, |T x| :=
      Finset.single_le_sum (f := fun x => |T x|) (fun _ _ => abs_nonneg _) hxs
    linarith
  obtain ⟨W', ρ', hyW', hρ', hp'⟩ := hT x t hTx y hyx
  obtain ⟨W, ρ, hW, hρ, hp⟩ := OpensRestriction.exists_witness_of_chart e (complexChartAt x) hye
    (hNs x hyx) hyW' hρ' hp'
  rw [hy, e.val.right_inv hz] at hW
  exact ⟨W, ρ, hW, hρ, hp⟩

end SGPT.Envelopes.DNTC11
