import SGPT.NPP.DNNefMain
import SGPT.NPP.LocalMetricLaplacianLimits
import SGPT.NPP.DNTBigLowDim
import SGPT.NPP.DNTBigReduction
import SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

/-!
# `thm:DNT23_C11bar` for nef and big classes

Source: SGPT `thm:DNT23_C11bar` (`chapter_npp.tex`, Di Nezza–Trapani), proved here for
classes `{θ}` that are **big and nef**, in every dimension, with the proof of Berman,
*From Monge–Ampère equations to envelopes and geodesic rays in the zero temperature limit*,
Math. Z. 291 (2019), Proposition 3.5 (`references/berman19-zero-temperature`), extended from
`V_θ` to obstacles `f ∈ C^{1,1̄}_ω(X)`.

Let `X` be compact connected with a Kähler form `ω`, `{θ}` big and nef, `f ∈ C^{1,1̄}_ω(X)`.  Then
`P_θ(f)` is real-valued off the non-Kähler locus and has bounded `ω`-Laplacian on every compact
subset of `X ∖ nK({θ})`; in particular so does `V_θ`.

## Proof

Boucksom's theorem gives a Kähler current `θ + ddᶜψ ≥ ω₀` with analytic singularities whose pole
set is `nK({θ})` (`exists_strict_reference`), and `ω₀ ≥ c₀ω`.  The obstacle is approximated by
smooth `F_j` with `Δ_ω F_j` bounded above (`LapClass.exists_smooth_laplacian_le`), and
`exists_nef_approximants` (Tsuji-weighted β-method in the Kähler classes `{θ + ε_j ω}`) produces
smooth `v_j` with `|v_j - P_θ(F_j)| ≤ δ_j + (ε_j/c₀)(B - ψ)` and
`|Δ_ω v_j| ≤ C e^{-aψ}` where `ψ` is finite.  Near a point off `nK`, `ψ` is bounded, so the `v_j`
converge uniformly to `P_θ(f)` with uniformly bounded Laplacians, and
`DNTBig.hasBoundedMetricLaplacianOn_of_local_smooth_limits` concludes.

## Main results

* `rooftopEnvelope_hasBoundedMetricLaplacianOn_of_nef`: native form, off the native non-Kähler
  locus (positive Lelong numbers of all Kähler currents).
* `sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_nef`,
  `sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_nef`: the source statements
  (`def:Pthetaf`, `eq:Vtheta`, `def:nKlocus`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DNNef

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound
open KahlerLaplacianChart
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### The reference Kähler current -/

/-- **A Kähler current with analytic singularities and pole set `nK`** (Boucksom, *Divisorial
Zariski decompositions*, Theorem 3.17, via TN `exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`),
normalized: a `(θ - ω₀)`-psh potential `ψ ≤ c` whose pole set is the non-Kähler locus and which is
bounded near every point where it is finite. -/
theorem exists_strict_reference [CompactSpace Y] [Nonempty Y] (hN : 0 < N) (θ : ClosedRealOneOneForm N Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (c : ℝ) :
    ∃ (ω₀ : KahlerBackground N Y) (ψ : Y → EReal),
      IsThetaPshPotential (θ - ω₀.form).val ψ ∧ (∀ x, ψ x ≤ (c : EReal)) ∧
      poleSet ψ = nonKahlerLocus (RealBottChern.ofRepresentative θ) ∧
      ∀ x, ψ x ≠ ⊥ → ∃ U ∈ 𝓝 x, IsBoundedPotentialOn ψ U := by
  classical
  obtain ⟨T, hsing, -, hpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hN _ hbig
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  have hcont : Continuous h := KahlerCurrentMax.continuous_of_chartSmooth hh
  have hsub : ThetaPlurisubharmonic (θ - T.lowerBound.form).val
      (fun y => T.potential y - (h y : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh
      (fun e z hz => ?_) T.strictlyPsh.1
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg]
    rw [heq e z hz]
    abel
  have hnd : LocallyNondegenerate (fun y => T.potential y - (h y : EReal)) := by
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := T.strictlyPsh.2 x U hU hxU
    refine ⟨y, hyU, ?_⟩
    show T.potential y - (h y : EReal) ≠ ⊥
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩
  have hpot : IsThetaPshPotential (θ - T.lowerBound.form).val
      (fun y => T.potential y - (h y : EReal)) := ⟨hsub, hnd⟩
  obtain ⟨C, hC⟩ := hpot.exists_global_upper_bound
  have hbot_iff : ∀ x : Y,
      (T.potential x - (h x : EReal)) - ((C - c : ℝ) : EReal) = ⊥ ↔ T.potential x = ⊥ := by
    intro x
    constructor
    · intro hb
      by_contra hne
      have hnetop : T.potential x ≠ ⊤ :=
        T.strictlyPsh.1.quasiPlurisubharmonic.ne_top x
      have hcoe : T.potential x = (((T.potential x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hnetop hne).symm
      rw [hcoe, ← EReal.coe_sub, ← EReal.coe_sub] at hb
      exact (EReal.coe_ne_bot _) hb
    · intro hb
      rw [hb]
      simp
  refine ⟨T.lowerBound, fun y => (T.potential y - (h y : EReal)) - ((C - c : ℝ) : EReal),
    hpot.sub_const (C - c), fun x => ?_, ?_, ?_⟩
  · have h1 := hC x
    have h2 : (T.potential x - (h x : EReal)) - ((C - c : ℝ) : EReal) ≤
        (C : EReal) - ((C - c : ℝ) : EReal) := EReal.sub_le_sub h1 le_rfl
    refine h2.trans (le_of_eq ?_)
    rw [← EReal.coe_sub]
    congr 1
    ring
  · rw [← hpole]
    ext x
    simpa only [poleSet, Set.mem_ofPred_eq] using hbot_iff x
  · intro x hx
    have hTx : T.potential x ≠ ⊥ := fun hbot => hx ((hbot_iff x).mpr hbot)
    obtain ⟨N₁, hN₁, hb₁⟩ :=
      exists_isBoundedPotentialOn_of_hasAnalyticSingularities hsing hTx
    obtain ⟨K, -, hK⟩ := boundedRealGermAt_of_continuousAt (hcont.continuousAt (x := x))
    exact ⟨N₁ ∩ {y | |h y| ≤ K}, Filter.inter_mem hN₁ hK,
      BigClassSupremumContact.isBoundedPotentialOn_sub_of_abs_le
        (hb₁.mono inter_subset_left) (fun y hy => hy.2) (C - c)⟩

/-! ### The theorem -/

variable [CompactSpace Y] [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **`thm:DNT23_C11bar` for nef and big classes, native form.**  If `{θ}` is big and nef and
`f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f)` is real-valued off the non-Kähler locus and has bounded
`ω`-Laplacian on every compact subset of `X ∖ nK({θ})`. -/
theorem rooftopEnvelope_hasBoundedMetricLaplacianOn_of_nef (hN : 0 < N)
    (w : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hnef : NefWithRespectTo w θ)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ),
      rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
        (((rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (fun x => (rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal) := by
  classical
  obtain ⟨hfc, S₀, hLE, -⟩ := hf
  have hg : w.form.val.IsHermitian := w.isKahler.1
  -- a bound for `f`
  obtain ⟨Bf₀, hBf₀⟩ := isCompact_univ.exists_bound_of_continuousOn hfc.continuousOn
  set Bf := |Bf₀| with hBfdef
  have hBf : ∀ y, |f y| ≤ Bf := fun y => by
    have := hBf₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  have hBf0 : 0 ≤ Bf := abs_nonneg _
  -- the reference current
  obtain ⟨ω₀, ψ, hψ, hψle, hpole, hloc⟩ := exists_strict_reference hN θ hbig (-Bf - 2)
  -- `ω₀ ≥ c₀ ω`
  obtain ⟨A₀, hA₀, hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul (-w.form).val
    ω₀.form.val ω₀.isKahler.1
  set c₀ : ℝ := 1 / A₀ with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hω₀ : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
      c₀ * w.form.val.coeff e z ![v, Complex.I • v] ≤ ω₀.form.val.coeff e z ![v, Complex.I • v] := by
    intro e z hz v
    have h1 := hdom e z hz v
    rw [ClosedRealOneOneForm.coeff_neg] at h1
    simp only [ContinuousAlternatingMap.neg_apply] at h1
    rw [hc₀def, one_div, inv_mul_le_iff₀ hA₀]
    linarith
  -- bounds for traces
  obtain ⟨Cθ₀, hCθ₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_traceForm hg θ).continuousOn
  set Cθ := |Cθ₀| with hCθdef
  have hCθ : ∀ y, |traceForm w.form.val θ.val y| ≤ Cθ := fun y => by
    have := hCθ₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  obtain ⟨Cη₀, hCη₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_traceForm hg (θ - ω₀.form)).continuousOn
  set Cη := |Cη₀| with hCηdef
  have hCη : ∀ y, |traceForm w.form.val (θ - ω₀.form).val y| ≤ Cη := fun y => by
    have := hCη₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  -- the approximants
  obtain ⟨a, T, ha, hT, happ⟩ := exists_nef_approximants w ω₀ θ hnef hc₀ hω₀ hψ
  set S : ℝ := |S₀| + 1 + Cη with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hFj : ∀ j : ℕ, ∃ F : Y → ℝ, ChartSmooth (n := N) F ∧
      (∀ y, |F y - f y| ≤ 1 / ((j : ℝ) + 1)) ∧ ∀ y, laplacian w.form.val F y ≤ S₀ + 1 := by
    intro j
    have hη : (0 : ℝ) < 1 / (4 * ((j : ℝ) + 1)) := by positivity
    obtain ⟨F, hF, hFf, hFS⟩ := exists_smooth_laplacian_le w hfc hLE hη
    refine ⟨F, hF, fun y => ?_, fun y => ?_⟩
    · have := hFf y
      have he : 4 * (1 / (4 * ((j : ℝ) + 1))) = 1 / ((j : ℝ) + 1) := by field_simp
      linarith
    · have := hFS y
      have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      have he : 2 * (1 / (4 * ((j : ℝ) + 1))) ≤ 1 := by
        calc 2 * (1 / (4 * ((j : ℝ) + 1))) = 1 / (2 * ((j : ℝ) + 1)) := by field_simp; ring
          _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
  choose F hF hFf hFS using hFj
  set B : ℝ := Bf + 1 with hBdef
  have hjpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hjle : ∀ j : ℕ, 1 / ((j : ℝ) + 1) ≤ 1 := fun j => by
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hFB : ∀ j y, F j y ≤ B := fun j y => by
    have h1 := (abs_le.mp (hFf j y)).2
    have h2 := (abs_le.mp (hBf y)).2
    have := hjle j
    linarith
  have hψF : ∀ j y, ψ y ≤ ((F j y : ℝ) : EReal) := fun j y => by
    refine (hψle y).trans (EReal.coe_le_coe_iff.mpr ?_)
    have h1 := (abs_le.mp (hFf j y)).1
    have h2 := (abs_le.mp (hBf y)).1
    have := hjle j
    linarith
  have hFSj : ∀ j y, laplacian w.form.val (F j) y + traceForm w.form.val (θ - ω₀.form).val y ≤ S :=
    fun j y => by
      have h1 := hFS j y
      have h2 := (abs_le.mp (hCη y)).2
      have h3 := le_abs_self S₀
      rw [hSdef]
      linarith
  have hv := fun j : ℕ => happ (1 / ((j : ℝ) + 1)) (hjpos j) (hjle j) (1 / ((j : ℝ) + 1))
    (hjpos j) (hjle j) (F j) (hF j) S (hFSj j) B (hFB j) (hψF j)
  choose v hvs hvb using hv
  -- the envelope of `f`
  have hω₀semi : ω₀.form.val.IsSemipositive := KahlerBackground.isSemipositive ω₀
  have hψθ : IsThetaPshPotential θ.val ψ := by
    have := isThetaPshPotential_add_semipositive hω₀semi hψ
    rwa [sub_add_cancel] at this
  set P : Y → EReal := rooftopEnvelope θ.val (fun y => (f y : EReal)) with hPdef
  have hPpsh : IsThetaPshPotential θ.val P :=
    isThetaPshPotential_rooftopEnvelope_of_continuous w θ hfc hψθ
  have hPf : ∀ y, P y ≤ (f y : EReal) := rooftopEnvelope_le_of_isThetaPshPotential hfc hPpsh
  have hψf : ∀ y, ψ y ≤ (f y : EReal) := fun y => (hψle y).trans (EReal.coe_le_coe_iff.mpr (by
    have := (abs_le.mp (hBf y)).1; linarith))
  have hψP : ∀ y, ψ y ≤ P y := le_rooftopEnvelope hψθ (quasiEverywhere_of_forall hψf)
  have hreal : ∀ y, ψ y ≠ ⊥ → P y = (((P y).toReal : ℝ) : EReal) := by
    intro y hy
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hPf y))
      (ne_bot_of_le_ne_bot hy (hψP y))).symm
  have hnK : ∀ x, x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) → ψ x ≠ ⊥ := by
    intro x hx hb
    apply hx
    rw [← hpole]
    exact hb
  refine ⟨fun x hx => hreal x (hnK x hx), ?_⟩
  -- the complement of `nK` is open
  have hUo : IsOpen (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, a₁, b₁, hab⟩ := hloc x (hnK x hx)
    refine Filter.mem_of_superset hU fun y hy hyK => ?_
    rw [← hpole] at hyK
    have := (hab y hy).1
    rw [show ψ y = ⊥ from hyK] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  refine DNTBig.hasBoundedMetricLaplacianOn_of_local_smooth_limits w hUo fun x hx => ?_
  obtain ⟨U, hU, aψ, bψ, hab⟩ := hloc x (hnK x hx)
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  have hVK : V ⊆ (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ := by
    intro y hy hyK
    rw [← hpole] at hyK
    have := (hab y (hVU hy)).1
    rw [show ψ y = ⊥ from hyK] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  -- the finite values of `ψ` on `V`
  have hψV : ∀ y ∈ V, ψ y = (((ψ y).toReal : ℝ) : EReal) ∧ aψ ≤ (ψ y).toReal := by
    intro y hy
    obtain ⟨h1, h2⟩ := hab y (hVU hy)
    have hne : ψ y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
    have hnt : ψ y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hc := (EReal.coe_toReal hnt hne).symm
    refine ⟨hc, ?_⟩
    rw [hc] at h1
    exact EReal.coe_le_coe_iff.mp h1
  -- the uniform estimate
  set err : ℕ → ℝ := fun j => (2 + (B - aψ) / c₀) * (1 / ((j : ℝ) + 1)) with herrdef
  have hclose : ∀ j, ∀ y ∈ V, |v j y - (P y).toReal| ≤ err j := by
    intro j y hy
    obtain ⟨hψy, haψ⟩ := hψV y hy
    obtain ⟨h1, h2, -, -⟩ := hvb j y (ψ y).toReal hψy
    set ε := 1 / ((j : ℝ) + 1) with hεdef
    -- compare `P_θ(F_j)` with `P_θ(f)`
    have hFfle : ∀ y, F j y ≤ f y + ε := fun y => by
      have := (abs_le.mp (hFf j y)).2; linarith
    have hfFle : ∀ y, f y ≤ F j y + ε := fun y => by
      have := (abs_le.mp (hFf j y)).1; linarith
    have hP1 := rooftopEnvelope_le_of_le_add θ.val hFfle y
    have hP2 := rooftopEnvelope_le_of_le_add θ.val hfFle y
    have hPy := hreal y (by rw [hψy]; exact EReal.coe_ne_bot _)
    rw [← hPdef, hPy] at hP1
    rw [← hPdef, hPy] at hP2
    have hlow := (h1.trans hP1)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hlow
    have hup := hP2.trans (add_le_add h2 le_rfl)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hup
    have hrB : (ψ y).toReal ≤ B := by
      have h := hψle y
      rw [hψy, EReal.coe_le_coe_iff] at h
      linarith
    have hε0 : 0 ≤ ε := (hjpos j).le
    have hBa : 0 ≤ B - aψ := by linarith
    have hdiv : ε / c₀ * (B - (ψ y).toReal) ≤ (B - aψ) / c₀ * ε := by
      have h1 : ε * (B - (ψ y).toReal) ≤ ε * (B - aψ) :=
        mul_le_mul_of_nonneg_left (by linarith) hε0
      calc ε / c₀ * (B - (ψ y).toReal) = ε * (B - (ψ y).toReal) / c₀ := by ring
        _ ≤ ε * (B - aψ) / c₀ := div_le_div_of_nonneg_right h1 hc₀.le
        _ = (B - aψ) / c₀ * ε := by ring
    have hnn : 0 ≤ (B - aψ) / c₀ * ε := mul_nonneg (div_nonneg hBa hc₀.le) hε0
    have herr : err j = 2 * ε + (B - aψ) / c₀ * ε := by
      rw [herrdef]; simp only; rw [← hεdef]; ring
    rw [herr, abs_le]
    constructor <;> linarith
  have hconv : TendstoUniformlyOn v (fun y => (P y).toReal) atTop V := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro r hr
    have hlim : Tendsto err atTop (𝓝 0) := by
      have h : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h.const_mul (2 + (B - aψ) / c₀)
      rw [mul_zero] at h2
      exact h2
    filter_upwards [hlim.eventually (gt_mem_nhds hr)] with j hj y hy
    rw [Real.dist_eq, abs_sub_comm]
    exact (hclose j y hy).trans_lt hj
  -- the uniform Laplacian bound
  set M : ℝ := 2 * (T + S) * Real.exp (a * (B + 2 - aψ)) + Cθ + N with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : 0 ≤ 2 * (T + S) * Real.exp (a * (B + 2 - aψ)) := by positivity
    positivity
  refine ⟨V, hVo, hxV, hVK, v, hvs, hconv, M, hM0, fun j y hy => ?_⟩
  obtain ⟨hψy, haψ⟩ := hψV y hy
  obtain ⟨-, -, h3, h4⟩ := hvb j y (ψ y).toReal hψy
  have hexp : Real.exp (a * (B + 2 - (ψ y).toReal)) ≤ Real.exp (a * (B + 2 - aψ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ha.le)
  have hTS : 0 ≤ 2 * (T + S) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hexp hTS
  have hθy := abs_le.mp (hCθ y)
  have hεN : 0 ≤ 1 / ((j : ℝ) + 1) * N := by positivity
  have hεN' : 1 / ((j : ℝ) + 1) * N ≤ N := by
    have := hjle j
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  rw [abs_le, hMdef]
  constructor <;> nlinarith

/-! ### The source statements -/

section Source

open SGPT.PSH SGPT.PSH.VariableComplexAtlas

omit [ConnectedSpace Y] [BorelSpace Y] in
/-- `C^{1,1̄}_ω(U)` passes to smaller sets. -/
theorem hasBoundedMetricLaplacianOn_mono (w : KahlerBackground N Y) {U U' : Set Y} (hUU' : U ⊆ U')
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacianOn w U' f) : HasBoundedMetricLaplacianOn w U f :=
  ⟨hf.1.mono hUU', fun K hK hKc => hf.2 K (hK.trans hUU') hKc⟩

/-- **Source `thm:DNT23_C11bar` for nef and big classes** (book class `C^{1,1̄}`, bounded
`ω`-Laplacian): if `{θ}` is big and nef (`NefWithRespectTo ω θ`: `θ + εω` is cohomologous to a
semipositive form for every `ε > 0`) and `f ∈ C^{1,1̄}_ω(X)`, then
`P_θ(f) = sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`) is real-valued on `X ∖ nK({θ})` and lies in
`C^{1,1̄}_ω(X ∖ nK({θ}))`, with `nK = sourceNonKahlerLocus` (`def:nKlocus`). -/
theorem sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_nef
    (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hnef : NefWithRespectTo w (atlasClosedFormToNative θ)) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
        (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) :
          EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · obtain ⟨h1, h2⟩ :=
      DNTBig.sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one
        (by omega) w θ hbig hf
    exact ⟨fun x _ => h1 x, h2⟩
  · rw [sourceObstacleEnvelope_eq_native]
    obtain ⟨h1, h2⟩ := rooftopEnvelope_hasBoundedMetricLaplacianOn_of_nef hN w _ hbig hnef hf
    have hsub := nativeNonKahlerLocus_subset_source hN
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
    exact ⟨fun x hx => h1 x fun h => hx (hsub h),
      hasBoundedMetricLaplacianOn_mono w (compl_subset_compl.mpr hsub) h2⟩

/-- **The "in particular" of source `thm:DNT23_C11bar` for nef and big classes**: `V_θ`
(`sourceMinimalEnvelope`, `eq:Vtheta`) is real-valued on `X ∖ nK({θ})` and lies in
`C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_nef
    (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hnef : NefWithRespectTo w (atlasClosedFormToNative θ)) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  obtain ⟨φ, hφ⟩ := Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hV : sourceMinimalEnvelope θ =
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun _ => ((0 : ℝ) : EReal)) := by
    rw [sourceMinimalEnvelope_eq_native, sourceObstacleEnvelope_eq_native]
    exact thetaPshSupremum_eq_rooftopEnvelope_zero w _ hφ
  rw [hV]
  exact sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_nef w θ hbig hnef
    (f := fun _ => 0) (hasBoundedMetricLaplacian_of_chartSmooth w fun _ => contDiffOn_const)

end Source

end SGPT.NPP.DNNef
