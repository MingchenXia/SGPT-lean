import SGPT.Siu.LocalDivisorBound
import SGPT.Siu.PrimeDivisorCurrent
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.Foundations.Analysis.Pending.ResidualNefReduction
import SGPT.Foundations.Analysis.Pending.DivisorialSliceBound

/-!
# Siu's lemma: `T - ν(T, D)[D]` is a closed positive current

Source: `lma:Siudec` of the book (chapter *Plurisubharmonic functions*, section *The space of
currents*): for a prime divisor `D` on a compact complex manifold `X` and a closed positive
`(1,1)`-current `T`, the difference `T - ν(T, D)[D]` is a closed positive `(1,1)`-current.  The
book cites Demailly; we follow Xia, *Foundations of pluripotential theory*,
`thm:siu-divisorial-decomposition`, Step 1, with the singular points of `D` handled by the slicing
argument of `SGPT.Siu.LocalDivisorBound` instead of a measure argument.

## Proof

Write `T = σ + ddᶜφ` and `[D] = Θ + ddᶜψ`, `ψ = log |s_D|²_h` for a smooth metric `h` on `𝒪(D)`.
For `0 ≤ c' < c = ν(T, D)` put `v = φ - c' ψ` off `D`.

* Off `D`, `ψ` is a smooth local potential of `-Θ`, so `v` is `(σ - c' Θ)`-psh there
  (`thetaPshOff_sub_smul_weight`).
* Near a point of `D`, in a chart, `ψ = log |f|² + smooth` with `f` a local generator of the
  reduced ideal of `D`, so `f` has multiplicity one at every regular point of its divisor
  (`regularPresentation_m_eq_one`), and every point of `D` has Lelong number `≥ c > c'`.  The
  local Siu bound `exists_nhds_le_mul_log_normSq_add` gives `φ - c' log |f|² ≤ C`, so `v` is
  bounded above near `D`.
* The removable-singularity theorem across the analytic set `D`
  (`PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed`) extends `v` to a `(σ - c' Θ)`-psh
  potential `w`, equal to `v` off `D`, a null set in every chart.
* Hence `T - c'[D] = (σ - c' Θ) + ddᶜ w` is closed and positive; letting `c' → c` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent LelongPoincareDivisor
open SquaredLogLelongSourceNormalization
open ThetaPshCodimTwoExtension PshAnalyticSetExtension
open DivisorRegularLocus
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-! ### Local equations of a metrized divisor in a chart -/

/-- A local generator `g` of a metrized divisor whose weight is locally nondegenerate vanishes
identically near no point, read in any chart. -/
theorem chart_generator_frequently_ne {E : MeteredEffectiveQDivisor (m + 1) M}
    (hnd : LocallyNondegenerate E.weight) {V' : Set M} (hV' : IsOpen V') {g : M → ℂ} {h : M → ℝ}
    (hw : ∀ y ∈ V', E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal))
    (e : ComplexChart (m + 1) M) :
    ∀ z ∈ e.val.target ∩ e.val.symm ⁻¹' V', ∃ᶠ w in 𝓝 z, g (e.val.symm w) ≠ 0 := by
  intro z hz
  rw [Filter.frequently_iff]
  intro s hs
  have hdom : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V') := e.val.isOpen_inter_preimage_symm hV'
  obtain ⟨O, hOs, hOo, hzO⟩ := _root_.mem_nhds_iff.mp (inter_mem hs (hdom.mem_nhds hz))
  have hOt : O ⊆ e.val.symm.source := fun w hw => (hOs hw).2.1
  have hOopen : IsOpen (e.val.symm '' O) := e.val.symm.isOpen_image_of_subset_source hOo hOt
  obtain ⟨_, ⟨w, hwO, rfl⟩, hne⟩ := hnd (e.val.symm z) _ hOopen (mem_image_of_mem _ hzO)
  refine ⟨w, (hOs hwO).1, fun hg0 => hne ?_⟩
  rw [hw _ (hOs hwO).2.2]
  have : generatorLog (fun _ : Fin 1 => g) (e.val.symm w) = ⊥ :=
    (generatorLog_eq_bot_iff _ _).mpr fun _ => hg0
  rw [this, EReal.bot_add]

/-- **A reduced local equation has multiplicity one.**  If `g` generates the vanishing ideal of a
set near every point of an open `V'`, then at every regular point of the divisor of `g` (read in
any chart) the multiplicity is `1`. -/
theorem regularPresentation_m_eq_one {Pv V' : Set M} (hV' : IsOpen V') {g : M → ℂ}
    (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g V')
    (hgen : ∀ y ∈ V', ∀ f, (vanishingIdeal (n := m + 1) Pv).mem y f ↔
      IsInSpanAt (n := m + 1) (· = g) y f)
    (e : ComplexChart (m + 1) M) {y' : ComplexModel (m + 1)}
    (hy' : y' ∈ e.val.target ∩ e.val.symm ⁻¹' V')
    (Q : RegularPresentation (fun z => g (e.val.symm z)) y') : Q.m = 1 := by
  set y := e.val.symm y' with hydef
  have hysrc : y ∈ e.val.source := e.val.map_target hy'.1
  have hyV : y ∈ V' := hy'.2
  have hey : e.val y = y' := e.val.right_inv hy'.1
  -- `g` lies in its own span, so it vanishes on `Pv` near `y`
  have hgHol : HolomorphicAt (m + 1) g y :=
    eventually_of_mem (hV'.mem_nhds hyV) fun z hz => (hg z hz).mdifferentiableAt (hV'.mem_nhds hz)
  have hgspan : IsInSpanAt (n := m + 1) (· = g) y g := by
    refine ⟨hgHol, 1, fun _ => g, fun _ => fun _ => 1, fun _ => rfl,
      fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const, ?_⟩
    exact Eventually.of_forall fun z => by simp
  have hgvan : ∀ᶠ z in 𝓝 y, z ∈ Pv → g z = 0 := ((hgen y hyV g).mpr hgspan).2
  -- the defining function `h` of the presentation, pulled back to `M`
  set H : M → ℂ := fun z => Q.h (e.val z) with hHdef
  have hmem : e.val.source ∩ e.val ⁻¹' Q.U ∈ 𝓝 y :=
    e.val.isOpen_inter_preimage Q.isOpen |>.mem_nhds
      ⟨hysrc, by rw [Set.mem_preimage, hey]; exact Q.mem⟩
  have hHhol : HolomorphicAt (m + 1) H y := by
    filter_upwards [hmem] with z hz
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) e.val z :=
      mdifferentiableAt_atlas e.property hz.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) Q.h (e.val z) :=
      (Q.h_diff.differentiableAt (Q.isOpen.mem_nhds hz.2)).mdifferentiableAt
    exact h2.comp z h1
  have hHvan : ∀ᶠ z in 𝓝 y, z ∈ Pv → H z = 0 := by
    filter_upwards [hgvan, hmem] with z hgz hz hzPv
    have h0 : g z = 0 := hgz hzPv
    have hQ := Q.eq (e.val z) hz.2
    simp only [e.val.left_inv hz.1, h0] at hQ
    have hv := Q.v_ne (e.val z) hz.2
    have : Q.h (e.val z) ^ Q.m = 0 := by
      rcases mul_eq_zero.mp hQ.symm with h | h
      · exact h
      · exact absurd h hv
    exact pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp Q.m_pos) |>.mp this
  obtain ⟨-, N, s, a, hs, ha, hHeq⟩ := (hgen y hyV H).mp ⟨hHhol, hHvan⟩
  -- in the chart: `h = A g = A hᵐ v` near `y'`
  set A : ComplexModel (m + 1) → ℂ := fun w => ∑ i, a i (e.val.symm w) with hAdef
  have hsymm : Tendsto e.val.symm (𝓝 y') (𝓝 y) := e.val.continuousAt_symm hy'.1
  have hAcont : ContinuousAt A y' := by
    show Tendsto (fun w => ∑ i, a i (e.val.symm w)) (𝓝 y') (𝓝 (∑ i, a i (e.val.symm y')))
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ((ha i).self_of_nhds.continuousAt).comp (e.val.continuousAt_symm hy'.1)
  have hchart : ∀ᶠ w in 𝓝 y', Q.h w = A w * (Q.h w ^ Q.m * Q.v w) := by
    filter_upwards [hsymm.eventually hHeq, e.val.open_target.mem_nhds hy'.1,
      Q.isOpen.mem_nhds Q.mem] with w hw hwt hwU
    have h1 : H (e.val.symm w) = Q.h w := by simp only [hHdef, e.val.right_inv hwt]
    have h2 : g (e.val.symm w) = Q.h w ^ Q.m * Q.v w := Q.eq w hwU
    have hs' : ∀ i, s i = g := hs
    calc Q.h w = H (e.val.symm w) := h1.symm
      _ = ∑ i, a i (e.val.symm w) * s i (e.val.symm w) := hw
      _ = A w * g (e.val.symm w) := by simp only [hs', hAdef, Finset.sum_mul]
      _ = A w * (Q.h w ^ Q.m * Q.v w) := by rw [h2]
  by_contra hm
  have hm2 : 2 ≤ Q.m := by have := Q.m_pos; omega
  set K : ComplexModel (m + 1) → ℂ := fun w => A w * Q.h w ^ (Q.m - 1) * Q.v w with hKdef
  have hKcont : ContinuousAt K y' :=
    (hAcont.mul ((Q.h_diff.differentiableAt (Q.isOpen.mem_nhds Q.mem)).continuousAt.pow _)).mul
      (Q.v_diff.differentiableAt (Q.isOpen.mem_nhds Q.mem)).continuousAt
  have hK0 : K y' = 0 := by
    simp only [hKdef, Q.h_zero, zero_pow (by omega : Q.m - 1 ≠ 0), mul_zero, zero_mul]
  have hKev : ∀ᶠ w in 𝓝 y', ‖K w‖ < 1 := by
    have h' : ‖K y'‖ < 1 := by rw [hK0, norm_zero]; exact one_pos
    exact hKcont.norm.eventually (gt_mem_nhds h')
  have hfreq : ∃ᶠ w in 𝓝 y', Q.h w ≠ 0 := by
    intro hev
    have hev' : Q.h =ᶠ[𝓝 y'] fun _ => (0 : ℂ) := hev.mono fun w hw => not_not.mp hw
    exact Q.dh_ne y' Q.mem (by rw [hev'.fderiv_eq, fderiv_const_apply])
  obtain ⟨w, ⟨hwh, hwK⟩, hwc⟩ := ((hfreq.and_eventually hKev).and_eventually hchart).exists
  have hK1 : K w = 1 := by
    have hpow : Q.h w ^ Q.m = Q.h w * Q.h w ^ (Q.m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow] at hwc
    have : Q.h w * (1 - K w) = 0 := by
      simp only [hKdef]; linear_combination hwc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hwh
    · exact (sub_eq_zero.mp h).symm
  rw [hK1, norm_one] at hwK
  exact lt_irrefl _ hwK

/-- Off the support of a metrized divisor `E`, `φ - c ψ_E` is `(σ - c Θ_E)`-psh: `ψ_E` is a
smooth local potential of `-Θ_E` there. -/
theorem thetaPshOff_sub_smul_weight {σ : ClosedRealOneOneForm (m + 1) M} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic σ.val φ) (E : MeteredEffectiveQDivisor (m + 1) M) (c : ℝ) :
    ThetaPshOff (σ - c • E.curvature).val E.support
      (fun x => φ x + ((-(c * (E.weight x).toReal) : ℝ) : EReal)) := by
  intro e z hz hzsupp
  have hxsource : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hex : e.val (e.val.symm z) = z := e.val.right_inv hz
  obtain ⟨W₁, hzW₁, hpot₁⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hzsupp e hxsource
  rw [hex] at hzW₁
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := hφ e z hz
  have hWopen : IsOpen (W₁ ∩ W₂) := hpot₁.1.inter hpot₂.1
  have hw₁ : ContDiffOn ℝ ∞ (fun ζ => (E.weight (e.val.symm ζ)).toReal) (W₁ ∩ W₂) :=
    hpot₁.2.2.1.mono inter_subset_left
  have hρ₂ : ContDiffOn ℝ ∞ ρ₂ (W₁ ∩ W₂) := hpot₂.2.2.1.mono inter_subset_right
  refine ⟨W₁ ∩ W₂, fun y => ρ₂ y + c • (E.weight (e.val.symm y)).toReal, ⟨hzW₁, hzW₂⟩, ?_, ?_⟩
  · refine ⟨hWopen, fun y hy => hpot₂.2.1 hy.2, hρ₂.add (hw₁.const_smul c), ?_⟩
    intro y hy
    rw [smoothDDC_add hWopen hρ₂ (hw₁.const_smul c) hy, smoothDDC_smul hWopen hw₁ c hy,
      hpot₂.2.2.2 hy.2, hpot₁.2.2.2 hy.1, BlowupBigPullback.coeff_sub,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg]
    simp only [smul_neg]
    abel
  · refine plurisubharmonicOn_congr_of_isOpen hWopen (hpsh₂.mono inter_subset_right) ?_
    intro y _hy
    show φ (e.val.symm y) + ((ρ₂ y : ℝ) : EReal) =
      (φ (e.val.symm y) + ((-(c * (E.weight (e.val.symm y)).toReal) : ℝ) : EReal)) +
        ((ρ₂ y + c • (E.weight (e.val.symm y)).toReal : ℝ) : EReal)
    generalize φ (e.val.symm y) = a
    induction a using EReal.rec with
    | bot => simp only [EReal.bot_add]
    | top => rw [EReal.top_add_coe, EReal.top_add_coe, EReal.top_add_coe]
    | coe a =>
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
      congr 1
      rw [smul_eq_mul]
      ring

/-- The support of a metrized divisor with locally nondegenerate weight and local single
generators is a null set in every chart. -/
theorem ae_chart_notMem_support {E : MeteredEffectiveQDivisor (m + 1) M}
    (hnd : LocallyNondegenerate E.weight)
    (hloc : ∀ x : M, ∃ V' : Set M, IsOpen V' ∧ x ∈ V' ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g V' ∧ ∃ h : M → ℝ,
        ∀ y ∈ V', E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal))
    (e : ComplexChart (m + 1) M) :
    ∀ᵐ z ∂(volume.restrict (e.val.target)), e.val.symm z ∉ E.support := by
  rw [ae_restrict_iff' e.val.open_target.measurableSet]
  set S : Set (ComplexModel (m + 1)) := {z | z ∈ e.val.target ∧ e.val.symm z ∈ E.support}
    with hSdef
  have hS : volume S = 0 := by
    refine measure_null_of_locally_null S fun z hz => ?_
    obtain ⟨V', hV', hxV', g, hg, h, hw⟩ := hloc (e.val.symm z)
    set O : Set (ComplexModel (m + 1)) := e.val.target ∩ e.val.symm ⁻¹' V' with hOdef
    have hOopen : IsOpen O := e.val.isOpen_inter_preimage_symm hV'
    have hzO : z ∈ O := ⟨hz.1, hxV'⟩
    have hG : DifferentiableOn ℂ (fun w => g (e.val.symm w)) O :=
      MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg
    have hG0 := chart_generator_frequently_ne hnd hV' hw e
    have hae := LelongPoincareDivisor.ae_ne_zero hOopen hG hG0
    rw [ae_restrict_iff' hOopen.measurableSet] at hae
    have hnull : volume {w | w ∈ O ∧ g (e.val.symm w) = 0} = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hae.mono fun w hw hws => hw hws.1 hws.2)
    refine ⟨S ∩ O, inter_mem_nhdsWithin _ (hOopen.mem_nhds hzO), measure_mono_null ?_ hnull⟩
    intro w hw'
    refine ⟨hw'.2, ?_⟩
    have hbot : E.weight (e.val.symm w) = ⊥ := hw'.1.2
    rw [hw _ hw'.2.2] at hbot
    have hgl : generatorLog (fun _ : Fin 1 => g) (e.val.symm w) = ⊥ := by
      revert hbot
      generalize generatorLog (fun _ : Fin 1 => g) (e.val.symm w) = a
      intro hbot
      induction a using EReal.rec with
      | bot => rfl
      | top => rw [EReal.top_add_coe] at hbot; exact absurd hbot (by simp)
      | coe a => rw [← EReal.coe_add] at hbot; exact absurd hbot (EReal.coe_ne_bot _)
    exact (generatorLog_eq_bot_iff _ _).mp hgl 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS] with z hz hzt hzE
  exact hz ⟨hzt, hzE⟩

/-! ### The upper bound near the divisor -/

/-- **Local boundedness of `φ - c ψ` near the divisor.**  If every point of a prime divisor `D`
has Lelong number `> c` for the `σ`-psh potential `φ`, and `ψ` is the weight of a smooth metric on
`𝒪(D)`, then `φ - c ψ` is locally bounded above off `D`. -/
theorem locallyBoundedAboveOff_sub_smul_weight
    {σ : ClosedRealOneOneForm (m + 1) M} {φ : M → EReal} (hφ : IsThetaPshPotential σ.val φ)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E)
    {c : ℝ} (hc : 0 ≤ c)
    (hν : ∀ x ∈ D.val, ENNReal.ofReal c < squaredLogLelongNumber (n := m + 1) φ x) :
    LocallyBoundedAboveOff E.support
      (fun x => φ x + ((-(c * (E.weight x).toReal) : ℝ) : EReal)) := by
  classical
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE
  have hoff := thetaPshOff_sub_smul_weight hφ.1 E c
  have hφtop : ∀ x, φ x ≠ ⊤ := hφ.1.quasiPlurisubharmonic.ne_top
  intro x
  by_cases hx : x ∉ E.support
  · -- off the divisor: upper semicontinuity
    have husc := upperSemicontinuousAt_of_thetaPshOff hoff hx
    have hlt : φ x + ((-(c * (E.weight x).toReal) : ℝ) : EReal) < ⊤ :=
      EReal.add_lt_top (hφtop x) (EReal.coe_ne_top _)
    obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt hlt
    exact ⟨_, husc _ hq, q, fun y hy _ => hy.le⟩
  push Not at hx
  -- near the divisor: the local Siu bound in a chart
  set e := complexChartAt (n := m + 1) x with hedef
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  set z0 := e.val x with hz0def
  have hz0 : z0 ∈ e.val.target := e.val.map_source hxe
  have hz0x : e.val.symm z0 = x := e.val.left_inv hxe
  obtain ⟨V', hV', hxV', g, hg, hgen, h, hh, hwV⟩ := hE x
  have hgen' : ∀ y ∈ V', ∀ f, (vanishingIdeal (n := m + 1) D.val).mem y f ↔
      IsInSpanAt (n := m + 1) (· = g) y f := by
    intro y hy f
    rw [← SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal D]
    exact hgen y hy f
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := hφ.1 e z0 hz0
  set dom : Set (ComplexModel (m + 1)) := e.val.target ∩ e.val.symm ⁻¹' V' with hdomdef
  have hdom : IsOpen dom := e.val.isOpen_inter_preimage_symm hV'
  set Ω : Set (ComplexModel (m + 1)) := W₂ ∩ dom with hΩdef
  have hΩ : IsOpen Ω := hpot₂.1.inter hdom
  have hz0Ω : z0 ∈ Ω := ⟨hzW₂, hz0, by rw [Set.mem_preimage, hz0x]; exact hxV'⟩
  set u : ComplexModel (m + 1) → EReal := fun z => chartFunction φ e z + (ρ₂ z : EReal) with hudef
  have hu : PlurisubharmonicOn u Ω := hpsh₂.mono inter_subset_left
  set G : ComplexModel (m + 1) → ℂ := fun z => g (e.val.symm z) with hGdef
  have hG : DifferentiableOn ℂ G Ω :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg).mono inter_subset_right
  have hG0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, G z ≠ 0 := fun y hy =>
    chart_generator_frequently_ne hw.2 hV' hwV e y hy.2
  -- zeros of `g` in `V'` lie on `D`
  have hzeroD : ∀ y ∈ V', g y = 0 → y ∈ D.val := by
    intro y hy hgy
    rw [← hEsupp]
    show E.weight y = ⊥
    rw [hwV y hy, (generatorLog_eq_bot_iff _ _).mpr fun _ => hgy, EReal.bot_add]
  have hνloc : ∀ y' ∈ Ω, ∀ Q : RegularPresentation G y', ∃ γ : ℝ, 2 * c * Q.m ≤ γ ∧
      ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] y', u z ≤ ((γ * Real.log ‖z - y'‖ + C : ℝ) : EReal) := by
    intro y' hy' Q
    have hm1 : Q.m = 1 := regularPresentation_m_eq_one hV' hg hgen' e hy'.2 Q
    have hyD : e.val.symm y' ∈ D.val := hzeroD _ hy'.2.2 Q.g_x
    have hysrc : e.val.symm y' ∈ e.val.source := e.val.map_target hy'.2.1
    have hρc : ContinuousAt ρ₂ y' :=
      (hpot₂.2.2.1.continuousOn _ hy'.1).continuousAt (hpot₂.1.mem_nhds hy'.1)
    have hlel : lelongNumber (n := m + 1) u y' =
        2 * squaredLogLelongNumber (n := m + 1) φ (e.val.symm y') := by
      rw [hudef, LelongChartReaderInvariance.lelongNumber_add_continuous_eq hρc]
      have := LelongChartReaderInvariance.lelongNumber_chartFunction_eq (u := φ) e hysrc
      rw [e.val.right_inv hy'.2.1] at this
      rw [this, lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
    have hlt : ((Real.toNNReal (2 * c) : NNReal) : ℝ≥0∞) < lelongNumber (n := m + 1) u y' := by
      rw [hlel]
      have h1 := hν _ hyD
      have h2 : ((Real.toNNReal (2 * c) : NNReal) : ℝ≥0∞) = 2 * ENNReal.ofReal c := by
        change ENNReal.ofReal (2 * c) = _
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      rw [h2]
      exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) h1
    obtain ⟨γ', hγ', C, hC⟩ := DivisorialSliceBound.exists_admissible_of_lt_lelongNumber hlt
    refine ⟨γ', ?_, C, hC⟩
    rw [hm1]
    have : ((Real.toNNReal (2 * c) : NNReal) : ℝ) = 2 * c := Real.coe_toNNReal _ (by positivity)
    rw [this] at hγ'
    simpa using hγ'.le
  obtain ⟨U, hU, C, hC⟩ := exists_nhds_le_mul_log_normSq_add hΩ hu hG hG0 hc hνloc hz0Ω
  -- continuity of the smooth parts at the point
  have hρc0 : ContinuousAt ρ₂ z0 :=
    (hpot₂.2.2.1.continuousOn _ hzW₂).continuousAt (hpot₂.1.mem_nhds hzW₂)
  have hhc0 : ContinuousAt (fun z => h (e.val.symm z)) z0 :=
    ((hh e).continuousOn _ ⟨hz0, by rw [Set.mem_preimage, hz0x]; exact hxV'⟩).continuousAt
      (hdom.mem_nhds ⟨hz0, by rw [Set.mem_preimage, hz0x]; exact hxV'⟩)
  have hρev : ∀ᶠ z in 𝓝 z0, ρ₂ z0 - 1 < ρ₂ z :=
    continuousAt_const.eventually_lt hρc0 (by linarith)
  have hhev : ∀ᶠ z in 𝓝 z0, h x - 1 < h (e.val.symm z) := by
    have := continuousAt_const.eventually_lt hhc0 (show h (e.val.symm z0) - 1 < h (e.val.symm z0)
      by linarith)
    simpa only [hz0x] using this
  set Uc : Set (ComplexModel (m + 1)) :=
    U ∩ Ω ∩ {z | ρ₂ z0 - 1 < ρ₂ z} ∩ {z | h x - 1 < h (e.val.symm z)} with hUcdef
  have hUc : Uc ∈ 𝓝 z0 :=
    inter_mem (inter_mem (inter_mem hU (hΩ.mem_nhds hz0Ω)) hρev) hhev
  have hUM : e.val.source ∩ e.val ⁻¹' Uc ∈ 𝓝 x :=
    inter_mem (e.val.open_source.mem_nhds hxe) (e.val.continuousAt hxe |>.preimage_mem_nhds hUc)
  refine ⟨_, hUM, C - (ρ₂ z0 - 1) - c * (h x - 1), ?_⟩
  intro y hy hyE
  have hysrc : y ∈ e.val.source := hy.1
  have hyUc : e.val y ∈ Uc := hy.2
  have hey : e.val.symm (e.val y) = y := e.val.left_inv hysrc
  have hyV : y ∈ V' := by have := hyUc.1.1.2.2.2; rwa [Set.mem_preimage, hey] at this
  have hgy : g y ≠ 0 := fun h0 => hyE (hEsupp ▸ hzeroD y hyV h0)
  have hGy : G (e.val y) ≠ 0 := by simp only [hGdef, hey]; exact hgy
  have hbound := hC (e.val y) hyUc.1.1.1 hGy
  simp only [hudef, hGdef, chartFunction, hey] at hbound
  have hwy : (E.weight y).toReal = Real.log (‖g y‖ ^ 2) + h y := by
    rw [hwV y hyV, generatorLog_one_of_ne_zero hgy, ← EReal.coe_add, EReal.toReal_coe]
  show φ y + ((-(c * (E.weight y).toReal) : ℝ) : EReal) ≤ _
  rw [hwy]
  have hρy : ρ₂ z0 - 1 < ρ₂ (e.val y) := hyUc.1.2
  have hhy : h x - 1 < h y := by have := hyUc.2; rwa [Set.mem_ofPred_eq, hey] at this
  revert hbound
  generalize φ y = a
  intro hbound
  induction a using EReal.rec with
  | bot => simp
  | top => exact absurd (EReal.top_add_coe _ ▸ hbound) (not_le.mpr (EReal.coe_lt_top _))
  | coe a =>
    rw [← EReal.coe_add] at hbound ⊢
    have hb := EReal.coe_le_coe_iff.mp hbound
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left hhy.le hc]

/-! ### Siu's lemma -/

/-- Two theta-potential currents agree when their forms agree and their potentials agree almost
everywhere in every chart. -/
theorem thetaPotentialCurrent_congr_ae {θ θ' : SmoothRealForm (m + 1) M 2} (hθ : θ = θ')
    {u u' : M → EReal} (hu : IsThetaPshPotential θ u) (hu' : IsThetaPshPotential θ' u')
    (hae : ∀ e : ComplexChart (m + 1) M,
      chartFunction u e =ᵐ[volume.restrict (e.val.target)] chartFunction u' e) :
    thetaPotentialCurrent θ u hu = thetaPotentialCurrent θ' u' hu' := by
  subst hθ
  unfold thetaPotentialCurrent
  congr 1
  apply GlobalCurrentPotentials.globalDDC_congr_ae
  intro e
  rw [addHaar_canonicalBasis]
  exact hae e

/-- **Siu's lemma below the generic Lelong number.**  For `0 ≤ c < ν(T, D)`, `T - c[D]` is a closed
positive `(1,1)`-current; explicitly `T - c[D] = (σ - c Θ) + ddᶜ w` for the extension `w` of
`φ - c ψ` across `D`. -/
theorem isClosedPositiveCurrent_sub_smul_primeDivisorCurrent_of_lt [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {c : ℝ} (hc : 0 ≤ c)
    (hlt : ENNReal.ofReal c < currentGenericLelong T hT D) :
    IsClosedPositiveCurrent (T - c • primeDivisorCurrent D) := by
  classical
  obtain ⟨σ, φ, hφ, hTeq⟩ := hT.exists_thetaPotential
  have hν : ∀ x ∈ D.val, ENNReal.ofReal c < squaredLogLelongNumber (n := m + 1) φ x := by
    intro x hx
    have h1 := currentGenericLelong_le hT D hx
    rw [currentLelong_eq_of_eq_thetaPotentialCurrent hT hTeq] at h1
    exact hlt.trans_le h1
  have hEspec :=
    Classical.choose_spec (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
  set E := Classical.choose (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
    with hEdef
  have hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E := hEspec.2
  have hEsupp : E.support = D.val :=
    hEspec.1.trans (SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_support D)
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE
  set v : M → EReal := fun x => φ x + ((-(c * (E.weight x).toReal) : ℝ) : EReal) with hvdef
  have hoff := thetaPshOff_sub_smul_weight hφ.1 E c
  have hbound := locallyBoundedAboveOff_sub_smul_weight hφ D E hEsupp hE hc hν
  have hAclosed : IsClosed E.support := by rw [hEsupp]; exact D.isClosed
  have hAan : IsComplexAnalyticSubset (n := m + 1) E.support := by
    rw [hEsupp, ← D.subvariety_carrier]; exact D.subvariety.analytic
  have hAne : E.support ≠ univ := by
    obtain ⟨x, -⟩ := D.nonempty
    obtain ⟨y, -, hy⟩ := hw.2 x univ isOpen_univ trivial
    intro hA
    have hyA : y ∈ E.support := hA ▸ mem_univ y
    exact hy hyA
  have hclosure := PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed
    (σ - c • E.curvature) E.support v hAan hAne hoff hbound
  have hWpsh := thetaPlurisubharmonic_extensionAcross_of_localClosure hAclosed hoff hclosure
  set W := extensionAcross E.support v with hWdef
  have hWeq : ∀ y, y ∉ E.support → W y = v y := fun y hy =>
    extensionAcross_eq_of_notMem hAclosed hoff hy
  have hWnd : LocallyNondegenerate W := by
    intro x U hU hxU
    obtain ⟨y0, hy0U, hy0⟩ := hw.2 x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hφ.2 y0 (U ∩ E.supportᶜ) (hU.inter hAclosed.isOpen_compl) ⟨hy0U, hy0⟩
    refine ⟨y, hyU.1, ?_⟩
    rw [hWeq y hyU.2]
    intro hbot
    rcases EReal.add_eq_bot_iff.mp hbot with h | h
    · exact hy h
    · exact EReal.coe_ne_bot _ h
  have hW : IsThetaPshPotential (σ - c • E.curvature).val W := ⟨hWpsh, hWnd⟩
  have hloc : ∀ x : M, ∃ V' : Set M, IsOpen V' ∧ x ∈ V' ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g V' ∧ ∃ h : M → ℝ,
        ∀ y ∈ V', E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal) := by
    intro x
    obtain ⟨V', hV', hxV', g, hg, -, h, -, hweq⟩ := hE x
    exact ⟨V', hV', hxV', g, hg, h, hweq⟩
  -- the current identity `T = ((σ - cΘ) + ddᶜ w) + c [D]`
  obtain ⟨hcw, hcw_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul hw hc
  obtain ⟨hsum, hsum_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hW hcw
  have hD : primeDivisorCurrent D = thetaPotentialCurrent E.curvature.val E.weight hw :=
    primeDivisorCurrent_eq_thetaPotentialCurrent D E hE
  have hcongr : thetaPotentialCurrent (σ - c • E.curvature + c • E.curvature).val
      (fun x => W x + (c : EReal) * E.weight x) hsum = thetaPotentialCurrent σ.val φ hφ := by
    apply thetaPotentialCurrent_congr_ae (by rw [sub_add_cancel])
    intro e
    filter_upwards [ae_chart_notMem_support hw.2 hloc e] with z hz
    simp only [chartFunction]
    rw [hWeq _ hz]
    show φ (e.val.symm z) + ((-(c * (E.weight (e.val.symm z)).toReal) : ℝ) : EReal) +
      (c : EReal) * E.weight (e.val.symm z) = φ (e.val.symm z)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, E.weight (e.val.symm z) = r :=
      ⟨_, (EReal.coe_toReal (hw.1.quasiPlurisubharmonic.ne_top _) hz).symm⟩
    rw [hr, EReal.toReal_coe, ← EReal.coe_mul]
    generalize φ (e.val.symm z) = a
    induction a using EReal.rec with
    | bot => simp only [EReal.bot_add]
    | top => rw [EReal.top_add_coe, EReal.top_add_coe]
    | coe a =>
      rw [← EReal.coe_add, ← EReal.coe_add]
      congr 1
      ring
  have hTid : T = thetaPotentialCurrent (σ - c • E.curvature).val W hW +
      c • primeDivisorCurrent D := by
    rw [hTeq, ← hcongr, hsum_eq, hcw_eq, hD]
  have hTW : T - c • primeDivisorCurrent D =
      thetaPotentialCurrent (σ - c • E.curvature).val W hW := by
    rw [hTid]
    abel
  rw [hTW]
  exact isClosedPositiveCurrent_thetaPotentialCurrent _ _ _

/-- **Siu's lemma** (`lma:Siudec`).  Let `D` be a prime divisor on a compact complex manifold `X`.
For every closed positive `(1,1)`-current `T` on `X`, `T - ν(T, D)[D]` is a closed positive
`(1,1)`-current. -/
theorem isClosedPositiveCurrent_sub_currentGenericLelong_smul [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    IsClosedPositiveCurrent
      (T - (currentGenericLelong T hT D).toReal • primeDivisorCurrent D) := by
  set c := (currentGenericLelong T hT D).toReal with hcdef
  have hcne := currentGenericLelong_ne_top hT D
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hDp := isClosedPositiveCurrent_primeDivisorCurrent D
  have hsubt : ∀ t : ℝ, T - t • primeDivisorCurrent D = T + (-t) • primeDivisorCurrent D :=
    fun t => (sub_eq_add_neg _ _).trans (congrArg (T + ·) (neg_smul t _).symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsubt]; exact hT.1.add _ (hDp.1.smul _ (-c))
  · rw [hsubt]; exact hT.2.1.add _ (hDp.2.1.smul _ (-c))
  · intro e α hα
    rcases hc0.eq_or_lt with h0 | hpos
    · have h00 : T - c • primeDivisorCurrent D = T := by
        rw [hsubt, ← h0, neg_zero, zero_smul]
        exact add_zero T
      rw [h00]; exact hT.2.2 e α hα
    set β := CanonicalComplementaryCurrentTests.castTestDegree
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α with hβdef
    have hlin : ∀ t : ℝ, (T - t • primeDivisorCurrent D).inChart e β =
        T.inChart e β - t * (primeDivisorCurrent D).inChart e β := by
      intro t
      rw [hsubt, GlobalCurrent.inChart_add, GlobalCurrent.inChart_smul]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      ring
    have hev : ∀ᶠ t in 𝓝[<] c, 0 ≤ T.inChart e β - t * (primeDivisorCurrent D).inChart e β := by
      filter_upwards [Ioo_mem_nhdsLT hpos] with t ht
      have hlt : ENNReal.ofReal t < currentGenericLelong T hT D :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht.1.le hcne).mpr ht.2
      have := (isClosedPositiveCurrent_sub_smul_primeDivisorCurrent_of_lt hT D ht.1.le hlt).2.2
        e α hα
      rw [← hlin t]
      exact this
    have htend : Tendsto (fun t => T.inChart e β - t * (primeDivisorCurrent D).inChart e β)
        (𝓝[<] c) (𝓝 (T.inChart e β - c * (primeDivisorCurrent D).inChart e β)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (continuous_const.sub (continuous_id.mul continuous_const)).tendsto c
    have := ge_of_tendsto htend hev
    rw [← hlin c] at this
    exact this

end SGPT.Siu
