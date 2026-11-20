import SGPT.NPP.LogConcavityGeneralReduction
import SGPT.NPP.LogConcavityDinewDensity

/-!
# Dinew's inequality against the Kähler volume, and `thm:logconc` in general

* `kahlerVolumeMixedLowerBound`: a proof of S52's `SGPT.NPP.LogConcavity.KahlerVolumeMixedLowerBound`
  (FPT `prop:nonpluripolar-multifactor-common-measure` with `ν = ωⁿ`, `fᵢ = cᵢ`) on every compact
  complex manifold, in every dimension: if `⟨(θᵢ + ddᶜwᵢ)ⁿ⟩ ≥ cᵢ ωⁿ` for all `i`, then
  `⟨(θ₁ + ddᶜw₁) ∧ ⋯ ∧ (θₙ + ddᶜwₙ)⟩ ≥ (∏ᵢ cᵢ^{1/n}) ωⁿ`. In a common potential patch all measures
  are the push-forwards of coordinate non-pluripolar products, `ωⁿ` that of the smooth
  Monge–Ampère measure of a local Kähler potential; the coordinate statement is
  `mixedTruncationLimitMeasure_ge_smoothMeasure`, and patches are glued by compactness.
* `prod_sourceMass_rpow_le_sourceMixedMass`: the second assertion of `thm:logconc` for arbitrary
  closed positive currents (S52's reduction applied to the proved bound).
* the first assertion of `thm:logconc` for arbitrary endpoints `φ₀, φ₁ ∈ PSH(X, θ)`:
  `m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)` for `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ`
  (`sourceConvexCombMass_logConcave`), concavity of `m^{1/n}`
  (`concaveOn_sourceConvexCombMass_rpow`) and, for positive endpoint masses, concavity of
  `log m` (`concaveOn_log_sourceConvexCombMass`). The algebra is S52's
  (`LogConcavityGeneralIGood`), with the general mixed inequality in place of the `𝓘`-good one.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent

section Patches

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M]

/-- A transported coordinate measure evaluated on the chart preimage of a coordinate set. -/
theorem pushMeasure_source_inter_preimage {θ : Fin n → ClosedRealOneOneForm n M}
    {w : Fin n → M → EReal} (P : Patch θ w) (μ : Measure (ComplexModel n))
    (t : Set (ComplexModel n)) :
    P.pushMeasure μ (P.chart.val.source ∩ P.chart.val ⁻¹' t) =
      μ ((P.domain : Set (ComplexModel n)) ∩ t) := by
  rw [P.pushMeasure_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hys⟩
    refine ⟨hy, ?_⟩
    have h : P.chart.val (P.chart.val.symm y) ∈ t := hys.2
    rwa [P.chart.val.right_inv (P.domain_le_target hy)] at h
  · rintro ⟨hy, hyt⟩
    refine ⟨hy, P.chart.val.map_target (P.domain_le_target hy), ?_⟩
    change P.chart.val (P.chart.val.symm y) ∈ t
    rwa [P.chart.val.right_inv (P.domain_le_target hy)]

variable [CompactSpace M]

/-- **Dinew's inequality against `ωⁿ` near a point.** -/
theorem exists_nhds_kahlerVolume_mixed_lower_bound (hn : 0 < n) (ω : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (w : Fin n → M → EReal)
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, ENNReal.ofReal (c i) • kahlerVolume ω ≤
      globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      (ENNReal.ofReal (∏ i, c i ^ ((n : ℝ)⁻¹)) • kahlerVolume ω).restrict U ≤
        (globalMixedMeasure θ w hw).restrict U := by
  classical
  have hω0 : IsThetaPshPotential ω.form.val (fun _ => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  set e := complexChartAt (n := n) x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W₀, g, hzW₀, hg, hgpsh⟩ := hω0.1 e (e.val x) hz
  choose W ρ hzW hρ hpsh using fun i => hw i e (e.val x) hz
  let V : TopologicalSpace.Opens (ComplexModel n) :=
    ⟨e.val.target ∩ W₀ ∩ ⋂ i, W i,
      (e.val.open_target.inter hg.1).inter (isOpen_iInter_of_finite fun i => (hρ i).1)⟩
  have hVt : (V : Set (ComplexModel n)) ⊆ e.val.target := fun y hy => hy.1.1
  have hVW₀ : (V : Set (ComplexModel n)) ⊆ W₀ := fun y hy => hy.1.2
  have hVW : ∀ i, (V : Set (ComplexModel n)) ⊆ W i := fun i y hy => mem_iInter.mp hy.2 i
  have hzV : e.val x ∈ V := ⟨⟨hz, hzW₀⟩, mem_iInter.mpr hzW⟩
  let Pω : Patch (fun _ : Fin n => ω.form) (fun _ => fun _ => (0 : EReal)) :=
    { chart := e, domain := V, domain_le_target := hVt, potential := fun _ => g
      localPotential := fun _ => hg.mono V.isOpen hVW₀
      plurisubharmonic := fun _ => hgpsh.mono hVW₀ }
  let Pi : ∀ i, Patch (fun _ : Fin n => θ i) (fun _ => w i) := fun i =>
    { chart := e, domain := V, domain_le_target := hVt, potential := fun _ => ρ i
      localPotential := fun _ => (hρ i).mono V.isOpen (hVW i)
      plurisubharmonic := fun _ => (hpsh i).mono (hVW i) }
  let P : Patch θ w :=
    { chart := e, domain := V, domain_le_target := hVt, potential := ρ
      localPotential := fun i => (hρ i).mono V.isOpen (hVW i)
      plurisubharmonic := fun i => (hpsh i).mono (hVW i) }
  set S : Set M := (P.source : Set M) with hS
  have hSm : MeasurableSet S := P.source.isOpen.measurableSet
  -- the coordinate functions and measures
  set v : Fin n → ComplexModel n → EReal :=
    fun i y => chartFunction (w i) e y + (ρ i y : EReal) with hvdef
  have hv : ∀ i, PlurisubharmonicOn (v i) V := fun i => (hpsh i).mono (hVW i)
  have hgV : IsSmoothPshOn V g := by
    refine FirstPass.MongeAmpere.isSmoothPshOn_of_psh (hg.2.2.1.mono hVW₀) ?_
    have h1 := hgpsh.mono hVW₀
    have h2 : (fun y => chartFunction (fun _ : M => (0 : EReal)) e y + (g y : EReal)) =
        fun y => (g y : EReal) := funext fun y => zero_add _
    rwa [h2] at h1
  have hNPω : mixedTruncationLimitMeasure V Pω.corrected Pω.plurisubharmonic =
      smoothMeasure V g hgV := by
    have hcongr : mixedTruncationLimitMeasure V Pω.corrected Pω.plurisubharmonic =
        mixedTruncationLimitMeasure V (fun _ => fun y => (g y : EReal)) (fun _ => hgV.2.1) :=
      mixedTruncationLimitMeasure_congr _ _ (fun i y _ => zero_add _)
    rw [hcongr, mixedTruncationLimitMeasure_diagonal hn hgV.2.1]
    exact (SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const hgV).1
  have hNPi : ∀ i, mixedTruncationLimitMeasure V (Pi i).corrected (Pi i).plurisubharmonic =
      truncationLimitMeasure V (v i) (hv i) := fun i =>
    mixedTruncationLimitMeasure_diagonal hn (hv i)
  -- restrictions of the global measures to the patch
  have hRω : (kahlerVolume ω).restrict S = Pω.pushMeasure (smoothMeasure V g hgV) := by
    have h1 := globalMixedMeasure_restrict_patch (fun _ : Fin n => hω0.1) Pω
    rw [patchMeasure, hNPω] at h1
    exact h1
  have hRi : ∀ i, (globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)).restrict S =
      (Pi i).pushMeasure (truncationLimitMeasure V (v i) (hv i)) := fun i => by
    have h1 := globalMixedMeasure_restrict_patch (fun _ : Fin n => hw i) (Pi i)
    rw [patchMeasure, hNPi i] at h1
    exact h1
  have hR : (globalMixedMeasure θ w hw).restrict S =
      P.pushMeasure (mixedTruncationLimitMeasure V v hv) :=
    globalMixedMeasure_restrict_patch hw P
  -- the hypotheses in coordinates
  have hcompl : smoothMeasure V g hgV (V : Set (ComplexModel n))ᶜ = 0 := by
    rw [← hNPω]
    exact mixedTruncationLimitMeasure_compl _
  have hcoord : ∀ i, ENNReal.ofReal (c i) • smoothMeasure V g hgV ≤
      truncationLimitMeasure V (v i) (hv i) := by
    intro i
    refine Measure.le_iff'.mpr fun t => ?_
    set s : Set M := e.val.source ∩ e.val ⁻¹' ((V : Set (ComplexModel n)) ∩ t) with hs
    have hsS : s ∩ S = s := inter_eq_left.mpr fun y hy => ⟨hy.1, hy.2.1⟩
    have h1 := Measure.le_iff'.mp (h i) s
    have hkv : kahlerVolume ω s = smoothMeasure V g hgV ((V : Set (ComplexModel n)) ∩ t) := by
      rw [← hsS, ← Measure.restrict_apply' hSm, hRω]
      have := pushMeasure_source_inter_preimage Pω (smoothMeasure V g hgV)
        ((V : Set (ComplexModel n)) ∩ t)
      rw [← inter_assoc, inter_self] at this
      exact this
    have hgm : globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i) s =
        truncationLimitMeasure V (v i) (hv i) ((V : Set (ComplexModel n)) ∩ t) := by
      rw [← hsS, ← Measure.restrict_apply' hSm, hRi i]
      have := pushMeasure_source_inter_preimage (Pi i) (truncationLimitMeasure V (v i) (hv i))
        ((V : Set (ComplexModel n)) ∩ t)
      rw [← inter_assoc, inter_self] at this
      exact this
    rw [Measure.smul_apply, smul_eq_mul, hkv] at h1
    rw [Measure.smul_apply, smul_eq_mul, ← measure_inter_conull hcompl, inter_comm]
    exact h1.trans (le_of_eq hgm) |>.trans (measure_mono inter_subset_right)
  have hmain := mixedTruncationLimitMeasure_ge_smoothMeasure hn hv hgV hc hcoord
  refine ⟨S, P.source.isOpen, ⟨hx, hzV⟩, ?_⟩
  rw [Measure.restrict_smul, hRω, hR]
  refine Measure.le_iff'.mpr fun s => ?_
  rw [Measure.smul_apply, smul_eq_mul, Patch.pushMeasure_apply, Patch.pushMeasure_apply]
  have := Measure.le_iff'.mp hmain ((V : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' s)
  rw [Measure.smul_apply, smul_eq_mul] at this
  exact this

end Patches

/-- **Dinew's inequality against the Kähler volume with constant densities** (FPT
`prop:nonpluripolar-multifactor-common-measure`, `ν = ωⁿ`, `fᵢ = cᵢ`): S52's
`KahlerVolumeMixedLowerBound` holds on every compact complex manifold of every dimension. -/
theorem kahlerVolumeMixedLowerBound (k : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] : SGPT.NPP.LogConcavity.KahlerVolumeMixedLowerBound k M := by
  intro ω θ w hw c hc h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : θ = fun _ => ω.form := funext fun i => i.elim0
    obtain rfl : w = fun _ => fun _ => 0 := funext fun i => i.elim0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, one_smul]
    exact le_of_eq rfl
  · have hloc := fun x => exists_nhds_kahlerVolume_mixed_lower_bound hk ω θ w hw c hc h x
    have hglue := restrict_le_restrict_of_isLindelof isCompact_univ.isLindelof
      (fun x _ => hloc x)
    rwa [Measure.restrict_univ, Measure.restrict_univ] at hglue

/-! ### `thm:logconc` in general -/

section LogConc

open SGPT.NPP.LogConcavity SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`thm:logconc`, second assertion, in general.** On a compact connected Kähler manifold of
dimension `n = q + 1`, for closed real `(1,1)`-forms `θᵢ` and arbitrary `θᵢ`-psh `uᵢ`,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜuᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜu₁) ∧ ⋯ ∧ (θₙ + ddᶜuₙ)⟩`. -/
theorem prod_sourceMass_rpow_le_sourceMixedMass (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal :=
  prod_sourceMass_rpow_le_sourceMixedMass_of_kahlerVolumeMixedLowerBound
    (kahlerVolumeMixedLowerBound (q + 1) M) ω θ u hu

/-- The key inequality `((1-s) m(t₀)^{1/n} + s m(t₁)^{1/n})ⁿ ≤ m((1-s)t₀ + st₁)` for arbitrary
endpoints. -/
theorem pow_le_sourceConvexCombMass (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    {t₀ t₁ s : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ((1 - s) * sourceConvexCombMass θ h₀ h₁ t₀ ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
        s * sourceConvexCombMass θ h₀ h₁ t₁ ^ (((q + 1 : ℕ) : ℝ)⁻¹)) ^ (q + 1) ≤
      sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁) := by
  classical
  have hr0 : 0 ≤ (1 - s) * t₀ + s * t₁ := by nlinarith [ht₀.1, ht₁.1, hs.1, hs.2]
  have hr1 : (1 - s) * t₀ + s * t₁ ≤ 1 := by nlinarith [ht₀.2, ht₁.2, hs.1, hs.2]
  rw [sourceConvexCombMass_eq_sum ω θ h₀ h₁ ht₀.1 ht₀.2,
    sourceConvexCombMass_eq_sum ω θ h₀ h₁ ht₁.1 ht₁.2,
    sourceConvexCombMass_eq_sum ω θ h₀ h₁ hr0 hr1]
  apply pow_le_of_mixed_inequality _ hs.1 hs.2
  intro τ
  let tb : Fin (q + 1) → ℝ := fun i => if τ i then t₁ else t₀
  have htb0 : ∀ i, 0 ≤ tb i := fun i => by
    dsimp only [tb]; split_ifs
    · exact ht₁.1
    · exact ht₀.1
  have htb1 : ∀ i, tb i ≤ 1 := fun i => by
    dsimp only [tb]; split_ifs
    · exact ht₁.2
    · exact ht₀.2
  have hmixed := prod_sourceMass_rpow_le_sourceMixedMass ω (fun _ => θ)
    (fun i => convexComb (tb i) φ₁ φ₀) (fun i => isThetaPSH_convexComb h₁ h₀ (htb0 i) (htb1 i))
  rw [sourceMixedMass_convexComb_eq_sum ω θ h₀ h₁ tb htb0 htb1] at hmixed
  refine le_of_eq_of_le (Finset.prod_congr rfl fun i _ => ?_) hmixed
  rw [sourceMixedMass_convexComb_eq_sum ω θ h₀ h₁ (fun _ => tb i) (fun _ => htb0 i)
    (fun _ => htb1 i)]

/-- **`thm:logconc`, first assertion, general endpoints: concavity of `m^{1/n}`.** For
`φ₀, φ₁ ∈ PSH(X, θ)`, `t ↦ (∫_X θ_{tφ₁+(1-t)φ₀}ⁿ)^{1/n}` is concave on `[0, 1]`. -/
theorem concaveOn_sourceConvexCombMass_rpow (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun t => sourceConvexCombMass θ h₀ h₁ t ^ (((q + 1 : ℕ) : ℝ)⁻¹)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hs : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  have h := pow_le_sourceConvexCombMass ω θ h₀ h₁ hx hy hs
  simp only [smul_eq_mul]
  have hnn : 0 ≤ (1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
      b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹) := by
    have := sourceConvexCombMass_nonneg θ h₀ h₁ x
    have := sourceConvexCombMass_nonneg θ h₀ h₁ y
    positivity
  calc (1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
        b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹)
      = (((1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
          b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹)) ^ (q + 1)) ^
          (((q + 1 : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hnn (Nat.succ_ne_zero q)).symm
    _ ≤ sourceConvexCombMass θ h₀ h₁ ((1 - b) * x + b * y) ^ (((q + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)

/-- **`thm:logconc`, first assertion, general endpoints: log-concavity.** For
`φ₀, φ₁ ∈ PSH(X, θ)` and `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ`,
`m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)` for all `t₀, t₁, s ∈ [0, 1]`; i.e. `log m` is concave on
`[0, 1]` with the convention `log 0 = -∞`. -/
theorem sourceConvexCombMass_logConcave (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    {t₀ t₁ s : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceConvexCombMass θ h₀ h₁ t₀ ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ t₁ ^ s ≤
      sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁) := by
  set m := sourceConvexCombMass θ h₀ h₁ with hm
  set e : ℝ := ((q + 1 : ℕ) : ℝ)⁻¹ with he
  have hm0 : ∀ t, 0 ≤ m t := sourceConvexCombMass_nonneg θ h₀ h₁
  set a := m t₀ ^ e
  set b := m t₁ ^ e
  have ha : 0 ≤ a := Real.rpow_nonneg (hm0 _) _
  have hb : 0 ≤ b := Real.rpow_nonneg (hm0 _) _
  have hapow : m t₀ = a ^ (q + 1) := (Real.rpow_inv_natCast_pow (hm0 _) (Nat.succ_ne_zero q)).symm
  have hbpow : m t₁ = b ^ (q + 1) := (Real.rpow_inv_natCast_pow (hm0 _) (Nat.succ_ne_zero q)).symm
  have hamgm : a ^ (1 - s) * b ^ s ≤ (1 - s) * a + s * b :=
    Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hs.2) hs.1 ha hb (by ring)
  have hkey := pow_le_sourceConvexCombMass ω θ h₀ h₁ ht₀ ht₁ hs
  refine le_trans (le_of_eq ?_) ((pow_le_pow_left₀ (by positivity) hamgm (q + 1)).trans hkey)
  rw [hapow, hbpow, mul_pow, ← Real.rpow_natCast (a ^ (1 - s)), ← Real.rpow_natCast (b ^ s),
    ← Real.rpow_mul ha, ← Real.rpow_mul hb, ← Real.rpow_natCast a, ← Real.rpow_natCast b,
    ← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_comm (1 - s), mul_comm s]

/-- **`thm:logconc`, first assertion, general endpoints of positive mass.** If the endpoint
masses are positive, all masses `m(t)`, `t ∈ [0, 1]`, are positive and `log m` is concave on
`[0, 1]`. -/
theorem concaveOn_log_sourceConvexCombMass (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hpos₀ : 0 < sourceConvexCombMass θ h₀ h₁ 0) (hpos₁ : 0 < sourceConvexCombMass θ h₀ h₁ 1) :
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < sourceConvexCombMass θ h₀ h₁ t) ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => Real.log (sourceConvexCombMass θ h₀ h₁ t)) := by
  set m := sourceConvexCombMass θ h₀ h₁ with hm
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < m t := by
    intro t ht
    have h := sourceConvexCombMass_logConcave ω θ h₀ h₁
      (t₀ := 0) (t₁ := 1) (s := t) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ ht
    simp only [mul_zero, zero_add, mul_one] at h
    exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hpos₀ _) (Real.rpow_pos_of_pos hpos₁ _)) h
  refine ⟨hpos, convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hs : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  have h := sourceConvexCombMass_logConcave ω θ h₀ h₁ hx hy hs
  simp only [smul_eq_mul]
  have hx' := hpos x hx
  have hy' := hpos y hy
  calc (1 - b) * Real.log (m x) + b * Real.log (m y)
      = Real.log (m x ^ (1 - b) * m y ^ b) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hx' _).ne' (Real.rpow_pos_of_pos hy' _).ne',
          Real.log_rpow hx', Real.log_rpow hy']
    _ ≤ Real.log (m ((1 - b) * x + b * y)) :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hx' _) (Real.rpow_pos_of_pos hy' _)) h

end LogConc

end SGPT.NPP.LogConcavityDinew
