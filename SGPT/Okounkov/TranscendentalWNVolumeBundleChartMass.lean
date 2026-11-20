import SGPT.Okounkov.TranscendentalWNVolumeBundleLocal
import SGPT.Okounkov.TranscendentalWNVolumeGlobalMeasurable

/-!
# The bundle Legendre identity over one bundle chart (package WN-VF4)

Blueprint `claude-tok-wn-vf4`, node `tok-wn-vf4:chart-identity`; source WN21 Theorem 3.5 (as
applied at the end of §4) in the coordinates `(ζ, w) = (z', z̃₁)` of a bundle chart of `ℰ`.

Let `Λ` be a bundle chart of `ℰ` over the chart `e_Z` of `Z` on `Ω` (`IsExcBundleChart`), with
twist `g`, and `ρ_X` a local potential of `θ` near `e_Z⁻¹(Ω)`; put `x(ζ) = e_Z⁻¹ ζ`,
`ρ_Z = ρ_X ∘ x`, and remove from `Ω` the closed set of `ζ` with `x(ζ) ∈ E_nK(ξ) ∪ E_nK(ξ_c)`
(the open set `Ω'`).  On `Ω' × ℂ*`, by the formula for `φ` and `log S₂ - log S₁ = log |w|² - g`,

  `φ(Λ(ζ, w)) + ρ_Z(ζ) - c log S₁(Λ(ζ, w)) = sup_{t ∈ [0, c]} (v_t(ζ) + t log |w|²)`,
  `v_t = W_t ∘ x + ρ_Z - t g`,

the inverse partial Legendre transform of the concave family `v_t` of psh functions
(`ρ_Z - t g` is a local potential of `(θ - tη)|_Z`).  The left side is the corrected potential of
`φ` in the patches given by `Λ` and the local potential `ρ_Z - c log S₁` of `θ̃|_ℰ`
(`isSmoothLocalPotential_pullback_deformationForm`), so `globalMixedMeasure_image_eq` and WN21
Theorem 3.3 (`IsLegendreMAData.mongeAmpere_eq'`) give, for every Borel `C ⊆ e_Z⁻¹(Ω')`,

  `⟨(θ̃|_ℰ + dd^c φ)^{m+1}⟩({S₁ > 0, S₂ > 0} ∩ π_Z⁻¹ C) = (m + 1) ∫₀^c ⟨((θ - tη)|_Z + dd^c W_t|_Z)^m⟩(C) dt`

(`excBundle_chart_identity`), together with the a.e. measurability of the integrand
(`legendreMAMeasurable`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The measures `⟨((θ - tη)|_Z + dd^c W_t|_Z)^m⟩` on `Z` (`0` for `t ∉ [0, c]`). -/
def excZMeasure (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (c : ℝ) (W : ℝ → F.carrier → EReal)
    (hW : ∀ t ∈ Icc 0 c, ThetaPlurisubharmonic (θ - t • E.curvature).val (W t)) (t : ℝ) :
    @Measure F.tail.carrier (borel F.tail.carrier) :=
  letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
  if h : t ∈ Icc 0 c then
    globalMixedMeasure
      (fun _ : Fin m => ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F)
        (θ - t • E.curvature))
      (fun _ => fun y => W t (firstFlagInclusion F y))
      (fun _ => GlobalPotentialPullback.thetaPlurisubharmonic_comp
        (contMDiff_firstFlagInclusion F) (hW t h))
  else 0

/-- Concavity at a point only depends on the values at that point. -/
theorem IsConcaveFamilyAt.congr_at {X X' : Type*} {v : ℝ → X → EReal} {v' : ℝ → X' → EReal}
    {I : Set ℝ} {x : X} {x' : X'}
    (h : IsConcaveFamilyAt v I x) (heq : ∀ t, v' t x' = v t x) : IsConcaveFamilyAt v' I x' := by
  intro l₁ hl₁ l₂ hl₂ s hs0 hs1
  rw [heq, heq, heq]
  exact h l₁ hl₁ l₂ hl₂ s hs0 hs1

/-- The local potential `ρ_Z - t g` of `(θ - tη)|_Z`. -/
theorem isSmoothLocalPotential_pullback_sub_smul {θ η : ClosedRealOneOneForm (m + 1) F.carrier}
    {eZ : ComplexChart m F.tail.carrier} {Ω : Set (ComplexModel m)} {ρ g : ComplexModel m → ℝ}
    (hρ : IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) θ).val eZ Ω ρ)
    (hg : IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) η).val eZ Ω g) (t : ℝ) :
    IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) (θ - t • η)).val eZ Ω
      (fun ζ => ρ ζ - t * g ζ) := by
  have hcg : ContDiffOn ℝ ∞ (fun y => t * g y) Ω := contDiffOn_const.mul hg.2.2.1
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.1.sub hcg, fun z hz => ?_⟩
  have h1 := PositiveClasses.smoothDDC_sub hρ.1 hρ.2.2.1 hcg hz
  have h2 := smoothDDC_smul hρ.1 hg.2.2.1 t hz
  simp only [smul_eq_mul] at h2
  have hform : ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) (θ - t • η) =
      ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) θ +
        (-t) • ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) η := by
    rw [sub_eq_add_neg, ← neg_smul, NefCoreKahlerCurrent.pullback_add_smul]
  rw [h1, h2, hρ.2.2.2 hz, hg.2.2.2 hz, hform, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul]
  ext v
  simp [sub_eq_add_neg]

/-! ### The identity over one bundle chart -/

section Chart

variable {F}
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-vf4:chart-identity`** (WN21 Theorem 3.5 over one bundle chart): for every Borel
`C ⊆ Z` inside the chart domain and off `E_nK(ξ) ∪ E_nK(ξ_c)`,
`⟨(θ̃|_ℰ + dd^c φ)^{m+1}⟩({S₁ > 0, S₂ > 0} ∩ π_Z⁻¹ C) = (m + 1) ∫₀^c ⟨((θ - tη)|_Z + dd^c W_t)^m⟩(C) dt`,
and the integrand is a.e.-measurable. -/
theorem excBundle_chart_identity
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c)
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature))
    {W : ℝ → F.carrier → EReal}
    (hW1 : ∀ t ∈ Icc 0 c, ThetaPlurisubharmonic (θ - t • E.curvature).val (W t))
    (hW2 : ∀ x, IsConcaveFamilyAt W (Icc 0 c) x) {C₀ : ℝ}
    (hW3 : ∀ t ∈ Icc 0 c, ∀ x, thetaPshSupremum (θ - t • E.curvature).val x ≤ W t x ∧
      W t x ≤ thetaPshSupremum (θ - t • E.curvature).val x + (C₀ : EReal))
    {φ : 𝒳 → EReal}
    (hformula : ∀ p ∈ exceptionalSet F μ, 0 < strictWeight F E μ p → 0 < zStrictWeight F E μ p →
      (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) →
      (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ -
        c • RealBottChern.ofRepresentative E.curvature) →
      φ p = ⨆ t ∈ Icc 0 c, W t (μ p).1 +
        ((t * Real.log (zStrictWeight F E μ p) +
          (c - t) * Real.log (strictWeight F E μ p) : ℝ) : EReal))
    {eZ : ComplexChart m F.tail.carrier} {Ω : Set (ComplexModel m)} {Λ : ComplexModel m → ℂ → 𝒳}
    {g : ComplexModel m → ℝ} (hch : IsExcBundleChart F E hμ eZ Ω Λ g)
    (dX : ComplexChart (m + 1) F.carrier) {WX : Set (ComplexModel (m + 1))}
    {ρX : ComplexModel (m + 1) → ℝ} (hρX : IsSmoothLocalPotential θ.val dX WX ρX)
    (hΩX : Ω ⊆ potentialDomain (firstFlagInclusion F) eZ dX WX) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    haveI := compactSpace_exceptional F hμ
    ∀ (hφ : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback
        (contMDiff_exceptionalInclusion F hμ) (deformationForm F hμ.contMDiff θ b c Eℰ)).val
        (fun y : exceptionalSet F μ => φ y))
      (C : Set F.tail.carrier), @MeasurableSet _ (borel F.tail.carrier) C → C ⊆ eZ.val.source →
      (∀ y ∈ C, eZ.val y ∈ Ω ∧ firstFlagInclusion F y ∉
        nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪
          nonKahlerLocus (RealBottChern.ofRepresentative θ -
            c • RealBottChern.ofRepresentative E.curvature)) →
      globalMixedMeasure (fun _ : Fin (m + 1) => ClosedRealOneOneForm.pullback
          (contMDiff_exceptionalInclusion F hμ) (deformationForm F hμ.contMDiff θ b c Eℰ))
          (fun _ => fun y : exceptionalSet F μ => φ y) (fun _ => hφ)
          {p | 0 < strictWeight F E μ p ∧ 0 < zStrictWeight F E μ p ∧
            (μ p).1 ∈ firstFlagInclusion F '' C} =
        ((m + 1 : ℕ) : ℝ≥0∞) * ∫⁻ t in Icc 0 c, excZMeasure F E θ c W hW1 t C ∧
      AEMeasurable (fun t => excZMeasure F E θ c W hW1 t C) (volume.restrict (Icc 0 c)) := by
  intro hφ C hCm hCs hCΩ
  classical
  letI := exceptionalChartedSpace F hμ
  haveI := isComplexManifold_exceptional F hμ
  letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  haveI := compactSpace_exceptional F hμ
  letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
  have hι := contMDiff_firstFlagInclusion F
  have : Nonempty F.carrier := by
    obtain ⟨y, -, -⟩ := hξ.2
    exact ⟨y⟩
  set ξ := RealBottChern.ofRepresentative θ with hξdef
  set ξc := RealBottChern.ofRepresentative θ - c • RealBottChern.ofRepresentative E.curvature
    with hξcdef
  have hbig0 : IsBigClass ξ := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξ.1
  have hbigc : IsBigClass ξc := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξc.1
  set bad : Set F.carrier := nonKahlerLocus ξ ∪ nonKahlerLocus ξc with hbaddef
  have hbadc : IsClosed bad :=
    (NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (Nat.succ_pos m) ξ
      hbig0).isClosed.union
      (NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (Nat.succ_pos m) ξc
        hbigc).isClosed
  set xZ : ComplexModel m → F.carrier := fun ζ => firstFlagInclusion F (eZ.val.symm ζ)
    with hxZdef
  have hxZc : ContinuousOn xZ Ω :=
    hι.continuous.comp_continuousOn (eZ.val.continuousOn_symm.mono hch.subset_target)
  set Ω' : TopologicalSpace.Opens (ComplexModel m) :=
    ⟨Ω ∩ xZ ⁻¹' badᶜ, hxZc.isOpen_inter_preimage hch.isOpen hbadc.isOpen_compl⟩ with hΩ'def
  have hΩ'Ω : (Ω' : Set (ComplexModel m)) ⊆ Ω := inter_subset_left
  -- the potentials on `Z`
  set ρZ : ComplexModel m → ℝ := fun ζ => ρX (dX.val (xZ ζ)) with hρZdef
  have hpotθ : IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) θ).val eZ Ω ρZ :=
    (isSmoothLocalPotential_pullback hι eZ hρX).mono hch.isOpen hΩX
  have hpott : ∀ t : ℝ, IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) (θ - t • E.curvature)).val
      eZ Ω (fun ζ => ρZ ζ - t * g ζ) := fun t =>
    isSmoothLocalPotential_pullback_sub_smul F hpotθ hch.twist t
  -- the concave family `v_t = W_t ∘ x + ρ_Z - t g`
  set vt : ℝ → ComplexModel m → EReal :=
    fun t ζ => W t (xZ ζ) + ((ρZ ζ - t * g ζ : ℝ) : EReal) with hvdef
  have hpshv : ∀ t ∈ Icc 0 c, PlurisubharmonicOn (vt t) Ω' := fun t ht =>
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι (hW1 t ht)) eZ (hpott t)).mono hΩ'Ω
  have hconcv : ∀ z ∈ Ω', IsConcaveFamilyAt vt (Icc 0 c) z := by
    intro z _
    refine IsConcaveFamilyAt.congr_at (((hW2 (xZ z)).add_affine (-g z)).add_const (ρZ z))
      fun t => ?_
    simp only [hvdef]
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    ring
  have hWle : ∀ t ∈ Icc 0 c, ∀ x, W t x ≤ (C₀ : EReal) := by
    intro t ht x
    refine (hW3 t ht x).2.trans ?_
    have h0 := thetaPshSupremum_le_zero (θ - t • E.curvature).val x
    simpa using add_le_add_left h0 (C₀ : EReal)
  have hρZc : ∀ z ∈ Ω, ContinuousAt ρZ z := fun z hz =>
    hpotθ.2.2.1.continuousOn.continuousAt (hch.isOpen.mem_nhds hz)
  have hgc : ∀ z ∈ Ω, ContinuousAt g z := fun z hz =>
    hch.twist.2.2.1.continuousOn.continuousAt (hch.isOpen.mem_nhds hz)
  have hbddv : ∀ t ∈ Icc 0 c, ∀ z ∈ Ω', ∃ C : ℝ, ∀ᶠ w in 𝓝 z,
      ((-C : ℝ) : EReal) ≤ vt t w ∧ vt t w ≤ (C : EReal) := by
    intro t ht z hz
    have hbigt : IsBigClass (RealBottChern.ofRepresentative (θ - t • E.curvature)) := by
      rw [ofRepresentative_sub_smul]
      exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp
        (isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht).1
    have hVpot := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _ hbigt
    have hx : xZ z ∉ nonKahlerLocus
        (RealBottChern.ofRepresentative (θ - t • E.curvature)) := by
      rw [ofRepresentative_sub_smul]
      intro hmem
      exact hz.2 (nonKahlerLocus_sub_smul_subset (Nat.succ_pos m) hbig0 hbigc ht hmem)
    obtain ⟨N, hN, a₀, b₀, hab⟩ :=
      BigClassEnvelopeContact.exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus
        (Nat.succ_pos m) _ hbigt hVpot hx
    set r : ComplexModel m → ℝ := fun w => ρZ w - t * g w with hrdef
    have hrc : ContinuousAt r z := (hρZc z hz.1).sub (continuousAt_const.mul (hgc z hz.1))
    have hev1 : ∀ᶠ w in 𝓝 z, |r w - r z| < 1 := by
      have := Metric.tendsto_nhds.mp hrc 1 one_pos
      filter_upwards [this] with w hw
      simpa [Real.dist_eq] using hw
    have hev2 : ∀ᶠ w in 𝓝 z, xZ w ∈ N :=
      (hxZc.continuousAt (hch.isOpen.mem_nhds hz.1)).eventually hN
    refine ⟨|a₀| + |C₀| + |r z| + 1, ?_⟩
    filter_upwards [hev1, hev2] with w hw1 hw2
    have hlo : (a₀ : EReal) ≤ W t (xZ w) := (hab _ hw2).1.trans (hW3 t ht _).1
    have hhi := hWle t ht (xZ w)
    have hb1 : r z - 1 ≤ r w := by linarith [(abs_lt.mp hw1).1]
    have hb2 : r w ≤ r z + 1 := by linarith [(abs_lt.mp hw1).2]
    constructor
    · have h := add_le_add hlo (EReal.coe_le_coe_iff.mpr hb1)
      rw [← EReal.coe_add] at h
      refine le_trans ?_ h
      rw [EReal.coe_le_coe_iff]
      have := neg_abs_le a₀; have := neg_abs_le (r z); have := abs_nonneg C₀
      linarith
    · have h := add_le_add hhi (EReal.coe_le_coe_iff.mpr hb2)
      rw [← EReal.coe_add] at h
      refine h.trans ?_
      rw [EReal.coe_le_coe_iff]
      have := le_abs_self C₀; have := le_abs_self (r z); have := abs_nonneg a₀
      linarith
  have hupv : ∀ z ∈ Ω', ∃ C : ℝ, ∀ᶠ w in 𝓝 z, ∀ t ∈ Icc 0 c, vt t w ≤ (C : EReal) := by
    intro z hz
    have hev1 : ∀ᶠ w in 𝓝 z, |ρZ w - ρZ z| < 1 := by
      have := Metric.tendsto_nhds.mp (hρZc z hz.1) 1 one_pos
      filter_upwards [this] with w hw
      simpa [Real.dist_eq] using hw
    have hev2 : ∀ᶠ w in 𝓝 z, |g w - g z| < 1 := by
      have := Metric.tendsto_nhds.mp (hgc z hz.1) 1 one_pos
      filter_upwards [this] with w hw
      simpa [Real.dist_eq] using hw
    refine ⟨C₀ + (|ρZ z| + 1) + c * (|g z| + 1), ?_⟩
    filter_upwards [hev1, hev2] with w hw1 hw2 t ht
    have hhi := hWle t ht (xZ w)
    have hreal : ρZ w - t * g w ≤ (|ρZ z| + 1) + c * (|g z| + 1) := by
      have h1 : ρZ w ≤ |ρZ z| + 1 := by
        have := (abs_lt.mp hw1).2; have := le_abs_self (ρZ z); linarith
      have h2 : -(t * g w) ≤ c * (|g z| + 1) := by
        have hg1 : |g w| ≤ |g z| + 1 := by
          have := abs_sub_abs_le_abs_sub (g w) (g z); linarith
        have : -(t * g w) ≤ t * |g w| := by
          have := neg_abs_le (g w); nlinarith [ht.1]
        have : t * |g w| ≤ c * (|g z| + 1) :=
          mul_le_mul ht.2 hg1 (abs_nonneg _) hc.le
        linarith
      linarith
    have h := add_le_add hhi (EReal.coe_le_coe_iff.mpr hreal)
    rw [← EReal.coe_add] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  have hdata := isLegendreMAData_inverseLegendre hc hpshv hconcv hbddv hupv
  set u := inverseLegendre vt 0 c with hudef
  have hpartial : ∀ t ∈ Ioo 0 c, ∀ z ∈ Ω', partialLegendre u t z = vt t z :=
    fun t ht z hz => partialLegendre_inverseLegendre_eq hconcv hbddv ht hz
  -- the measures on `Z` in the chart
  have hZ : ∀ t (ht : t ∈ Icc 0 c) (B : Set (ComplexModel m)), MeasurableSet B →
      B ⊆ Ω' → excZMeasure F E θ c W hW1 t (eZ.val.symm '' B) =
        MongeAmpere.truncationLimitMeasure Ω' (vt t) (hpshv t ht) B := by
    intro t ht B hB hBΩ
    rw [excZMeasure, dif_pos ht]
    exact (globalMixedMeasure_image_eq
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι (hW1 t ht)) Ω' eZ.val.symm
      (eZ.val.symm.injOn.mono (by
        rw [OpenPartialHomeomorph.symm_source]; exact hΩ'Ω.trans hch.subset_target)) (fun ζ => ρZ ζ - t * g ζ) (vt t)
      (hpshv t ht) (fun z hz => ⟨eZ, Ω', Ω'.isOpen, hz, subset_rfl,
        hΩ'Ω.trans hch.subset_target, fun _ _ => rfl, (hpott t).mono Ω'.isOpen hΩ'Ω,
        fun _ _ => rfl⟩) (Or.inr fun z hz => by
          obtain ⟨C, hC⟩ := hbddv t ht z hz
          exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hC.self_of_nhds.1) hB hBΩ).2
  -- the coordinate image of `C`
  set B : Set (ComplexModel m) := eZ.val '' C with hBdef
  have hBm : MeasurableSet B := by
    rw [hBdef, eZ.val.image_eq_target_inter_inv_preimage hCs]
    exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      eZ.val.open_target.measurableSet eZ.val.continuousOn_symm hCm
  have hBΩ' : B ⊆ Ω' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(hCΩ y hy).1, ?_⟩
    show firstFlagInclusion F (eZ.val.symm (eZ.val y)) ∈ badᶜ
    rw [eZ.val.left_inv (hCs hy)]
    exact (hCΩ y hy).2
  have hBC : eZ.val.symm '' B = C := eZ.val.symm_image_image_of_subset_source hCs
  -- the parameters in `(0, c)` have full measure
  have hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) c)), t ∈ Ioo 0 c := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hRHS : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) c)),
      MongeAmpere.truncationLimitMeasure Ω' (partialLegendre u t)
        (hdata.plurisubharmonicOn_partialLegendre t) B = excZMeasure F E θ c W hW1 t C := by
    filter_upwards [hae] with t ht
    have htI : t ∈ Icc 0 c := Ioo_subset_Icc_self ht
    rw [truncationLimitMeasure_congr _ (hpshv t htI) (fun z hz => hpartial t ht z hz),
      ← hZ t htI B hBm hBΩ', hBC]
  refine ⟨?_, (legendreMAMeasurable Ω' u 0 c ∅ hdata hdata.plurisubharmonicOn_partialLegendre
    B hBm).congr hRHS⟩
  -- the exceptional side
  rcases C.eq_empty_or_nonempty with hC0 | ⟨y₀, hy₀⟩
  · subst hC0
    simp [excZMeasure]
  have hp₀ : Λ (eZ.val y₀) 1 ∈ (exceptionalSet F μ) := hch.mem _ (hCΩ y₀ hy₀).1 1
  set Λh : ComplexModel (m + 1) → (exceptionalSet F μ) := fun v =>
    if h : bundleMap Λ v ∈ (exceptionalSet F μ) then ⟨bundleMap Λ v, h⟩ else ⟨_, hp₀⟩ with hΛhdef
  have hΛh : ∀ v, (stripModelEquiv m v).1 ∈ Ω → ((Λh v : (exceptionalSet F μ)) : 𝒳) = bundleMap Λ v := by
    intro v hv
    simp only [hΛhdef]
    split_ifs with h
    · rfl
    · exact absurd (hch.mem _ hv _) h
  set O := puncturedProductOpens Ω' with hOdef
  have hmemO : ∀ v, v ∈ O ↔ (stripModelEquiv m v).1 ∈ Ω' ∧ (stripModelEquiv m v).2 ≠ 0 :=
    fun v => Iff.rfl
  set ρB : ComplexModel (m + 1) → ℝ := fun v =>
    ρZ (stripModelEquiv m v).1 - c * Real.log (strictWeight F E μ (bundleMap Λ v)) with hρBdef
  have hu' := hdata.plurisubharmonicOn_productModelFunction
  -- the corrected potential in bundle coordinates is the inverse Legendre transform
  have hformO : ∀ v ∈ O, φ (Λh v) + (ρB v : EReal) = productModelFunction u v := by
    intro v hv
    obtain ⟨hvΩ', hw0⟩ := (hmemO v).mp hv
    have hvΩ : (stripModelEquiv m v).1 ∈ Ω := hvΩ'.1
    set ζ := (stripModelEquiv m v).1 with hζ
    set w := (stripModelEquiv m v).2 with hw
    obtain ⟨hS1, hS2, hL⟩ := hch.weights ζ hvΩ w hw0
    have hp : Λ ζ w ∈ (exceptionalSet F μ) := hch.mem ζ hvΩ w
    have hxp : (μ (Λ ζ w)).1 = xZ ζ := hch.proj ζ hvΩ w
    have hxbad : xZ ζ ∉ bad := hvΩ'.2
    have hφp := hformula (Λ ζ w) hp hS1 hS2 (fun h => hxbad (Or.inl (hxp ▸ h)))
      (fun h => hxbad (Or.inr (hxp ▸ h)))
    rw [hΛh v hvΩ]
    change φ (Λ ζ w) + (ρB v : EReal) = inverseLegendre vt 0 c ζ w
    rw [hφp, iSup₂_add_coe, inverseLegendre]
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    rw [hxp, hvdef]
    simp only
    rw [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
    congr 2
    simp only [hρBdef, bundleMap]
    rw [← hζ, ← hw]
    linear_combination t * hL
  have hinj : InjOn Λh O := by
    intro v hv v' hv' hvv
    obtain ⟨hvΩ', hw0⟩ := (hmemO v).mp hv
    obtain ⟨hvΩ'', hw0'⟩ := (hmemO v').mp hv'
    have h1 : bundleMap Λ v = bundleMap Λ v' := by
      rw [← hΛh v hvΩ'.1, ← hΛh v' hvΩ''.1, hvv]
    have h2 : xZ (stripModelEquiv m v).1 = xZ (stripModelEquiv m v').1 := by
      have := congrArg (fun z => (μ z).1) h1
      simp only [bundleMap] at this
      rwa [hch.proj _ hvΩ'.1, hch.proj _ hvΩ''.1] at this
    have h3 : (stripModelEquiv m v).1 = (stripModelEquiv m v').1 :=
      eZ.val.symm.injOn (hch.subset_target hvΩ'.1) (hch.subset_target hvΩ''.1)
        (Subtype.val_injective h2)
    have h4 : (stripModelEquiv m v).2 = (stripModelEquiv m v').2 := by
      refine hch.inj _ hvΩ'.1 _ _ ?_
      have := h1
      simp only [bundleMap] at this
      rw [h3] at this ⊢
      exact this
    exact (stripModelEquiv m).injective (Prod.ext h3 h4)
  have hj0 : ∀ y : (exceptionalSet F μ), (μ (y : 𝒳)).2 = projectiveZero := fun y =>
    ((mem_deformationCentre_iff F).mp y.2).2
  have hloc : ∀ v ∈ O, ∃ (e : ComplexChart (m + 1) (exceptionalSet F μ)) (G : Set (ComplexModel (m + 1))),
      IsOpen G ∧ v ∈ G ∧ G ⊆ O ∧ G ⊆ e.val.target ∧ (∀ z ∈ G, e.val.symm z = Λh z) ∧
      IsSmoothLocalPotential (ClosedRealOneOneForm.pullback
        (contMDiff_exceptionalInclusion F hμ) (deformationForm F hμ.contMDiff θ b c Eℰ)).val e G ρB ∧
      ∀ z ∈ G, φ (Λh z) + (ρB z : EReal) = productModelFunction u z := by
    intro v hv
    obtain ⟨hvΩ', hw0⟩ := (hmemO v).mp hv
    have hvΩ : (stripModelEquiv m v).1 ∈ Ω := hvΩ'.1
    obtain ⟨Ech, D, hD, hvD, hDt, hDΛ⟩ := hch.chart v hvΩ hw0
    set y := Ech.val.symm v with hydef
    have hy : y ∈ Ech.val.source := Ech.val.map_target (hDt hvD)
    have hyv : (y : 𝒳) = bundleMap Λ v := (hDΛ v hvD).2
    have hS : 0 < strictWeight F E μ (y : 𝒳) := by
      rw [hyv]; exact (hch.weights _ hvΩ _ hw0).1
    have hyx : (μ (y : 𝒳)).1 = xZ (stripModelEquiv m v).1 := by
      rw [hyv]; exact hch.proj _ hvΩ _
    have hΩX' := hΩX hvΩ
    have hyX : (μ (y : 𝒳)).1 ∈ dX.val.source := by rw [hyx]; exact hΩX'.1.2
    have hyW : dX.val (μ (y : 𝒳)).1 ∈ WX := by rw [hyx]; exact hΩX'.2
    obtain ⟨D', hvD', hpotB⟩ := isSmoothLocalPotential_pullback_deformationForm F hμ hE hEℰ θ b c
      (contMDiff_exceptionalInclusion F hμ) hj0 Ech hy hS dX hρX hyX hyW
    rw [hydef, Ech.val.right_inv (hDt hvD)] at hvD'
    set G := D ∩ D' ∩ (O : Set (ComplexModel (m + 1))) with hGdef
    have hGo : IsOpen G := (hD.inter hpotB.1).inter O.isOpen
    refine ⟨Ech, G, hGo, ⟨⟨hvD, hvD'⟩, hv⟩, inter_subset_right, fun z hz => hDt hz.1.1,
      fun z hz => ?_, ?_, fun z hz => hformO z hz.2⟩
    · apply Subtype.ext
      rw [(hDΛ z hz.1.1).2, hΛh z (hDΛ z hz.1.1).1]
    · refine IsSmoothLocalPotential.of_eqOn_sub_const (K := 0)
        (hpotB.mono hGo fun z hz => hz.1.2) fun z hz => ?_
      have hzΩ := (hDΛ z hz.1.1).1
      simp only [hρBdef, sub_zero]
      rw [(hDΛ z hz.1.1).2]
      simp only [bundleMap]
      rw [hch.proj _ hzΩ]
  set S : Set (ComplexModel (m + 1)) := stripModelEquiv m ⁻¹' (B ×ˢ puncturedPlane) with hSdef
  have hSm : MeasurableSet S :=
    (stripModelEquiv m).continuous.measurable (hBm.prod isOpen_puncturedPlane.measurableSet)
  have hSO : S ⊆ O := fun v hv => ⟨hBΩ' hv.1, hv.2⟩
  obtain ⟨-, hA⟩ := globalMixedMeasure_image_eq hφ O Λh hinj ρB
    (productModelFunction u) hu' hloc (Or.inl (Nat.succ_pos m)) hSm hSO
  have himg : Λh '' S = {p : (exceptionalSet F μ) | 0 < strictWeight F E μ p ∧ 0 < zStrictWeight F E μ p ∧
      (μ p).1 ∈ firstFlagInclusion F '' C} := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨⟨y, hyC, hyζ⟩, hw0⟩ := hv
      have hvΩ : (stripModelEquiv m v).1 ∈ Ω := hyζ ▸ (hCΩ y hyC).1
      obtain ⟨hS1, hS2, -⟩ := hch.weights _ hvΩ _ hw0
      have hval := hΛh v hvΩ
      simp only [mem_ofPred_eq, hval]
      refine ⟨hS1, hS2, y, hyC, ?_⟩
      rw [bundleMap, hch.proj _ hvΩ, ← hyζ, eZ.val.left_inv (hCs hyC)]
    · rintro ⟨h1, h2, y, hyC, hy⟩
      have hζ := (hCΩ y hyC).1
      obtain ⟨w, hw0, hwp⟩ := hch.cover p p.2 h1 h2 (eZ.val y) hζ
        (by rw [eZ.val.left_inv (hCs hyC)]; exact hy.symm)
      refine ⟨(stripModelEquiv m).symm (eZ.val y, w), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · simp only [ContinuousLinearEquiv.apply_symm_apply]
          exact ⟨y, hyC, rfl⟩
        · show (stripModelEquiv m ((stripModelEquiv m).symm (eZ.val y, w))).2 ≠ 0
          simpa using hw0
      · apply Subtype.ext
        rw [hΛh _ (by simpa using hζ), bundleMap]
        simpa using hwp
  rw [← himg, hA, hdata.mongeAmpere_eq' hBm]
  congr 1
  exact lintegral_congr_ae hRHS

end Chart

end SGPT.Okounkov.TranscendentalWN
