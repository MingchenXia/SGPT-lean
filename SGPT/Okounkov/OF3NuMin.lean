import SGPT.Okounkov.OF3SiuSections
import SGPT.NAPotential.BJPrepLelongConvex
import SGPT.Trace.BertiniGeneralTrace
import SGPT.IGood.DXMainStatement
import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Projective.OkounkovOriginalIdealProducts
import SGPT.Okounkov.AlgPOBComparison
import SGPT.Okounkov.MultiplierCancellation
import SGPT.Okounkov.TranscendentalCoreAlgebra

/-!
# `cor:numin` for every prime divisor over `X`

Source: chapter *The theory of Okounkov bodies*, `cor:numin`: *let `E` be a prime divisor over
`X`; then `ν(V_θ, E) = lim_{k → ∞} k⁻¹ ord_E H⁰(X, L^k)`.*

Setting: `X` an integral smooth projective complex scheme of dimension `m + 1`, `L` a big line
bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, `V_θ` the potential with minimal
singularities (`thetaPshSupremum`); a prime divisor over `X` is a
`SGPT.PSH.CompactPrimeOver.PrimePresentation` of `X(ℂ)` (source `def:primdiv`: a connected
smooth hypersurface `E` of a resolution `π : Y → X(ℂ)`), `ν(V_θ, E) = ν(π^* V_θ, E)` its generic
Lelong number (`presentationReader`) and `ord_E H⁰(X, L^k) = min_{s ≠ 0} ord_E(π^* s)`
(`sectionSpaceDivisorOrder`, `+∞` when `H⁰(X, L^k) = 0`).

## Proof

The book deduces the corollary from `thm:nuOk` after realizing `E` on a modification. We argue
directly with multiplier ideals, which avoids flags and modifications altogether:

* `≥`: every section of `L^k` lies in `H⁰(X, L^k ⊗ 𝓘(k V_θ))` (`eq:H0eqH0IVtheta`), so
  `ord_E H⁰(X, L^k) ≥ ord_E 𝓘(k V_θ)`, and `k⁻¹ ord_E 𝓘(k V_θ) → ν(V_θ, E)`
  (`prop:Lelongnumfrommis`).
* `≤`: take a Kähler current `θ_s`, `s ≤ P = P_θ[V_θ]_𝓘` (`lma:kahcurrentposmass`; `vol L > 0`)
  and `χ_t = t s + (1 - t) P`, a Kähler current. By Siu's uniform global generation and GAGA
  (`exists_section_sectionDivisorOrder_le`), `ord_E H⁰(X, L^k) ≤ ord_E 𝓘(k χ_t)` for `k ≫ 0`, and
  `k⁻¹ ord_E 𝓘(k χ_t) → ν(χ_t, E) ≤ t ν(s, E) + (1 - t) ν(P, E)`, with `ν(P, E) = ν(V_θ, E)`
  (`P ∼_𝓘 V_θ`). Let `t → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF3

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov SGPT.PSH.VariableComplexAtlas
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder SGPT.PSH.CompactPrimeMultiplierLimit
open scoped Topology ENNReal

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of3NuMinTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of3NuMinCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of3NuMinManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance of3NuMinMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance of3NuMinBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- **`ord_E H⁰(X, L^k)`**: the minimal order of vanishing along `E` of a nonzero section of
`L^k` (`⊤` if `H⁰(X, L^k) = 0`). -/
def sectionSpaceDivisorOrder (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    (L : X.Modules) (k : ℕ) : ℕ∞ :=
  ⨅ (s : bundlePowerGlobalSections L k) (_ : s ≠ 0), sectionDivisorOrder f E p s

omit [IsIntegral X] in
/-- `ord_E 𝓘(kφ)/k → ν(φ, E)` in `ℝ` (`prop:Lelongnumfrommis`), for finite `ν(φ, E)`. -/
theorem tendsto_presentationMultiplierOrder_div_toReal {u : SchemeComplexPoint f → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) (htop : presentationReader u p ≠ ⊤) :
    Tendsto (fun k : ℕ =>
      (presentationMultiplierOrder hu (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity) p : ℝ) /
        ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (presentationReader u p).toReal) := by
  have h := (ENNReal.tendsto_toReal htop).comp (tendsto_presentationMultiplierOrder_ratio hu p)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, ENNReal.toReal_div, ENNReal.toReal_natCast]

omit [IsIntegral X] in
/-- `𝓘`-equivalent potentials have the same orders `ord_E 𝓘(cφ)`. -/
theorem presentationMultiplierOrder_eq_of_iEquivalent {u w : SchemeComplexPoint f → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hw : IsGlobalQuasiPshPotential (n := m + 1) w)
    (huw : IEquivalentOnManifold (n := m + 1) u w) {c : ℝ} (hc : 0 < c)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) :
    presentationMultiplierOrder hu hc p = presentationMultiplierOrder hw hc p := by
  have hE := isClosedConnectedSubmanifold_divisor p
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have h1 := multiplierIdeal_le_of_iOrderOnManifold huw.1 hc
  have h2 := multiplierIdeal_le_of_iOrderOnManifold huw.2 hc
  have hI : multiplierIdeal (n := m + 1) c u = multiplierIdeal (n := m + 1) c w := by
    apply GermIdeal.ext
    funext x g
    exact propext ⟨h1 x g, h2 x g⟩
  have e1 := presentationMultiplierOrder_eq_originalStalkNormalOrder hu hc p hy Φ
  have e2 := presentationMultiplierOrder_eq_originalStalkNormalOrder hw hc p hy Φ
  rw [hI] at e1
  exact_mod_cast e1.trans e2.symm

omit [IsIntegral X] in
/-- `ν(φ, E) < ∞` for `θ`-psh `φ`. -/
theorem presentationReader_ne_top_of_isThetaPshPotential {θ : ClosedRealOneOneForm (m + 1)
    (SchemeComplexPoint f)} {u : SchemeComplexPoint f → EReal}
    [CompactSpace (SchemeComplexPoint f)] (hu : IsThetaPshPotential θ.val u)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) : presentationReader u p ≠ ⊤ := by
  have hA : (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH (nativeClosedFormToAtlas θ) u :=
    (isThetaPSH_iff_nativeThetaPotential _ u).mpr hu
  exact SGPT.NAPotential.BJPrep.presentationReader_ne_top hA p

omit [IsIntegral X] in
/-- Convexity: `ν(t s + (1 - t) P, E) ≤ t ν(s, E) + (1 - t) ν(P, E)`. -/
theorem presentationReader_convexComb_le' {θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)}
    {u w : SchemeComplexPoint f → EReal} (hu : IsThetaPshPotential θ.val u)
    (hw : IsThetaPshPotential θ.val w) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) :
    presentationReader (convexComb t u w) p ≤
      ENNReal.ofReal t * presentationReader u p + ENNReal.ofReal (1 - t) * presentationReader w p :=
  SGPT.NAPotential.BJPrep.presentationReader_convexComb_le (θ := nativeClosedFormToAtlas θ)
    ((isThetaPSH_iff_nativeThetaPotential _ u).mpr hu)
    ((isThetaPSH_iff_nativeThetaPotential _ w).mpr hw) ht0 ht1 p

variable [Nonempty (SchemeComplexPoint f)]

/-- **Source `cor:numin`, eq:nuVthetaE, for every prime divisor `E` over `X`**: for a big line bundle
`L`, `k⁻¹ ord_E H⁰(X, L^k) → ν(V_θ, E)`. -/
theorem tendsto_sectionSpaceDivisorOrder_div
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hL : SGPT.LineBundle.IsBig f L (m + 1)) :
    Tendsto (fun k : ℕ => ((sectionSpaceDivisorOrder f E p L k).toNat : ℝ) / k) atTop
      (𝓝 (presentationReader (thetaPshSupremum (H.curvature a).val) p).toReal) := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  set θ := H.curvature a with hθ
  set V := thetaPshSupremum θ.val with hVdef
  have hV : IsThetaPshPotential θ.val V := AlgPOB.isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hL
  have hqV : IsGlobalQuasiPshPotential (n := m + 1) V := ⟨hV.1.quasiPlurisubharmonic, hV.2⟩
  set R := presentationReader V p with hRdef
  have hRtop : R ≠ ⊤ := presentationReader_ne_top_of_isThetaPshPotential f hV p
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  -- the `𝓘`-envelope `P` of `V_θ` and a Kähler current `s ≤ P`
  obtain ⟨Y, hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m + 1) E
  have hvol := SGPT.IGood.DXMain.volume_le_iVolume_thetaPshSupremum f E a H Y hY hV
  have hiV : 0 < iVolume θ hlocal V hV := hL.volume_pos.trans_le hvol
  set P := iSingularityEnvelope θ.val V with hPdef
  have hP : IsThetaPshPotential θ.val P :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2 hlocal V hV
  have hqP : IsGlobalQuasiPshPotential (n := m + 1) P := ⟨hP.1.quasiPlurisubharmonic, hP.2⟩
  have hequiv := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2 hlocal V hV
  have hmass : DiagonalMass.HasPositivePotentialMass θ P hP := hiV
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  obtain ⟨δ, hδ, s, hs, -⟩ := SGPT.Trace.BertiniGeneral.exists_kahlerCurrent_le (Nat.succ_pos m)
    ω hP hmass
  have hsθ : IsThetaPshPotential θ.val s := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hs
      (KahlerDomination.isSemipositive_smul ω.isSemipositive hδ.le)
    rwa [sub_add_cancel] at h
  have hRP : presentationReader P p = R := by
    refine tendsto_nhds_unique (tendsto_presentationMultiplierOrder_ratio hqP p) ?_
    refine (tendsto_presentationMultiplierOrder_ratio hqV p).congr fun k => ?_
    rw [presentationMultiplierOrder_eq_of_iEquivalent f hqV hqP hequiv]
  have hStop : presentationReader s p ≠ ⊤ := presentationReader_ne_top_of_isThetaPshPotential f hsθ p
  set S := (presentationReader s p).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  -- the Kähler currents `χ_t = t s + (1 - t) P`
  have hχ : ∀ t : ℝ, 0 < t → t < 1 →
      IsThetaPshPotential (θ - (t * δ) • ω.form).val (convexComb t s P) := by
    intro t ht0 ht1
    have h1 := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul hs ht0.le
    have h2 := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul hP
      (sub_nonneg.mpr ht1.le)
    have h3 := SGPT.Okounkov.isThetaPshPotential_add_from_positive_sum h1 h2
    have hform : t • (θ - δ • ω.form) + (1 - t) • θ = θ - (t * δ) • ω.form := by module
    rw [hform] at h3
    exact h3
  have hχθ : ∀ t : ℝ, 0 < t → t < 1 → IsThetaPshPotential θ.val (convexComb t s P) := by
    intro t ht0 ht1
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hχ t ht0 ht1)
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (mul_pos ht0 hδ).le)
    rwa [sub_add_cancel] at h
  -- lower bound: every nonzero section lies in `𝓘(k V_θ)`
  have hlow : ∀ (k : ℕ) (hk : (0 : ℝ) < k),
      (presentationMultiplierOrder hqV hk p : ℕ∞) ≤ sectionSpaceDivisorOrder f E p L k := by
    intro k hk
    refine le_iInf fun σ => le_iInf fun hσ => ?_
    have hm := SGPT.IGood.isMultiplierSection_thetaPshSupremum (f := f) (n := m + 1) (E := E) H a
      k σ hσ
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    have hI := hm.resolve_left hk0
    have hplain := OriginalIdealProducts.isPlainMultiplierIdealSection_of_isIdealSection f (m + 1) E
      a V k σ hI
    exact presentationMultiplierOrder_le_sectionDivisorOrder f E hqV hk p hplain
  -- upper bound: Siu's sections of `L^k ⊗ 𝓘(k χ_t)`
  have hup : ∀ (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (hk : (0 : ℝ) < k),
      sectionSpaceDivisorOrder f E p L k ≤
        presentationMultiplierOrder (⟨(hχθ t ht0 ht1).1.quasiPlurisubharmonic, (hχθ t ht0 ht1).2⟩ :
          IsGlobalQuasiPshPotential (n := m + 1) (convexComb t s P)) hk p := by
    intro t ht0 ht1
    obtain ⟨k₀, hk₀⟩ := exists_section_sectionDivisorOrder_le f E a H ω (mul_pos ht0 hδ)
    refine ⟨k₀, fun k hk hkR => ?_⟩
    obtain ⟨σ, hσ0, -, hσ⟩ := hk₀ k hk _ (hχ t ht0 ht1) _ hkR p
    exact (iInf_le_of_le σ (iInf_le_of_le hσ0 le_rfl)).trans hσ
  -- the real sequence and the limit
  set u : ℕ → ℝ := fun k => ((sectionSpaceDivisorOrder f E p L k).toNat : ℝ) / k with hudef
  suffices hshift : Tendsto (fun k : ℕ => u (k + 1)) atTop (𝓝 R.toReal) from
    (tendsto_add_atTop_iff_nat 1).mp hshift
  -- squeeze between the two multiplier sequences, for `k ≥ k₀(t)`
  have hsq : ∀ t : ℝ, ∀ (ht0 : 0 < t) (ht1 : t < 1), ∀ᶠ k : ℕ in atTop,
      (presentationMultiplierOrder hqV (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity) p : ℝ) /
          ((k + 1 : ℕ) : ℝ) ≤ u (k + 1) ∧
        u (k + 1) ≤ (presentationMultiplierOrder
          (⟨(hχθ t ht0 ht1).1.quasiPlurisubharmonic, (hχθ t ht0 ht1).2⟩ :
            IsGlobalQuasiPshPotential (n := m + 1) (convexComb t s P))
          (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity) p : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    intro t ht0 ht1
    obtain ⟨k₀, hk₀⟩ := hup t ht0 ht1
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hkR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hl := hlow (k + 1) hkR
    have hu' := hk₀ (k + 1) (hk.trans (Nat.le_succ k)) hkR
    have hfin : sectionSpaceDivisorOrder f E p L (k + 1) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) hu'
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hN] at hl hu'
    have hl' := ENat.natCast_le_natCast.mp hl
    have hu'' := ENat.natCast_le_natCast.mp hu'
    have huN : u (k + 1) = (N : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      simp only [hudef, ← hN, ENat.toNat_natCast]
    rw [huN]
    constructor
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hl') hkR.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hu'') hkR.le
  rw [tendsto_order]
  constructor
  · intro b hb
    have hV' := tendsto_presentationMultiplierOrder_div_toReal f hqV p hRtop
    filter_upwards [hV'.eventually (lt_mem_nhds hb), hsq (1 / 2) (by norm_num) (by norm_num)]
      with k h1 h2
    exact h1.trans_le h2.1
  · intro b hb
    -- choose `t` with `t S < b - ν(V_θ, E)`
    set t : ℝ := min (1 / 2) ((b - R.toReal) / (2 * (S + 1))) with htdef
    have hbR : 0 < b - R.toReal := sub_pos.mpr hb
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have htS : t * S < b - R.toReal := by
      have h1 : t ≤ (b - R.toReal) / (2 * (S + 1)) := min_le_right _ _
      have h2 : t * S ≤ (b - R.toReal) / (2 * (S + 1)) * S :=
        mul_le_mul_of_nonneg_right h1 hS0
      have h3 : (b - R.toReal) / (2 * (S + 1)) * S < b - R.toReal := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have hχp : IsGlobalQuasiPshPotential (n := m + 1) (convexComb t s P) :=
      ⟨(hχθ t ht0 ht1).1.quasiPlurisubharmonic, (hχθ t ht0 ht1).2⟩
    have hconv := presentationReader_convexComb_le' f hsθ hP ht0 ht1 p
    rw [hRP] at hconv
    have hχtop : presentationReader (convexComb t s P) p ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStop,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop⟩) hconv
    have hχle : (presentationReader (convexComb t s P) p).toReal ≤ t * S + (1 - t) * R.toReal := by
      have h := (ENNReal.toReal_le_toReal hχtop (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStop,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop⟩)).mpr hconv
      rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStop)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal ht0.le, ENNReal.toReal_ofReal (by linarith)] at h
    have hRnn : 0 ≤ R.toReal := ENNReal.toReal_nonneg
    have hlt : (presentationReader (convexComb t s P) p).toReal < b := by
      nlinarith [mul_nonneg ht0.le hRnn]
    have hχ' := tendsto_presentationMultiplierOrder_div_toReal f hχp p hχtop
    filter_upwards [hχ'.eventually (gt_mem_nhds hlt), hsq t ht0 ht1] with k h1 h2
    exact h2.2.trans_lt h1

end SGPT.Okounkov.OF3
