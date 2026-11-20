import SGPT.Okounkov.OF7GermOrder
import SGPT.Okounkov.OF7PointJets
import SGPT.Okounkov.OF5NuOk
import SGPT.Okounkov.OF3FlagFirstCoordinate

/-!
# `thm:nuOk`: `ν(φ, E) = min_{x ∈ E} ν(φ, x)` is the first-coordinate minimum

Source: chapter *The theory of Okounkov bodies*, subsection *Recover Lelong numbers from partial
Okounkov bodies*, `thm:nuOk`:

*Let `E` be a prime divisor on `X`. Let `Y•` be an admissible flag with `E = Y₁`. Then
`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`.*

Here `E` is a prime divisor on the smooth projective `X`, so `E(ℂ)` is an irreducible analytic
subset and `ν(φ, E) = min_{x ∈ E(ℂ)} ν(φ, x)` is its generic Lelong number
(`def:pshfunctions:L1101`). Lane OF5 proved the formula with `ν(φ, E)` read on a prime divisor
`Ẽ` over `X(ℂ)` (the strict transform of the analytic branch `W` of `E(ℂ)` through a smooth point
of `E`): `ν(φ, Ẽ) = min_{x ∈ W} ν(φ, x) = min_{x ∈ Δ} x₁`. We prove that this number is the
minimum over the **whole** of `E(ℂ)`, without proving that `E(ℂ)` is analytically irreducible:

* `presentationReader_le_squaredLog`: `ν(φ, Ẽ) ≤ ν(φ, x)` for **every** `x ∈ E(ℂ)`. Proof: after
  twisting `L` by `𝒪(1)` (Fubini–Study), `θ_φ` is a Kähler current. For `k ≫ 0`, Demailly's
  inequality at `x` (`exists_multiplier_member_not_mem_pow`) gives `F ∈ 𝓘(kφ)_x` of multiplicity
  `a ≤ k ν(φ, x)` at `x`; by Siu's uniform global generation and GAGA some algebraic section
  `σ ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` has multiplicity `≤ a` at `x`; the algebraic inequality
  `ord_E(σ) ≤ mult_x(σ)` (`stalkToModel_mem_maximalIdeal_pow_of_le_ord`, valid at every point of
  `E`, singular or not) and `ord_E 𝓘(kφ) ≤ ord_E(σ)` (orders read on `Ẽ` at a point where `Ẽ`
  realizes `ord_E`) give `ord_E 𝓘(kφ) ≤ k ν(φ, x)`; finally `k⁻¹ ord_E 𝓘(kφ) → ν(φ, Ẽ)`
  (`prop:Lelongnumfrommis`).
* `isLeast_firstCoordinate_admissibleFlag_iInf` (**`thm:nuOk`**): for every admissible flag
  `Y•` with `E = Y₁` and every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
  `min_{x ∈ E(ℂ)} ν(φ, x) = ν(φ, Ẽ) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`.

Lelong numbers: `squaredLogLelongNumber` is the book's normalization; TN's `lelongNumber` is
twice it.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF7

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MeasureTheory IsLocalRing
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.NAPotential.FSPos
open SGPT.NAPotential.TowerAlg
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder
open SGPT.PSH.CompactPrimeMultiplierLimit
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.NAPotential.GAGAMult SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov.OF3 SGPT.Okounkov.OF5 SquaredLogLelongSourceNormalization

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of7NuOkTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of7NuOkCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of7NuOkManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance of7NuOkMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance of7NuOkBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [IsIntegral X] in
/-- The analytic germ at `x` of the frame coefficient of an algebraic section is the analytic
germ (`stalkToModel`) of its algebraic germ. -/
theorem chartTranslatedGerm_sectionFrameCoefficient {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (s : bundlePowerGlobalSections L k)
    {x : SchemeComplexPoint f} (hx : schemeComplexPointImage f x ∈ U)
    (hh : HolomorphicAt (m + 1) (sectionFrameCoefficient f (m + 1) E α k s) x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (sectionFrameCoefficient f (m + 1) E α k s) hh =
      stalkToModel f (m + 1) x (X.presheaf.germ U (schemeComplexPointImage f x) hx
        ((α.tensorPower k).coefficients (𝟙 U)
          ((bundleTensorPower L k).val.map (homOfLE le_top).op s))) := by
  change _ = NativeHolGerm.chartEquiv x (schemeNativeStalkGerm f (m + 1) x _)
  rw [← schemeOpenRegularFunction_germ f (m + 1) E U _ x hx, OF3.chartEquiv_mk_eq]
  rfl

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`ord_E 𝓘(kφ) ≤ k ν(φ, x)` at every point `x ∈ E(ℂ)`, Kähler currents.** Let `θ_φ` be a
Kähler current, `z` a point of codimension one (`E = {z}‾`) and `p` a prime divisor over `X(ℂ)`
realizing `ord_E` (`RealizesOrder`). For every complex point `x` of `E` and all `k ≫ 0`,
`2 ord_E 𝓘(kφ) ≤ k ν(φ, x)` (TN normalization of `ν`). -/
theorem two_mul_presentationMultiplierOrder_le_of_kahler [IsLocallyNoetherian X]
    {φ : SchemeComplexPoint f → EReal} (hφ : IsKahlerCurrentPotential (H.curvature a) φ)
    (hq : IsGlobalQuasiPshPotential (n := m + 1) φ) {z : X} (hz : Order.coheight z = 1)
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hp : RealizesOrder f E p z)
    {x : SchemeComplexPoint f} (hzx : z ⤳ schemeComplexPointImage f x) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ hk : (0 : ℝ) < k,
      (2 : ℝ≥0∞) * (presentationMultiplierOrder hq hk p : ℝ≥0∞) ≤
        ENNReal.ofReal (k : ℝ) * lelongNumber (n := m + 1) φ x := by
  classical
  let := E.isProper
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hφθ : IsThetaPshPotential (H.curvature a).val φ :=
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨ω', hω'⟩ := hφ
  have hφδ : IsThetaPshPotential (H.curvature a - (1 : ℝ) • ω'.form).val φ := by
    rwa [one_smul]
  let μ := IntegrationCurrent.kahlerVolume ω'
  have hμ : IsSmoothPositiveVolume (n := m + 1) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ω'
  obtain ⟨k₀, hk₀⟩ := siuGlobalGeneration_iff ω' hμ
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f (m + 1) E a H)
    SGPT.PSH.GlobalL2.isSourceSmoothHermitianMetric_unit
    (isOwnFirstChernForm_schemeHermitianLineBundle f (m + 1) E a H) one_pos
  refine ⟨k₀, fun k hk hkR => ?_⟩
  obtain ⟨y₀, hy₀, Φ₀, hzP₀, hord⟩ := hp
  by_cases hfin : lelongNumber (n := m + 1) φ x = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hkR).ne']
    exact le_top
  have hkN : 0 < k := by exact_mod_cast hkR
  -- Demailly at `x`: a member of `𝓘(kφ)_x` of multiplicity `A ≤ k ν(φ, x) / 2`
  obtain ⟨F, hF, A, hFmem, hFnot, hbound⟩ :=
    exists_multiplier_member_not_mem_pow hq.1 x k hkN hfin
  -- Siu: a section of `L^k ⊗ 𝓘(kφ)` of multiplicity `≤ A` at `x`
  set P := schemeComplexPointImage f x with hPdef
  obtain ⟨i, hi⟩ := a.covers P
  let e := twistedFrame f (m + 1) E a H (a.frame i) k
  have hxe : x ∈ e.val.baseSet := mem_twistedFrame_baseSet f (m + 1) E a H _ k hi
  have hspan := (hk₀ k hk φ hφδ x e hxe F).mp hFmem
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
    (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  have hsec : ∃ σ : bundlePowerGlobalSections L k, σ ≠ 0 ∧ IsMultiplierSection f (m + 1) E φ k σ ∧
      ∃ hh : HolomorphicAt (m + 1) (sectionFrameCoefficient f (m + 1) E (a.frame i) k σ) x,
        chartTranslatedGerm x x (mem_chart_source _ x)
          (sectionFrameCoefficient f (m + 1) E (a.frame i) k σ) hh ∉
            maximalIdeal (HolGerm (ComplexModel (m + 1))) ^ (A + 1) := by
    by_contra hcon
    push Not at hcon
    apply hFnot
    refine chartTranslatedGerm_mem_of_isInSpanAt hspan _ ?_
    rintro _ ⟨s, hs, rfl⟩
    set σ := SGPT.GAGA.H0L.algSection a H s with hσdef
    have hσ := SGPT.GAGA.H0L.isAnalytificationOf_algSection a H s
    have hcoef : (fun w => e.val.continuousLinearMapAt ℂ w (s w)) =ᶠ[𝓝 x]
        sectionFrameCoefficient f (m + 1) E (a.frame i) k σ := by
      filter_upwards [hO.mem_nhds hi] with w hw
      exact hσ i w hw
    have hhol : HolomorphicAt (m + 1) (sectionFrameCoefficient f (m + 1) E (a.frame i) k σ) x :=
      schemeOpenRegularFunction_holomorphicAt f (m + 1) E (a.opens i) _ _ hi
    refine ⟨hhol.congr hcoef.symm, ?_⟩
    rw [chartTranslatedGerm_congr x _ hhol hcoef]
    by_cases hσ0 : σ = 0
    · have h0 : sectionFrameCoefficient f (m + 1) E (a.frame i) k σ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hi] with w hw
        rw [hσ0]
        exact SGPT.IGood.sectionFrameCoefficient_zero (f := f) (n := m + 1) (E := E)
          (a.frame i) k hw
      have hc0 : HolomorphicAt (m + 1) (fun _ : SchemeComplexPoint f => (0 : ℂ)) x :=
        holomorphicAt_const 0
      have hz0 : chartTranslatedGerm x x (mem_chart_source _ x)
          (fun _ : SchemeComplexPoint f => (0 : ℂ)) hc0 = 0 := rfl
      rw [chartTranslatedGerm_congr x hhol hc0 h0, hz0]
      exact Ideal.zero_mem _
    · exact hcon σ hσ0 (SGPT.GAGA.H0L.isMultiplierSection_algSection a H hφθ hμ hs) hhol
  obtain ⟨σ, hσ0, hmult, hhx, hnot⟩ := hsec
  have hmultI := hmult.resolve_left hkN.ne'
  -- the algebraic coefficients of `σ` near `P` and near `P₀ = μ(y₀)`
  set P₀ := schemeComplexPointImage f (p.projection y₀) with hP₀def
  obtain ⟨i₀, hi₀⟩ := a.covers P₀
  have : Nonempty (a.opens i₀) := ⟨⟨P₀, hi₀⟩⟩
  have : Nonempty (a.opens i) := ⟨⟨P, hi⟩⟩
  set β₀ := (a.frame i₀).tensorPower k with hβ₀
  set β := (a.frame i).tensorPower k with hβ
  set r₀ := β₀.coefficients (𝟙 _) ((bundleTensorPower L k).val.map (homOfLE le_top).op σ)
    with hr₀
  set r := β.coefficients (𝟙 _) ((bundleTensorPower L k).val.map (homOfLE le_top).op σ)
    with hr
  have hzU₀ : z ∈ a.opens i₀ := hzP₀.mem_open (a.opens _).isOpen hi₀
  have hzU : z ∈ a.opens i := hzx.mem_open (a.opens _).isOpen hi
  have hgerm₀ : algebraMap (X.presheaf.stalk P₀) X.functionField
      (X.presheaf.germ (a.opens i₀) P₀ hi₀ r₀) = globalSectionToFunctionField β₀ σ :=
    X.algebraMap_germ_eq_germToFunctionField hi₀ r₀
  have hgerm : algebraMap (X.presheaf.stalk P) X.functionField
      (X.presheaf.germ (a.opens i) P hi r) = globalSectionToFunctionField β σ :=
    X.algebraMap_germ_eq_germToFunctionField hi r
  have hne : ∀ {U : X.Opens} [Nonempty U] (γ : LocalBundleFrame (bundleTensorPower L k) U),
      globalSectionToFunctionField γ σ ≠ 0 := fun γ h0 =>
    hσ0 (globalSectionToFunctionField_injective (a.tensorPower k) γ (by rw [h0, map_zero]))
  have hg₀ : X.presheaf.germ (a.opens i₀) P₀ hi₀ r₀ ≠ 0 := by
    intro h0
    apply hne β₀
    rw [← hgerm₀, h0, map_zero]
  have hg : X.presheaf.germ (a.opens i) P hi r ≠ 0 := by
    intro h0
    apply hne β
    rw [← hgerm, h0, map_zero]
  -- `ord_E 𝓘(kφ) ≤ ord_E(σ)`, read on `Ẽ` at `y₀`
  have hhol₀ : HolomorphicAt (m + 1) (sectionFrameCoefficient f (m + 1) E (a.frame i₀) k σ)
      (p.projection y₀) :=
    schemeOpenRegularFunction_holomorphicAt f (m + 1) E (a.opens i₀) _ _ hi₀
  have hmem₀ := hmultI (a.opens i₀) (a.frame i₀) (p.projection y₀) hi₀
  have hle₀ : (presentationMultiplierOrder hq hkR p : ℕ∞) ≤ pullbackNormalOrder p.modification Φ₀
      (sectionFrameCoefficient f (m + 1) E (a.frame i₀) k σ) hhol₀ := by
    rw [presentationMultiplierOrder_eq_originalStalkNormalOrder hq hkR p hy₀ Φ₀]
    exact originalStalkNormalOrder_le_functionNormalOrder Φ₀
      (mem_pullback_comp p.modification hmem₀ hhol₀) _
  have hst : stalkOrd p Φ₀ (X.presheaf.germ (a.opens i₀) P₀ hi₀ r₀) =
      pullbackNormalOrder p.modification Φ₀
        (sectionFrameCoefficient f (m + 1) E (a.frame i₀) k σ) hhol₀ :=
    stalkOrd_eq p Φ₀ _ _ (schemeOpenRegularFunction_germ f (m + 1) E (a.opens i₀) r₀ _ hi₀).symm
  have hordP₀ := hord _ hg₀
  rw [hgerm₀] at hordP₀
  have hsame := ord_globalSectionToFunctionField_frame (a.tensorPower k) β₀ β hzU₀ hzU hσ0
  -- `ord_E(σ) ≤ A`: otherwise the germ of `σ` at `x` would lie in `𝔪^{A+1}`
  have hordx : Scheme.ord (globalSectionToFunctionField β σ) z ≤ A := by
    by_contra hlt
    push Not at hlt
    have hb : ((A + 1 : ℕ) : ℤ) ≤ Scheme.ord (algebraMap (X.presheaf.stalk P) X.functionField
        (X.presheaf.germ (a.opens i) P hi r)) z := by
      rw [hgerm]
      push_cast
      omega
    apply hnot
    rw [chartTranslatedGerm_sectionFrameCoefficient f E (a.frame i) k σ hi hhx]
    exact stalkToModel_mem_maximalIdeal_pow_of_le_ord x hz hzx hg hb
  have hchain : (presentationMultiplierOrder hq hkR p : ℕ∞) ≤ (A : ℕ∞) := by
    refine hle₀.trans ?_
    rw [← hst, hordP₀, ← hsame]
    exact_mod_cast (Int.toNat_le.mpr hordx)
  have hA : presentationMultiplierOrder hq hkR p ≤ A := by exact_mod_cast hchain
  calc (2 : ℝ≥0∞) * (presentationMultiplierOrder hq hkR p : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞) * (A : ℝ≥0∞) := by gcongr
    _ = ENNReal.ofReal (2 * (A : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
    _ ≤ _ := hbound

/-- **`ν(φ, Ẽ) ≤ ν(φ, x)` at every point `x ∈ E(ℂ)`, Kähler currents.** -/
theorem presentationReader_le_squaredLog_of_kahler [IsLocallyNoetherian X]
    {φ : SchemeComplexPoint f → EReal} (hφ : IsKahlerCurrentPotential (H.curvature a) φ)
    {z : X} (hz : Order.coheight z = 1)
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hp : RealizesOrder f E p z)
    {x : SchemeComplexPoint f} (hzx : z ⤳ schemeComplexPointImage f x) :
    presentationReader φ p ≤ squaredLogLelongNumber (n := m + 1) φ x := by
  have hφθ : IsThetaPshPotential (H.curvature a).val φ :=
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφθ.1.quasiPlurisubharmonic, hφθ.2⟩
  obtain ⟨k₀, hk₀⟩ := two_mul_presentationMultiplierOrder_le_of_kahler f E a H hφ hq hz hp hzx
  have hR := tendsto_presentationMultiplierOrder_ratio hq p
  refine le_of_tendsto hR ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have h := hk₀ (k + 1) (hk.trans (Nat.le_succ k)) (by positivity)
  rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), ENNReal.ofReal_natCast,
    mul_left_comm] at h
  have h' := (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp h
  apply ENNReal.div_le_of_le_mul
  rwa [mul_comm] at h'

/-- **`ν(φ, Ẽ) ≤ ν(φ, x)` at every point `x ∈ E(ℂ)`.** For every `φ ∈ PSH(X, θ)`, every prime
divisor `E = {z}‾` of `X` and every prime divisor `Ẽ` over `X(ℂ)` realizing `ord_E`, the generic
Lelong number `ν(φ, Ẽ)` is at most the Lelong number of `φ` at every point of `E(ℂ)`. (The
twist by `𝒪(1)` makes `θ_φ` a Kähler current without changing `φ`.) -/
theorem presentationReader_le_squaredLog [IsLocallyNoetherian X] [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    {z : X} (hz : Order.coheight z = 1)
    {p : PrimePresentation (m + 1) (SchemeComplexPoint f)} (hp : RealizesOrder f E p z)
    {x : SchemeComplexPoint f} (hzx : z ⤳ schemeComplexPointImage f x) :
    presentationReader φ p ≤ squaredLogLelongNumber (n := m + 1) φ x := by
  obtain ⟨hKφ, -⟩ := OriginalBook.original_positivePerturbation_kahler_and_big f (m + 1) E a H
    (hyperplaneAtlas E) (fubiniStudyMetric f E (m + 1)) (fubiniStudy_curvature_isKahler f (m + 1) E)
    hφ 1 1 one_pos one_pos
  have hfun : (fun y => ((1 : ℕ) : EReal) * φ y) = φ := by
    funext y
    simp
  rw [hfun] at hKφ
  exact presentationReader_le_squaredLog_of_kahler f E _ _ hKφ hz hp hzx

/-- **Source `thm:nuOk`.** Let `Y•` be an admissible flag of `X` (`def:admfl`) and `E = Y₁` (a
prime divisor of `X`, possibly singular), with generic Lelong number
`ν(φ, E) = min_{x ∈ E(ℂ)} ν(φ, x)` (`def:pshfunctions:L1101`; `squaredLogLelongNumber`, the book's
normalization). Then for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`, where `Δ_{Y•}(θ, φ)` is the partial Okounkov body
(`def:Okounkov:L687`) of the valuation `ν_{Y•}` of the flag (`admissibleFlagValuation`).

Moreover `ν(φ, E)` is the generic Lelong number `ν(φ, Ẽ) = ν(π^*φ, Ẽ)` (`def:pshfunctions:L1112`)
of a prime divisor `Ẽ` over `X(ℂ)` (`def:primdiv`) with centre in `E(ℂ)` that realizes the order of
vanishing `ord_E` (`RealizesOrder`). -/
theorem isLeast_firstCoordinate_admissibleFlag_iInf [Nonempty (SchemeComplexPoint f)]
    {Y : Fin (m + 1 + 1) → Set X} (hY : IsAdmissibleFlag f (m + 1) Y)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    (hpos : haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    haveI : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ p : PrimePresentation (m + 1) (SchemeComplexPoint f),
      RealizesOrder f E p (memberPoint hY 1) ∧
      p.projection '' p.divisor ⊆ schemeNativeAlgebraicTrace f (Y 1) ∧
      presentationReader φ p =
        (⨅ x ∈ schemeNativeAlgebraicTrace f (Y 1), squaredLogLelongNumber (n := m + 1) φ x) ∧
      ∃ (hKc : IsCompact (centreOkounkovBody f (admissibleFlagValuation hY) a))
        (hKv : Convex ℝ (centreOkounkovBody f (admissibleFlagValuation hY) a)),
        IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
            ValGen.partialBody f (m + 1) E (admissibleFlagValuation hY)
              (valuationCenter f (admissibleFlagValuation hY)) a
              (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)
          (⨅ x ∈ schemeNativeAlgebraicTrace f (Y 1), squaredLogLelongNumber (n := m + 1) φ x).toReal := by
  let := E.isProper
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hz1 : Order.coheight (memberPoint hY 1) = 1 := by
    rw [coheight_memberPoint]
    simp
  obtain ⟨p, W, hWsub, -, himage, hreader, y₀, hy₀, Φ₀, hzP, hord⟩ :=
    exists_primePresentation_ord (m := m) E hz1
  have hY1 : closure {memberPoint hY 1} = Y 1 := by
    rw [hY.closure_genericPoint]
    rfl
  have hq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
  have hR := presentationReader_eq_iInf_of_lelong f p W.carrier φ (hreader φ hq)
  have hWY : W.carrier ⊆ schemeNativeAlgebraicTrace f (Y 1) := by
    rw [← hY1]
    exact hWsub
  have hreal : RealizesOrder f E p (memberPoint hY 1) := ⟨y₀, hy₀, Φ₀, hzP, hord⟩
  have heq : presentationReader φ p =
      ⨅ x ∈ schemeNativeAlgebraicTrace f (Y 1), squaredLogLelongNumber (n := m + 1) φ x := by
    apply le_antisymm
    · refine le_iInf₂ fun x hx => ?_
      have hzx : memberPoint hY 1 ⤳ schemeComplexPointImage f x := by
        rw [specializes_iff_mem_closure, hY1]
        exact hx
      exact presentationReader_le_squaredLog f E a H hφ hz1 hreal hzx
    · rw [hR]
      exact biInf_mono hWY
  have hfirst := isFirstCoordinateOrder_admissibleFlag E hY p hreal
  obtain ⟨hKc, hKv, hleast⟩ := isLeast_firstCoordinate_partialBody f E p a H
    (admissibleFlagValuation hY) (admissibleFlagValuation_surjective hY) hfirst hφ hpos
  refine ⟨p, hreal, ?_, heq, hKc, hKv, ?_⟩
  · rw [himage]
    exact hWY
  · rw [← heq]
    exact hleast

end SGPT.Okounkov.OF7
