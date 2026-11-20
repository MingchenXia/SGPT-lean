import SGPT.TestCurve.QwNAFlagFree
import SGPT.TestCurve.RWNObstacleIGood
import SGPT.IGood.DXMainTwisted
import SGPT.Foundations.Analysis.Pending.ProductTestForms

/-!
# `rmk:NApotential:L862` for an arbitrary smooth metric `h`


Source `rmk:NApotential:L862`: *when `{θ}` is a Hodge class and `Γ` is induced by a test
configuration, our Duistermaat–Heckman measure coincides with the more traditional definition of
[BHJ17, §3.2]*.  Lanes NA-NS, TC-ENC, FG-REL and QW-NA proved the convergence
`(n!/kⁿ) ν_k → DH(Γ^𝓕)` when `θ = c₁(L, h)` for a metric `h` of **Kähler curvature**; the Kähler
hypothesis enters only through the Skoda inclusion `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k`
(`SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal`), where `ψ_τ` is the obstacle of `ex:RWN`.

Here `θ = c₁(L, h)` for an **arbitrary** smooth metric `h`, and `{θ}` is a Hodge class: its
Bott–Chern class contains a Kähler form `ω`.  Then `ω = c₁(L, h₀)` for the smooth metric
`h₀ = h e^{ψ}`, `θ = ω + dd^c ψ` (`exists_kahler_metric_of_hodge`).  Writing
`h₀ = h e^{-g}` (`g = log(h/h₀)`, `SchemeLineBundleMetric.logRatio`, bounded on the compact
`X(ℂ)`), the section norms change by `|s|²_{h₀^k} = |s|²_{h^k} e^{-kg}`, hence the obstacles of
`ex:RWN` for `h` and `h₀` differ by a bounded function:
`ψ^h_τ ≤ ψ^{h₀}_τ + 2 sup|g|` (`obstacle_le_add`).  Multiplier ideals only see singularity types, so
the Skoda inclusion for `h₀` implies the one for `h` (`skodaInclusionIdeal_of_metric`), and the
whole chain of lanes NA-NS/TC-ENC/QW-NA runs for `h`:

* `rescaledJumpMeasure_tendsto_of_skoda`: for every filtration with the Skoda inclusion, on `X`
  with a smooth flag, `(n!/kⁿ) ν_k → DH(Γ^𝓕)` weakly (`DH` computed with `h`);
* `testConfiguration_rescaledJumpMeasure_tendsto_hodge`,
  `testConfiguration_normalized_tendsto_hodge`, and the variants with equivariant coordinates:
  **`rmk:NApotential:L862` with `θ = c₁(L, h)`, `h` any smooth metric, `{θ}` a Hodge class**, on
  every integral smooth projective `X` (no flag hypothesis).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.MiscM

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Filter Set SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.TestCurve.TCEnc SGPT.TestCurve.FGRel SGPT.NAPotential.NANS.TestConfig
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance miscMTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance miscMCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance miscMManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance miscMMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance miscMBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-! ### Change of the smooth metric -/

section Compare

variable {L : X.Modules} {a : LineBundleAtlas L} (H H₀ : SchemeLineBundleMetric f (m + 1) E L)

/-- `h₀ = h e^{-g}` in every frame, with `g = log(h/h₀)` the log ratio. -/
theorem frameNormSq_eq_mul_exp {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    H₀.frameNormSq α p = H.frameNormSq α p * Real.exp (-(H.logRatio H₀ a p)) := by
  rw [H.logRatio_frame H₀ a α p hp, Real.exp_neg,
    Real.exp_log (div_pos (H.positive α p hp) (H₀.positive α p hp))]
  have h1 := (H.positive α p hp).ne'
  have h2 := (H₀.positive α p hp).ne'
  field_simp

/-- `|s|²_{h₀^k} = |s|²_{h^k} e^{-kg}`. -/
theorem sectionNormSq_eq_mul_exp (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) :
    H₀.sectionNormSq a k s p =
      H.sectionNormSq a k s p * Real.exp (-((k : ℝ) * H.logRatio H₀ a p)) := by
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  rw [H₀.sectionNormSq_frame a α k s p hp, H.sectionNormSq_frame a α k s p hp,
    frameNormSq_eq_mul_exp H H₀ α p hp, mul_pow, ← Real.exp_nat_mul]
  ring_nf

/-- `log |s|²_{h₀^k} = log |s|²_{h^k} - k g`. -/
theorem sectionLogNormSq_eq_add (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) :
    H₀.sectionLogNormSq a k s p =
      H.sectionLogNormSq a k s p + ((-((k : ℝ) * H.logRatio H₀ a p) : ℝ) : EReal) := by
  unfold SchemeLineBundleMetric.sectionLogNormSq
  rw [sectionNormSq_eq_mul_exp H H₀ (a := a) k s p,
    ENNReal.ofReal_mul (SchemeLineBundleMetric.sectionNormSq_nonneg H a k s p),
    ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]

end Compare


/-! ### The obstacles of `ex:RWN` for two smooth metrics -/

section Obstacle

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H H₀ : SchemeLineBundleMetric f (m + 1) E L)

/-- `k⁻¹ Γ^{𝓕,k,h}_τ ≤ k⁻¹ Γ^{𝓕,k,h₀}_τ + 2C` when `|log(h/h₀)| ≤ C`: rescale each normalized
section by `e^{-kC/2}`. -/
theorem normalizedPotential_le_add {C : ℝ} (hC : ∀ p, |H.logRatio H₀ a p| ≤ C) {k : ℕ}
    (hk : 0 < k) (τ : ℝ) (x : SchemeComplexPoint f) :
    F.normalizedPotential H k τ x ≤ F.normalizedPotential H₀ k τ x + ((2 * C : ℝ) : EReal) := by
  rw [F.normalizedPotential_eq_iSup H k hk τ x, F.normalizedPotential_eq_iSup H₀ k hk τ x]
  refine iSup_le fun s => ?_
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℂ := ((Real.exp (-((k : ℝ) * C) / 2) : ℝ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact_mod_cast (Real.exp_pos _).ne'
  have hnormc : Complex.normSq c = Real.exp (-((k : ℝ) * C)) := by
    rw [hcdef, Complex.normSq_ofReal, ← Real.exp_add]
    ring_nf
  have hmem : c • s.1 ∈ F.normalizedSections H₀ k τ := by
    refine ⟨Submodule.smul_mem _ c s.2.1, fun p => ?_⟩
    rw [H₀.sectionNormSq_smul a k c s.1 p, sectionNormSq_eq_mul_exp H H₀ (a := a) k s.1 p, hnormc]
    have h1 := s.2.2 p
    have h2 : Real.exp (-((k : ℝ) * C)) * Real.exp (-((k : ℝ) * H.logRatio H₀ a p)) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      have := (abs_le.mp (hC p)).1
      nlinarith
    have h0 := H.sectionNormSq_nonneg a k s.1 p
    calc Real.exp (-((k : ℝ) * C)) *
          (H.sectionNormSq a k s.1 p * Real.exp (-((k : ℝ) * H.logRatio H₀ a p)))
        = H.sectionNormSq a k s.1 p *
          (Real.exp (-((k : ℝ) * C)) * Real.exp (-((k : ℝ) * H.logRatio H₀ a p))) := by ring
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  refine le_trans ?_ (add_le_add (le_iSup (fun s' : F.normalizedSections H₀ k τ =>
    ((((k : ℝ)⁻¹ : ℝ) : EReal) * H₀.sectionLogNormSq a k s'.1 x)) ⟨c • s.1, hmem⟩) le_rfl)
  change ((((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s.1 x) ≤
    ((((k : ℝ)⁻¹ : ℝ) : EReal) * H₀.sectionLogNormSq a k (c • s.1) x) + ((2 * C : ℝ) : EReal)
  rw [SGPT.LineBundle.SectionFiltration.sectionLogNormSq_smul H₀ k hc0 s.1 x,
    sectionLogNormSq_eq_add H H₀ (a := a) k s.1 x, hnormc, Real.log_exp]
  have hℓ := (abs_le.mp (hC x)).2
  generalize H.sectionLogNormSq a k s.1 x = A
  induction A using EReal.rec with
  | bot => rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr hkR))]; exact bot_le
  | top =>
    rw [EReal.top_add_coe, EReal.coe_add_top,
      EReal.mul_top_of_pos (EReal.coe_pos.mpr (inv_pos.mpr hkR)), EReal.top_add_coe]
  | coe A =>
    have key : (k : ℝ)⁻¹ * A ≤
        (k : ℝ)⁻¹ * (-((k : ℝ) * C) + (A + -((k : ℝ) * H.logRatio H₀ a x))) + 2 * C := by
      have : (k : ℝ)⁻¹ * (-((k : ℝ) * C) + (A + -((k : ℝ) * H.logRatio H₀ a x))) =
          (k : ℝ)⁻¹ * A - C - H.logRatio H₀ a x := by
        field_simp
        ring
      rw [this]
      linarith
    exact_mod_cast key

/-- The raw obstacles: `sup_k k⁻¹ Γ^{𝓕,k,h}_τ ≤ sup_k k⁻¹ Γ^{𝓕,k,h₀}_τ + 2C`. -/
theorem rawObstacle_le_add {C : ℝ} (hC : ∀ p, |H.logRatio H₀ a p| ≤ C) (τ : ℝ)
    (x : SchemeComplexPoint f) :
    F.rawObstacle H τ x ≤ F.rawObstacle H₀ τ x + ((2 * C : ℝ) : EReal) :=
  iSup₂_le fun k hk => (normalizedPotential_le_add F H H₀ hC hk τ x).trans
    (add_le_add (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H₀ k τ x) k hk) le_rfl)

/-- **The obstacles of `ex:RWN` for two smooth metrics differ by a bounded function**:
`ψ^h_τ ≤ ψ^{h₀}_τ + 2C` when `|log(h/h₀)| ≤ C`. -/
theorem obstacle_le_add {C : ℝ} (hC : ∀ p, |H.logRatio H₀ a p| ≤ C) (τ : ℝ)
    (x : SchemeComplexPoint f) :
    F.obstacle H τ x ≤ F.obstacle H₀ τ x + ((2 * C : ℝ) : EReal) := by
  have h := uscRegularization_mono (fun y => rawObstacle_le_add F H H₀ hC τ y) x
  rw [uscRegularization_add_coe_const] at h
  exact h

omit [IsIntegral X] in
/-- The log ratio of two smooth metrics is bounded on the compact `X(ℂ)`. -/
theorem exists_abs_logRatio_le :
    ∃ C : ℝ, ∀ p : SchemeComplexPoint f, |H.logRatio H₀ a p| ≤ C := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ProductTestForms.ChartSmooth.continuous (H.logRatio_chartSmooth H₀ a)).continuousOn
  exact ⟨C, fun p => by simpa [Real.norm_eq_abs] using hC p (mem_univ p)⟩

/-- The obstacles for `h` and `h₀` have the same singularity type (one direction). -/
theorem singularityLE_obstacle (τ : ℝ) :
    SGPT.PSH.SingularityLE (F.obstacle H τ) (F.obstacle H₀ τ) := by
  obtain ⟨C, hC⟩ := exists_abs_logRatio_le H H₀ (a := a)
  exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    ⟨2 * C, fun x => obstacle_le_add F H H₀ hC τ x⟩

/-- **The Skoda inclusion does not depend on the smooth metric**: if it holds for `𝓕` and the
metric `h₀`, it holds for `𝓕` and any other smooth metric `h` on `L`. -/
theorem skodaInclusionIdeal_of_metric
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H₀) :
    SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H := by
  let := E.isSeparated
  let := E.quasiCompact
  intro τ' τ hlt hτ
  obtain ⟨k₀, hk₀⟩ := hSk τ' τ hlt hτ
  refine ⟨k₀, fun k hk σ hσ => hk₀ k hk σ ?_⟩
  rcases hσ with h0 | hI
  · exact Or.inl h0
  · exact Or.inr (SGPT.IGood.DXMain.isIdealSection_mono_of_singularityLE f E
      (F.obstacle_isThetaPshPotential H₀ hτ).1.quasiPlurisubharmonic
      (singularityLE_obstacle F H H₀ τ) hI)

end Obstacle


/-! ### The Duistermaat–Heckman limit from the Skoda inclusion -/

section DH

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Tails of `DH(Γ^𝓕)` against the jumping measures, from the Skoda inclusion** (any smooth
metric `h`, `X` with a smooth flag, `{θ}` big): for `τ' < τ < τ(𝓕)`,
`DH(Γ^𝓕)[τ, ∞) ≤ liminf n! k⁻ⁿ ν_k[τ', ∞) ≤ limsup n! k⁻ⁿ ν_k[τ', ∞) ≤ DH(Γ^𝓕)[τ', ∞)`. -/
theorem filtrationDH_tail_sandwich_of_skoda
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ' τ : ℝ} (hlt : τ' < τ) (hτ : τ < SGPT.TestCurve.TestConf.slopeReal F) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    filtrationDH F H Y hY hbig (Ici τ) ≤
      liminf (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
        (k : ℝ≥0∞) ^ (m + 1)) atTop ∧
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
        (k : ℝ≥0∞) ^ (m + 1)) atTop ≤ filtrationDH F H Y hY hbig (Ici τ') := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  have hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)
  have hτE : (τ : EReal) < F.slope :=
    SGPT.TestCurve.TestConf.coe_lt_slope_of_lt F H (hbig := hbig) (hb := hb) hτ
  have hτ'E : (τ' : EReal) < F.slope := (EReal.coe_lt_coe_iff.mpr hlt).trans hτE
  obtain ⟨h1, h2⟩ := jumpMeasure_tail_sandwich F H Y hY hSk hlt hτE
  rw [iVolume_obstacle_eq_mass F H Y hY hbig hτE] at h1
  rw [iVolume_obstacle_eq_mass F H Y hY hbig hτ'E] at h2
  unfold filtrationDH
  rw [naDuistermaatHeckman_filtration_Ici F H Y hY hbig hτ,
    naDuistermaatHeckman_filtration_Ici F H Y hY hbig (hlt.trans hτ)]
  exact ⟨h1, h2⟩

/-- **`DH(Γ^𝓕)` is the weak limit of `(n!/kⁿ) ν_k`, for every smooth metric, from the Skoda
inclusion** (`X` with a smooth flag, `{θ}` big; the proof of
`SGPT.NAPotential.NANS.TestConfig.testConfig_rescaledJumpMeasure_tendsto` with the Kähler
hypothesis replaced by the Skoda inclusion, which is all it uses). -/
theorem rescaledJumpMeasure_tendsto_of_skoda
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => rescaledFiniteMeasure F (m + 1) j) atTop
      (𝓝 (filtrationDHFinite F H Y hY hbig)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  set T := SGPT.TestCurve.TestConf.slopeReal F with hT
  set μ := filtrationDH F H Y hY hbig with hμdef
  have hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)
  have hslope := SGPT.TestCurve.TestConf.coe_slopeReal F H hbig hb
  have hvol := SGPT.GAGA.H0L.volume_pos H Y hY hbig
  have hCT : -(F.bound : ℝ) - 1 < T := by
    have h1 := SGPT.TestCurve.RWN.neg_bound_sub_one_lt_slope F hvol
    rw [← hslope] at h1
    exact_mod_cast h1
  let g : ℝ → ℕ → ℝ≥0∞ := fun t k =>
    (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici t)) / (k : ℝ≥0∞) ^ (m + 1)
  let h : ℝ → ℕ → ℝ≥0∞ := fun t k =>
    (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ioi t)) / (k : ℝ≥0∞) ^ (m + 1)
  have hhg : ∀ t k, h t k ≤ g t k := fun t k => by
    simp only [h, g]
    gcongr
    exact Ioi_subset_Ici_self
  have hgh : ∀ t t', t < t' → ∀ k, g t' k ≤ h t k := fun t t' htt' k => by
    simp only [h, g]
    gcongr
  have hS : ∀ τ' τ, τ' < τ → τ < T →
      μ (Ici τ) ≤ liminf (g τ') atTop ∧ limsup (g τ') atTop ≤ μ (Ici τ') :=
    fun τ' τ hlt hτ => filtrationDH_tail_sandwich_of_skoda F H Y hY hSk hbig hlt hτ
  have hzero : ∀ t, T < t → ∀ k, 0 < k → g t k = 0 := by
    intro t ht k hk
    have := SectionSpace.finiteDimensional f E a k
    exact (filtration_tails_eq_zero_of_slope_lt F H Y hY hbig ht).1 k hk
  have hμzero : ∀ t, T < t → μ (Ici t) = 0 :=
    fun t ht => (filtration_tails_eq_zero_of_slope_lt F H Y hY hbig ht).2
  have hshift : ∀ (u : ℝ → ℕ → ℝ≥0∞) (S : Set ℝ) (t : ℝ),
      (fun j => (rescaledFiniteMeasure F (m + 1) j : Measure ℝ) S) =
        (fun j => u t (j + 1)) → Tendsto (u t) atTop (𝓝 (μ S)) →
      Tendsto (fun j => (rescaledFiniteMeasure F (m + 1) j : Measure ℝ) S) atTop (𝓝 (μ S)) := by
    intro u S t heq hu
    rw [heq]
    exact hu.comp (tendsto_add_atTop_nat 1)
  have hgeq : ∀ t, (fun j => (rescaledFiniteMeasure F (m + 1) j : Measure ℝ) (Ici t)) =
      fun j => g t (j + 1) := fun t => by
    funext j
    exact rescaledJumpMeasure_apply F (m + 1) j (Ici t)
  have hheq : ∀ t, (fun j => (rescaledFiniteMeasure F (m + 1) j : Measure ℝ) (Ioi t)) =
      fun j => h t (j + 1) := fun t => by
    funext j
    exact rescaledJumpMeasure_apply F (m + 1) j (Ioi t)
  let D : Set ℝ := {t | μ {t} = 0 ∧ t ≠ T}
  have hD : Dᶜ.Countable := by
    have h1 := SGPT.NAPotential.NANS.countable_atoms μ
    rw [compl_compl] at h1
    refine (h1.union (countable_singleton T)).mono ?_
    intro t ht
    by_cases htT : t = T
    · exact Or.inr htT
    · left
      intro h0
      exact ht ⟨h0, htT⟩
  have hDdense : Dense D := by
    have := Set.Countable.dense_compl ℝ hD
    rwa [compl_compl] at this
  obtain ⟨t₀, ht₀D, ht₀⟩ := hDdense.exists_between
    (show -(F.bound : ℝ) - 2 < -(F.bound : ℝ) - 1 by linarith)
  have ht₀C : t₀ ≤ -(F.bound : ℝ) := by linarith [ht₀.2]
  have ht₀T : t₀ < T := by linarith [ht₀.2]
  have htails := fun t (htT : t < T) (hat : μ {t} = 0) =>
    SGPT.NAPotential.NANS.tendsto_tails_of_sandwich μ hhg hgh hS htT hat
  apply SGPT.NAPotential.NANS.tendsto_of_tendsto_tails (D := D) ?_ hD
  · intro t ⟨hat, htT⟩
    change Tendsto _ atTop (𝓝 (μ (Ioi t)))
    rcases lt_or_gt_of_ne htT with htT | htT
    · exact hshift h (Ioi t) t (hheq t) (htails t htT hat).2
    · rw [hheq t]
      have h0 : μ (Ioi t) = 0 := measure_mono_null Ioi_subset_Ici_self (hμzero t htT)
      rw [h0]
      refine tendsto_const_nhds.congr fun j => ?_
      exact (le_antisymm ((hhg t (j + 1)).trans (hzero t htT (j + 1) (Nat.succ_pos j)).le)
        bot_le).symm
  · intro t ⟨hat, htT⟩
    change Tendsto _ atTop (𝓝 (μ (Ici t)))
    rcases lt_or_gt_of_ne htT with htT | htT
    · exact hshift g (Ici t) t (hgeq t) (htails t htT hat).1
    · rw [hgeq t, hμzero t htT]
      exact tendsto_const_nhds.congr fun j => (hzero t htT (j + 1) (Nat.succ_pos j)).symm
  · have hmass : (fun j => (rescaledFiniteMeasure F (m + 1) j : Measure ℝ) univ) =
        fun j => g t₀ (j + 1) := by
      funext j
      have := SectionSpace.finiteDimensional f E a (j + 1)
      change rescaledJumpMeasure F (m + 1) j univ = _
      rw [rescaledJumpMeasure_apply, ← jumpMeasure_Ici_eq_univ F ht₀C (Nat.succ_pos j)]
    rw [hmass]
    show Tendsto _ atTop (𝓝 (μ univ))
    rw [filtrationDH_univ F H Y hY hbig ht₀C ht₀T]
    exact (htails t₀ ht₀T ht₀D.1).1.comp (tendsto_add_atTop_nat 1)
  · intro hzero'
    exact filtrationDHFinite_ne_zero F H Y hY hbig hzero'

/-- Normalized form of `rescaledJumpMeasure_tendsto_of_skoda`: `N_k⁻¹ ν_k → DH(Γ^𝓕)/DH(Γ^𝓕)(ℝ)`
and `n! N_k / kⁿ → DH(Γ^𝓕)(ℝ)`. -/
theorem normalized_tendsto_of_skoda
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure F (m + 1) j).normalize)
        atTop (𝓝 (filtrationDHFinite F H Y hY hbig).normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure F (m + 1) j).mass)
        atTop (𝓝 (filtrationDHFinite F H Y hY hbig).mass) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto
    (filtrationDHFinite_ne_zero F H Y hY hbig)).mpr
    (rescaledJumpMeasure_tendsto_of_skoda F H Y hY hSk hbig)

end DH


/-! ### A Hodge class is the class of a Kähler curvature form -/

section Hodge

variable {L : X.Modules} (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The smooth metric `h e^{ψ}` on `L`, for a chart-smooth real function `ψ`. -/
def twistMetric (ψ : SchemeComplexPoint f → ℝ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := m + 1) ψ) :
    SchemeLineBundleMetric f (m + 1) E L where
  frameNormSq α p := H.frameNormSq α p * Real.exp (ψ p)
  smooth α e := (H.smooth α e).mul ((hψ e).mono inter_subset_left).exp
  positive α p hp := mul_pos (H.positive α p hp) (Real.exp_pos _)
  transition α β p hp hq := by
    rw [H.transition α β p hp hq]
    ring

/-- `log(h / (h e^{ψ})) = -ψ`. -/
theorem logRatio_twistMetric (a : LineBundleAtlas L) (ψ : SchemeComplexPoint f → ℝ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := m + 1) ψ)
    (p : SchemeComplexPoint f) : H.logRatio (twistMetric H ψ hψ) a p = -ψ p := by
  rw [H.logRatio_frame (twistMetric H ψ hψ) a (schemePointFrame f p a) p
    (schemePointFrame_mem f p a)]
  change Real.log (H.frameNormSq _ p / (H.frameNormSq _ p * Real.exp (ψ p))) = -ψ p
  have hpos := H.positive (schemePointFrame f p a) p (schemePointFrame_mem f p a)
  rw [div_mul_cancel_left₀ hpos.ne', Real.log_inv, Real.log_exp]

/-- **A Hodge class carries a Kähler curvature metric**: if the Bott–Chern class `{θ}` of
`θ = c₁(L, h)` contains a Kähler form `ω`, then `ω` is (geometrically) the curvature of the smooth
metric `h e^{ψ}` on `L`, where `θ = ω + dd^c ψ`; in particular `L` carries a smooth metric of
Kähler curvature. -/
theorem exists_kahler_metric_of_hodge (a : LineBundleAtlas L)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a)) :
    ∃ H₀ : SchemeLineBundleMetric f (m + 1) E L,
      letI := E.isSeparated; letI := E.quasiCompact; (H₀.curvature a).val.IsKahler := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨ω, hω, hcl⟩ := hHodge
  obtain ⟨ψ, hψ, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff ω (H.curvature a)).mp hcl
  refine ⟨twistMetric H ψ hψ, ?_⟩
  have hgeom : ((twistMetric H ψ hψ).curvature a).val.GeometricallyEq ω.val := by
    intro e u hu
    rw [H.curvature_change (twistMetric H ψ hψ) a a e hu]
    change (H.curvature a).val.coeff e u +
        smoothDDC (fun y => H.logRatio (twistMetric H ψ hψ) a (e.val.symm y)) u = ω.val.coeff e u
    have hfun : (fun y => H.logRatio (twistMetric H ψ hψ) a (e.val.symm y)) =
        fun y => -ψ (e.val.symm y) :=
      funext fun y => logRatio_twistMetric H a ψ hψ (e.val.symm y)
    rw [hfun, smoothDDC_neg e.val.open_target (hψ e) hu, hrel e u hu]
    abel
  exact hgeom.isKahler_iff.mpr hω

end Hodge

/-! ### Test configurations, arbitrary smooth metric, Hodge class -/

section TestConfiguration

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **The Skoda inclusion for the filtration of a test configuration, for an arbitrary smooth
metric** `h` on `L`, as soon as `L` carries some smooth metric `h₀` of Kähler curvature: lanes
SKODA-INC/GLOBAL-SKODA give it for `h₀`, and it does not depend on the metric
(`skodaInclusionIdeal_of_metric`). -/
theorem skodaInclusionIdeal_inducedFiltration_of_kahler [Nonempty (SchemeComplexPoint f)]
    (T : TestConfiguration f a) (hfg : T.FiltrationFinitelyGenerated E)
    {H₀ : SchemeLineBundleMetric f (m + 1) E L}
    (hK₀ : letI := E.isSeparated; letI := E.quasiCompact; (H₀.curvature a).val.IsKahler) :
    SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal (T.inducedFiltration E hfg) H := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hgaga : ∀ᶠ j in atTop,
      SGPT.NAPotential.GAGAMult.SchemeSectionsAlgebraic f (m + 1) E a H₀ j :=
    Eventually.of_forall fun j => SGPT.GAGA.H0L.schemeSectionsAlgebraic a H₀ j
  exact skodaInclusionIdeal_of_metric _ H H₀
    (SGPT.TestCurve.SkodaInc.skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision
      (T.zFiltration E) hfg (T.zFiltration_piece_zero_zero E) H₀ hK₀ hgaga
      (SGPT.TestCurve.GlobalSkoda.globalSkodaDivision_of_sectionsAlgebraic H₀ a hgaga))

/-- **Source `rmk:NApotential:L862` for an arbitrary smooth metric `h`** (`θ = c₁(L, h)`, `{θ}` a
Hodge class: it contains a Kähler form): for a test configuration
`(𝓧, 𝓛)` of `(X, L)` with finitely generated induced filtration `𝓕`, on every integral smooth
projective `X`, the rescaled weight measures `(n!/kⁿ) ν_k` converge weakly to a finite measure `μ`
which is the Duistermaat–Heckman measure `DH(Γ^𝓕)` (`def:DHm`, `Γ^𝓕` the test curve of `ex:RWN`
built with `h`) computed with every smooth flag of `X`. -/
theorem testConfiguration_rescaledJumpMeasure_tendsto_hodge (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j) atTop
        (𝓝 μ) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨H₀, hK₀⟩ := exists_kahler_metric_of_hodge H a hHodge
  have hSk := skodaInclusionIdeal_inducedFiltration_of_kahler H T hfg hK₀
  obtain ⟨Y₀, hY₀⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
  have h₀ := rescaledJumpMeasure_tendsto_of_skoda _ H Y₀ hY₀ hSk hbig
  exact ⟨_, h₀, fun Y hY =>
    tendsto_nhds_unique h₀ (rescaledJumpMeasure_tendsto_of_skoda _ H Y hY hSk hbig)⟩

/-- Normalized form of `testConfiguration_rescaledJumpMeasure_tendsto_hodge`:
`N_k⁻¹ ν_k → μ / μ(ℝ)` and `n! N_k / kⁿ → μ(ℝ)`, `μ = DH(Γ^𝓕)` (any smooth flag). -/
theorem testConfiguration_normalized_tendsto_hodge (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).normalize)
        atTop (𝓝 μ.normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).mass)
        atTop (𝓝 μ.mass) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨Y₀, hY₀⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
  obtain ⟨μ, -, hμ⟩ := testConfiguration_rescaledJumpMeasure_tendsto_hodge H T hfg hHodge hbig
  obtain ⟨H₀, hK₀⟩ := exists_kahler_metric_of_hodge H a hHodge
  have hSk := skodaInclusionIdeal_inducedFiltration_of_kahler H T hfg hK₀
  obtain ⟨h1, h2⟩ := normalized_tendsto_of_skoda _ H Y₀ hY₀ hSk hbig
  rw [← hμ Y₀ hY₀] at h1 h2
  exact ⟨μ, h1, h2, hμ⟩

/-- **`rmk:NApotential:L862` for ample test configurations (equivariant coordinates), arbitrary
smooth metric, `{θ}` a Hodge class**: `(n!/kⁿ) ν_k → DH(Γ^𝓕)` weakly, with no finite generation
or flag hypothesis. -/
theorem equivariantCoordinates_rescaledJumpMeasure_tendsto_hodge (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j) atTop (𝓝 μ) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite
          (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
          H Y hY hbig :=
  testConfiguration_rescaledJumpMeasure_tendsto_hodge H T _ hHodge hbig

/-- Normalized form of `equivariantCoordinates_rescaledJumpMeasure_tendsto_hodge`. -/
theorem equivariantCoordinates_normalized_tendsto_hodge (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).normalize) atTop (𝓝 μ.normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).mass) atTop (𝓝 μ.mass) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite
          (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
          H Y hY hbig :=
  testConfiguration_normalized_tendsto_hodge H T _ hHodge hbig

/-- **Independence of the smooth metric** (`rmk:NApotential:L47` for the test curves of test
configurations): for two smooth metrics `h, h'` on `L` with `{c₁(L, h)}` a Hodge class, the
Duistermaat–Heckman measures `DH(Γ^𝓕)` built with `h` and with `h'` coincide (both are the weak
limit of `(n!/kⁿ) ν_k`, which does not involve a metric). -/
theorem filtrationDHFinite_eq_of_metric (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E) (H' : SchemeLineBundleMetric f (m + 1) E L)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hbig' : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H'.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig =
        filtrationDHFinite (T.inducedFiltration E hfg) H' Y hY hbig' := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  intro Y hY
  have hcl : RealBottChern.ofRepresentative (H'.curvature a) =
      RealBottChern.ofRepresentative (H.curvature a) := (H.chernClass_independent H' a a).symm
  have hHodge' : ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
      RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H'.curvature a) := by
    obtain ⟨ω, hω, hωcl⟩ := hHodge
    exact ⟨ω, hω, hωcl.trans hcl.symm⟩
  obtain ⟨μ, hμ, hμY⟩ := testConfiguration_rescaledJumpMeasure_tendsto_hodge H T hfg hHodge hbig
  obtain ⟨μ', hμ', hμ'Y⟩ :=
    testConfiguration_rescaledJumpMeasure_tendsto_hodge H' T hfg hHodge' hbig'
  rw [← hμY Y hY, ← hμ'Y Y hY]
  exact tendsto_nhds_unique hμ hμ'

end TestConfiguration

end SGPT.TestCurve.MiscM

end
