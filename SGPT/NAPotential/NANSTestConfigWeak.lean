import SGPT.NAPotential.NANSTestConfigVolume
import SGPT.NAPotential.NANSWeakLimit

/-! # `rmk:NApotential:L862`: `DH(Γ^𝓕)` is the weak limit of the rescaled weight measures

Source `chapter_NApotential.tex`, `rmk:NApotential:L862`: *when `{θ}` is a Hodge class and `Γ` is
induced by a test configuration as in `ex:RWN` and `rmk:PhongSturm`, our Duistermaat–Heckman
measure coincides with the more traditional definition of [BHJ17, §3.2]*.  Blueprint
`claude-na-ns`.

[BHJ17, §3.2] defines the Duistermaat–Heckman measure of an ample test configuration as the weak
limit of the rescaled weight measures of the central fibre, i.e. (by [BHJ17, §1.1, §5]) of
`N_k⁻¹ ν_k` with the jumping measures `ν_k` of the induced filtration `𝓕`.  We prove that
`(n!/kⁿ) ν_k → DH(Γ^𝓕)` weakly (`testConfig_rescaledJumpMeasure_tendsto`), where `DH(Γ^𝓕)` is the
book's measure (`def:DHm`) of the test curve `Γ^𝓕` of `ex:RWN`; normalizing,
`N_k⁻¹ ν_k → DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)` (`testConfig_normalized_tendsto`).  Thus the BHJ measure
exists and `DH(Γ^𝓕) = DH(Γ^𝓕)(ℝ) · DH_BHJ`: the two measures coincide up to the normalization
of the total mass (the book's `DH(Γ)` has mass `vol Γ`, the BHJ measure is a probability measure;
the erratum on the normalization is recorded in `claude-testconf2`).

Proof: the tails of `(n!/kⁿ) ν_k` converge to those of `DH(Γ^𝓕)` at the non-atoms
(`testConfig_DH_tail_sandwich`, `tendsto_tails_of_sandwich`), above the slope both vanish, the
total masses converge since the supports are uniformly bounded below and `Γ^𝓕_τ = V_θ` for
`τ ≤ -C`, and weak convergence follows (`tendsto_of_tendsto_tails`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ENNReal

namespace SGPT.NAPotential.NANS.TestConfig

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance nansTWTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansTWCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance nansTWManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance nansTWMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance nansTWBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-! ### Rescaled jumping measures -/

section Rescaled

variable {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)

/-- The rescaled jumping measure `(n!/kⁿ) ν_k` in degree `k = j + 1`. -/
def rescaledJumpMeasure (n j : ℕ) : Measure ℝ :=
  ((n.factorial : ℝ≥0∞) / ((j + 1 : ℕ) : ℝ≥0∞) ^ n) • F.jumpMeasure (j + 1)

theorem rescaledJumpMeasure_apply (n j : ℕ) (s : Set ℝ) :
    rescaledJumpMeasure F n j s =
      ((n.factorial : ℝ≥0∞) * F.jumpMeasure (j + 1) s) / ((j + 1 : ℕ) : ℝ≥0∞) ^ n := by
  rw [rescaledJumpMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, mul_assoc]

instance (n j : ℕ) : IsFiniteMeasure (rescaledJumpMeasure F n j) := by
  constructor
  rw [rescaledJumpMeasure_apply, F.jumpMeasure_univ]
  exact ENNReal.div_lt_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.natCast_ne_top _)) (pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero j))

/-- `(n!/kⁿ) ν_k`, `k = j + 1`, as a finite measure. -/
def rescaledFiniteMeasure (n j : ℕ) : FiniteMeasure ℝ :=
  ⟨rescaledJumpMeasure F n j, inferInstance⟩

/-- The normalization of `(n!/kⁿ) ν_k` is the rescaled weight measure `N_k⁻¹ ν_k` of [BHJ17]
(`bhjWeightMeasure`), as soon as `N_k = h⁰(X, L^k) ≠ 0`. -/
theorem normalize_rescaledFiniteMeasure (n j : ℕ)
    (hN : (Module.finrank ℂ (SectionSpace f L (j + 1)) : ℝ≥0∞) ≠ 0) :
    ((rescaledFiniteMeasure F n j).normalize : Measure ℝ) = F.bhjWeightMeasure (j + 1) := by
  set K : ℝ≥0∞ := ((j + 1 : ℕ) : ℝ≥0∞) ^ n with hK
  set N : ℝ≥0∞ := (Module.finrank ℂ (SectionSpace f L (j + 1)) : ℝ≥0∞) with hNdef
  set c : ℝ≥0∞ := (n.factorial : ℝ≥0∞) with hc
  have hK0 : K ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))
  have hKt : K ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hct : c ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have huniv : rescaledJumpMeasure F n j univ = c * N / K := by
    rw [rescaledJumpMeasure_apply, F.jumpMeasure_univ]
  have hne : rescaledFiniteMeasure F n j ≠ 0 := by
    intro h0
    have := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) univ) h0
    change rescaledJumpMeasure F n j univ = _ at this
    rw [huniv] at this
    simp only [FiniteMeasure.toMeasure_zero, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.div_pos (mul_ne_zero hc0 hN) hKt).ne' this
  ext s _
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    FiniteMeasure.normalize_eq_of_nonzero _ hne, ENNReal.coe_mul,
    ENNReal.coe_inv ((FiniteMeasure.mass_nonzero_iff _).mpr hne), FiniteMeasure.ennreal_mass,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (rescaledJumpMeasure F n j univ)⁻¹ * rescaledJumpMeasure F n j s = _
  rw [huniv, rescaledJumpMeasure_apply, SectionFiltration.bhjWeightMeasure, Measure.smul_apply,
    smul_eq_mul, ← hNdef, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hKt)) (Or.inl (ENNReal.inv_ne_top.mpr hK0)),
    inv_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc K * (c⁻¹ * N⁻¹) * (K⁻¹ * (c * F.jumpMeasure (j + 1) s))
      = (K * K⁻¹) * (c⁻¹ * c) * (N⁻¹ * F.jumpMeasure (j + 1) s) := by ring
    _ = N⁻¹ * F.jumpMeasure (j + 1) s := by
      rw [ENNReal.mul_inv_cancel hK0 hKt, ENNReal.inv_mul_cancel hc0 hct, one_mul, one_mul]

end Rescaled

/-! ### The weak limit -/

section Weak

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The book's `DH(Γ^𝓕)` (`def:DHm`), computed with the smooth flag `Y`. -/
def filtrationDH [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) : Measure ℝ :=
  @SGPT.NAPotential.DH.naDuistermaatHeckman m
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
    (@BorelSpace.mk _ _ (borel _) rfl) _ (curvatureAtlasForm_isBig H hbig)
    (filtrationNACurve F H Y hY hbig)

instance [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    IsFiniteMeasure (filtrationDH F H Y hY hbig) :=
  @SGPT.NAPotential.DH.naDuistermaatHeckman_finite m
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
    (@BorelSpace.mk _ _ (borel _) rfl) _ (curvatureAtlasForm_isBig H hbig)
    (filtrationNACurve F H Y hY hbig)

/-- `DH(Γ^𝓕)` as a finite measure. -/
def filtrationDHFinite [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) : FiniteMeasure ℝ :=
  ⟨filtrationDH F H Y hY hbig, inferInstance⟩

omit [IsIntegral X] in
/-- `ν_k[τ, ∞) = ν_k(ℝ)` for `τ ≤ -C` (linear boundedness) and `k > 0`. -/
theorem jumpMeasure_Ici_eq_univ {τ : ℝ} (hτ : τ ≤ -(F.bound : ℝ)) {k : ℕ} (hk : 0 < k)
    [FiniteDimensional ℂ (SectionSpace f L k)] :
    F.jumpMeasure k (Ici τ) = F.jumpMeasure k univ := by
  rw [F.jumpMeasure_Ici hk τ, F.jumpMeasure_univ, SectionFiltration.pieceDim,
    F.piece_eq_top_of_le_neg_bound hτ hk, finrank_top]

section Instances

variable [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
  [ConnectedSpace (SchemeComplexPoint f)]
  (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))

/-- `DH(Γ^𝓕)[t, ∞)` is constant for `t ≤ t₀ ≤ -C` (`Γ^𝓕_t = V_θ`). -/
theorem filtrationDH_Ici_const {t t₀ : ℝ} (htt₀ : t ≤ t₀) (ht₀C : t₀ ≤ -(F.bound : ℝ))
    (ht₀ : t₀ < SGPT.TestCurve.TestConf.slopeReal F) :
    filtrationDH F H Y hY hbig (Ici t) = filtrationDH F H Y hY hbig (Ici t₀) := by
  have hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)
  unfold filtrationDH
  rw [naDuistermaatHeckman_filtration_Ici F H Y hY hbig (lt_of_le_of_lt htt₀ ht₀),
    naDuistermaatHeckman_filtration_Ici F H Y hY hbig ht₀]
  exact SGPT.IGood.Misc2VolBigL.diagonalPotentialMass_congr _
    ((hb t (htt₀.trans ht₀C)).trans (hb t₀ ht₀C).symm) _ _

/-- `DH(Γ^𝓕)(ℝ) = DH(Γ^𝓕)[t₀, ∞)` for `t₀ ≤ -C`, `t₀ < τ(𝓕)`. -/
theorem filtrationDH_univ {t₀ : ℝ} (ht₀C : t₀ ≤ -(F.bound : ℝ))
    (ht₀ : t₀ < SGPT.TestCurve.TestConf.slopeReal F) :
    filtrationDH F H Y hY hbig univ = filtrationDH F H Y hY hbig (Ici t₀) := by
  have hmono : Monotone fun j : ℕ => Ici (t₀ - j) := by
    intro i j hij
    apply Ici_subset_Ici.mpr
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hU : (⋃ j : ℕ, Ici (t₀ - j)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt (t₀ - x)
    exact mem_iUnion.mpr ⟨j, show t₀ - j ≤ x by linarith⟩
  rw [← hU, hmono.measure_iUnion]
  apply le_antisymm
  · refine iSup_le fun j => le_of_eq ?_
    exact filtrationDH_Ici_const F H Y hY hbig
      (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith) ht₀C ht₀
  · exact le_iSup_of_le 0 (by simp)

end Instances

/-- **Source `rmk:NApotential:L862`: `DH(Γ^𝓕)` is the weak limit of the rescaled weight
measures.**  Let `𝓕` be the filtration of an ample test configuration (a finitely generated
normalized `ℤ`-filtration of `R(X, L)`), `h` a smooth metric with Kähler curvature
`θ = c₁(L, h)` (a Hodge class), and `X` with a smooth flag.  Then `(n!/kⁿ) ν_k → DH(Γ^𝓕)` weakly
as finite measures on `ℝ`, where `ν_k = ∑_j δ_{λ^{(k)}_j / k}` is the jumping measure of `𝓕`
(the weights of the central fibre) and `DH(Γ^𝓕)` the book's Duistermaat–Heckman measure of the
test curve `Γ^𝓕` of `ex:RWN`. -/
theorem testConfig_rescaledJumpMeasure_tendsto
    (G : SGPT.TestCurve.TestConfig.SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => rescaledFiniteMeasure (G.fgFiltration hG h0) (m + 1) j) atTop
      (𝓝 (filtrationDHFinite (G.fgFiltration hG h0) H Y hY hbig)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  set F := G.fgFiltration hG h0 with hF
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
  -- closed and open tails of `(n!/kⁿ) ν_k`
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
    fun τ' τ hlt hτ => testConfig_DH_tail_sandwich H Y hY G hG h0 hK hbig hlt hτ
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
  -- the set of good points: non-atoms of `DH(Γ^𝓕)` other than `τ(𝓕)`
  let D : Set ℝ := {t | μ {t} = 0 ∧ t ≠ T}
  have hD : Dᶜ.Countable := by
    have h1 := countable_atoms μ
    rw [compl_compl] at h1
    refine (h1.union (countable_singleton T)).mono ?_
    intro t ht
    by_cases htT : t = T
    · exact Or.inr htT
    · left
      intro h0
      exact ht ⟨h0, htT⟩
  -- a non-atom `t₀ ≤ -C` below the slope, for the total masses
  have hDdense : Dense D := by
    have := Set.Countable.dense_compl ℝ hD
    rwa [compl_compl] at this
  obtain ⟨t₀, ht₀D, ht₀⟩ := hDdense.exists_between
    (show -(F.bound : ℝ) - 2 < -(F.bound : ℝ) - 1 by linarith)
  have ht₀C : t₀ ≤ -(F.bound : ℝ) := by linarith [ht₀.2]
  have ht₀T : t₀ < T := by linarith [ht₀.2]
  have htails := fun t (htT : t < T) (hat : μ {t} = 0) =>
    tendsto_tails_of_sandwich μ hhg hgh hS htT hat
  apply tendsto_of_tendsto_tails (D := D) ?_ hD
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
  · -- `DH(Γ^𝓕) ≠ 0`
    intro hzero'
    have hpos : 0 < filtrationDH F H Y hY hbig univ := by
      rw [filtrationDH_univ F H Y hY hbig ht₀C ht₀T]
      unfold filtrationDH
      have hτ₀ : (t₀ : EReal) < F.slope := by
        rw [← hslope]
        exact EReal.coe_lt_coe_iff.mpr ht₀T
      rw [naDuistermaatHeckman_filtration_Ici F H Y hY hbig ht₀T,
        ← iVolume_obstacle_eq_mass F H Y hY hbig hτ₀]
      exact hvol.trans_le (SGPT.TestCurve.RWN.volume_le_iVolume_obstacle F H Y hY hτ₀ ht₀C)
    have h0 : μ univ = 0 := by
      have := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) univ) hzero'
      simpa [filtrationDHFinite] using this
    exact (ne_of_gt hpos) h0

/-- `DH(Γ^𝓕)` is a nonzero finite measure (its mass is `vol θ_{V_θ} ≥ vol L > 0`). -/
theorem filtrationDHFinite_ne_zero [IsSeparated f] [QuasiCompact f]
    [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    filtrationDHFinite F H Y hY hbig ≠ 0 := by
  have hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)
  have hslope := SGPT.TestCurve.TestConf.coe_slopeReal F H hbig hb
  have hvol := SGPT.GAGA.H0L.volume_pos H Y hY hbig
  have h1 := SGPT.TestCurve.RWN.neg_bound_sub_one_lt_slope F hvol
  have hτ₀ : ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := h1
  have hT : -(F.bound : ℝ) - 1 < SGPT.TestCurve.TestConf.slopeReal F := by
    rw [← hslope] at h1
    exact_mod_cast h1
  have hC : -(F.bound : ℝ) - 1 ≤ -(F.bound : ℝ) := by linarith
  intro hzero
  have hpos : 0 < filtrationDH F H Y hY hbig univ := by
    rw [filtrationDH_univ F H Y hY hbig hC hT]
    unfold filtrationDH
    rw [naDuistermaatHeckman_filtration_Ici F H Y hY hbig hT,
      ← iVolume_obstacle_eq_mass F H Y hY hbig hτ₀]
    exact hvol.trans_le (SGPT.TestCurve.RWN.volume_le_iVolume_obstacle F H Y hY hτ₀ hC)
  have h0 : filtrationDH F H Y hY hbig univ = 0 := by
    have := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) univ) hzero
    simpa [filtrationDHFinite] using this
  exact (ne_of_gt hpos) h0

/-- **Source `rmk:NApotential:L862`, normalized form**: under the hypotheses of
`testConfig_rescaledJumpMeasure_tendsto`, the probability measures obtained by normalizing
`(n!/kⁿ) ν_k` (i.e. `N_k⁻¹ ν_k`, the rescaled weight measures of [BHJ17]) converge weakly to the
normalization of `DH(Γ^𝓕)`, and the total masses `n! N_k / kⁿ` converge to `DH(Γ^𝓕)(ℝ)`.  Hence
the Duistermaat–Heckman measure of [BHJ17, §3.2] exists and equals `DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)`. -/
theorem testConfig_normalized_tendsto
    (G : SGPT.TestCurve.TestConfig.SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure (G.fgFiltration hG h0) (m + 1) j).normalize)
        atTop (𝓝 (filtrationDHFinite (G.fgFiltration hG h0) H Y hY hbig).normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (G.fgFiltration hG h0) (m + 1) j).mass)
        atTop (𝓝 (filtrationDHFinite (G.fgFiltration hG h0) H Y hY hbig).mass) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto
    (filtrationDHFinite_ne_zero (G.fgFiltration hG h0) H Y hY hbig)).mpr
    (testConfig_rescaledJumpMeasure_tendsto H Y hY G hG h0 hK hbig)

end Weak

end SGPT.NAPotential.NANS.TestConfig

end
