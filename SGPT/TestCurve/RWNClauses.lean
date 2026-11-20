import SGPT.TestCurve.RWNClauseReduction
import SGPT.IGood.DXMainStatement
import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope

/-!
# The two open clauses of `ex:RWN`, and `rmk:max_filt`

Source `ex:RWN` (chapter *Test curves*): for a filtration `𝓕` of `R(X, L)` (`L` big, `h` a
smooth metric, `θ = c₁(L, h)`) the book defines `Γ^𝓕_τ = P_θ[ψ_τ]`,
`ψ_τ = usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ`, and claims

* (a) (`SGPT.TestCurve.TestConf.RWNIModelClause`) each `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model;
* (b) (`SGPT.TestCurve.TestConf.RWNMinimalClause`, `eq:Gammatautheta`) `Γ^𝓕_τ = V_θ` for
  `τ ≤ -C`.

The book's argument for (a): `ψ_τ` is `𝓘`-good (`prop:Igoodsup`, proved in
`SGPT.TestCurve.RWNObstacleIGood`), "hence the `P`- and `𝓘`-envelopes of this obstacle agree".
The last step needs `ψ_τ` to have *positive mass* in the background `θ` itself (`def:Igoodpot`
only provides some background in which `ψ_τ` has positive mass; the footnote of `ex:ImodelIgood`
records that the zero-mass case is not known). We supply this as follows.

* `SGPT.TestCurve.RWN.iGoodWith_of_iGood_of_iEnvelope_mass_pos` (`RWNClauseReduction`): an
  `𝓘`-good `u ∈ PSH(X, θ)` whose `𝓘`-envelope `P_θ[u]_𝓘` has positive mass has positive mass
  itself and `P_θ[u] = P_θ[u]_𝓘` (`u` and `P_θ[u]_𝓘` are `P`-equivalent in a common positive
  background, hence have the same mass in every background).
* For `τ ≤ -C` every section of `L^k` is a section of `L^k ⊗ 𝓘(kψ_τ)` (the book's argument in
  the proof of (b)), so by the proved upper bound of `thm:DXmain1`
  (`SGPT.IGood.DXMain.limsup_multiplierH0_le`, on `X` with a smooth flag)
  `vol L ≤ vol θ_{ψ_τ} = ∫_X θ_{P_θ[ψ_τ]_𝓘}ⁿ`. Hence if `vol L > 0`, `ψ_{-C-1}` has positive
  mass, and by concavity of `τ ↦ ψ_τ` (`SectionFiltration.obstacle_concave`) and the scaling
  `∫ θ_{tu+(1-t)v}ⁿ ≥ tⁿ ∫ θ_uⁿ`, every `ψ_τ`, `τ < τ(𝓕)`, has positive mass
  (`SGPT.TestCurve.RWN.obstacle_hasPositiveMass_of_pos`).
* (b): with the lower bound `DXMainLowerBound` of `thm:DXmain1` at `V_θ`,
  `vol θ_{ψ_τ} ≥ vol L ≥ ∫_X θ_{V_θ}ⁿ` for `τ ≤ -C`; `P_θ[ψ_τ]_𝓘` is model, below `V_θ` and of
  full mass, hence equal to `V_θ` (`thm:Pvarphidiffdef`); and `Γ^𝓕_τ = P_θ[ψ_τ] = P_θ[ψ_τ]_𝓘`.
  This is the book's elementary argument, with `thm:DXmain1` for `Γ^𝓕_τ` replaced by its proved
  upper bound and its lower bound used only at `V_θ`.

## Main results

* **`rwnIModelClause_of_volume_pos`** (clause (a)): if `X` carries a smooth flag and
  `vol L = limsup n! h⁰(X, L^k)/kⁿ > 0` (`L` big in the algebraic sense), every `Γ^𝓕_τ`,
  `τ < τ(𝓕)`, is `𝓘`-model.
* **`rwnMinimalClause_of_lowerBound`** (clause (b)): if `X` carries a smooth flag, `{θ}` is big
  and the lower bound of `thm:DXmain1` holds for `V_θ`, then `Γ^𝓕_τ = V_θ` for `τ ≤ -C`.
* `volume_pos_of_lowerBound`: under the same hypotheses `vol L > 0`, so
  `rwnIModelClause_of_lowerBound` gives (a) without the algebraic bigness hypothesis.
* **`filtrationRay_mem_maximal_of_lowerBound`** (`rmk:max_filt`): the Legendre transform of
  `Γ^𝓕` is a maximal geodesic ray, conditional only on the smooth flag and on the lower bound of
  `thm:DXmain1` at `V_θ`.

## Standing setting

As in the existing formalization of `ex:RWN`: `X` an integral smooth projective complex scheme of
dimension `n = m + 1` with connected analytic space, `L` a line bundle with a smooth metric `H`,
`θ = c₁(L, H)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.POrder SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ENNReal

namespace SGPT.TestCurve.RWN


variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance rwnTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance rwnCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance rwnManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-! ### A section lies in the multiplier ideal of its own normalized potential -/

section Multiplier

variable {L : X.Modules}

/-- The local estimate (the same as in the proof of `eq:H0eqH0IVtheta`): in the chart at `p` and
a frame `α` around `p`, the coefficient `g` of `s` lies in `𝓘(k · k⁻¹ log |s|²_{h^k})`: the
weighted density `|g|² e^{-log |s|²}` is bounded by `|α|^{-2k}_h` near `p`. -/
theorem multiplierIntegrableAt_normalizedPotential (H : SchemeLineBundleMetric f (m + 1) E L)
    (b : LineBundleAtlas L) {k : ℕ} (hk : 0 < k) (s : bundlePowerGlobalSections L k)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    MultiplierIntegrableAt
      (chartFunction (SGPT.IGood.DXMain.normalizedPotential f (m + 1) E b H k s)
        (complexChartAt (n := m + 1) p))
      (k : ℝ)
      (fun z => sectionFrameCoefficient f (m + 1) E α k s
        ((complexChartAt (n := m + 1) p).val.symm z))
      ((complexChartAt (n := m + 1) p).val p) volume := by
  let := E.isSeparated
  let := E.quasiCompact
  set e := complexChartAt (n := m + 1) p with he_def
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set G : ComplexModel (m + 1) → ℂ := fun z => sectionFrameCoefficient f (m + 1) E α k s
    (e.val.symm z)
  set Fn : ComplexModel (m + 1) → ℝ := fun z => H.frameNormSq α (e.val.symm z)
  set D : Set (ComplexModel (m + 1)) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) with hD_def
  have hDopen : IsOpen D :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz0D : e.val p ∈ D := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r' := r / 2
  have hr' : 0 < r' := half_pos hr
  have hcb : Metric.closedBall (e.val p) r' ⊆ D := fun z hz =>
    hrD (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (half_lt_self hr))
  have hFcont : ContinuousOn Fn D := (H.smooth α e).continuousOn
  have hFpos : ∀ z ∈ D, 0 < Fn z := fun z hz => H.positive α _ hz.2
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_closedBall (e.val p) r').exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr'.le) (hFcont.mono hcb)
  set μ := Fn zm
  have hm : 0 < μ := hFpos zm (hcb hzm)
  set dens := multiplierDensity
    (chartFunction (SGPT.IGood.DXMain.normalizedPotential f (m + 1) E b H k s) e)
    (k : ℝ) G
  have hdens_eq : ∀ z, dens z = ENNReal.ofReal (‖G z‖ ^ 2) *
      (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹ := by
    intro z
    have hcancel : ∀ x : EReal, ((k : ℝ) : EReal) * (((k⁻¹ : ℝ) : EReal) * x) = x := by
      intro x
      rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hkR.ne', EReal.coe_one, one_mul]
    simp only [dens, multiplierDensity, multiplierWeight, chartFunction,
      SGPT.IGood.DXMain.normalizedPotential, hcancel,
      SchemeLineBundleMetric.sectionLogNormSq, EReal.exp_neg, ENNReal.exp_log]
  have hnorm : ∀ z ∈ D, H.sectionNormSq b k s (e.val.symm z) = ‖G z‖ ^ 2 * Fn z ^ k := by
    intro z hz
    rw [H.sectionNormSq_frame b α k s _ hz.2, Complex.normSq_eq_norm_sq]
    rfl
  have hbound : ∀ z ∈ Metric.closedBall (e.val p) r', dens z ≤ ENNReal.ofReal ((μ ^ k)⁻¹) := by
    intro z hz
    have hzD := hcb hz
    rw [hdens_eq z, hnorm z hzD]
    by_cases hG : G z = 0
    · simp only [hG, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ENNReal.ofReal_zero, zero_mul, zero_le]
    · have ha : 0 < ‖G z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hG) 2
      have hb : 0 < Fn z ^ k := pow_pos (hFpos z hzD) k
      rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_div_div, div_self ha.ne', one_div]
      exact inv_anti₀ (pow_pos hm k) (pow_le_pow_left₀ hm.le (hmin hz) k)
  refine ⟨hkR, Metric.ball (e.val p) r', Metric.isOpen_ball, Metric.mem_ball_self hr', ?_, ?_, ?_⟩
  · intro z hz
    have hzD : z ∈ D := hcb (Metric.ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ _ hzD.2).mdifferentiableAt
      ).differentiableWithinAt
  · have hGc : ContinuousOn G (Metric.ball (e.val p) r') := by
      intro z hz
      have hzD : z ∈ D := hcb (Metric.ball_subset_closedBall hz)
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
        (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ _ hzD.2).mdifferentiableAt
        ).continuousAt.continuousWithinAt
    have hNc : ContinuousOn (fun z => H.sectionNormSq b k s (e.val.symm z))
        (Metric.ball (e.val p) r') :=
      ((H.sectionNormSq_chartSmooth b k s e).continuousOn).mono
        (fun z hz => (hcb (Metric.ball_subset_closedBall hz)).1)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (Metric.ball (e.val p) r')) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹)
        (volume.restrict (Metric.ball (e.val p) r')) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hNc.aemeasurable measurableSet_ball)).inv
    have hfun : dens = fun z => ENNReal.ofReal (‖G z‖ ^ 2) *
        (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹ := funext hdens_eq
    change AEMeasurable dens _
    rw [hfun]
    exact h1.mul h2
  · calc (∫⁻ y in Metric.ball (e.val p) r', dens y ∂volume)
        ≤ ∫⁻ _ in Metric.ball (e.val p) r', ENNReal.ofReal ((μ ^ k)⁻¹) ∂volume :=
          setLIntegral_mono measurable_const
            (fun z hz => hbound z (Metric.ball_subset_closedBall hz))
      _ = ENNReal.ofReal ((μ ^ k)⁻¹) * volume (Metric.ball (e.val p) r') :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- A section `s` of `L^k` (`k > 0`) lies in `H⁰(X, L^k ⊗ 𝓘(kψ))` for every quasi-psh `ψ` with
`k⁻¹ log |s|²_{h^k} ⪯ ψ`. -/
theorem isMultiplierSection_of_singularityLE (H : SchemeLineBundleMetric f (m + 1) E L)
    (b : LineBundleAtlas L) {k : ℕ} (hk : 0 < k) (s : bundlePowerGlobalSections L k)
    {ψ : SchemeComplexPoint f → EReal}
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) ψ)
    (hle : SGPT.PSH.SingularityLE (SGPT.IGood.DXMain.normalizedPotential f (m + 1) E b H k s) ψ) :
    IsMultiplierSection f (m + 1) E ψ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  have hself : IsMultiplierSection f (m + 1) E
      (SGPT.IGood.DXMain.normalizedPotential f (m + 1) E b H k s) k s := by
    right
    intro U α p hp
    exact ⟨schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ p hp,
      multiplierIntegrableAt_normalizedPotential H b hk s α p hp⟩
  exact Or.inr (SGPT.IGood.DXMain.isIdealSection_multiplierIdeal_of_singularityLE f (m + 1) E
    hψ hle hk hself)

end Multiplier

/-! ### The obstacle in degree `τ ≤ -C` -/

section Main

variable [IsIntegral X] [ConnectedSpace (SchemeComplexPoint f)]

local instance rwnMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance rwnBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}
  (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f (m + 1) E L)

omit [ConnectedSpace (SchemeComplexPoint f)] in
/-- For `τ < τ(𝓕)`, every `s ∈ 𝓕^{kτ}_k` lies in `H⁰(X, L^k ⊗ 𝓘(kψ_τ))`,
`ψ_τ = usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` (the book's argument for `eq:Gammatautheta`:
`log |s|²_{h^k} ≤ Γ^{𝓕,k}_τ ≤ k ψ_τ` after normalization). -/
theorem isMultiplierSection_obstacle {τ : ℝ} (hτ : (τ : EReal) < F.slope) {k : ℕ}
    {s : SectionSpace f L k} (hs : s ∈ F.piece ((k : ℝ) * τ) k) :
    IsMultiplierSection f (m + 1) E (F.obstacle H τ) k s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  let := E.isSeparated
  let := E.quasiCompact
  exact isMultiplierSection_of_singularityLE H a hk s
    (F.obstacle_isThetaPshPotential H hτ).1.quasiPlurisubharmonic
    (F.normalizedPotential_singularityLE_obstacle H hk hs)

omit [ConnectedSpace (SchemeComplexPoint f)] in
/-- For `τ < τ(𝓕)` with `τ ≤ -C`: `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) = H⁰(X, L^k)` for every `k`. -/
theorem multiplierH0_obstacle {τ : ℝ} (hτ : (τ : EReal) < F.slope) (hτC : τ ≤ -(F.bound : ℝ))
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (F.obstacle H τ)) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.IGood.DXMain.multiplierH0 f (m + 1) E hψ.1.quasiPlurisubharmonic L k = h0 f L k := by
  let := E.isSeparated
  let := E.quasiCompact
  have htop : SGPT.IGood.DXMain.multiplierSubmodule f (m + 1) E hψ.1.quasiPlurisubharmonic L k =
      ⊤ := by
    rw [eq_top_iff]
    intro s _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl rfl
    have hs : s ∈ F.piece ((k : ℝ) * τ) k := by
      rw [F.piece_eq_top_of_le_neg_bound hτC hk]
      exact Submodule.mem_top
    exact isMultiplierSection_obstacle F H hτ hs
  rw [SGPT.IGood.DXMain.multiplierH0, htop, finrank_top]
  rfl

omit [ConnectedSpace (SchemeComplexPoint f)] in
/-- **Source `ex:RWN`, first step of the proof of `eq:Gammatautheta`**: for `τ ≤ -C` (and
`τ < τ(𝓕)`), every section of `L^k` lies in `H⁰(X, L^k ⊗ 𝓘(kΓ^𝓕_τ))`:
`H⁰(X, L^k ⊗ 𝓘(kΓ^𝓕_τ)) = H⁰(X, L^k)` for every `k`. -/
theorem multiplierH0_testCurvePotential [Nonempty (SchemeComplexPoint f)] {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) (hτC : τ ≤ -(F.bound : ℝ)) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.IGood.DXMain.multiplierH0 f (m + 1) E
      (F.testCurvePotential_isThetaPshPotential H hτ).1.quasiPlurisubharmonic L k = h0 f L k := by
  let := E.isSeparated
  let := E.quasiCompact
  have hψ := F.obstacle_isThetaPshPotential H hτ
  have hΓ := F.testCurvePotential_isThetaPshPotential H hτ
  have hle : SGPT.PSH.SingularityLE (F.obstacle H τ) (F.testCurvePotential H τ) :=
    MoreSingularOn.of_le fun x _ => le_singularityEnvelope hψ (F.obstacle_le_zero H τ)
      ⟨0, fun y _ => by rw [EReal.coe_zero, add_zero]⟩ x
  have htop : SGPT.IGood.DXMain.multiplierSubmodule f (m + 1) E hΓ.1.quasiPlurisubharmonic L k =
      ⊤ := by
    rw [eq_top_iff]
    intro s _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl rfl
    have hs : s ∈ F.piece ((k : ℝ) * τ) k := by
      rw [F.piece_eq_top_of_le_neg_bound hτC hk]
      exact Submodule.mem_top
    exact Or.inr (SGPT.IGood.DXMain.isIdealSection_multiplierIdeal_of_singularityLE f (m + 1) E
      hΓ.1.quasiPlurisubharmonic hle hk (isMultiplierSection_obstacle F H hτ hs))
  rw [SGPT.IGood.DXMain.multiplierH0, htop, finrank_top]
  rfl

omit [SmoothOfRelativeDimension (m + 1) f] [IsIntegral X]
  [ConnectedSpace (SchemeComplexPoint f)] in
/-- If `vol L > 0`, then `H⁰(X, L^k) ≠ 0` for some `k > 0`. -/
theorem exists_nontrivial_of_volume_pos (hvol : 0 < SGPT.LineBundle.volume f L (m + 1)) :
    ∃ k : ℕ, 0 < k ∧ Nontrivial (SectionSpace f L k) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ k : ℕ, 0 < k → h0 f L k = 0 := by
    intro k hk
    have h : Subsingleton (SectionSpace f L k) := hcon k hk
    exact Module.finrank_zero_of_subsingleton
  apply hvol.ne'
  unfold SGPT.LineBundle.volume
  have hev : (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) /
      (k : ℝ≥0∞) ^ (m + 1)) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [hzero k hk]
    simp
  rw [limsup_congr hev, limsup_const]

omit [SmoothOfRelativeDimension (m + 1) f] [IsIntegral X]
  [ConnectedSpace (SchemeComplexPoint f)] in
/-- If `vol L > 0`, then `τ(𝓕) ≥ -C > -C - 1`. -/
theorem neg_bound_sub_one_lt_slope (hvol : 0 < SGPT.LineBundle.volume f L (m + 1)) :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  obtain ⟨k, hk, hnt⟩ := exists_nontrivial_of_volume_pos (f := f) hvol
  exact neg_bound_sub_one_lt_slope_of_nontrivial F hk hnt

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

include Y hY in
/-- **`vol L ≤ vol θ_{ψ_τ}` for `τ ≤ -C`** (`X` with a smooth flag): by the upper bound of
`thm:DXmain1` and `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) = H⁰(X, L^k)`. -/
theorem volume_le_iVolume_obstacle {τ : ℝ} (hτ : (τ : EReal) < F.slope)
    (hτC : τ ≤ -(F.bound : ℝ)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    SGPT.LineBundle.volume f L (m + 1) ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hψ := F.obstacle_isThetaPshPotential H hτ
  have h := SGPT.IGood.DXMain.limsup_multiplierH0_le f E Y hY a H hψ
  simp only [multiplierH0_obstacle F H hτ hτC hψ] at h
  exact h

include Y hY in
/-- **If `vol L > 0`, the obstacle `ψ_{-C-1}` is `𝓘`-good in the background `θ`**: it has
positive mass and `P_θ[ψ] = P_θ[ψ]_𝓘`. -/
theorem obstacle_iGoodWith_of_volume_pos (hvol : 0 < SGPT.LineBundle.volume f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IGoodWith (H.curvature a) (F.obstacle H (-(F.bound : ℝ) - 1))
      (F.obstacle_isThetaPshPotential H (neg_bound_sub_one_lt_slope F hvol)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hτ0 := neg_bound_sub_one_lt_slope F hvol
  have hψ := F.obstacle_isThetaPshPotential H hτ0
  have hgood := F.obstacle_iGood_of_lt_slope H hτ0
  have hvolψ := volume_le_iVolume_obstacle F H Y hY hτ0 (by linarith)
  have hw := iSingularityEnvelope_isThetaPshPotential (H.curvature a).val
    (H.curvature a).property.1 (H.curvature a).property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) _ hψ
  exact iGoodWith_of_iGood_of_iEnvelope_mass_pos (schemeProjectiveTNKahlerBackground f (m + 1) E)
    hψ hgood hw (hvol.trans_le hvolψ)

include Y hY in
/-- **Positive mass of the obstacle** (`vol L > 0`, smooth flag): for every `τ < τ(𝓕)`,
`∫_X θ_{ψ_τ}ⁿ > 0`. For `τ ≤ -C - 1` by monotonicity, otherwise by concavity of
`τ ↦ ψ_τ` and `∫ θ_{tu+(1-t)v}ⁿ ≥ tⁿ ∫ θ_uⁿ`. -/
theorem obstacle_hasPositiveMass (hvol : 0 < SGPT.LineBundle.volume f L (m + 1)) {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    HasPositivePotentialMass (H.curvature a) (F.obstacle H τ)
      (F.obstacle_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact obstacle_hasPositiveMass_of_pos F H (neg_bound_sub_one_lt_slope F hvol)
    (obstacle_iGoodWith_of_volume_pos F H Y hY hvol).positiveMass hτ

include Y hY in
/-- **Clause (a) of `ex:RWN`** (`RWNIModelClause`), for `L` big in the algebraic sense
(`vol L > 0`) on `X` with a smooth flag: every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model. The obstacle
`ψ_τ` is `𝓘`-good (`obstacle_iGood_of_lt_slope`) and has positive mass
(`obstacle_hasPositiveMass`), so `Γ^𝓕_τ = P_θ[ψ_τ] = P_θ[ψ_τ]_𝓘`, which is `𝓘`-model. -/
theorem rwnIModelClause_of_volume_pos (hvol : 0 < SGPT.LineBundle.volume f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact rwnIModelClause_of_obstacle_mass_pos F H (neg_bound_sub_one_lt_slope F hvol)
    (obstacle_iGoodWith_of_volume_pos F H Y hY hvol).positiveMass

include Y hY in
/-- Clause (a) of `ex:RWN` for `L` big in the section-growth sense (`h⁰(X, L^k) ≥ c kⁿ`,
`SGPT.LineBundle.IsBig`), on `X` with a smooth flag. -/
theorem rwnIModelClause_of_isBig (hL : SGPT.LineBundle.IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H :=
  rwnIModelClause_of_volume_pos F H Y hY hL.volume_pos

/-! ### Clause (b): `Γ^𝓕_τ = V_θ` for `τ ≤ -C` -/

omit [IsIntegral X] in
/-- The lower bound of `thm:DXmain1` at `V_θ` gives `∫_X θ_{V_θ}ⁿ = vol θ_{V_θ} ≤ vol L`
(the inequality `≥` of `cor:volbigL`). -/
theorem iVolume_thetaPshSupremum_le_volume [IsIntegral X]
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H hV) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (thetaPshSupremum (H.curvature a).val) hV ≤ SGPT.LineBundle.volume f L (m + 1) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  refine le_trans hlow ?_
  have heq : SGPT.IGood.DXMain.normalizedMultiplierH0 f E a H hV =
      fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1) := by
    funext k
    unfold SGPT.IGood.DXMain.normalizedMultiplierH0
    rw [SGPT.IGood.DXMain.multiplierH0_thetaPshSupremum f E a H hV k]
  rw [heq]
  exact liminf_le_limsup

/-- If `{θ}` is big and the lower bound of `thm:DXmain1` holds at `V_θ`, then `vol L > 0`. -/
theorem volume_pos_of_lowerBound
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig)) :
    0 < SGPT.LineBundle.volume f L (m + 1) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hmodel := SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum
    (schemeProjectiveTNKahlerBackground f (m + 1) E) (H.curvature a) hbig
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    (H.curvature a) hbig
  have hle := iVolume_thetaPshSupremum_le_volume H hV hlow
  rw [SGPT.IGood.Misc2VolBigL.iVolume_thetaPshSupremum] at hle
  exact hmodel.positive_mass.trans_le hle

include Y hY in
/-- **Clause (b) of `ex:RWN`** (`RWNMinimalClause`, `eq:Gammatautheta`), on `X` with a smooth flag,
`{θ}` big, conditional on the lower bound of `thm:DXmain1` at `V_θ`: `Γ^𝓕_τ = V_θ` for all
`τ ≤ -C`. Proof: `Γ^𝓕_τ = Γ^𝓕_{-C-1} = P_θ[ψ] = P_θ[ψ]_𝓘` (`ψ = ψ_{-C-1}` is `𝓘`-good in
`θ`), and `P_θ[ψ]_𝓘` is a model potential below `V_θ` with
`∫ θ_{P_θ[ψ]_𝓘}ⁿ = vol θ_ψ ≥ vol L ≥ ∫ θ_{V_θ}ⁿ`, hence equal to `V_θ` (`thm:Pvarphidiffdef`). -/
theorem rwnMinimalClause_of_lowerBound
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNMinimalClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set θ := H.curvature a with hθ
  let omega := schemeProjectiveTNKahlerBackground f (m + 1) E
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  have hvol := volume_pos_of_lowerBound H hbig hlow
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  intro τ hτC
  have hτ₀ := neg_bound_sub_one_lt_slope F hvol
  rw [F.testCurvePotential_eq_of_le_neg_bound H hτC (show -(F.bound : ℝ) - 1 ≤ -(F.bound : ℝ)
    by linarith)]
  have hψ := F.obstacle_isThetaPshPotential H hτ₀
  have hgw := obstacle_iGoodWith_of_volume_pos F H Y hY hvol
  change singularityEnvelope θ.val (F.obstacle H (-(F.bound : ℝ) - 1)) = _
  rw [hgw.envelope_eq]
  set w := iSingularityEnvelope θ.val (F.obstacle H (-(F.bound : ℝ) - 1)) with hw_def
  have hw : IsThetaPshPotential θ.val w :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2 hlocal _ hψ
  have hwV : w ≤ thetaPshSupremum θ.val := fun x =>
    le_thetaPshSupremum hw (iSingularityEnvelope_le_zero θ.val _) x
  have hvolψ := volume_le_iVolume_obstacle F H Y hY hτ₀ (by linarith)
  have hVvol := iVolume_thetaPshSupremum_le_volume H hV hlow
  rw [SGPT.IGood.Misc2VolBigL.iVolume_thetaPshSupremum] at hVvol
  have hmass_ge : diagonalPotentialMass θ (thetaPshSupremum θ.val) hV ≤
      diagonalPotentialMass θ w hw := hVvol.trans hvolψ
  have hmass_le : diagonalPotentialMass θ w hw ≤ diagonalPotentialMass θ (thetaPshSupremum θ.val) hV :=
    diagonalPotentialMass_mono_of_kahler omega hw hV (MoreSingularOn.of_le fun x _ => hwV x)
  have hwpos : HasPositivePotentialMass θ w hw := hvol.trans_le hvolψ
  have hVle := equalMassLeSingularityEnvelope omega θ w (thetaPshSupremum θ.val) hw hV hwpos
    (thetaPshSupremum_le_zero θ.val) (MoreSingularOn.of_le fun x _ => hwV x)
    (le_antisymm hmass_le hmass_ge)
  rw [hw_def, singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2 hlocal _
    hψ, ← hw_def] at hVle
  exact le_antisymm hwV hVle

include Y hY in
/-- **Clause (a) of `ex:RWN` with the book's notion of bigness** (`{c₁(L, h)}` big), on `X` with
a smooth flag, conditional on the lower bound of `thm:DXmain1` at `V_θ` (which gives `vol L > 0`,
`volume_pos_of_lowerBound`). -/
theorem rwnIModelClause_of_lowerBound
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H :=
  rwnIModelClause_of_volume_pos F H Y hY (volume_pos_of_lowerBound H hbig hlow)

end Main

/-! ### The conclusion of `ex:RWN` and `rmk:max_filt` -/

section Consequences

variable [IsIntegral X] [ConnectedSpace (SchemeComplexPoint f)]

local instance rwnMeasurable' : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance rwnBorel' : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}
  (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Conclusion of `ex:RWN`** (`X` with a smooth flag, `{θ}` big, conditional on the lower bound
of `thm:DXmain1` at `V_θ`): the family `Γ^𝓕 = (Γ^𝓕_τ)_{τ < τ(𝓕)}` is an `𝓘`-model test curve
based at `V_θ`, i.e. `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)`, and it is bounded. -/
theorem filtrationTestCurve_mem_iModel_and_isBounded_of_lowerBound
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig
        (rwnIModelClause_of_lowerBound F H Y hY hbig hlow)
        (rwnMinimalClause_of_lowerBound F H Y hY hbig hlow) ∈
      SourceIModelTestCurves (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) ∧
    SourceTestCurveIsBounded
      (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
      (SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig
        (rwnIModelClause_of_lowerBound F H Y hY hbig hlow)
        (rwnMinimalClause_of_lowerBound F H Y hY hbig hlow)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact ⟨SGPT.TestCurve.TestConf.filtrationTestCurve_mem_iModel F H hbig _ _,
    SGPT.TestCurve.TestConf.filtrationTestCurve_isBounded F H hbig _ _⟩

/-- **Source `rmk:max_filt`** (`X` with a smooth flag, `{θ}` big, conditional only on the lower
bound of `thm:DXmain1` at `V_θ`): the ray `Γ^{𝓕*}` induced by the filtration `𝓕` — the Legendre
transform of the actual family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` of `ex:RWN` — is a maximal geodesic ray
emanating from `V_θ`, for every Kähler background `ω` of `X^{an}`. The two open clauses of
`ex:RWN` used by `SGPT.TestCurve.TestConf.filtrationRay_mem_maximal_of_projective` are
`rwnIModelClause_of_lowerBound` and `rwnMinimalClause_of_lowerBound`. -/
theorem filtrationRay_mem_maximal_of_lowerBound
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hlow : SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig))
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground (m + 1) (SchemeComplexPoint f)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    sourceTestCurveLegendreRay (SGPT.TestCurve.TestConf.filtrationTestCurvePredata F H hbig
        (rwnIModelClause_of_lowerBound F H Y hY hbig hlow)
        (rwnMinimalClause_of_lowerBound F H Y hY hbig hlow)) ∈
      sourceMaximalGeodesicRays omega (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact SGPT.TestCurve.TestConf.filtrationRay_mem_maximal_of_projective F H hbig _ _ omega

end Consequences

end SGPT.TestCurve.RWN
