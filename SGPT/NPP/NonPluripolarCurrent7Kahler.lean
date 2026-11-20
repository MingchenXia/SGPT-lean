import SGPT.NPP.NonPluripolarCurrent7Mass
import SGPT.NPP.NonPluripolarCurrent4Opens
import SGPT.NPP.NonPluripolarClosedManifold
import SGPT.PSH.BookCurrentSpace
import SGPT.Currents.PluriharmonicPotential
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination

/-!
# Non-pluripolar products of closed positive `(1,1)`-currents on compact Kähler manifolds

Source: `chapter_npp.tex`, `prop:nppwelldef`: *on a compact Kähler manifold `X`, for closed
positive `(1,1)`-currents `T₁, …, T_p`, the non-pluripolar product `T₁ ∧ ⋯ ∧ T_p` is well defined*
(`def:npp:L146`).  Proof: Xia, *Foundations of pluripotential theory*,
`thm:compact-nonpluripolar-finiteness` ("Local finiteness"), with the uniform compact
truncation-mass estimate of BEGZ (`pro:finite`, `equ:welldef`) in top degree from
SGPT.Foundations.Analysis (`GlobalNonPluripolar.patch_uniformCompactTruncationMass`).

## The objects

* Closed positive `(1,1)`-currents on `X` are the book's `𝒵₊(X)`,
  `SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X` (`def:spaceofcurrents`, `def:pos_curr`: TN
  geometric currents, closed, of type `(1,1)`, weakly positive).
* `def:npp:L146` is formalized (`SGPT.NPP.IsCurrentProductWellDefined`) for S17's chart families
  `SGPT.NPP.PositiveCurrent (m + 1) X m` (positive currents of bidimension `(m,m)` given by their
  coordinate expressions `γ ↦ T(· γ)` on constant forms).  `readingCurrent T` is the chart family of
  `T ∈ 𝒵₊(X)`: in every chart `e` its expression is TN's reading `chartSpanCurrent T e`
  (`T(φ γ)` for test functions `φ` and constant `(m,m)`-forms `γ`); compatibility on overlaps is
  proved from a presentation `T = θ + dd^c u` (`chartSpanCurrent_thetaPotentialCurrent_compatible`).

## Main results

* `restrict_chartSpanCurrent_thetaPotentialCurrent` — near any point, in any chart, with any smooth
  local potential `ρ` of `θ`, the reading of `θ + dd^c u` is `dd^c (u ∘ e⁻¹ + ρ)` (`ddcL1`).
* `thetaReadingCurrent`, `readingCurrent`, `readingCurrent_eq` — the chart families.
* `isLocalPotential_patch` — on `e⁻¹(B)` the functions `uᵢ + ρᵢ ∘ e` are local potentials of the
  `θᵢ + dd^c uᵢ` (`IsLocalPotential`).
* `isNonPluripolarWellDefinedOn_of_chart` — well-definedness on an open subset of one chart domain
  follows from the local condition in that chart.
* `exists_ball_kahler_lower` — a Kähler form dominates `c ω₀` near every point of a chart.
* **`isCurrentProductWellDefined_thetaReadingCurrent`** — `prop:nppwelldef` for currents given by
  presentations `Tᵢ = θᵢ + dd^c uᵢ`, `uᵢ ∈ PSH(X, θᵢ)`;
* **`isCurrentProductWellDefined_readingCurrent`** — `prop:nppwelldef`: for all
  `T₁, …, T_p ∈ 𝒵₊(X)` on a compact Kähler manifold, `T₁ ∧ ⋯ ∧ T_p` is well defined.

The proof: at `x ∈ X` take a chart ball `B` on which `θᵢ = dd^c ρᵢ` and `ω = dd^c ρ ≥ c ω₀`
(`ρ ≥ 1`).  TN's top-degree estimate for the `n` global quasi-psh functions `(0, …, 0, u₁, …, u_p)`
with backgrounds `(ω, …, ω, θ₁, …, θ_p)` gives `sup_k μ_k(K) < ∞`, where `μ_k` is the mixed
Bedford–Taylor measure of `(ρ, …, ρ, (u₁ + ρ₁) ∨ (-k), …)` on the common strict locus; and
`μ_k ≥ c^q σ_{S_k}` there (`smul_traceMeasure_le_recursiveMixedTraceMeasure_of_eq`) for the truncated
products `S_k = ⋀ dd^c ((uᵢ + ρᵢ) ∨ (-k))`.  This is the Euclidean mass condition, equivalent to
`eq:welldefinepluri` (`isWellDefinedOn_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold ENNReal

namespace SGPT.NPP

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity
open SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
open SGPT.NPP.NonPluripolarCurrent
open SGPT.NPP.BedfordTaylorTopDegree

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-! ### A Kähler form dominates a multiple of the Euclidean form near every point -/

/-- The quadratic form `v ↦ β(v, i v)` is homogeneous of degree two. -/
theorem apply_smul_I_smul (β : RealForm (m + 1) 2) (t : ℝ) (w : ComplexModel (m + 1)) :
    β ![t • w, Complex.I • (t • w)] = t ^ 2 * β ![w, Complex.I • w] := by
  have e1 : (![t • w, Complex.I • (t • w)] : Fin 2 → ComplexModel (m + 1)) =
      fun i => t • (![w, Complex.I • w] : Fin 2 → ComplexModel (m + 1)) i := by
    funext i
    fin_cases i
    · rfl
    · exact smul_comm _ _ _
  rw [e1]
  have h := β.toContinuousMultilinearMap.map_smul_univ (fun _ => t) ![w, Complex.I • w]
  change β.toContinuousMultilinearMap (fun i => t • ![w, Complex.I • w] i) = _
  rw [h]
  simp [sq, smul_eq_mul]

/-- **A Kähler form dominates `c ω₀` near every point of a chart**: there are `c > 0` and a ball
`B(z₀, r)` in the chart domain with `ω(v, i v) ≥ c |v|²` on it. -/
theorem exists_ball_kahler_lower (ωK : KahlerBackground (m + 1) M) (e : ComplexChart (m + 1) M)
    {z₀ : ComplexModel (m + 1)} (hz₀ : z₀ ∈ e.val.target) :
    ∃ c : ℝ, 0 < c ∧ ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ e.val.target ∧
      ∀ z ∈ Metric.ball z₀ r, ∀ v : ComplexModel (m + 1),
        c * ‖v‖ ^ 2 ≤ ωK.form.val.coeff e z ![v, Complex.I • v] := by
  set β₀ := ωK.form.val.coeff e z₀ with hβ₀
  have hpos : ∀ v : ComplexModel (m + 1), v ≠ 0 → 0 < β₀ ![v, Complex.I • v] :=
    (ωK.isKahler.1 e z₀ hz₀).2
  have hcv : Continuous fun v : ComplexModel (m + 1) =>
      (![v, Complex.I • v] : Fin 2 → ComplexModel (m + 1)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id
    · exact continuous_const_smul Complex.I
  have hg : Continuous fun v : ComplexModel (m + 1) => β₀ ![v, Complex.I • v] :=
    β₀.coe_continuous.comp hcv
  set v₀ : ComplexModel (m + 1) := EuclideanSpace.single 0 1
  have hv₀ : v₀ ∈ Metric.sphere (0 : ComplexModel (m + 1)) 1 := by simp [v₀]
  obtain ⟨v₁, hv₁, hmin⟩ := (isCompact_sphere (0 : ComplexModel (m + 1)) 1).exists_isMinOn
    ⟨v₀, hv₀⟩ hg.continuousOn
  have hv₁0 : v₁ ≠ 0 := by
    rintro rfl
    simp at hv₁
  set a := β₀ ![v₁, Complex.I • v₁]
  have ha : 0 < a := hpos v₁ hv₁0
  have hlow0 : ∀ v : ComplexModel (m + 1), a * ‖v‖ ^ 2 ≤ β₀ ![v, Complex.I • v] := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [β₀.map_coord_zero (0 : Fin 2) rfl]
      simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set w := ‖v‖⁻¹ • v with hw_def
      have hw : w ∈ Metric.sphere (0 : ComplexModel (m + 1)) 1 := by
        rw [mem_sphere_zero_iff_norm, hw_def, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hn.ne']
      have hvw : v = ‖v‖ • w := by
        rw [hw_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h1 : β₀ ![v, Complex.I • v] = ‖v‖ ^ 2 * β₀ ![w, Complex.I • w] := by
        conv_lhs => rw [hvw]
        exact apply_smul_I_smul β₀ _ _
      have h2 : a ≤ β₀ ![w, Complex.I • w] := isMinOn_iff.mp hmin w hw
      rw [h1]
      nlinarith [sq_nonneg ‖v‖]
  have hcont : ContinuousAt (ωK.form.val.coeff e) z₀ :=
    (ωK.form.val.smooth e).continuousOn.continuousAt (e.val.open_target.mem_nhds hz₀)
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuousAt_iff.mp hcont (a / 2) (half_pos ha)
  obtain ⟨r₀, hr₀, hr₀t⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  refine ⟨a / 2, half_pos ha, min δ r₀, lt_min hδ hr₀,
    fun z hz => hr₀t (Metric.ball_subset_ball (min_le_right _ _) hz), fun z hz v => ?_⟩
  have hd : ‖ωK.form.val.coeff e z - β₀‖ < a / 2 := by
    rw [← dist_eq_norm]
    exact hδball (lt_of_lt_of_le hz (min_le_left _ _))
  have hb := (ωK.form.val.coeff e z - β₀).le_opNorm ![v, Complex.I • v]
  rw [Fin.prod_univ_two] at hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul, Complex.norm_I, one_mul,
    Real.norm_eq_abs, ContinuousAlternatingMap.sub_apply] at hb
  have h0 := hlow0 v
  have hab := abs_le.mp (hb.trans (le_refl _))
  nlinarith [sq_nonneg ‖v‖, norm_nonneg (ωK.form.val.coeff e z - β₀),
    mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖v‖)]

/-! ### Chart readings of `θ + dd^c u` -/

section Reading

/-- **The reading of `θ + dd^c u` near a point** (any chart `e`, any open `W` of `e`, any smooth
local potential `ρ` of `θ` on `W`): `u ∘ e⁻¹ + ρ` is psh and locally integrable on `W`, and the
restriction to `W` of the chart reading of `θ + dd^c u` is `dd^c (u ∘ e⁻¹ + ρ)`. -/
theorem restrict_chartSpanCurrent_thetaPotentialCurrent (θ : SmoothRealForm (m + 1) M 2)
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} {ρ : ComplexModel (m + 1) → ℝ}
    (hpot : IsSmoothLocalPotential θ e W ρ) :
    IsL1PshOn W (fun z => chartFunction u e z + (ρ z : EReal)) ∧
      restrict (show W ≤ chartTarget e from hpot.2.1)
          (chartSpanCurrent (thetaPotentialCurrent θ u hu) e) =
        ddcL1 W (fun z => chartFunction u e z + (ρ z : EReal)) := by
  obtain ⟨hp, -, hL, -, hreader, -⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader θ hu e ρ hpot
  refine ⟨isL1PshOn_of_exists_ne_bot hp ?_, ?_⟩
  · intro O hO hOW z hz
    have hzt : z ∈ e.val.target := hpot.2.1 (hOW hz)
    obtain ⟨y, hy, hyb⟩ := hu.2 (e.val.symm z) (e.val.source ∩ e.val ⁻¹' O)
      (e.val.isOpen_inter_preimage hO)
      ⟨e.val.map_target hzt, by simpa only [mem_preimage, e.val.right_inv hzt] using hz⟩
    refine ⟨e.val y, hy.2, ?_⟩
    simp only [chartFunction, e.val.left_inv hy.1]
    exact EReal.add_ne_bot_iff.mpr ⟨hyb, EReal.coe_ne_bot _⟩
  · rw [ddcL1, SGPT.Currents.l1Current_eq_scalarTopCurrent hL]
    exact hreader

/-- **The chart readings of `θ + dd^c u` are compatible on overlaps**: in S17's sense, the
expression in `e` is the pull-back of the expression in `f` along the coordinate change. -/
theorem chartSpanCurrent_thetaPotentialCurrent_compatible (θ : SmoothRealForm (m + 1) M 2)
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (e f : ComplexChart (m + 1) M) :
    restrict (overlapSource_le e f) (chartSpanCurrent (thetaPotentialCurrent θ u hu) e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (isPositive_chartSpanCurrent θ u hu f) (overlapTarget_le e f)) := by
  set T := thetaPotentialCurrent θ u hu
  have hh := chartTransition_isBiholomorphicPair e f
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro z hz
  have hz' : z ∈ (chartTransition e f).source := hz
  have hyt : chartTransition e f z ∈ (chartTransition e f).target :=
    (chartTransition e f).map_source hz'
  have hyf : chartTransition e f z ∈ f.val.target := (overlapTarget_le e f) hyt
  obtain ⟨Wf, ρf, hyW, hρf⟩ := hu.1.hasSmoothLocalPotentials f _ hyf
  let V : Opens (ComplexModel (m + 1)) :=
    ⟨Wf ∩ (chartTransition e f).target, hρf.1.inter (chartTransition e f).open_target⟩
  have hVB : V ≤ overlapTarget e f := fun y hy => hy.2
  let A := preOpen hh V
  have hAs : A ≤ overlapSource e f := preOpen_le hh V
  refine ⟨A, hAs, ⟨hz, hyW, hyt⟩, ?_⟩
  have hρV : IsSmoothLocalPotential θ f V ρf := hρf.mono V.isOpen fun y hy => hy.1
  have hρA : IsSmoothLocalPotential θ e A (ρf ∘ chartTransition e f) :=
    (ThetaPshChartLimitGluing.isSmoothLocalPotential_comp_transition e f hρf).mono A.isOpen
      fun x hx => ⟨hx.1, hx.2.1⟩
  obtain ⟨hLf, hrf⟩ := restrict_chartSpanCurrent_thetaPotentialCurrent θ hu f hρV
  obtain ⟨hLe, hre⟩ := restrict_chartSpanCurrent_thetaPotentialCurrent θ hu e hρA
  rw [restrict_restrict hAs (overlapSource_le e f), hre]
  have hh' := isBiholomorphicPair_preOpen hh hVB
  rw [← pullback_restrict hh _ hVB]
  have e1 : restrict hVB (restrict (overlapTarget_le e f) (chartSpanCurrent T f)) =
      ddcL1 V (fun z => chartFunction u f z + (ρf z : EReal)) := by
    rw [restrict_restrict]
    exact hrf
  rw [pullback_congr_current hh' _ hLf.isPositive_ddcL1 e1, pullback_ddcL1 hh' hLf]
  refine ddcL1_congr hLe.locallyIntegrableOn (hLf.comp hh').locallyIntegrableOn fun x hx => ?_
  simp only [chartFunction, Function.comp_apply]
  rw [chart_comp_transition u e f x (hAs hx)]

/-- **The chart family of `θ + dd^c u`** (`u ∈ PSH(X, θ)`): the S17 positive current of
bidimension `(m,m)` whose expression in a chart `e` is the reading `chartSpanCurrent` of TN's
geometric current `θ + dd^c u`. -/
def thetaReadingCurrent (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) : PositiveCurrent (m + 1) M m where
  inChart e := chartSpanCurrent (thetaPotentialCurrent θ u hu) e
  isPositive e := isPositive_chartSpanCurrent θ u hu e
  compatible e f := chartSpanCurrent_thetaPotentialCurrent_compatible θ hu e f

@[simp] theorem thetaReadingCurrent_inChart (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M) :
    (thetaReadingCurrent θ u hu).inChart e = chartSpanCurrent (thetaPotentialCurrent θ u hu) e :=
  rfl

/-- Compatibility of the readings of a geometric current with a presentation. -/
theorem chartSpanCurrent_compatible_of_eq {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal} {hu : IsThetaPshPotential θ u}
    (hT : T = thetaPotentialCurrent θ u hu) (hpos : ∀ e, IsPositive (chartSpanCurrent T e))
    (e f : ComplexChart (m + 1) M) :
    restrict (overlapSource_le e f) (chartSpanCurrent T e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (hpos f) (overlapTarget_le e f)) := by
  subst hT
  exact chartSpanCurrent_thetaPotentialCurrent_compatible θ hu e f

/-- The chart family of `θ + dd^c u` is closed (in every chart; locally it is `dd^c` of the psh
function `u ∘ e⁻¹ + ρ`). -/
theorem isClosed_thetaReadingCurrent (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) : (thetaReadingCurrent θ u hu).IsClosed := by
  intro e
  refine isClosedAny_of_local fun z hz => ?_
  obtain ⟨W, ρ, hzW, hρ⟩ := hu.1.hasSmoothLocalPotentials e z hz
  let V : Opens (ComplexModel (m + 1)) := ⟨W, hρ.1⟩
  have hρV : IsSmoothLocalPotential θ e V ρ := hρ
  refine ⟨V, hρ.2.1, hzW, ?_⟩
  rw [thetaReadingCurrent_inChart, (restrict_chartSpanCurrent_thetaPotentialCurrent θ hu e hρV).2]
  exact isClosedAny_ddcL1 _

variable [CompactSpace M]

/-- **The chart family of a closed positive `(1,1)`-current** `T ∈ 𝒵₊(X)` (`def:spaceofcurrents`):
the S17 positive current of bidimension `(m,m)` whose expression in a chart `e` is the reading
`γ ↦ T(· γ)` of `T` on constant `(m,m)`-forms (`chartSpanCurrent`). -/
def readingCurrent (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M) :
    PositiveCurrent (m + 1) M m where
  inChart e := chartSpanCurrent T.current e
  isPositive e := GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent T.current
    (SGPT.PSH.BookCurrent.isFullPositive_of_isPositiveCurrent T.current T.isClosed
      T.isTypeOneOne T.isPositive) e
  compatible e f := by
    obtain ⟨θ, u, hu, hT⟩ := SGPT.PSH.BookCurrent.exists_presentation T
    exact chartSpanCurrent_compatible_of_eq hT (fun e =>
      GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent T.current
        (SGPT.PSH.BookCurrent.isFullPositive_of_isPositiveCurrent T.current T.isClosed
          T.isTypeOneOne T.isPositive) e) e f

@[simp] theorem readingCurrent_inChart (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M)
    (e : ComplexChart (m + 1) M) : (readingCurrent T).inChart e = chartSpanCurrent T.current e :=
  rfl

/-- The chart family of `T` is that of any presentation `T = θ + dd^c u`. -/
theorem readingCurrent_eq {T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M}
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal} {hu : IsThetaPshPotential θ.val u}
    (hT : T.current = thetaPotentialCurrent θ.val u hu) :
    readingCurrent T = thetaReadingCurrent θ.val u hu :=
  PositiveCurrent.ext fun e => by rw [readingCurrent_inChart, thetaReadingCurrent_inChart, hT]

/-- The chart family of a closed positive `(1,1)`-current is closed. -/
theorem isClosed_readingCurrent (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M) :
    (readingCurrent T).IsClosed := by
  obtain ⟨θ, u, hu, hT⟩ := SGPT.PSH.BookCurrent.exists_presentation T
  rw [readingCurrent_eq hT]
  exact isClosed_thetaReadingCurrent θ.val u hu

end Reading

/-! ### Local potentials on a chart patch -/

section Patch

omit [IsComplexManifold (m + 1) M] in
/-- The open set `e⁻¹(B)` of `M` for an open `B` of the coordinate domain of `e`. -/
def patchSource (e : ComplexChart (m + 1) M) (B : Opens (ComplexModel (m + 1))) : Opens M :=
  ⟨e.val.source ∩ e.val ⁻¹' B, e.val.isOpen_inter_preimage B.isOpen⟩

omit [IsComplexManifold (m + 1) M] in
theorem patchSource_le_source (e : ComplexChart (m + 1) M) (B : Opens (ComplexModel (m + 1))) :
    ((patchSource e B : Opens M) : Set M) ⊆ e.val.source := fun _ hy => hy.1

omit [IsComplexManifold (m + 1) M] in
/-- The coordinate expression of `e⁻¹(B)` in `e` is `B`. -/
theorem chartDomain_patchSource (e : ComplexChart (m + 1) M) {B : Opens (ComplexModel (m + 1))}
    (hB : (B : Set (ComplexModel (m + 1))) ⊆ e.val.target) : chartDomain e (patchSource e B) = B := by
  ext z
  change z ∈ e.val.target ∧ e.val.symm z ∈ e.val.source ∧ e.val (e.val.symm z) ∈ B ↔ z ∈ B
  constructor
  · rintro ⟨hz, -, hzB⟩
    rwa [e.val.right_inv hz] at hzB
  · intro hz
    exact ⟨hB hz, e.val.map_target (hB hz), by rwa [e.val.right_inv (hB hz)]⟩

/-- A local potential in the chart `e` on `B` transports to the coordinate expression of
`e⁻¹(B)` in any chart `f`. -/
theorem isSmoothLocalPotential_chartDomain_patchSource {θ : SmoothRealForm (m + 1) M 2}
    (e : ComplexChart (m + 1) M) {B : Opens (ComplexModel (m + 1))} {ρ : ComplexModel (m + 1) → ℝ}
    (hρ : IsSmoothLocalPotential θ e B ρ) (f : ComplexChart (m + 1) M) :
    IsSmoothLocalPotential θ f (chartDomain f (patchSource e B)) (ρ ∘ chartTransition f e) := by
  refine (ThetaPshChartLimitGluing.isSmoothLocalPotential_comp_transition f e hρ).mono
    (chartDomain f (patchSource e B)).isOpen fun z hz => ?_
  have hz' : z ∈ f.val.target ∧ f.val.symm z ∈ e.val.source ∧ e.val (f.val.symm z) ∈ B := hz
  refine ⟨?_, hz'.2.2⟩
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
  exact ⟨hz'.1, hz'.2.1⟩

/-- **Local potentials on a chart patch**: if `ρᵢ` are smooth local potentials of `θᵢ` on an open
`B` of the chart `e`, then `uᵢ + ρᵢ ∘ e` are local potentials of the currents `θᵢ + dd^c uᵢ` on
`e⁻¹(B)` (`IsLocalPotential`: psh on `e⁻¹(B)` and `dd^c (uᵢ + ρᵢ ∘ e) = θᵢ + dd^c uᵢ` there, in every
chart). -/
theorem isLocalPotential_patch {p : ℕ} (θ : Fin p → SmoothRealForm (m + 1) M 2)
    (u : Fin p → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i) (u i))
    (e : ComplexChart (m + 1) M) {B : Opens (ComplexModel (m + 1))}
    (ρ : Fin p → ComplexModel (m + 1) → ℝ) (hρ : ∀ i, IsSmoothLocalPotential (θ i) e B (ρ i)) :
    IsLocalPotential (fun i => thetaReadingCurrent (θ i) (u i) (hu i)) (patchSource e B)
      (fun i y => u i y + (ρ i (e.val y) : EReal)) where
  psh i := by
    refine (SGPT.PSH.VariableComplexAtlas.isPSHOn_iff_chart_and_nondegenerate
      (patchSource e B).isOpen).mpr ⟨fun f => ?_, ?_⟩
    · exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hu i).1 f
        (isSmoothLocalPotential_chartDomain_patchSource e (hρ i) f)
    · intro x hx O hO hxO
      obtain ⟨y, hy, hyb⟩ := (hu i).2 x (patchSource e B ∩ O) ((patchSource e B).isOpen.inter hO)
        ⟨hx, hxO⟩
      exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyb, EReal.coe_ne_bot _⟩⟩
  ddc i f :=
    (restrict_chartSpanCurrent_thetaPotentialCurrent (θ i) (hu i) f
      (isSmoothLocalPotential_chartDomain_patchSource e (hρ i) f)).2

end Patch

/-! ### Well-definedness from one chart -/

/-- **Well-definedness on an open subset of one chart domain** (`IsNonPluripolarWellDefinedOn`,
in every chart) follows from the local condition `eq:welldefinepluri` in that chart (biholomorphic
invariance, `isWellDefinedOn_preOpen_overlapDomain`). -/
theorem isNonPluripolarWellDefinedOn_of_chart {p q : ℕ} (hqp : q + p = m + 1)
    {φ : Fin p → M → EReal} {O : Opens M}
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O)
    (e : ComplexChart (m + 1) M) (hOe : (O : Set M) ⊆ e.val.source)
    (hW : IsWellDefinedOn hqp (chartDomain e O) fun i z => φ i (e.val.symm z)) :
    IsNonPluripolarWellDefinedOn hqp φ O := by
  intro f
  have h := isWellDefinedOn_preOpen_overlapDomain O hqp hφ f e hW
  have hset : preOpen (chartTransition_isBiholomorphicPair f e) (overlapDomain f e O) =
      chartDomain f O := by
    ext z
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_preOpen_overlapDomain]
    exact ⟨fun h => h.1, fun h => ⟨h, hOe h.2⟩⟩
  rwa [hset] at h

/-! ### `prop:nppwelldef` -/

section Main

variable [CompactSpace M]

/-- **`prop:nppwelldef`, potential form**: on a compact Kähler manifold, for closed smooth real
`(1,1)`-forms `θᵢ` and `uᵢ ∈ PSH(X, θᵢ)`, the non-pluripolar product of the currents
`Tᵢ = θᵢ + dd^c uᵢ` is well defined (`def:npp:L146`). -/
theorem isCurrentProductWellDefined_thetaReadingCurrent (ωK : KahlerBackground (m + 1) M)
    {p q : ℕ} (hqp : q + p = m + 1) (θ : Fin p → ClosedRealOneOneForm (m + 1) M)
    (u : Fin p → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) :
    IsCurrentProductWellDefined hqp fun i => thetaReadingCurrent (θ i).val (u i) (hu i) := by
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  set T := fun i => thetaReadingCurrent (θ i).val (u i) (hu i)
  refine ⟨{O | ∃ φ, IsLocalPotential T O φ ∧ IsNonPluripolarWellDefinedOn hqp φ O},
    fun x => ?_, fun O hO => hO⟩
  set e : ComplexChart (m + 1) M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hx
  choose W ρ hzW hρ using fun i => (hu i).1.hasSmoothLocalPotentials e z₀ hz₀
  obtain ⟨WωK, ρωK, hzWωK, hρωK⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials ωK.form e z₀ hz₀
  obtain ⟨c, hc, r₁, hr₁, hr₁t, hlow⟩ := exists_ball_kahler_lower ωK e hz₀
  have hopen : IsOpen (WωK ∩ ⋂ i, W i) := hρωK.1.inter (isOpen_iInter_of_finite fun i => (hρ i).1)
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp hopen z₀ ⟨hzWωK, mem_iInter.mpr hzW⟩
  set r := min r₁ r₂ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hcl : Metric.closedBall z₀ r ⊆ Metric.ball z₀ r₁ ∩ (WωK ∩ ⋂ i, W i) := by
    intro z hz
    have hz' : dist z z₀ < min r₁ r₂ := lt_of_le_of_lt (Metric.mem_closedBall.mp hz)
      (by rw [hr_def]; linarith [lt_min hr₁ hr₂])
    exact ⟨Metric.mem_ball.mpr (lt_of_lt_of_le hz' (min_le_left _ _)),
      hball (Metric.mem_ball.mpr (lt_of_lt_of_le hz' (min_le_right _ _)))⟩
  let B : Opens (ComplexModel (m + 1)) := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
  have hBcl : (B : Set (ComplexModel (m + 1))) ⊆ Metric.closedBall z₀ r :=
    Metric.ball_subset_closedBall
  have hBt : (B : Set (ComplexModel (m + 1))) ⊆ e.val.target := fun z hz =>
    hr₁t (hcl (hBcl hz)).1
  have hBW : ∀ i, (B : Set (ComplexModel (m + 1))) ⊆ W i := fun i z hz =>
    mem_iInter.mp (hcl (hBcl hz)).2.2 i
  have hBWωK : (B : Set (ComplexModel (m + 1))) ⊆ WωK := fun z hz => (hcl (hBcl hz)).2.1
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
    (hρωK.2.2.1.continuousOn.mono fun z hz => (hcl hz).2.1)
  set ρ' : ComplexModel (m + 1) → ℝ := fun z => ρωK z + (C + 1) with hρ'_def
  have hρ'1 : ∀ z ∈ (B : Set (ComplexModel (m + 1))), 1 ≤ ρ' z := by
    intro z hz
    have h := hC z (hBcl hz)
    rw [Real.norm_eq_abs, abs_le] at h
    simp only [hρ'_def]
    linarith [h.1]
  have hρ'smooth : ContDiffOn ℝ ∞ ρ' B := (hρωK.2.2.1.mono hBWωK).add contDiffOn_const
  have hρ'ddc : ∀ z ∈ (B : Set (ComplexModel (m + 1))), smoothDDC ρ' z = ωK.form.val.coeff e z := by
    intro z hz
    rw [hρ'_def, smoothDDC_add B.isOpen (hρωK.2.2.1.mono hBWωK) contDiffOn_const hz,
      GlobalPotentialTransforms.smoothDDC_const, add_zero]
    exact hρωK.2.2.2 (hBWωK hz)
  have hρ'pot : IsSmoothLocalPotential ωK.form.val e B ρ' :=
    ⟨B.isOpen, hBt, hρ'smooth, fun z hz => hρ'ddc z hz⟩
  have hρpot : ∀ i, IsSmoothLocalPotential (θ i).val e B (ρ i) := fun i =>
    (hρ i).mono B.isOpen (hBW i)
  -- the top-degree data of TN: backgrounds `(ωK, …, ωK, θ₁, …, θ_p)`, potentials `(0, …, 0, u)`
  let Θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M := fun j =>
    Fin.append (fun _ : Fin q => ωK.form) θ (Fin.cast hqp.symm j)
  let U' : Fin (m + 1) → M → EReal := fun j =>
    Fin.append (fun _ : Fin q => fun _ : M => (0 : EReal)) u (Fin.cast hqp.symm j)
  let pot : Fin (m + 1) → ComplexModel (m + 1) → ℝ := fun j =>
    Fin.append (fun _ : Fin q => ρ') ρ (Fin.cast hqp.symm j)
  have hΘ : ∀ j, ThetaPlurisubharmonic (Θ j).val (U' j) := fun j =>
    Fin.addCases (motive := fun k => ThetaPlurisubharmonic
        (Fin.append (fun _ : Fin q => ωK.form) θ k).val
        (Fin.append (fun _ : Fin q => fun _ : M => (0 : EReal)) u k))
      (fun i => by
        simp only [Fin.append_left]
        exact (PluripolarCapacityDichotomy.isThetaPshPotential_zero ωK).1)
      (fun i => by
        simp only [Fin.append_right]
        exact (hu i).1) (Fin.cast hqp.symm j)
  have hpotP : ∀ j, IsSmoothLocalPotential (Θ j).val e B (pot j) := fun j =>
    Fin.addCases (motive := fun k => IsSmoothLocalPotential
        (Fin.append (fun _ : Fin q => ωK.form) θ k).val e B
        (Fin.append (fun _ : Fin q => ρ') ρ k))
      (fun i => by
        simp only [Fin.append_left]
        exact hρ'pot)
      (fun i => by
        simp only [Fin.append_right]
        exact hρpot i) (Fin.cast hqp.symm j)
  have hpshP : ∀ j, PlurisubharmonicOn
      (fun z => chartFunction (U' j) e z + (pot j z : EReal)) B := fun j =>
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hΘ j) e
      (hpotP j)
  let P : GlobalPotentialPatches.Patch Θ U' :=
    { chart := e
      domain := B
      domain_le_target := hBt
      potential := pot
      localPotential := hpotP
      plurisubharmonic := hpshP }
  have hmass := GlobalNonPluripolar.patch_uniformCompactTruncationMass ωK hΘ P
  -- the local potentials of `T` on `e⁻¹(B)`
  set φ : Fin p → M → EReal := fun i y => u i y + (ρ i (e.val y) : EReal) with hφ_def
  have hpot : IsLocalPotential T (patchSource e B) φ :=
    isLocalPotential_patch (fun i => (θ i).val) u hu e ρ hρpot
  refine ⟨patchSource e B, ⟨φ, hpot, ?_⟩, hx, Metric.mem_ball_self hr⟩
  refine isNonPluripolarWellDefinedOn_of_chart hqp hpot.psh e (patchSource_le_source e B) ?_
  rw [chartDomain_patchSource e hBt]
  -- the local condition on `B`
  set ψ : Fin p → ComplexModel (m + 1) → EReal := fun i z => φ i (e.val.symm z) with hψ_def
  have hψ : ∀ z ∈ (B : Set (ComplexModel (m + 1))), ∀ i,
      ψ i z = chartFunction (u i) e z + (ρ i z : EReal) := by
    intro z hz i
    simp only [hψ_def, hφ_def, chartFunction, e.val.right_inv (hBt hz)]
  have hψpsh : ∀ i, PlurisubharmonicOn (ψ i) B := by
    intro i
    have h := hpot.chartPsh e i
    rw [chartDomain_patchSource e hBt] at h
    exact h
  have hcorr : ∀ z ∈ (B : Set (ComplexModel (m + 1))), ∀ j, P.corrected j z =
      Fin.append (fun _ : Fin q => ((ρ' z : ℝ) : EReal)) (fun i => ψ i z) (Fin.cast hqp.symm j) := by
    intro z hz j
    change chartFunction (U' j) e z + (pot j z : EReal) = _
    refine Fin.addCases (motive := fun k =>
        chartFunction (Fin.append (fun _ : Fin q => fun _ : M => (0 : EReal)) u k) e z +
          ((Fin.append (fun _ : Fin q => ρ') ρ k z : ℝ) : EReal) =
        Fin.append (fun _ : Fin q => ((ρ' z : ℝ) : EReal)) (fun i => ψ i z) k)
      (fun i => ?_) (fun i => ?_) (Fin.cast hqp.symm j)
    · simp only [Fin.append_left, chartFunction, zero_add]
    · simp only [Fin.append_right]
      exact (hψ z hz i).symm
  have hlocus : ∀ k : ℕ, BedfordTaylorTopDegree.strictLocus B ψ k =
      commonStrictLocus B P.corrected k := by
    intro k
    ext z
    simp only [BedfordTaylorTopDegree.strictLocus, commonStrictLocus]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun j => ?_⟩
      rw [hcorr z hz j]
      refine Fin.addCases (motive := fun k' => ((-(k : ℝ) : ℝ) : EReal) <
          Fin.append (fun _ : Fin q => ((ρ' z : ℝ) : EReal)) (fun i => ψ i z) k')
        (fun i => ?_) (fun i => ?_) (Fin.cast hqp.symm j)
      · rw [Fin.append_left, EReal.coe_lt_coe_iff]
        linarith [hρ'1 z hz, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      · rw [Fin.append_right]
        exact h i
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun i => ?_⟩
      have h1 := h (Fin.cast hqp (Fin.natAdd q i))
      rw [hcorr z hz] at h1
      have e1 : Fin.cast hqp.symm (Fin.cast hqp (Fin.natAdd q i)) = Fin.natAdd q i := Fin.ext rfl
      rwa [e1, Fin.append_right] at h1
  -- the Euclidean mass condition
  rw [isWellDefinedOn_iff hqp hψpsh, (isTruncationFamily hqp hψpsh).hasLocallyFiniteMass_iff]
  intro K hK hKB
  obtain ⟨Cm, hCm, hCk⟩ := hmass K hK hKB
  have hcq : (0 : ℝ) < c ^ q := pow_pos hc q
  have hcq' : ENNReal.ofReal (c ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr hcq).ne'
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.div_lt_top hCm.ne hcq')
  rw [ENNReal.le_div_iff_mul_le (Or.inl hcq') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  refine le_trans ?_ (hCk k)
  -- `c^q σ_{S_k} ≤ μ_k` on the strict locus
  set v : Fin p → ComplexModel (m + 1) → ℝ := fun i => truncationReal (ψ i) k with hv_def
  have hv : ∀ i, IsLocallyBoundedPshOn B (v i) := fun i =>
    truncationReal_isLocallyBoundedPshOn (hψpsh i) k
  have hρ'psh : IsLocallyBoundedPshOn B ρ' :=
    LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
      (SmoothPotentialDomination.plurisubharmonicOn_coe_of_smoothDDC_nonneg B.isOpen hρ'smooth
        fun z hz w => by
          rw [hρ'ddc z hz]
          exact ωK.isSemipositive e z (hBt hz) w)
      hρ'smooth.continuousOn
  have hquad : ContDiffOn ℝ ∞ (fun z => c * quadPot (kahlerForm (m + 1)) z) B :=
    (contDiffOn_const.mul (contDiff_quadPot _).contDiffOn)
  have hρc : IsLocallyBoundedPshOn B fun z => ρ' z - c * quadPot (kahlerForm (m + 1)) z := by
    refine LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
      (SmoothPotentialDomination.plurisubharmonicOn_coe_of_smoothDDC_nonneg B.isOpen
        (hρ'smooth.sub hquad) fun z hz w => ?_) (hρ'smooth.sub hquad).continuousOn
    rw [smoothDDC_sub B.isOpen hρ'smooth hquad hz, hρ'ddc z hz]
    have e2 : (fun z => c * quadPot (kahlerForm (m + 1)) z) = quadPot (c • kahlerForm (m + 1)) :=
      (quadPot_smul c _).symm
    rw [e2, smoothDDC_quadPot ((isSemipositiveOneOne_kahlerForm.smul hc.le).1)]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, kahlerForm_apply_I]
    linarith [hlow z (hcl (hBcl hz)).1 w]
  set w : Fin (m + 1) → ComplexModel (m + 1) → ℝ := fun j =>
    Fin.append (fun _ : Fin q => ρ') v (Fin.cast hqp.symm j) with hw_def
  have hw : ∀ j, IsLocallyBoundedPshOn B (w j) := fun j =>
    isLocallyBoundedPshOn_append (fun _ => hρ'psh) hv (Fin.cast hqp.symm j)
  have hle := smul_traceMeasure_le_recursiveMixedTraceMeasure_of_eq hqp hv hc.le hρc w hw
    (fun j => rfl)
  have hwcorr : ∀ j, ∀ z ∈ (B : Set (ComplexModel (m + 1))),
      w j z = mixedTruncationReal P.corrected k j z := by
    intro j z hz
    simp only [mixedTruncationReal, truncationReal, truncation, hw_def]
    rw [hcorr z hz j]
    refine Fin.addCases (motive := fun k' => Fin.append (fun _ : Fin q => ρ') v k' z =
        (max (Fin.append (fun _ : Fin q => ((ρ' z : ℝ) : EReal)) (fun i => ψ i z) k')
          ((-(k : ℝ) : ℝ) : EReal)).toReal) (fun i => ?_) (fun i => ?_) (Fin.cast hqp.symm j)
    · rw [Fin.append_left, Fin.append_left, max_eq_left (EReal.coe_le_coe_iff.mpr
        (by linarith [hρ'1 z hz, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])), EReal.toReal_coe]
    · rw [Fin.append_right, Fin.append_right]
      rfl
  have hmeas : SGPT.Foundations.Analysis.Pending.MixedNonPluripolar.mixedTruncationMeasure B P.corrected P.plurisubharmonic k K =
      recursiveMixedTraceMeasure B w hw (K ∩ BedfordTaylorTopDegree.strictLocus B ψ k) := by
    unfold SGPT.Foundations.Analysis.Pending.MixedNonPluripolar.mixedTruncationMeasure
    rw [Measure.restrict_apply hK.measurableSet,
      LocalBedfordTaylorCanonicalTraceMeasure.canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure,
      hlocus k]
    exact congrArg (fun μ : Measure (ComplexModel (m + 1)) => μ (K ∩ commonStrictLocus B P.corrected k))
      (recursiveMixedTraceMeasure_congr _ hw fun j z hz => (hwcorr j z hz).symm)
  rw [hmeas, ← smul_eq_mul, ← Measure.smul_apply]
  exact Measure.le_iff'.mp hle _

/-- **`prop:nppwelldef`**: on a compact Kähler manifold `X` (a compact complex manifold of
dimension `m + 1` with a Kähler form `ωK`), for closed positive `(1,1)`-currents
`T₁, …, T_p ∈ 𝒵₊(X)`, the non-pluripolar product `T₁ ∧ ⋯ ∧ T_p` is well defined
(`def:npp:L146`, for the chart families `readingCurrent Tᵢ` of the currents). -/
theorem isCurrentProductWellDefined_readingCurrent (ωK : KahlerBackground (m + 1) M)
    {p q : ℕ} (hqp : q + p = m + 1) (T : Fin p → SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M) :
    IsCurrentProductWellDefined hqp fun i => readingCurrent (T i) := by
  choose θ u hpres using fun i => SGPT.PSH.BookCurrent.exists_presentation (T i)
  choose hu hT using hpres
  have e : (fun i => readingCurrent (T i)) = fun i => thetaReadingCurrent (θ i).val (u i) (hu i) :=
    funext fun i => readingCurrent_eq (hT i)
  rw [e]
  exact isCurrentProductWellDefined_thetaReadingCurrent ωK hqp θ u hu

/-- **The non-pluripolar product `T₁ ∧ ⋯ ∧ T_p`** (`def:npp:L146`) of closed positive
`(1,1)`-currents on a compact Kähler manifold, well defined by `prop:nppwelldef`
(`isCurrentProductWellDefined_readingCurrent`); a positive current of bidimension `(q,q)`. -/
def kahlerCurrentProduct (ωK : KahlerBackground (m + 1) M) {p q : ℕ} (hqp : q + p = m + 1)
    (T : Fin p → SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M) : PositiveCurrent (m + 1) M q :=
  currentProduct hqp (fun i => readingCurrent (T i))
    (isCurrentProductWellDefined_readingCurrent ωK hqp T)

/-- `T₁ ∧ ⋯ ∧ T_p` is closed (`def:npp:L146`: "the closed positive `(p,p)`-current"). -/
theorem isClosed_kahlerCurrentProduct (ωK : KahlerBackground (m + 1) M) {p q : ℕ}
    (hqp : q + p = m + 1) (T : Fin p → SGPT.PSH.BookCurrent.ClosedPositiveCurrent m M) :
    (kahlerCurrentProduct ωK hqp T).IsClosed :=
  isClosed_currentProduct hqp _

end Main

end SGPT.NPP
