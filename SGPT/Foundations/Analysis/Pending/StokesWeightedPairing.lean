import SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction
import SGPT.Foundations.Analysis.Pending.PatchParameterNull
import SGPT.Foundations.Analysis.Pending.BedfordTaylorInduction
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false

/-!
# Weighted-pairing data for any finite regular-piece family

Blueprint `ana:stokes-weighted-pairing-data` (TN.4 #4, Stokes against `[V]`, part A of
Stokes' theorem on the regular locus).

`FiniteTelescopeLocalWeightedPairing.FiniteTelescopeLocalWeightedPairingData T` asks, for every
piece `Sᵢ` of a finite regular-piece family `G` with telescope data `T`, a finite Borel measure on
`M` of the form `(γᵢ)_*(ρᵢ · vol|_{Sᵢ})` (`γᵢ` the patch parametrization) and a test function
`tᵢ ∈ C_c(M, ℝ)` with `fᵢ = ρᵢ · (tᵢ ∘ γᵢ)` a.e. on `Sᵢ`, where `fᵢ = T.telescopeIntegrand i`.
Integrability of `fᵢ` on `Sᵢ` is necessary (`|tᵢ|` is bounded and the measure is finite); this
module shows it is sufficient (`M` compact):

* `exhaustFun`, `isCompact_exhaustFun_le`: `g(w) = d(w, Ωᶜ)⁻¹ + ‖w‖` is continuous on an open
  `Ω` of a proper space and its sublevel sets in `Ω` are compact.
* `exists_properWeight`: for a finite measure `μ` there is a continuous `ψ ≥ 1` on `Ω` with
  `∫ ψ dμ < ∞` and `ψ → ∞` off the compacts of `Ω` (`ψ = Φ ∘ g`, `Φ = 1 + ∑ 2ˡ clamp(· - tₗ)`
  with `μ{g > tₗ} ≤ 4⁻ˡ`).
* `parameterOf`: the inverse `y ↦ pr(Φ(e y))` of a regular patch on the trace of an open set
  of `M` on `V`; `exists_continuousMap_toManifold_eq`: a function continuous on an open `Ω` of
  parameters and tending to `0` off the compacts of `Ω` is `t ∘ γ` on `Ω` for some `t ∈ C(M, ℝ)`
  (extension by `0` on `V`, then Tietze).
* `nonempty_finiteTelescopeLocalWeightedPairingData`: with `u = (1 + ‖w‖)^{-(2k+1)} + |f|`
  (`k = dim V`), `ρ = ψ u` and `t ∘ γ = f / (ψ u)`.
* `finiteTelescopePairingRemainderData_of_integrableOn`, `..._of_finite`: hence the
  pairing-remainder datum of every finite family with remainder `|∑ᵢ ∫_{Sᵢ} fᵢ|`, the
  integrability coming from finiteness of the two masses.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.StokesWeightedPairing

noncomputable section

/-! ### An exhaustion function of an open set, and a proper integrable weight -/

section Weight

variable {E : Type*} [NormedAddCommGroup E]

/-- The exhaustion function `g(w) = d(w, Ωᶜ)⁻¹ + ‖w‖` of an open set `Ω` (when `Ω = univ` the
first term is `0`). -/
def exhaustFun (Ω : Set E) (w : E) : ℝ :=
  (infDist w Ωᶜ)⁻¹ + ‖w‖

theorem norm_le_exhaustFun (Ω : Set E) (w : E) : ‖w‖ ≤ exhaustFun Ω w :=
  le_add_of_nonneg_left (inv_nonneg.mpr infDist_nonneg)

theorem continuous_infDist_inv_on {Ω : Set E} (hΩ : IsOpen Ω) :
    ContinuousOn (fun w => (infDist w Ωᶜ)⁻¹) Ω := by
  rcases (Ωᶜ).eq_empty_or_nonempty with h | h
  · simp only [h, infDist_empty, inv_zero]
    exact continuousOn_const
  · refine ((continuous_infDist_pt _).continuousOn).inv₀ fun w hw => ?_
    exact ((hΩ.isClosed_compl.notMem_iff_infDist_pos h).mp (not_not.mpr hw)).ne'

theorem continuousOn_exhaustFun {Ω : Set E} (hΩ : IsOpen Ω) : ContinuousOn (exhaustFun Ω) Ω :=
  (continuous_infDist_inv_on hΩ).add continuous_norm.continuousOn

theorem measurable_exhaustFun [MeasurableSpace E] [BorelSpace E] (Ω : Set E) :
    Measurable (exhaustFun Ω) :=
  (continuous_infDist_pt _).measurable.inv.add continuous_norm.measurable

/-- The sublevel sets of the exhaustion function inside `Ω` are compact. -/
theorem isCompact_exhaustFun_le [ProperSpace E] {Ω : Set E} (hΩ : IsOpen Ω) (c : ℝ) :
    IsCompact {w | w ∈ Ω ∧ exhaustFun Ω w ≤ c} := by
  have hbdd : Bornology.IsBounded {w | w ∈ Ω ∧ exhaustFun Ω w ≤ c} :=
    (isBounded_closedBall (x := (0 : E)) (r := c)).subset fun w hw => by
      rw [mem_closedBall, dist_zero_right]
      exact (norm_le_exhaustFun Ω w).trans hw.2
  refine isCompact_of_isClosed_isBounded ?_ hbdd
  rcases (Ωᶜ).eq_empty_or_nonempty with h | h
  · have hΩu : Ω = univ := compl_empty_iff.mp h
    have : {w | w ∈ Ω ∧ exhaustFun Ω w ≤ c} = univ ∩ exhaustFun Ω ⁻¹' Iic c := by
      ext w; simp [hΩu]
    rw [this]
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_univ isClosed_Iic
    rw [← hΩu]; exact continuousOn_exhaustFun hΩ
  · rcases le_or_gt c 0 with hc | hc
    · have : {w | w ∈ Ω ∧ exhaustFun Ω w ≤ c} = ∅ := by
        ext w
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
        intro hw
        have hpos : 0 < infDist w Ωᶜ :=
          (hΩ.isClosed_compl.notMem_iff_infDist_pos h).mp (not_not.mpr hw)
        exact hc.trans_lt (add_pos_of_pos_of_nonneg (inv_pos.mpr hpos) (norm_nonneg w))
      rw [this]; exact isClosed_empty
    · set F : Set E := {w | c⁻¹ ≤ infDist w Ωᶜ} with hF
      have hFc : IsClosed F := isClosed_le continuous_const (continuous_infDist_pt _)
      have hFΩ : F ⊆ Ω := fun w hw => by
        by_contra hw'
        have : infDist w Ωᶜ = 0 := infDist_zero_of_mem hw'
        have := hw.trans_eq this
        exact (inv_pos.mpr hc).not_ge this
      have heq : {w | w ∈ Ω ∧ exhaustFun Ω w ≤ c} = F ∩ exhaustFun Ω ⁻¹' Iic c := by
        ext w
        constructor
        · rintro ⟨hw, hle⟩
          refine ⟨?_, hle⟩
          have hpos : 0 < infDist w Ωᶜ :=
            (hΩ.isClosed_compl.notMem_iff_infDist_pos h).mp (not_not.mpr hw)
          have h1 : (infDist w Ωᶜ)⁻¹ ≤ c :=
            (le_add_of_nonneg_right (norm_nonneg w)).trans hle
          show c⁻¹ ≤ infDist w Ωᶜ
          rw [inv_le_comm₀ hc hpos]; exact h1
        · rintro ⟨hw, hle⟩
          exact ⟨hFΩ hw, hle⟩
      rw [heq]
      exact ((continuousOn_exhaustFun hΩ).mono hFΩ).preimage_isClosed_of_isClosed hFc
        isClosed_Iic

/-- The ramp `clamp(x) = max 0 (min 1 x)`. -/
def ramp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem continuous_ramp : Continuous ramp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem ramp_nonneg (x : ℝ) : 0 ≤ ramp x := le_max_left _ _

theorem ramp_le_one (x : ℝ) : ramp x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero {x : ℝ} (hx : x ≤ 0) : ramp x = 0 :=
  max_eq_left ((min_le_right _ _).trans hx)

theorem ramp_eq_one {x : ℝ} (hx : 1 ≤ x) : ramp x = 1 := by
  unfold ramp; rw [min_eq_left hx]; exact max_eq_right zero_le_one

/-- The weight profile `Φ(x) = 1 + ∑ₗ 2ˡ clamp(x - tₗ)` for thresholds `tₗ ≥ l`. -/
def weightProfile (t : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + ∑' l : ℕ, (2 : ℝ) ^ l * ramp (x - t l)

theorem weightTerm_eq_zero {t : ℕ → ℝ} {x : ℝ} {l : ℕ} (hl : x ≤ t l) :
    (2 : ℝ) ^ l * ramp (x - t l) = 0 := by
  rw [ramp_eq_zero (sub_nonpos.mpr hl), mul_zero]

theorem weightTerm_nonneg (t : ℕ → ℝ) (x : ℝ) (l : ℕ) : 0 ≤ (2 : ℝ) ^ l * ramp (x - t l) :=
  mul_nonneg (pow_nonneg zero_le_two _) (ramp_nonneg _)

theorem weightTerm_eq_zero_of_ge {t : ℕ → ℝ} (ht : ∀ l : ℕ, (l : ℝ) ≤ t l) {x : ℝ} {l : ℕ}
    (hl : ⌈x⌉₊ ≤ l) : (2 : ℝ) ^ l * ramp (x - t l) = 0 :=
  weightTerm_eq_zero ((Nat.le_ceil x).trans ((Nat.cast_le.mpr hl).trans (ht l)))

theorem summable_weightTerm {t : ℕ → ℝ} (ht : ∀ l : ℕ, (l : ℝ) ≤ t l) (x : ℝ) :
    Summable fun l : ℕ => (2 : ℝ) ^ l * ramp (x - t l) :=
  summable_of_ne_finset_zero (s := Finset.range ⌈x⌉₊) fun l hl =>
    weightTerm_eq_zero_of_ge ht (by simpa using hl)

theorem one_le_weightProfile {t : ℕ → ℝ} (x : ℝ) : 1 ≤ weightProfile t x :=
  le_add_of_nonneg_right (tsum_nonneg fun l => weightTerm_nonneg t x l)

theorem continuous_weightProfile {t : ℕ → ℝ} (ht : ∀ l : ℕ, (l : ℝ) ≤ t l) (hmono : Monotone t) :
    Continuous (weightProfile t) := by
  refine continuous_iff_continuousAt.mpr fun x0 => ?_
  set N : ℕ := ⌈x0⌉₊ + 1 with hN
  have hlt : x0 < t N := by
    calc x0 ≤ ⌈x0⌉₊ := Nat.le_ceil x0
      _ < N := by rw [hN]; push_cast; linarith
      _ ≤ t N := ht N
  have hev : weightProfile t =ᶠ[𝓝 x0]
      fun x => 1 + ∑ l ∈ Finset.range N, (2 : ℝ) ^ l * ramp (x - t l) := by
    filter_upwards [Iio_mem_nhds hlt] with x hx
    unfold weightProfile
    congr 1
    refine tsum_eq_sum fun l hl => weightTerm_eq_zero ?_
    have : N ≤ l := by simpa using hl
    exact (le_of_lt hx).trans (hmono this)
  refine ContinuousAt.congr ?_ hev.symm
  exact (continuous_const.add (continuous_finsetSum _ fun l _ =>
    continuous_const.mul (continuous_ramp.comp (continuous_id.sub continuous_const)))).continuousAt

theorem le_weightProfile {t : ℕ → ℝ} (ht : ∀ l : ℕ, (l : ℝ) ≤ t l) {x : ℝ} {l : ℕ}
    (hx : t l + 1 ≤ x) : (2 : ℝ) ^ l ≤ weightProfile t x := by
  have h1 : (2 : ℝ) ^ l * ramp (x - t l) = 2 ^ l := by
    rw [ramp_eq_one (by linarith), mul_one]
  have h2 : (2 : ℝ) ^ l * ramp (x - t l) ≤ ∑' l : ℕ, (2 : ℝ) ^ l * ramp (x - t l) :=
    (summable_weightTerm ht x).le_tsum l fun j _ => weightTerm_nonneg t x j
  unfold weightProfile
  linarith

/-- `ofReal Φ(x) ≤ 1 + ∑ₗ 2ˡ 1_{x > tₗ}`. -/
theorem ofReal_weightProfile_le {t : ℕ → ℝ} (ht : ∀ l : ℕ, (l : ℝ) ≤ t l) (x : ℝ) :
    ENNReal.ofReal (weightProfile t x) ≤
      1 + ∑' l : ℕ, (2 : ℝ≥0∞) ^ l * (Ioi (t l)).indicator 1 x := by
  unfold weightProfile
  rw [ENNReal.ofReal_add zero_le_one (tsum_nonneg fun l => weightTerm_nonneg t x l),
    ENNReal.ofReal_one, ENNReal.ofReal_tsum_of_nonneg (fun l => weightTerm_nonneg t x l)
      (summable_weightTerm ht x)]
  gcongr with l
  rw [ENNReal.ofReal_mul (pow_nonneg zero_le_two _), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]
  gcongr
  by_cases hx : x ∈ Ioi (t l)
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact ENNReal.ofReal_le_one.mpr (ramp_le_one _)
  · rw [indicator_of_notMem hx, ramp_eq_zero (sub_nonpos.mpr (not_lt.mp hx)),
      ENNReal.ofReal_zero]

/-- **A proper integrable weight.**  For a finite measure `μ` on a proper space and an open `Ω`,
there is a measurable `ψ ≥ 1`, continuous on `Ω`, with `∫ ψ dμ < ∞` and `ψ ≥ L` off a compact
subset of `Ω`, for every `L`. -/
theorem exists_properWeight [ProperSpace E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ ψ : E → ℝ, Measurable ψ ∧ ContinuousOn ψ Ω ∧ (∀ w, 1 ≤ ψ w) ∧
      ∫⁻ w, ENNReal.ofReal (ψ w) ∂μ < ⊤ ∧
      ∀ L : ℝ, ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ ∀ w ∈ Ω, w ∉ K → L ≤ ψ w := by
  set g := exhaustFun Ω with hg
  -- tails of `g` under `μ`
  have htail : ∀ l : ℕ, ∃ T : ℕ, μ {w | (T : ℝ) < g w} ≤ (4 : ℝ≥0∞)⁻¹ ^ l := by
    intro l
    have hlim : Tendsto (fun T : ℕ => μ {w | (T : ℝ) < g w}) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun T : ℕ => {w | (T : ℝ) < g w})
        (fun T => (measurableSet_lt measurable_const (measurable_exhaustFun Ω)).nullMeasurableSet)
        (fun a b hab w hw => show (a : ℝ) < g w from lt_of_le_of_lt (Nat.cast_le.mpr hab) hw)
        ⟨0, measure_ne_top μ _⟩
      have hempty : (⋂ T : ℕ, {w | (T : ℝ) < g w}) = ∅ := by
        ext w
        simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
          not_lt]
        exact ⟨⌈g w⌉₊, Nat.le_ceil _⟩
      rw [hempty, measure_empty] at h
      exact h
    have hpos : (0 : ℝ≥0∞) < (4 : ℝ≥0∞)⁻¹ ^ l :=
      ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) l
    obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
    exact ⟨T, hT.le⟩
  choose T hT using htail
  set t : ℕ → ℝ := fun l => ∑ j ∈ Finset.range (l + 1), ((T j : ℝ) + 1) with ht_def
  have hterm : ∀ j, (0 : ℝ) ≤ (T j : ℝ) + 1 := fun j => by positivity
  have htmono : Monotone t := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun j _ _ => hterm j
  have htT : ∀ l, (T l : ℝ) ≤ t l := fun l => by
    have := Finset.single_le_sum (fun j _ => hterm j) (Finset.self_mem_range_succ l)
    simp only [ht_def]; linarith
  have htl : ∀ l : ℕ, (l : ℝ) ≤ t l := fun l => by
    have h : ∑ j ∈ Finset.range (l + 1), (1 : ℝ) ≤ t l :=
      Finset.sum_le_sum fun j _ => by have := (T j).cast_nonneg (α := ℝ); linarith
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
    push_cast at h; linarith
  have hμt : ∀ l, μ {w | t l < g w} ≤ (4 : ℝ≥0∞)⁻¹ ^ l := fun l =>
    (measure_mono fun w hw => lt_of_le_of_lt (htT l) hw).trans (hT l)
  refine ⟨fun w => weightProfile t (g w),
    (continuous_weightProfile htl htmono).measurable.comp (measurable_exhaustFun Ω),
    (continuous_weightProfile htl htmono).comp_continuousOn (continuousOn_exhaustFun hΩ),
    fun w => one_le_weightProfile _, ?_, ?_⟩
  · calc ∫⁻ w, ENNReal.ofReal (weightProfile t (g w)) ∂μ
        ≤ ∫⁻ w, (1 + ∑' l : ℕ, (2 : ℝ≥0∞) ^ l * (Ioi (t l)).indicator 1 (g w)) ∂μ :=
          lintegral_mono fun w => ofReal_weightProfile_le htl (g w)
      _ = μ univ + ∑' l : ℕ, (2 : ℝ≥0∞) ^ l * μ {w | t l < g w} := by
          rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
            lintegral_tsum fun l => ?_]
          · congr 1
            refine tsum_congr fun l => ?_
            rw [lintegral_const_mul _ ?_]
            · congr 1
              have : (fun w => (Ioi (t l)).indicator (1 : ℝ → ℝ≥0∞) (g w)) =
                  {w | t l < g w}.indicator 1 := by
                ext w; simp [indicator, mem_Ioi]
              rw [this, lintegral_indicator_one
                (measurableSet_lt measurable_const (measurable_exhaustFun Ω))]
            · exact (measurable_one.indicator measurableSet_Ioi).comp (measurable_exhaustFun Ω)
          · exact (measurable_const.mul ((measurable_one.indicator measurableSet_Ioi).comp
              (measurable_exhaustFun Ω))).aemeasurable
      _ ≤ μ univ + ∑' l : ℕ, (2 : ℝ≥0∞)⁻¹ ^ l := by
          gcongr with l
          calc (2 : ℝ≥0∞) ^ l * μ {w | t l < g w} ≤ 2 ^ l * (4 : ℝ≥0∞)⁻¹ ^ l := by
                gcongr; exact hμt l
            _ = (2 : ℝ≥0∞)⁻¹ ^ l := by
                rw [← mul_pow]; congr 1
                rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
                  ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      _ < ⊤ := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
          exact ENNReal.add_lt_top.mpr ⟨measure_lt_top μ _, ENNReal.ofNat_lt_top⟩
  · intro L
    obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt L (by norm_num : (1 : ℝ) < 2)
    refine ⟨{w | w ∈ Ω ∧ g w ≤ t l + 1}, isCompact_exhaustFun_le hΩ _, fun w hw => hw.1, ?_⟩
    intro w hw hwK
    have hgw : t l + 1 ≤ g w := by
      by_contra h
      exact hwK ⟨hw, (not_le.mp h).le⟩
    exact hl.le.trans (le_weightProfile htl hgw)

end Weight

/-! ### Test functions on `M` from functions of the parameters of a regular patch -/

section Patch

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood PatchParameterNull

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The open set of `M` on which a regular patch has its parameter map: the chart source of
the centre, cut down to the source of the flattening. -/
def parameterNbhd (P : RegularPatch V) : Set M :=
  (complexChartAt (n := n) P.center).val.source ∩
    (complexChartAt (n := n) P.center).val ⁻¹' P.flattening.source

/-- The parameter map `y ↦ pr(Φ(e y))` of a regular patch (`e` the chart at the centre, `Φ`
the flattening, `pr` the projection onto the first `dim V` coordinates). -/
def parameterOf (P : RegularPatch V) (y : M) : ComplexModel V.dim :=
  planeProjection V.dim n (P.flattening.toFun ((complexChartAt (n := n) P.center).val y))

theorem isOpen_parameterNbhd (P : RegularPatch V) : IsOpen (parameterNbhd P) :=
  (complexChartAt (n := n) P.center).val.isOpen_inter_preimage P.flattening.isOpen_source

theorem continuousOn_parameterOf (P : RegularPatch V) :
    ContinuousOn (parameterOf P) (parameterNbhd P) := by
  refine (continuous_planeProjection V.dim n).comp_continuousOn ?_
  exact P.flattening.toFun_holomorphic.continuousOn.comp
    ((complexChartAt (n := n) P.center).val.continuousOn.mono inter_subset_left)
    fun y hy => hy.2

theorem toManifold_mem_parameterNbhd (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) : P.toManifold w ∈ parameterNbhd P := by
  refine ⟨RegularPatch.toManifold_mem_chart_source P hw, ?_⟩
  show (complexChartAt (n := n) P.center).val (P.toManifold w) ∈ P.flattening.source
  rw [RegularPatch.chart_toManifold P hw]
  exact RegularPatch.coordinateParametrization_mem_source P hw

theorem parameterOf_toManifold (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) : parameterOf P (P.toManifold w) = w := by
  unfold parameterOf
  rw [RegularPatch.chart_toManifold P hw]
  change planeProjection V.dim n (P.flattening.toFun
    (P.flattening.invFun (planeInclusion V.dim n w))) = w
  rw [P.flattening.right_inv _ hw, planeProjection_planeInclusion V.dim_le]

/-- On the trace of `parameterNbhd P` on `V`, the parameter map inverts the parametrization. -/
theorem toManifold_parameterOf (P : RegularPatch V) {y : M} (hyV : y ∈ V.carrier)
    (hy : y ∈ parameterNbhd P) :
    parameterOf P y ∈ P.parameterDomain ∧ P.toManifold (parameterOf P y) = y := by
  have hplane := (P.flattens hy.1 hy.2).1 hyV
  have hincl : planeInclusion V.dim n (parameterOf P y) =
      P.flattening.toFun ((complexChartAt (n := n) P.center).val y) :=
    planeInclusion_planeProjection hplane
  refine ⟨?_, ?_⟩
  · show planeInclusion V.dim n (parameterOf P y) ∈ P.flattening.target
    rw [hincl]
    exact P.flattening.mapsTo_toFun hy.2
  · change (complexChartAt (n := n) P.center).val.symm
      (P.flattening.invFun (planeInclusion V.dim n (parameterOf P y))) = y
    rw [hincl, P.flattening.left_inv _ hy.2, (complexChartAt (n := n) P.center).val.left_inv hy.1]

/-- **Test functions from parameter functions.**  A function `h`, continuous on an open set `Ω`
of parameters of a regular patch and tending to `0` off the compact subsets of `Ω`, is `t ∘ γ`
on `Ω` for a continuous `t` on the compact manifold (`γ` the parametrization): extend
`h ∘ γ⁻¹` by `0` to `V`, which is continuous on the closed set `V`, then by Tietze to `M`. -/
theorem exists_continuousMap_toManifold_eq [CompactSpace M] (P : RegularPatch V)
    {Ω : Set (ComplexModel V.dim)} (hΩo : IsOpen Ω) (hΩ : Ω ⊆ P.parameterDomain)
    {h : ComplexModel V.dim → ℝ} (hh : ContinuousOn h Ω)
    (hdecay : ∀ ε > 0, ∃ K : Set (ComplexModel V.dim), IsCompact K ∧ K ⊆ Ω ∧
      ∀ w ∈ Ω, w ∉ K → |h w| ≤ ε) :
    ∃ t : C(M, ℝ), ∀ w ∈ Ω, t (P.toManifold w) = h w := by
  classical
  set W : Set M := parameterNbhd P ∩ parameterOf P ⁻¹' Ω with hW
  have hWo : IsOpen W :=
    (continuousOn_parameterOf P).isOpen_inter_preimage (isOpen_parameterNbhd P) hΩo
  set t0 : V.carrier → ℝ := fun y => if (y : M) ∈ W then h (parameterOf P y) else 0 with ht0
  have hmemW : ∀ w ∈ Ω, P.toManifold w ∈ W := fun w hw =>
    ⟨toManifold_mem_parameterNbhd P (hΩ hw), by
      rw [mem_preimage, parameterOf_toManifold P (hΩ hw)]; exact hw⟩
  have hcont : Continuous t0 := by
    refine continuous_iff_continuousAt.mpr fun y0 => ?_
    by_cases hy0 : (y0 : M) ∈ W
    · -- inside the image: `t0 = h ∘ parameterOf` near `y0`
      have hev : t0 =ᶠ[𝓝 y0] fun y => h (parameterOf P (y : M)) := by
        have : ((↑) : V.carrier → M) ⁻¹' W ∈ 𝓝 y0 :=
          continuous_subtype_val.continuousAt.preimage_mem_nhds (hWo.mem_nhds hy0)
        filter_upwards [this] with y hy
        simp only [ht0, if_pos (show (y : M) ∈ W from hy)]
      refine ContinuousAt.congr ?_ hev.symm
      have h1 : ContinuousAt (parameterOf P) (y0 : M) :=
        (continuousOn_parameterOf P).continuousAt ((isOpen_parameterNbhd P).mem_nhds hy0.1)
      have h2 : ContinuousAt h (parameterOf P y0) := hh.continuousAt (hΩo.mem_nhds hy0.2)
      exact (h2.comp h1).comp continuous_subtype_val.continuousAt
    · -- outside the image: `t0 → 0`
      have ht0y0 : t0 y0 = 0 := by simp only [ht0, if_neg hy0]
      rw [ContinuousAt, ht0y0]
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      obtain ⟨K, hK, hKΩ, hKh⟩ := hdecay (ε / 2) (half_pos hε)
      have hKc : IsCompact (P.toManifold '' K) :=
        hK.image_of_continuousOn ((RegularPatch.continuousOn_toManifold P).mono
          (hKΩ.trans hΩ))
      have hy0K : (y0 : M) ∉ P.toManifold '' K := by
        rintro ⟨k, hk, hk0⟩
        exact hy0 (hk0 ▸ hmemW k (hKΩ hk))
      have hnhds : ((↑) : V.carrier → M) ⁻¹' (P.toManifold '' K)ᶜ ∈ 𝓝 y0 :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds
          (hKc.isClosed.isOpen_compl.mem_nhds hy0K)
      filter_upwards [hnhds] with y hy
      rw [Real.dist_eq, sub_zero]
      by_cases hyW : (y : M) ∈ W
      · simp only [ht0, if_pos hyW]
        have hpar := toManifold_parameterOf P y.2 hyW.1
        have hnot : parameterOf P y ∉ K := fun hk => hy ⟨_, hk, hpar.2⟩
        exact (hKh _ hyW.2 hnot).trans_lt (half_lt_self hε)
      · simp only [ht0, if_neg hyW, abs_zero]
        exact hε
  obtain ⟨t, ht⟩ := ContinuousMap.exists_restrict_eq V.isClosed_carrier ⟨t0, hcont⟩
  refine ⟨t, fun w hw => ?_⟩
  have hV : P.toManifold w ∈ V.carrier := RegularPatch.toManifold_mem_carrier P (hΩ hw)
  have := congrArg (fun f : C(V.carrier, ℝ) => f ⟨P.toManifold w, hV⟩) ht
  simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk] at this
  rw [this]
  simp only [ht0, if_pos (hmemW w hw), parameterOf_toManifold P (hΩ hw)]

end Patch

/-! ### Local weighted measures and tests for one piece, and for a finite family -/

section Family

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.RegularPatchNeighborhood
open ManifoldBorelFoundation LocalPatchWeightedMeasure FormPieceMassCurrentPairingBridge
  FiniteTelescopeLocalWeightedPairing PartitionPairingCollarErrorReduction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **One piece.**  A function `f`, continuous on an open set `Ω` of parameters of a regular
patch and integrable on a measurable `S ⊆ Ω`, is `ρ · (t ∘ γ)` on `S` for a local weighted
patch measure `(γ)_*(ρ · vol|_S)` and a test `t ∈ C_c(M, ℝ)` (`M` compact):
`ρ = ψ u` and `t ∘ γ = f / (ψ u)` with `u = (1 + ‖w‖)^{-r} + |f|` (`r > dim_ℝ`) and `ψ` a proper
weight for the finite measure `u · vol|_S` (`exists_properWeight`). -/
theorem exists_localWeightedPatchMeasure_test [CompactSpace M] (P : RegularPatch V)
    {S Ω : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hΩo : IsOpen Ω)
    (hΩ : Ω ⊆ P.parameterDomain) {f : ComplexModel V.dim → ℝ} (hf : ContinuousOn f Ω)
    (hfi : IntegrableOn f S) :
    ∃ (D : LocalWeightedPatchMeasure V P) (t : C_c(M, ℝ)), D.parameterSet = S ∧
      ∀ w ∈ S, f w = (D.density w).toReal * t (P.toManifold w) := by
  set r : ℝ := (Module.finrank ℝ (ComplexModel V.dim) : ℝ) + 1 with hr
  set e : ComplexModel V.dim → ℝ := fun w => (1 + ‖w‖) ^ (-r) with he
  have he_int : Integrable e volume := integrable_one_add_norm (by rw [hr]; linarith)
  have h1n : ∀ w : ComplexModel V.dim, (0 : ℝ) < 1 + ‖w‖ := fun w => by
    have := norm_nonneg w; linarith
  have he_pos : ∀ w, 0 < e w := fun w => Real.rpow_pos_of_pos (h1n w) _
  have he_cont : Continuous e :=
    (continuous_const.add continuous_norm).rpow_const fun w => Or.inl (h1n w).ne'
  set u : ComplexModel V.dim → ℝ := fun w => e w + |f w| with hu
  have hu_pos : ∀ w, 0 < u w := fun w => add_pos_of_pos_of_nonneg (he_pos w) (abs_nonneg _)
  have hu_int : IntegrableOn u S := he_int.integrableOn.add hfi.abs
  have hu_cont : ContinuousOn u Ω := he_cont.continuousOn.add hf.abs
  have hf_le : ∀ w, |f w| ≤ u w := fun w => le_add_of_nonneg_left (he_pos w).le
  set μ : Measure (ComplexModel V.dim) :=
    (volume.restrict S).withDensity fun w => ENNReal.ofReal (u w) with hμ
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hu_int.hasFiniteIntegral
  obtain ⟨ψ, hψm, hψc, hψ1, hψint, hψprop⟩ := exists_properWeight μ hΩo
  have hψpos : ∀ w, 0 < ψ w := fun w => zero_lt_one.trans_le (hψ1 w)
  set ρ : ComplexModel V.dim → ℝ≥0∞ := fun w => ENNReal.ofReal (ψ w * u w) with hρ
  have hρ_aem : AEMeasurable ρ (volume.restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hψm.aemeasurable.mul hu_int.aemeasurable)
  have hρ_int : ∫⁻ w in S, ρ w < ⊤ := by
    have h1 : ∫⁻ w, ENNReal.ofReal (ψ w) ∂μ =
        ∫⁻ w in S, ENNReal.ofReal (u w) * ENNReal.ofReal (ψ w) :=
      lintegral_withDensity_eq_lintegral_mul₀
        (ENNReal.measurable_ofReal.comp_aemeasurable hu_int.aemeasurable)
        (ENNReal.measurable_ofReal.comp hψm).aemeasurable
    have h2 : (fun w => ρ w) = fun w => ENNReal.ofReal (u w) * ENNReal.ofReal (ψ w) := by
      funext w
      simp only [hρ]
      rw [ENNReal.ofReal_mul (hψpos w).le, mul_comm]
    rw [h2, ← h1]
    exact hψint
  set h : ComplexModel V.dim → ℝ := fun w => f w / (ψ w * u w) with hh
  have hh_cont : ContinuousOn h Ω :=
    hf.div (hψc.mul hu_cont) fun w _ => (mul_pos (hψpos w) (hu_pos w)).ne'
  have hh_decay : ∀ ε > 0, ∃ K : Set (ComplexModel V.dim), IsCompact K ∧ K ⊆ Ω ∧
      ∀ w ∈ Ω, w ∉ K → |h w| ≤ ε := by
    intro ε hε
    obtain ⟨K, hK, hKΩ, hKψ⟩ := hψprop ε⁻¹
    refine ⟨K, hK, hKΩ, fun w hw hwK => ?_⟩
    have hψu : 0 < ψ w * u w := mul_pos (hψpos w) (hu_pos w)
    rw [hh, abs_div, abs_of_pos hψu, div_le_iff₀ hψu]
    calc |f w| ≤ u w := hf_le w
      _ = 1 * u w := (one_mul _).symm
      _ ≤ (ε * ψ w) * u w := by
          gcongr
          rw [← inv_le_iff_one_le_mul₀' hε]
          exact hKψ w hw hwK
      _ = ε * (ψ w * u w) := by ring
  obtain ⟨t, ht⟩ := exists_continuousMap_toManifold_eq P hΩo hΩ hh_cont hh_decay
  let _ : MeasurableSpace M := manifoldBorel M
  have _ : BorelSpace M := ⟨rfl⟩
  have hγ : AEMeasurable P.toManifold (parameterMeasure S ρ) :=
    (((RegularPatch.continuousOn_toManifold P).mono (hSΩ.trans hΩ)).aemeasurable hS).mono'
      (withDensity_absolutelyContinuous (volume.restrict S) ρ)
  refine ⟨{ parameterSet := S
            measurableSet_parameterSet := hS
            parameterSet_subset_domain := hSΩ.trans hΩ
            density := ρ
            density_aemeasurable := hρ_aem
            density_ae_lt_top := ae_of_all _ fun w => ENNReal.ofReal_lt_top
            measure := Measure.map P.toManifold (parameterMeasure S ρ)
            measure_eq_weightedPushforward := rfl
            measure_univ_lt_top := ?_ },
    CompactlySupportedContinuousMap.continuousMapEquiv t, rfl, fun w hw => ?_⟩
  · rw [Measure.map_apply_of_aemeasurable hγ MeasurableSet.univ, preimage_univ, parameterMeasure,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hρ_int
  · have hψu : 0 < ψ w * u w := mul_pos (hψpos w) (hu_pos w)
    change f w = (ρ w).toReal * t (P.toManifold w)
    rw [ht w (hSΩ hw), hρ, ENNReal.toReal_ofReal hψu.le, hh, mul_div_cancel₀ _ hψu.ne']

variable {beta : KahlerBackground n M}
  {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
  {avoid : Set M} {G : RegularPieceFamily V avoid}

/-- The telescope integrand of a piece is continuous on the piece's open set (its potentials are
smooth there). -/
theorem continuousOn_telescopeIntegrand (T : FormPieceTelescopeData beta q hvs G)
    (i : Fin G.size) : ContinuousOn (T.telescopeIntegrand i) (T.omega i) := by
  unfold FormPieceTelescopeData.telescopeIntegrand
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact BedfordTaylor.continuousOn_mixedDensity (U := ⟨T.omega i, T.omega_open i⟩)
    fun k => PatchDensityLocalPotential.contDiffOn_telescopeFunctions (T.potential_smooth i)
      (T.restricted_potential_smooth i) j k

/-- **Weighted-pairing data exist for every finite family** whose telescope integrands are
integrable on the pieces (`M` compact). -/
theorem nonempty_finiteTelescopeLocalWeightedPairingData [CompactSpace M]
    (T : FormPieceTelescopeData beta q hvs G)
    (hint : ∀ i, IntegrableOn (T.telescopeIntegrand i) (G.piece i)) :
    Nonempty (FiniteTelescopeLocalWeightedPairingData T) := by
  have hloc : ∀ i : Fin G.size, ∃ (D : LocalWeightedPatchMeasure V (G.patch i))
      (t : C_c(M, ℝ)), D.parameterSet = G.piece i ∧
        ∀ w ∈ G.piece i, T.telescopeIntegrand i w =
          (D.density w).toReal * t ((G.patch i).toManifold w) := fun i =>
    exists_localWeightedPatchMeasure_test (G.patch i) (G.measurableSet_piece i)
      (T.piece_subset i) (T.omega_open i) (T.omega_subset_domain i)
      (continuousOn_telescopeIntegrand T i) (hint i)
  choose D t hD ht using hloc
  exact ⟨{ localMeasure := D
           parameterSet_eq_piece := hD
           test := t
           telescope_eq_weightedTest := fun i => by
             filter_upwards [ae_restrict_mem (G.measurableSet_piece i)] with w hw
             exact ht i w hw }⟩

/-- The pairing-remainder datum of a finite family with integrable telescope integrands, with
the exact remainder `|∑ᵢ ∫_{Sᵢ} fᵢ|`. -/
def finiteTelescopePairingRemainderData_of_integrableOn [CompactSpace M]
    (T : FormPieceTelescopeData beta q hvs G)
    (hint : ∀ i, IntegrableOn (T.telescopeIntegrand i) (G.piece i)) :
    FiniteTelescopePairingRemainderData T where
  weightedPairing := (nonempty_finiteTelescopeLocalWeightedPairingData T hint).some
  remainder := |∑ i, ∫ w in G.piece i, T.telescopeIntegrand i w|
  abs_sum_pairing_le := by
    rw [← FiniteTelescopeLocalWeightedPairingData.sum_telescopeIntegral_eq_sum_pairing]

theorem finiteTelescopePairingRemainderData_of_integrableOn_remainder [CompactSpace M]
    (T : FormPieceTelescopeData beta q hvs G)
    (hint : ∀ i, IntegrableOn (T.telescopeIntegrand i) (G.piece i)) :
    (finiteTelescopePairingRemainderData_of_integrableOn T hint).remainder =
      |∑ i, ∫ w in G.piece i, T.telescopeIntegrand i w| := rfl

/-- The telescope integrands are integrable on the pieces as soon as both finite-piece masses
are finite (the two densities are nonnegative there). -/
theorem integrableOn_telescopeIntegrand (T : FormPieceTelescopeData beta q hvs G)
    (hcurrent_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
        (G.patch i) w)
    (hbackground_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)
    (hcurrent_finite : PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) G ≠ ⊤)
    (hbackground_finite : PatchFormMass.formPieceMass beta.form.val G ≠ ⊤) (i : Fin G.size) :
    IntegrableOn (T.telescopeIntegrand i) (G.piece i) := by
  have h1 := PatchFormMassSignedBridge.integrableOn_patchFormDensity
    (ACTopMassComparison.currentForm q hvs) (G.patch i) (G.measurableSet_piece i)
    (G.piece_subset i) (hcurrent_nonneg i)
    (PatchFormMassSignedBridge.setLIntegral_piece_ne_top G hcurrent_finite i)
  have h2 := PatchFormMassSignedBridge.integrableOn_patchFormDensity beta.form.val (G.patch i)
    (G.measurableSet_piece i) (G.piece_subset i) (hbackground_nonneg i)
    (PatchFormMassSignedBridge.setLIntegral_piece_ne_top G hbackground_finite i)
  exact (h1.sub h2).congr_fun (fun w hw => T.density_defect_eq_telescopeIntegrand i hw)
    (G.measurableSet_piece i)

/-- **The pairing-remainder datum of every finite family with finite masses**, with remainder
`|∑ᵢ ∫_{Sᵢ} fᵢ|`, which is `|mass_G(current) - mass_G(background)|`
(`abs_toReal_sub_le_remainder` is then an equality). -/
def finiteTelescopePairingRemainderData_of_finite [CompactSpace M]
    (T : FormPieceTelescopeData beta q hvs G)
    (hcurrent_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
        (G.patch i) w)
    (hbackground_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)
    (hcurrent_finite : PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) G ≠ ⊤)
    (hbackground_finite : PatchFormMass.formPieceMass beta.form.val G ≠ ⊤) :
    FiniteTelescopePairingRemainderData T :=
  finiteTelescopePairingRemainderData_of_integrableOn T
    (integrableOn_telescopeIntegrand T hcurrent_nonneg hbackground_nonneg hcurrent_finite
      hbackground_finite)

/-- The remainder of `finiteTelescopePairingRemainderData_of_finite` is exactly the difference
of the two finite-piece masses. -/
theorem finiteTelescopePairingRemainderData_of_finite_remainder [CompactSpace M]
    (T : FormPieceTelescopeData beta q hvs G)
    (hcurrent_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
        (G.patch i) w)
    (hbackground_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)
    (hcurrent_finite : PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) G ≠ ⊤)
    (hbackground_finite : PatchFormMass.formPieceMass beta.form.val G ≠ ⊤) :
    (finiteTelescopePairingRemainderData_of_finite T hcurrent_nonneg hbackground_nonneg
        hcurrent_finite hbackground_finite).remainder =
      |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) G).toReal -
        (PatchFormMass.formPieceMass beta.form.val G).toReal| := by
  rw [finiteTelescopePairingRemainderData_of_finite,
    finiteTelescopePairingRemainderData_of_integrableOn_remainder,
    current_toReal_sub_background_eq_sum_densityDefectIntegral hcurrent_nonneg
      hbackground_nonneg hcurrent_finite hbackground_finite]
  congr 1
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (G.measurableSet_piece i)] with w hw
  exact (T.density_defect_eq_telescopeIntegrand i hw).symm

end Family

end

end SGPT.Foundations.Analysis.Pending.StokesWeightedPairing
