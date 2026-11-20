import SGPT.Envelopes.MADirichlet3Convolution

/-!
# Convolution approximants with uniformly bounded energy

FPT `prop:canonical-grid-energy-control` (1), (3), (4) for `p = 1`, in the convolution variant of
lane MA-DIR2 (blueprint `claude-ma-dir2:route`), on a polydisk `Q = a + R·P`:

Let `α` be a finite measure carried by a compact `K ⊆ Q` with `α ≤ (ddᶜw)ⁿ` on `Q` for a
plurisubharmonic `w` with `b ≤ w ≤ b + M` on `Q`. For every `j` the density
`Fⱼⁿ = (α ∗ ρⱼ)/cₙ + δⱼ χⁿ` (`ρⱼ` TN's radial kernels, `χ` a smooth cut-off equal to `1` near
the supports, `δⱼ = 1/(j+1)`, `cₙ = n!/πⁿ`) has a `C²` (indeed smooth) root `Fⱼ ≥ 0` with compact
support in `Q` (`contDiff_rootDensity`), so MA-DIR2's polydisk Dirichlet problem gives the
solution `Uⱼ ∈ ℰ₀(Q)` of `(ddᶜUⱼ)ⁿ = cₙ Fⱼⁿ dV` with boundary values `0`; and the energies
`e₁(Uⱼ)` are **bounded uniformly in `j`** (`exists_convolution_approximants`). The bound comes from
the comparison `∫(-Uⱼ)(α ∗ ρⱼ) ≤ ∫(-Uⱼ) dα` (sub-mean values, `lintegral_convDensity_mul_le`),
the Cegrell–Persson estimate for `μ = α + cₙ dV|_Q ≤ (ddᶜ(w + |z|²))ⁿ`
(`lintegral_neg_rpow_le`), and the self-improving inequality of
`localEnergy_le_of_moment_control`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff Manifold

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- A smooth cut-off: `χ = 1` on `cthickening (2r) K`, `0 ≤ χ ≤ 1`, with compact support in
`cthickening (3r) K`. -/
theorem exists_smooth_cutoff {K : Set (ComplexModel n)} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      EqOn χ 1 (cthickening (2 * r) K) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ cthickening (3 * r) K := by
  have hd : Disjoint (thickening (3 * r) K)ᶜ (cthickening (2 * r) K) :=
    disjoint_compl_left_iff_subset.mpr
      (cthickening_subset_thickening' (by positivity) (by linarith) K)
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ (ComplexModel n)) (n := (⊤ : ℕ∞)) isOpen_thickening.isClosed_compl isClosed_cthickening hd
  have hsupp : Function.support f ⊆ thickening (3 * r) K := fun x hx => by
    by_contra h
    exact hx (hf0 h)
  have htsupp : tsupport f ⊆ cthickening (3 * r) K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening _ _)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x => hf01 x, hf1, ?_, htsupp⟩
  exact (hK.cthickening (r := 3 * r)).of_isClosed_subset (isClosed_tsupport _) htsupp

/-- The `n`-th root density `(g/c + δ χⁿ)^{1/n}`. -/
def rootDensity (g χ : ComplexModel n → ℝ) (c δ : ℝ) (k : ℕ) (x : ComplexModel n) : ℝ :=
  (g x / c + δ * χ x ^ k) ^ ((k : ℝ)⁻¹)

theorem rootDensity_nonneg (g χ : ComplexModel n → ℝ) (c δ : ℝ) (k : ℕ) (x : ComplexModel n)
    (h : 0 ≤ g x / c + δ * χ x ^ k) : 0 ≤ rootDensity g χ c δ k x :=
  Real.rpow_nonneg h _

theorem rootDensity_pow {g χ : ComplexModel n → ℝ} {c δ : ℝ} {k : ℕ} (hk : k ≠ 0)
    {x : ComplexModel n} (h : 0 ≤ g x / c + δ * χ x ^ k) :
    rootDensity g χ c δ k x ^ k = g x / c + δ * χ x ^ k :=
  Real.rpow_inv_natCast_pow h hk

/-- **Smoothness of the root density**: if `g, χ ≥ 0` are smooth, `g` vanishes off a closed set
`L` on which `χ = 1`, and `c, δ > 0`, then `(g/c + δ χᵏ)^{1/k}` is smooth: where the radicand is
positive this is the smoothness of `t ↦ t^{1/k}` on `(0, ∞)`, and near a zero of the radicand
`g = 0` and the root is `δ^{1/k} χ`. -/
theorem contDiff_rootDensity {g χ : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g)
    (hχ : ContDiff ℝ ∞ χ) (hg0 : ∀ x, 0 ≤ g x) (hχ0 : ∀ x, 0 ≤ χ x) {L : Set (ComplexModel n)}
    (hL : IsClosed L) (hgL : Function.support g ⊆ L) (hχL : EqOn χ 1 L) {c δ : ℝ} (hc : 0 < c)
    (hδ : 0 < δ) {k : ℕ} (hk : k ≠ 0) : ContDiff ℝ ∞ (rootDensity g χ c δ k) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  have hrad : ContDiff ℝ ∞ fun y => g y / c + δ * χ y ^ k :=
    (hg.div_const c).add (contDiff_const.mul (hχ.pow k))
  have hnn : ∀ y, 0 ≤ g y / c + δ * χ y ^ k := fun y =>
    add_nonneg (div_nonneg (hg0 y) hc.le) (mul_nonneg hδ.le (pow_nonneg (hχ0 y) k))
  by_cases hx : 0 < g x / c + δ * χ x ^ k
  · exact hrad.contDiffAt.rpow_const_of_ne hx.ne'
  · have hx0 : g x / c + δ * χ x ^ k = 0 := le_antisymm (not_lt.mp hx) (hnn x)
    have hχx : χ x = 0 := by
      have h1 : 0 ≤ g x / c := div_nonneg (hg0 x) hc.le
      have h2 : δ * χ x ^ k = 0 := by
        have := mul_nonneg hδ.le (pow_nonneg (hχ0 x) k)
        linarith
      exact pow_eq_zero_iff hk |>.mp ((mul_eq_zero.mp h2).resolve_left hδ.ne')
    have hxL : x ∉ L := fun h => by
      have := hχL h
      rw [hχx] at this
      exact zero_ne_one this
    have hev : rootDensity g χ c δ k =ᶠ[𝓝 x] fun y => δ ^ ((k : ℝ)⁻¹) * χ y := by
      filter_upwards [hL.isOpen_compl.mem_nhds hxL] with y hy
      have hgy : g y = 0 := by
        by_contra h
        exact hy (hgL h)
      rw [rootDensity, hgy, zero_div, zero_add, Real.mul_rpow hδ.le (pow_nonneg (hχ0 y) k),
        Real.pow_rpow_inv_natCast (hχ0 y) hk]
    exact (contDiff_const.mul hχ).contDiffAt.congr_of_eventuallyEq hev

/-- Locally bounded plurisubharmonic functions with boundary values `0` on a bounded open set are
bounded below. -/
theorem exists_lower_bound_of_tendsto_frontier {D : Opens (ComplexModel n)}
    (hDb : Bornology.IsBounded (D : Set (ComplexModel n))) {φ : ComplexModel n → ℝ}
    (hφ : IsLocallyBoundedPshOn D φ)
    (hbd : ∀ ζ ∈ frontier (D : Set (ComplexModel n)),
      Tendsto φ (𝓝[(D : Set (ComplexModel n))] ζ) (𝓝 0)) :
    ∃ C : ℝ, ∀ z ∈ D, -C ≤ φ z := by
  obtain ⟨hKc, hKD⟩ := exists_isCompact_sublevel hDb hbd one_pos
  obtain ⟨C, hC⟩ := IsLocallyBoundedPshOn.exists_abs_le hφ hKc hKD
  refine ⟨max C 1, fun z hz => ?_⟩
  by_cases h : φ z ≤ -1
  · have h1 := hC z (subset_closure ⟨hz, h⟩)
    have h2 := neg_abs_le (φ z)
    linarith [le_max_left C 1]
  · push Not at h
    linarith [le_max_right C 1]

theorem isBounded_polydiskAt (a : ComplexModel n) {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (polydiskAt a R) := by
  refine (Metric.isBounded_iff_subset_closedBall a).2 ⟨R * (n + 1), fun z hz => ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  have hz' : affineFrom a R z ∈ unitPolydisk n := hz
  have h1 := norm_sq_le_of_mem_unitPolydisk hz'
  have h2 : ‖affineFrom a R z‖ ≤ n + 1 := by nlinarith [norm_nonneg (affineFrom a R z)]
  have h3 : z - a = R • affineFrom a R z := by
    simp only [affineFrom, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [h3, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_le_mul_of_nonneg_left h2 hR.le

theorem norm_le_of_mem_polydiskAt {a z : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ polydiskAt a R) : ‖z‖ ≤ ‖a‖ + R * (n + 1) := by
  have hz' : affineFrom a R z ∈ unitPolydisk n := hz
  have h1 := norm_sq_le_of_mem_unitPolydisk hz'
  have h2 : ‖affineFrom a R z‖ ≤ n + 1 := by nlinarith [norm_nonneg (affineFrom a R z)]
  have h3 : z = a + R • affineFrom a R z := by
    simp only [affineFrom, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  calc ‖z‖ = ‖a + R • affineFrom a R z‖ := by rw [← h3]
    _ ≤ ‖a‖ + ‖R • affineFrom a R z‖ := norm_add_le _ _
    _ = ‖a‖ + R * ‖affineFrom a R z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ ‖a‖ + R * (n + 1) := by gcongr

/-- **Convolution approximants with uniformly bounded energy** (FPT
`prop:canonical-grid-energy-control` (1), (3), (4) for `p = 1`, convolution variant, on the
polydisk `Q = a + R·P`). Let `α` be a finite measure carried by a compact `K ⊆ Q` with
`α ≤ (ddᶜw)ⁿ` on `Q`, where `b ≤ w ≤ b + M` on `Q`. Then there are `r > 0`, a smooth cut-off
`0 ≤ χ ≤ 1` with compact support, smooth `Fⱼ ≥ 0` with compact support in `Q` and
`cₙ Fⱼⁿ = α ∗ ρⱼ + cₙ (j+1)⁻¹ χⁿ` (`ρⱼ = explicitRadialKernel r hr j`), the solutions `Uⱼ ∈ ℰ₀(Q)`
of `(ddᶜUⱼ)ⁿ = cₙ Fⱼⁿ dV` on `Q` (boundary values `0`), whose Monge–Ampère measures converge
weakly to `α`, and a constant `C` with `e₁(Uⱼ) ≤ C` for all `j`. -/
theorem exists_convolution_approximants (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R) (hαK : α Kᶜ = 0) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw) :
    ∃ (r : ℝ) (hr : 0 < r) (χ : ComplexModel n → ℝ) (F U : ℕ → ComplexModel n → ℝ)
      (hU : ∀ j, IsCegrellE0 (polydiskAtOpens a R) (U j)) (C : ℝ),
      cthickening (2 * r) K ⊆ polydiskAt a R ∧
      ContDiff ℝ ∞ χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ HasCompactSupport χ ∧
      (∀ j, ContDiff ℝ ∞ (F j) ∧ (∀ z, 0 ≤ F j z) ∧ HasCompactSupport (F j) ∧
        tsupport (F j) ⊆ polydiskAt a R) ∧
      (∀ j z, mongeAmpereConst n * F j z ^ n =
        convDensity α r hr j z + mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n) ∧
      (∀ j, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j) (hU j).psh =
        (volume.restrict (polydiskAt a R)).withDensity
          (fun z => ENNReal.ofReal (mongeAmpereConst n * F j z ^ n))) ∧
      (∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
        Tendsto (fun j => ∫ z, h z ∂canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j)
          (hU j).psh) atTop (𝓝 (∫ z, h z ∂α))) ∧
      ∀ j, (localEnergy (polydiskAtOpens a R) 1 (U j) (hU j).psh).toReal ≤ C := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQQ : (Q : Set (ComplexModel n)) = (polydiskAt a R) := rfl
  have hQm : MeasurableSet (polydiskAt a R) := (isOpen_polydiskAt a R).measurableSet
  have hQb : Bornology.IsBounded (polydiskAt a R) := isBounded_polydiskAt a hR
  obtain ⟨δ, hδ, hδQ⟩ := hK.exists_cthickening_subset_open (isOpen_polydiskAt a R) hKQ
  set r := δ / 4 with hrdef
  have hr : 0 < r := by positivity
  have h2r : cthickening (2 * r) K ⊆ polydiskAt a R :=
    (cthickening_mono (by rw [hrdef]; linarith) K).trans hδQ
  obtain ⟨χ, hχs, hχ01, hχ1, hχc, hχsupp⟩ := exists_smooth_cutoff hK hr
  set c := mongeAmpereConst n with hcdef
  have hc : 0 < c := mongeAmpereConst_pos
  set g : ℕ → ComplexModel n → ℝ := fun j => convDensity α r hr j with hgdef
  set ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹ with hεdef
  have hε : ∀ j, 0 < ε j := fun j => by positivity
  have hε1 : ∀ j, ε j ≤ 1 := fun j => inv_le_one_of_one_le₀ (by linarith [j.cast_nonneg (α := ℝ)])
  set F : ℕ → ComplexModel n → ℝ := fun j => rootDensity (g j) χ c (ε j) n with hFdef
  have hnn : ∀ j x, 0 ≤ g j x / c + ε j * χ x ^ n := fun j x =>
    add_nonneg (div_nonneg (convDensity_nonneg α hr j x) hc.le)
      (mul_nonneg (hε j).le (pow_nonneg (hχ01 x).1 n))
  have hgL : ∀ j, Function.support (g j) ⊆ cthickening r K :=
    fun j => support_convDensity_subset α hαK hr j
  have hχL : EqOn χ 1 (cthickening r K) := hχ1.mono (cthickening_mono (by linarith) K)
  have hFs : ∀ j, ContDiff ℝ ∞ (F j) := fun j =>
    contDiff_rootDensity (contDiff_convDensity α hr j) hχs (convDensity_nonneg α hr j)
      (fun x => (hχ01 x).1) isClosed_cthickening (hgL j) hχL hc (hε j) hn.ne'
  have hF0 : ∀ j x, 0 ≤ F j x := fun j x => rootDensity_nonneg _ _ _ _ _ x (hnn j x)
  have hFsupp : ∀ j, Function.support (F j) ⊆ Function.support χ := by
    intro j x hx
    by_contra hχx
    rw [Function.notMem_support] at hχx
    have hxL : x ∉ cthickening r K := fun h => by
      have := hχL h
      rw [hχx] at this
      exact zero_ne_one this
    have hgx : g j x = 0 := convDensity_eq_zero_of_notMem α hαK hr j hxL
    apply hx
    simp only [hFdef, rootDensity, hgx, hχx, zero_div, zero_add, ne_eq, hn.ne', not_false_eq_true,
      zero_pow, mul_zero]
    exact Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
  have hFc : ∀ j, HasCompactSupport (F j) := fun j =>
    hχc.mono' ((hFsupp j).trans (subset_tsupport χ))
  have hFtsupp : ∀ j, tsupport (F j) ⊆ polydiskAt a R := fun j =>
    (closure_mono (hFsupp j)).trans (hχsupp.trans ((cthickening_mono
      (by rw [hrdef]; linarith) K).trans hδQ))
  have hFpow : ∀ j x, c * F j x ^ n = g j x + c * ε j * χ x ^ n := by
    intro j x
    rw [hFdef, rootDensity_pow hn.ne' (hnn j x)]
    field_simp
  -- the Dirichlet problems
  have hsol := fun j => polydiskAt_dirichlet_C2 hn a hR
    ((hFs j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hF0 j) (hFc j) (hFtsupp j)
  choose U hUpsh hUma hUbd hUle _ using hsol
  have hUE0 : ∀ j, IsCegrellE0 Q (U j) := by
    intro j
    refine ⟨hUpsh j, exists_lower_bound_of_tendsto_frontier hQb (hUpsh j) (hUbd j), hUle j,
      hUbd j, ?_⟩
    obtain ⟨B, hB⟩ := (hFs j).continuous.bounded_above_of_compact_support (hFc j)
    change canonicalBedfordTaylorMeasure Q (U j) (hUpsh j) (polydiskAt a R) < ⊤
    rw [hUma j, withDensity_apply _ hQm]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal (c * B ^ n))
      measurable_const fun z _ => ?_) ?_
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc.le)
      have := hB z
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 j z)] at this
      exact pow_le_pow_left₀ (hF0 j z) this n
    · rw [setLIntegral_const]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [Measure.restrict_apply' hQm, inter_self]
      exact hQb.measure_lt_top
  -- the dominating measure and the dominating potential
  set μ : Measure (ComplexModel n) := α + ENNReal.ofReal c • volume.restrict (polydiskAt a R) with hμdef
  set W : ComplexModel n → ℝ := fun z => w z + 1 * (‖z‖ ^ 2 - 0) with hWdef
  have hW : IsLocallyBoundedPshOn Q W := by
    have := isLocallyBoundedPshOn_linComb hw hw (Ω := Q) (a := 1) (b := 0) (c := 1) zero_le_one
      le_rfl zero_le_one
    convert this using 1
    funext z
    simp [hWdef]
  set ρ := ‖a‖ + R * (n + 1) with hρdef
  have hWb : ∀ z ∈ Q, b ≤ W z ∧ W z ≤ b + (M + ρ ^ 2) := by
    intro z hz
    have h1 := hwb z hz
    have h2 : ‖z‖ ≤ ρ := norm_le_of_mem_polydiskAt hR hz
    have h3 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
    have h4 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    simp only [hWdef]
    constructor <;> nlinarith
  have hMW : 0 ≤ M + ρ ^ 2 := by positivity
  have hμW : μ.restrict Q ≤ canonicalBedfordTaylorMeasure Q W hW := by
    have hsum := ma_add_normSq_ge hn hw one_pos 0 hW
    rw [one_pow, mul_one] at hsum
    refine le_trans (le_of_eq ?_) (le_trans (add_le_add hα le_rfl) hsum)
    rw [hμdef, Measure.restrict_add, Measure.restrict_smul, hQQ, Measure.restrict_restrict hQm,
      inter_self]
  have hμfin : μ Q ≠ ⊤ := by
    rw [hμdef, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' hQm]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top α _, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
    rw [hQQ, inter_self]
    exact hQb.measure_lt_top.ne
  -- the energy comparison
  have hctrl : ∀ j, localEnergy Q 1 (U j) (hUE0 j).psh ≤
      ENNReal.ofReal 1 * ∫⁻ z in (Q : Set (ComplexModel n)), ENNReal.ofReal ((-U j z) ^ (1 : ℝ)) ∂μ := by
    intro j
    set Ũ : ComplexModel n → ℝ := (polydiskAt a R).indicator (U j) with hŨdef
    have hŨm : Measurable Ũ := measurable_indicator_of_plurisubharmonicOn (hUpsh j).1
    have hdm : Measurable fun z => ENNReal.ofReal (c * F j z ^ n) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul ((hFs j).continuous.measurable.pow_const n))
    rw [ENNReal.ofReal_one, one_mul]
    unfold localEnergy
    rw [hUma j, hQQ, restrict_withDensity hQm, Measure.restrict_restrict hQm, inter_self,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [Real.rpow_one, Pi.mul_apply]
    -- replace `U j` by the measurable `Ũ` on `Q`
    have e1 : ∫⁻ z in polydiskAt a R, ENNReal.ofReal (c * F j z ^ n) * ENNReal.ofReal (-U j z) =
        ∫⁻ z in polydiskAt a R, ENNReal.ofReal (g j z) * ENNReal.ofReal (-Ũ z) +
          ENNReal.ofReal (c * ε j * χ z ^ n) * ENNReal.ofReal (-Ũ z) := by
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hŨdef, indicator_of_mem hz]
      rw [hFpow, ENNReal.ofReal_add (convDensity_nonneg α hr j z)
        (by have := (hχ01 z).1; have := hε j; positivity), add_mul]
    have e2 : ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-U j z) ∂μ =
        ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-U j z) ∂α +
          ENNReal.ofReal c * ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-Ũ z) := by
      rw [hμdef, Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul,
        lintegral_smul_measure, Measure.restrict_restrict hQm, inter_self, smul_eq_mul]
      congr 2
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hŨdef, indicator_of_mem hz]
    have hm2 : Measurable fun z => ENNReal.ofReal (c * ε j * χ z ^ n) * ENNReal.ofReal (-Ũ z) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((hχs.continuous.measurable).pow_const n))).mul (ENNReal.measurable_ofReal.comp hŨm.neg)
    rw [e1, e2, lintegral_add_right _ hm2]
    refine add_le_add ?_ ?_
    · have := lintegral_convDensity_mul_le (Ω := Q) α hαK hr h2r (hUpsh j) (hUle j) j
      refine le_trans (le_of_eq ?_) this
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hgdef, hŨdef, indicator_of_mem hz]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hQm fun z hz => ?_
      gcongr
      have h1 := (hχ01 z).1
      have h2 : χ z ^ n ≤ 1 := pow_le_one₀ h1 (hχ01 z).2
      calc c * ε j * χ z ^ n ≤ c * 1 * 1 := by
            gcongr
            exact hε1 j
        _ = c := by ring
  -- weak convergence of the Monge–Ampère measures to `α`
  have hweak : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun j => ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUE0 j).psh) atTop
        (𝓝 (∫ z, h z ∂α)) := by
    intro h hhc hhs
    have hrep : ∀ j, ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUE0 j).psh =
        (∫ z, h z * g j z) + c * ε j * ∫ z in polydiskAt a R, χ z ^ n * h z := by
      intro j
      have hdm : Measurable fun z => ENNReal.ofReal (c * F j z ^ n) :=
        ENNReal.measurable_ofReal.comp
          (measurable_const.mul ((hFs j).continuous.measurable.pow_const n))
      change ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUpsh j) = _
      rw [hUma j, integral_withDensity_eq_integral_toReal_smul hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      have e : ∀ z, (ENNReal.ofReal (c * F j z ^ n)).toReal • h z =
          h z * g j z + c * ε j * (χ z ^ n * h z) := fun z => by
        rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (pow_nonneg (hF0 j z) n)), smul_eq_mul,
          hFpow]
        ring
      simp_rw [e]
      have hi1 : Integrable fun z => h z * g j z :=
        (hhc.mul (contDiff_convDensity α hr j).continuous).integrable_of_hasCompactSupport
          hhs.mul_right
      have hi2 : Integrable fun z => χ z ^ n * h z :=
        ((hχs.continuous.pow n).mul hhc).integrable_of_hasCompactSupport hhs.mul_left
      rw [integral_add hi1.integrableOn (hi2.integrableOn.const_mul _), integral_const_mul]
      congr 1
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
      have hzL : z ∉ cthickening r K := fun h' =>
        hz (h2r (cthickening_mono (by linarith) K h'))
      rw [show g j z = 0 from convDensity_eq_zero_of_notMem α hαK hr j hzL, mul_zero]
    simp_rw [hrep]
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa only [hεdef, one_div] using this
    have h2 : Tendsto (fun j => c * ε j * ∫ z in polydiskAt a R, χ z ^ n * h z) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := c)).mul hε0 |>.mul
        (tendsto_const_nhds (x := ∫ z in polydiskAt a R, χ z ^ n * h z))
      simpa only [mul_zero, zero_mul] using this
    simpa only [add_zero] using (tendsto_integral_mul_convDensity α hr hhc hhs).add h2
  refine ⟨r, hr, χ, F, U, hUE0, (1 * energyMomentConst n 1 (μ Q).toReal (M + ρ ^ 2)) ^
    (((n : ℝ) + 1) / n), h2r, hχs, hχ01, hχc, fun j => ⟨hFs j, hF0 j, hFc j, hFtsupp j⟩,
    fun j z => by rw [hFpow], fun j => hUma j, hweak, fun j => ?_⟩
  exact localEnergy_le_of_moment_control hn hQb (hUE0 j) hW hMW hWb hμW hμfin one_pos
    zero_le_one (hctrl j)

end SGPT.Envelopes.MADirichlet
