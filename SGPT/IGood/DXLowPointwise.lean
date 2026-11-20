import SGPT.IGood.DXLowCorrection
import SGPT.IGood.DXLowLocal

/-!
# The pointwise sharp lower bound of the weighted Bergman density

Blueprint `claude-dx-low`, node `claude-dx-low:pointwise`. Lower bound of the asymptotic
Riemann–Roch formula (source `thm:DXmain1`, `prop:DXmainanalytic`), Bergman-kernel route.

For a compact complex manifold `X` with a Kähler background `ω`, a smooth positive volume `μ`,
Hermitian holomorphic line bundles `L, T` with smooth metrics, `θ = c₁(L, h_L)` and
`φ ∈ PSH(X, θ - δω)` (`θ_φ` a Kähler current), the weighted Bergman density of
`H⁰(X, L^k ⊗ T)` is

`B_k(x) = sup {|s(x)|² e^{-kφ(x)} : ∫_X |s|² e^{-kφ} dμ ≤ 1}` (`bergmanDensity`).

Main result (`le_liminf_bergmanDensity`): at a point `x` near which `φ` is smooth (in the chart
`z_a` of a cover, `φ ∘ z_a⁻¹ = g` with `g` smooth near `p = z_a(x)`),

`smoothDensity Φ p / ρ(p) ≤ liminf_k (n!/kⁿ) B_k(x)`,

where `Φ = g - log |e_L|²` is the local weight of `h_L^k e^{-kφ}` (so `ddᶜΦ = θ_φ` near `x`),
`smoothDensity Φ p` is the density of `(ddᶜΦ)ⁿ` at `p` with respect to Lebesgue measure and
`ρ` is the density of `μ` in the chart: the right-hand side is the density of `θ_φⁿ / n!`
with respect to `μ`, times `n!`.

Proof (Tian, Demailly, Berman): the peak section `F = e^{k P(z - p)} e_L^k ⊗ e_T`, `P` the
quadratic holomorphic gauge of `Φ` at `p` (`DXLowLocal`), has
`|F|² e^{-kφ} = e^{-kΦ(p) - k(L(z-p) + R(z))} |e_T|²` with `L` the Levi form of `Φ` at `p` and
`|R| ≤ τ L` near `p`; cutting it off on a small ball and correcting it with the sharp
correction (`exists_section_through_point_sharp`) gives a global section `σ` with `σ(x) = F(x)`
and `∫ |σ|² e^{-kφ} ≤ e^{-kΦ(p)} |e_T(p)|² (A_τ k⁻ⁿ + C e^{-βk})`, where
`A_τ → ρ(p) n! / smoothDensity Φ p` as `τ → 0` (the Gaussian integral `lintegral_exp_neg_leviForm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section


open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SGPT.IGood.DXLow

/-- **The weighted Bergman density** of `H⁰(X, L^k ⊗ T)` for the weight `e^{-kφ}` and the measure
`μ`: `B_k(x) = sup {|s(x)|² e^{-kφ(x)} : ∫_X |s|² e^{-kφ} dμ ≤ 1}`. -/
def bergmanDensity (μ : Measure X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (φ : X → EReal) (k : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ s : twistedSections L T k, ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) *
      multiplierWeight (k : ℝ) (φ y) ∂μ ≤ 1),
    ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)

/-- Every section `σ` with `∫ |σ|² e^{-kφ} dμ ≤ c` gives `B_k(x) ≥ |σ(x)|² e^{-kφ(x)} / c`. -/
theorem div_le_bergmanDensity (μ : Measure X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (φ : X → EReal) (k : ℕ) (x : X) (σ : twistedSections L T k) {c : ℝ} (hc : 0 < c)
    (hσ : ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
      ENNReal.ofReal c) :
    ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) / ENNReal.ofReal c ≤
      bergmanDensity μ L T φ k x := by
  set t : ℝ := (Real.sqrt c)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  have ht2 : t ^ 2 = c⁻¹ := by rw [ht, inv_pow, Real.sq_sqrt hc.le]
  have hnorm : ∀ y, ‖((t : ℂ) • σ) y‖ ^ 2 = c⁻¹ * ‖σ y‖ ^ 2 := by
    intro y
    change ‖(t : ℂ) • σ y‖ ^ 2 = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le, mul_pow, ht2]
  have hci : ENNReal.ofReal c⁻¹ = (ENNReal.ofReal c)⁻¹ := ENNReal.ofReal_inv_of_pos hc
  have hint : ∫⁻ y, ENNReal.ofReal (‖((t : ℂ) • σ) y‖ ^ 2) *
      multiplierWeight (k : ℝ) (φ y) ∂μ ≤ 1 := by
    simp_rw [hnorm, ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hci]
    calc (ENNReal.ofReal c)⁻¹ * ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) *
          multiplierWeight (k : ℝ) (φ y) ∂μ ≤ (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c := by
          gcongr
      _ = 1 := ENNReal.inv_mul_cancel (by simpa using hc) ENNReal.ofReal_ne_top
  calc ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) / ENNReal.ofReal c
      = ENNReal.ofReal (‖((t : ℂ) • σ) x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) := by
        rw [hnorm, ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), hci, div_eq_mul_inv]
        ring
    _ ≤ bergmanDensity μ L T φ k x :=
        le_iSup_of_le ((t : ℂ) • σ) (le_iSup_of_le hint le_rfl)

end SGPT.IGood.DXLow

namespace SGPT.PSH.GlobalL2.CoverData

open SGPT.IGood.DXLow

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- The local weight `Φ = g - log |e_L|²` of `h_L^k e^{-kφ}` in chart `a`, for a local smooth
representative `g` of `φ`. -/
def peakWeight (a : Fin D.m) (g : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  g z + frameWeight (prefFrame L (D.pt a)) (D.chartA a) z

/-- The twist weight `-log |e_T|²` in chart `a`. -/
def peakTwistWeight (a : Fin D.m) (z : ComplexModel n) : ℝ :=
  frameWeight (prefFrame T (D.pt a)) (D.chartA a) z

/-- **The density in a chart** (finite weight): for `y` in chart `a` with `φ(y) = s` finite,
`|u|² e^{-k s} = |coef u|² e^{-k(s - log|e_L|²) + log |e_T|²}`. -/
theorem density_chart_eq (k : ℕ) (a : Fin D.m) {y : X} (hy : y ∈ (D.chartA a).val.source)
    (hyz : (D.chartA a).val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) (s : ℝ)
    (u : (twistedPower L T k).Fiber y) :
    ‖u‖ ^ 2 * Real.exp (-((k : ℝ) * s)) =
      ‖(D.frameE k a).val.continuousLinearMapAt ℂ y u‖ ^ 2 *
        Real.exp (-((k : ℝ) * (s + frameWeight (prefFrame L (D.pt a)) (D.chartA a)
          ((D.chartA a).val y))) - D.peakTwistWeight a ((D.chartA a).val y)) := by
  have hbs := D.mem_baseSets_of_mem hy hyz
  have hE := D.mem_frameE_baseSet (k := k) hy hyz
  have hsz : (D.chartA a).val.symm ((D.chartA a).val y) = y := (D.chartA a).val.left_inv hy
  set NL := ‖(prefFrame L (D.pt a)).val.symm y 1‖ with hNL
  set NT := ‖(prefFrame T (D.pt a)).val.symm y 1‖ with hNT
  have hNL0 : 0 < NL := frameNorm_pos L.Fiber (prefFrame L (D.pt a)).val hbs.1
  have hNT0 : 0 < NT := frameNorm_pos T.Fiber (prefFrame T (D.pt a)).val hbs.2
  have hnorm : ‖u‖ = ‖(D.frameE k a).val.continuousLinearMapAt ℂ y u‖ * (NL ^ k * NT) := by
    rw [norm_eq_coef_mul_norm_frame (D.frameE k a).val hE u]
    congr 1
    exact twistedPower_frame_norm _ _ hbs.1 hbs.2 k
  have hwL : frameWeight (prefFrame L (D.pt a)) (D.chartA a) ((D.chartA a).val y) =
      -Real.log (NL ^ 2) := by rw [frameWeight, hsz]
  have hwT : D.peakTwistWeight a ((D.chartA a).val y) = -Real.log (NT ^ 2) := by
    rw [peakTwistWeight, frameWeight, hsz]
  rw [hwL, hwT, hnorm]
  have h1 : Real.exp (-((k : ℝ) * (s + -Real.log (NL ^ 2))) - -Real.log (NT ^ 2)) =
      Real.exp (-((k : ℝ) * s)) * ((NL ^ 2) ^ k * NT ^ 2) := by
    rw [show -((k : ℝ) * (s + -Real.log (NL ^ 2))) - -Real.log (NT ^ 2) =
      -((k : ℝ) * s) + ((k : ℝ) * Real.log (NL ^ 2) + Real.log (NT ^ 2)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
  rw [h1]
  have : (NL ^ k * NT) ^ 2 = (NL ^ 2) ^ k * NT ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  rw [mul_pow, this]
  ring

/-- **The cut-off of the peak section**: a chart bump `χ = 1` on `B(p, 2ε)`, supported in
`B̄(p, 3ε)`, with the compact annulus `K` where it is not locally constant and a common bound for
`|∂̄χ|²` in all charts of the cover. -/
theorem exists_peak_cutoff (a : Fin D.m) {p : ComplexModel n}
    (hp : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {ε : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ D.cutEps a) :
    ∃ χ : X → ℝ, ∃ K : Set X, ChartSmooth (n := n) χ ∧ (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧
      tsupport χ ⊆ (D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' ball p (4 * ε) ∧
      (∀ y ∈ (D.chartA a).val.source, (D.chartA a).val y ∈ ball p ε → χ y = 1) ∧
      IsCompact K ∧ K ⊆ (D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' ball p (4 * ε) ∧
      (∀ y ∈ K, ε ≤ ‖(D.chartA a).val y - p‖) ∧
      (∀ y ∈ ((D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' ball p (4 * ε)) \ K,
        ∀ᶠ y' in 𝓝 y, χ y' = χ y) ∧
      ∃ Mχ : ℝ, 0 ≤ Mχ ∧ ∀ l, ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
        dbarNormSq (fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ Mχ := by
  set c := D.chartA a with hc
  let bump : ContDiffBump p := ⟨2 * ε, 3 * ε, by linarith, by linarith⟩
  set χ : X → ℝ := Pending.ChartPartition.chartExtend c bump with hχdef
  have htar : closedBall p (3 * ε) ⊆ c.val.target :=
    (D.closedBall_subset_of_mem hp (by linarith [D.cutEps_le a, D.R_pos a])).trans
      (D.closedBall_subset_target a)
  have htsupp : tsupport bump = closedBall p (3 * ε) := bump.tsupport_eq
  have hχ : ChartSmooth (n := n) χ :=
    Pending.ChartPartition.chartSmooth_chartExtend c bump.contDiff
      bump.hasCompactSupport.isCompact (by rw [htsupp]; exact htar)
  have himg : ∀ w ∈ closedBall p (3 * ε), c.val.symm w ∈ c.val.source ∧
      c.val (c.val.symm w) = w := fun w hw =>
    ⟨c.val.map_target (htar hw), c.val.right_inv (htar hw)⟩
  have hχU : tsupport χ ⊆ c.val.source ∩ c.val ⁻¹' ball p (4 * ε) := by
    refine (Pending.ChartPartition.support_chartExtend_subset c).trans ?_
    rw [htsupp]
    have hcomp : IsCompact (c.val.symm '' closedBall p (3 * ε)) :=
      (isCompact_closedBall p _).image_of_continuousOn (c.val.continuousOn_symm.mono htar)
    rw [hcomp.isClosed.closure_eq]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(himg w hw).1, ?_⟩
    rw [mem_preimage, (himg w hw).2, mem_ball]
    have : dist w p ≤ 3 * ε := hw
    linarith
  have hχone : ∀ y ∈ c.val.source, c.val y ∈ ball p ε → χ y = 1 := by
    intro y hy hyε
    rw [hχdef, Pending.ChartPartition.chartExtend_of_mem hy]
    refine bump.one_of_mem_closedBall ?_
    have : dist (c.val y) p < ε := hyε
    show dist (c.val y) p ≤ 2 * ε
    linarith
  set A₀ : Set (ComplexModel n) := closedBall p (3 * ε) ∩ {w | 2 * ε ≤ dist w p} with hA₀
  set K : Set X := c.val.symm '' A₀ with hKdef
  have hA₀c : IsCompact A₀ := (isCompact_closedBall p _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hK : IsCompact K :=
    hA₀c.image_of_continuousOn (c.val.continuousOn_symm.mono fun w hw => htar hw.1)
  have hKU : K ⊆ c.val.source ∩ c.val ⁻¹' ball p (4 * ε) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(himg w hw.1).1, ?_⟩
    rw [mem_preimage, (himg w hw.1).2, mem_ball]
    have : dist w p ≤ 3 * ε := hw.1
    linarith
  have hKann : ∀ y ∈ K, ε ≤ ‖c.val y - p‖ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [(himg w hw.1).2, ← dist_eq_norm]
    have : 2 * ε ≤ dist w p := hw.2
    linarith
  have hconst : ∀ y ∈ (c.val.source ∩ c.val ⁻¹' ball p (4 * ε)) \ K,
      ∀ᶠ y' in 𝓝 y, χ y' = χ y := by
    rintro y ⟨⟨hy, -⟩, hyK⟩
    by_cases h2 : dist (c.val y) p < 2 * ε
    · have hO : IsOpen (c.val.source ∩ c.val ⁻¹' ball p (2 * ε)) :=
        c.val.isOpen_inter_preimage isOpen_ball
      have hval : ∀ y' ∈ c.val.source ∩ c.val ⁻¹' ball p (2 * ε), χ y' = 1 := by
        intro y' hy'
        rw [hχdef, Pending.ChartPartition.chartExtend_of_mem hy'.1]
        exact bump.one_of_mem_closedBall (ball_subset_closedBall hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h2⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h2⟩]
    · have h3 : 3 * ε < dist (c.val y) p := by
        by_contra hle
        refine hyK ⟨c.val y, ⟨?_, ?_⟩, c.val.left_inv hy⟩
        · show dist (c.val y) p ≤ 3 * ε; linarith
        · show 2 * ε ≤ dist (c.val y) p; linarith
      have hO : IsOpen (c.val.source ∩ c.val ⁻¹' {w | 3 * ε < dist w p}) :=
        c.val.isOpen_inter_preimage (isOpen_lt continuous_const (continuous_id.dist continuous_const))
      have hval : ∀ y' ∈ c.val.source ∩ c.val ⁻¹' {w | 3 * ε < dist w p}, χ y' = 0 := by
        intro y' hy'
        rw [hχdef, Pending.ChartPartition.chartExtend_of_mem hy'.1]
        exact bump.zero_of_le_dist (le_of_lt hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h3⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h3⟩]
  have hM : ∀ l : Fin D.m, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ C :=
    fun l => bound_dbarNormSq_χ hχ (D.pt l) (D.closedBall_subset_target l)
  choose C hC0 hC using hM
  refine ⟨χ, K, hχ, Pending.ChartPartition.chartExtend_nonneg fun z => bump.nonneg,
    Pending.ChartPartition.chartExtend_le_one fun z => bump.le_one, hχU, hχone, hK, hKU,
    hKann, hconst, ∑ l, C l, Finset.sum_nonneg fun l _ => hC0 l, fun l z hz => ?_⟩
  exact (hC l z hz).trans (Finset.single_le_sum (f := C) (fun l _ => hC0 l) (Finset.mem_univ l))

/-- **Positivity of the local weight**: if `φ ∈ PSH(X, θ - δω)` agrees near `p` with a smooth
`g`, then `Levi(g - log |e_L|²)(p) ≥ δ c_ω |v|²`. -/
theorem le_leviForm_peakWeight (hL : IsSourceSmoothHermitianMetric L)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ) (a : Fin D.m)
    {p : ComplexModel n} (hp : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a))
    {g : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U) (hpU : p ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (hgφ : ∀ z ∈ U, φ ((D.chartA a).val.symm z) = (g z : EReal))
    (v : ComplexModel n) :
    δ * D.cω a * ‖v‖ ^ 2 ≤ leviForm (D.peakWeight a g) p v := by
  set c := D.chartA a with hc
  set ρ' := D.ρ' a with hρ'
  have hpot := D.pot a
  set U' : Set (ComplexModel n) := U ∩ ball (ctr (n := n) (D.pt a)) (2 * D.R a) with hU'
  have hU'o : IsOpen U' := hU.inter isOpen_ball
  have hpU' : p ∈ U' := ⟨hpU, D.ball_subset_two a hp⟩
  have hpsh := plurisubharmonicOn_add_localPotential hφ c hpot
  have hsm : ContDiffOn ℝ ∞ (fun z => ρ' z + g z) U' :=
    (hpot.2.2.1.mono inter_subset_right).add (hg.mono inter_subset_left)
  have hpsh' : PlurisubharmonicOn (fun z => ((ρ' z + g z : ℝ) : EReal)) U' := by
    intro z hz
    refine (hpsh z hz.2).congr (Filter.eventuallyEq_of_mem (hU'o.mem_nhds hz) fun w hw => ?_)
    show (ρ' w : EReal) + φ (c.val.symm w) = ((ρ' w + g w : ℝ) : EReal)
    rw [hgφ w hw.1, EReal.coe_add]
  have h0 : 0 ≤ leviForm (fun z => ρ' z + g z) p v :=
    leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := ⟨U', hU'o⟩) hsm hpsh' hpU' v
  have hfw : ContDiffOn ℝ ∞ (fun z => frameWeight (prefFrame L (D.pt a)) c z - ρ' z)
      (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
    (D.contDiffOn_frameWeight_L hL a).sub hpot.2.2.1
  have h1 : δ * D.cω a * ‖v‖ ^ 2 ≤
      leviForm (fun z => frameWeight (prefFrame L (D.pt a)) c z - ρ' z) p v :=
    D.levi_L a p hp v
  have hs1 : ContDiffAt ℝ 2 (fun z => ρ' z + g z) p :=
    ((hsm p hpU').contDiffAt (hU'o.mem_nhds hpU')).of_le (by norm_cast)
  have hs2 : ContDiffAt ℝ 2 (fun z => frameWeight (prefFrame L (D.pt a)) c z - ρ' z) p :=
    ((hfw p (D.ball_subset_two a hp)).contDiffAt (isOpen_ball.mem_nhds (D.ball_subset_two a hp))).of_le
      (by norm_cast)
  have heq : D.peakWeight a g = (fun z => ρ' z + g z) +
      (fun z => frameWeight (prefFrame L (D.pt a)) c z - ρ' z) := by
    funext z
    simp only [peakWeight, Pi.add_apply]
    ring
  rw [heq, leviForm_add hs1 hs2]
  linarith

/-- **The pole at the peak point** `ψ = (n+1) log |z_a - p|²` near `p` (as in
`globalPointExtension_pos`), and the psh property of the pole weight `φ + ψ/k`. -/
theorem exists_peak_pole (hn : 0 < n) (a : Fin D.m) {x : X} (hxa : x ∈ (D.chartA a).val.source)
    (hpc : (D.chartA a).val x ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) {ε : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ D.poleR a) :
    ∃ B' : ℝ, 0 < B' ∧ ∃ ψ : X → EReal, (∀ y, ψ y ≤ 0) ∧
      (∀ y ∈ (D.chartA a).val.source, (D.chartA a).val y ∈ ball ((D.chartA a).val x) ε →
        ψ y = (((n : ℝ) + 1 : ℝ) : EReal) * logNormSq ((D.chartA a).val y - (D.chartA a).val x)) ∧
      (∀ y, (y ∈ (D.chartA a).val.source →
          ε ≤ ‖(D.chartA a).val y - (D.chartA a).val x‖) →
        ((((n : ℝ) + 1) * Real.log (ε ^ 2) : ℝ) : EReal) ≤ ψ y) ∧
      ∀ {δ' : ℝ} {φ : X → EReal} {k : ℕ}, 0 < k → 2 * B' ≤ k * δ' →
        IsThetaPshPotential (θ - δ' • ωb.form).val φ →
        IsThetaPshPotential (θ - (δ' / 2) • ωb.form).val (poleWeight φ ψ k) := by
  set c := D.chartA a with hc
  set p := c.val x with hp
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_poleB
  have hP := D.poleRadii a hpc
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  have hpsh := thetaPlurisubharmonic_poleFun ωb hP (m := mω)
    (fun w hw v => hmω w (D.closedBall_subset_of_mem hpc (by linarith [D.R_pos a]) hw) v)
    hB0.le hBm
  have hinj : ∀ y ∈ c.val.source, c.val y = p → y = x := fun y hy h => c.val.injOn hy hxa h
  set ψ := D.polePsi a p with hψdef
  set B' : ℝ := ((n : ℝ) + 1) * B with hB'
  have hψpsh : ThetaPlurisubharmonic (B' • ωb.form).val ψ := by
    have := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
      (c := (n : ℝ) + 1) (by positivity) hpsh
    rwa [smul_smul] at this
  have hψne : ∀ y, y ≠ x → ψ y ≠ ⊥ := by
    intro y hyx
    have hP0 : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y ≠ ⊥ :=
      poleFun_ne_bot fun hy h => hyx (hinj y hy h)
    show (((n : ℝ) + 1 : ℝ) : EReal) * _ ≠ ⊥
    induction h : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y using EReal.rec with
    | bot => exact absurd h hP0
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
  refine ⟨B', by positivity, ψ, fun y => coe_mul_nonpos (by positivity) (poleFun_le hP y),
    ?_, ?_, ?_⟩
  · intro y hy hyε
    have hdist : dist (c.val y) p < ε := hyε
    show (((n : ℝ) + 1 : ℝ) : EReal) * poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y = _
    rw [poleFun_of_mem hy (by rw [mem_ball]; linarith [D.poleR_le a, D.R_pos a]),
      poleChart_eq_logNormSq (by rw [← dist_eq_norm]; linarith)]
  · intro y hy
    exact coe_mul_le_coe_mul (by positivity) (log_le_poleFun hε hεr hy)
  · intro δ' φ k hk hkB hφ
    exact isThetaPshPotential_poleWeight hn ωb hk hkB hφ hψpsh hψne

end SGPT.PSH.GlobalL2.CoverData

namespace SGPT.IGood.DXLow

/-- The peak profile `e^{k P(z - p)}`, `P` the quadratic holomorphic gauge of `Φ` at `p`. -/
def peakProfile (Φ : ComplexModel n → ℝ) (p : ComplexModel n) (k : ℕ) (z : ComplexModel n) : ℂ :=
  Complex.exp ((k : ℂ) * gaugeExponent Φ p (z - p))

theorem peakProfile_differentiable (Φ : ComplexModel n → ℝ) (p : ComplexModel n) (k : ℕ) :
    Differentiable ℂ (peakProfile Φ p k) := by
  unfold peakProfile
  exact Complex.differentiable_exp.comp ((differentiable_const _).mul
    ((gaugeExponent_differentiable Φ p).comp (differentiable_id.sub_const p)))

@[simp] theorem peakProfile_center (Φ : ComplexModel n → ℝ) (p : ComplexModel n) (k : ℕ) :
    peakProfile Φ p k p = 1 := by
  simp [peakProfile]

/-- `|e^{kP(z-p)}|² e^{-kΦ(z)} = e^{-kΦ(p)} e^{-k(L(z - p) + R(z))}`. -/
theorem norm_peakProfile_sq_mul (Φ : ComplexModel n → ℝ) (p : ComplexModel n) (k : ℕ)
    (z : ComplexModel n) (q : ℝ) :
    ‖peakProfile Φ p k z‖ ^ 2 * Real.exp (-((k : ℝ) * Φ z) - q) =
      Real.exp (-((k : ℝ) * Φ p)) *
        Real.exp (-((k : ℝ) * (leviForm Φ p (z - p) + taylorResidual Φ p z)) - q) := by
  have hn : ‖peakProfile Φ p k z‖ ^ 2 =
      Real.exp (2 * ((k : ℝ) * (gaugeExponent Φ p (z - p)).re)) := by
    rw [peakProfile, Complex.norm_exp, ← Real.exp_nat_mul]
    · congr 1
      rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      push_cast
      ring
  have hg := gauge_identity Φ p z
  rw [hn, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hg]
  ring

end SGPT.IGood.DXLow

namespace SGPT.IGood.DXLow

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}

/-- **The peak estimate for one `τ`** (blueprint `claude-dx-low:pointwise`): with
`A_τ = (1+τ)² ρ(p) / ((1-τ)ⁿ smoothDensity Φ p)`, there are `C ≥ 0`, `β > 0` with
`1 / (A_τ + C kⁿ e^{-βk}) ≤ (n!/kⁿ) B_k(x)` for all large `k`. -/
theorem eventually_peak_lower (hn : 0 < n) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (D : CoverData ωb μ L T θ (δ / 2)) (a : Fin D.m) {x : X}
    (hxa : x ∈ (D.chartA a).val.source)
    (hxr : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4))
    {g : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hxU : (D.chartA a).val x ∈ U) (hg : ContDiffOn ℝ ∞ g U)
    (hgφ : ∀ z ∈ U, φ ((D.chartA a).val.symm z) = (g z : EReal))
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    0 < D.dens a ((D.chartA a).val x) ∧
    0 < smoothDensity (D.peakWeight a g) ((D.chartA a).val x) ∧
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (1 / ((1 + τ) ^ 2 * D.dens a ((D.chartA a).val x) /
          ((1 - τ) ^ n * smoothDensity (D.peakWeight a g) ((D.chartA a).val x)) +
          C * ((k : ℝ) ^ n * Real.exp (-(β * k))))) ≤
        ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) * bergmanDensity μ L T φ k x := by
  classical
  set c := D.chartA a with hc
  set p := c.val x with hp
  set Φ := D.peakWeight a g with hΦdef
  set fT := D.peakTwistWeight a with hfT
  set ρ := D.dens a with hρ
  have hRa := D.R_pos a
  have hpR : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    ball_subset_ball (by linarith) hxr
  have hpc : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) := ball_subset_closedBall hxr
  have hφ2 : IsThetaPshPotential (θ - (δ / 2) • ωb.form).val φ := by
    have h := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
      (Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive (half_pos hδ).le)
    have hform : θ - δ • ωb.form + (δ / 2) • ωb.form = θ - (δ / 2) • ωb.form := by module
    rwa [hform] at h
  -- the smooth region
  set V : Set (ComplexModel n) := U ∩ ball (ctr (n := n) (D.pt a)) (D.R a) with hV
  have hVo : IsOpen V := hU.inter isOpen_ball
  have hpV : p ∈ V := ⟨hxU, hpR⟩
  have hfwL : ContDiffOn ℝ ∞ (frameWeight (prefFrame L (D.pt a)) c) V :=
    (D.contDiffOn_frameWeight_L hL a).mono fun z hz => D.ball_subset_two a hz.2
  have hΦs : ContDiffOn ℝ ∞ Φ V := (hg.mono inter_subset_left).add hfwL
  have hfTs : ContDiffOn ℝ ∞ fT V :=
    (D.contDiffOn_frameWeight_T hT a).mono fun z hz => D.ball_subset_two a hz.2
  have hVt : V ⊆ c.val.target := fun z hz => D.ball_subset_target a hz.2
  -- positivity of the Levi form
  set c₀ : ℝ := δ / 2 * D.cω a with hc₀def
  have hc₀ : 0 < c₀ := mul_pos (half_pos hδ) (D.cω_pos a)
  have hlevi : ∀ v, c₀ * ‖v‖ ^ 2 ≤ leviForm Φ p v :=
    fun v => D.le_leviForm_peakWeight hL hφ2 a hpR hU hxU hg hgφ v
  have hΦ2 : ContDiffAt ℝ 2 Φ p :=
    ((hΦs p hpV).contDiffAt (hVo.mem_nhds hpV)).of_le (by norm_cast)
  have hlevipos : ∀ v : ComplexModel n, v ≠ 0 → 0 < leviForm Φ p v := fun v hv =>
    lt_of_lt_of_le (mul_pos hc₀ (pow_pos (norm_pos_iff.mpr hv) 2)) (hlevi v)
  have hsD : 0 < smoothDensity Φ p := smoothDensity_pos hΦ2 hlevipos
  have hρp : 0 < ρ p := by
    have h1 := D.one_le a p hpR
    by_contra hneg
    have hneg' : ρ p ≤ 0 := not_lt.mp hneg
    have := mul_nonpos_of_nonneg_of_nonpos D.Aμ_pos.le hneg'
    linarith
  -- the radius
  obtain ⟨r₁, hr₁, hr₁V, hres⟩ := exists_taylorResidual_le hVo (hΦs.of_le (by norm_cast))
    hpV (η := τ * c₀) (by positivity)
  have hcontρ : ContinuousAt (fun z => Real.exp (-fT z) * ρ z) p := by
    have h1 : ContinuousAt fT p := (hfTs.continuousOn.continuousAt (hVo.mem_nhds hpV))
    have h2 : ContinuousAt ρ p := (D.dens_cont a).continuousAt
      ((c.val.open_target).mem_nhds (hVt hpV))
    exact (Real.continuous_exp.continuousAt.comp h1.neg).mul h2
  set M : ℝ := (1 + τ) * (Real.exp (-fT p) * ρ p) with hMdef
  have hM0 : 0 < Real.exp (-fT p) * ρ p := mul_pos (Real.exp_pos _) hρp
  have hMpos : 0 < M := by positivity
  obtain ⟨r₂, hr₂, hr₂ball⟩ := Metric.mem_nhds_iff.mp (hcontρ.eventually
    (gt_mem_nhds (show Real.exp (-fT p) * ρ p < M by rw [hMdef]; nlinarith)))
  set r : ℝ := min r₁ (r₂ / 2) with hrdef
  have hr : 0 < r := lt_min hr₁ (half_pos hr₂)
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrball : ∀ z ∈ closedBall p r, z ∈ V ∧
      |taylorResidual Φ p z| ≤ τ * c₀ * ‖z - p‖ ^ 2 ∧ Real.exp (-fT z) * ρ z ≤ M := by
    intro z hz
    have hz1 : z ∈ closedBall p r₁ := closedBall_subset_closedBall hrr₁ hz
    refine ⟨hr₁V hz1, hres z hz1, (hr₂ball ?_).le⟩
    have : dist z p ≤ r := hz
    rw [mem_ball]
    linarith [min_le_right r₁ (r₂ / 2)]
  set ε : ℝ := min (r / 4) (D.cutEps a) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (D.cutEps_pos a)
  have hε4 : 4 * ε ≤ r := by linarith [min_le_left (r / 4) (D.cutEps a)]
  have hεcut : ε ≤ D.cutEps a := min_le_right _ _
  have hεpole : ε ≤ D.poleR a := by
    have : D.cutEps a ≤ D.poleR a := by unfold CoverData.cutEps; linarith [D.poleR_pos a]
    linarith
  have hball4 : ball p (4 * ε) ⊆ closedBall p r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hε4)
  have hΩR : ball p (4 * ε) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2) := by
    intro z hz
    have h1 : dist z p < 4 * ε := hz
    have h2 : dist p (ctr (n := n) (D.pt a)) < D.R a / 4 := hxr
    have h3 : 4 * ε ≤ D.R a / 8 := by linarith [D.cutEps_le a]
    rw [mem_ball]
    linarith [dist_triangle z p (ctr (n := n) (D.pt a))]
  have hΩR' : ball p (4 * ε) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    hΩR.trans (ball_subset_ball (by linarith))
  -- the pole and the cut-off
  obtain ⟨B', hB', ψ, hψ0, hψpole, hψlow, hψpsh⟩ := D.exists_peak_pole hn a hxa hpc hε hεpole
  obtain ⟨χ, K, hχ, hχ0, hχ1, hχU, hχone, hK, hKU, hKann, hconst, Mχ, hMχ0, hMχ⟩ :=
    D.exists_peak_cutoff a hpc hε hεcut
  -- the constants
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2)))) with he
  set Cs : ℝ := (D.sharpConst Mχ e).toReal with hCs
  have hCsne : D.sharpConst Mχ e ≠ ⊤ := D.sharpConst_ne_top Mχ ENNReal.ofReal_ne_top
  set Vol : ℝ := (volume (ball p (4 * ε))).toReal with hVol
  set β : ℝ := (1 - τ) * c₀ * ε ^ 2 with hβ
  have hβ0 : 0 < β := by
    have : 0 < 1 - τ := by linarith
    positivity
  set C : ℝ := (1 + 1 / τ) * (1 + τ) * Cs * ρ p * Vol / (n.factorial : ℝ) with hCdef
  have hCs0 : 0 ≤ Cs := ENNReal.toReal_nonneg
  have hVol0 : 0 ≤ Vol := ENNReal.toReal_nonneg
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  refine ⟨hρp, hsD, C, β, by positivity, hβ0, ?_⟩
  obtain ⟨k₁, hk₁⟩ := D.exists_goodPower (half_pos hδ)
  filter_upwards [eventually_ge_atTop (max k₁ (⌈2 * B' / δ⌉₊ + 1))] with k hk
  have hkD : D.GoodPower k := hk₁ k (le_of_max_le_left hk)
  have hk0 : 0 < k := hkD.1
  have hkB : 2 * B' ≤ k * δ := by
    have h1 : ⌈2 * B' / δ⌉₊ + 1 ≤ k := le_of_max_le_right hk
    have h2 : 2 * B' / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans h1)
    rw [div_le_iff₀ hδ] at h2; linarith
  have hφ' := hψpsh hk0 hkB hφ
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  -- the peak section
  set F₀ := peakProfile Φ p k with hF₀def
  have hF₀ : DifferentiableOn ℂ F₀ (ball p (4 * ε)) :=
    (peakProfile_differentiable Φ p k).differentiableOn
  have hF₀p : F₀ p = 1 := peakProfile_center Φ p k
  set v : (twistedPower L T k).Fiber x := (D.frameE k a).val.symm x 1 with hvdef
  have hcoef : (D.frameE k a).val.continuousLinearMapAt ℂ x v = 1 :=
    trivialization_coef_frame _ (D.mem_frameE_baseSet hxa hpR)
  set F := D.chartSection k a (ball p (4 * ε)) 1 F₀ with hFdef
  set Uy : Set X := c.val.source ∩ c.val ⁻¹' ball p (4 * ε) with hUy
  have hUyo : IsOpen Uy := c.val.isOpen_inter_preimage isOpen_ball
  set G : X → ℝ≥0∞ := fun y => ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
    with hGdef
  set H : ComplexModel n → ℝ := fun z => ‖F₀ z‖ ^ 2 * Real.exp (-((k : ℝ) * Φ z) - fT z)
    with hHdef
  have hBt : ball p (4 * ε) ⊆ c.val.target := fun z hz => hVt (hrball z (hball4 hz)).1
  -- the density of `F` in the chart
  have hGeq : ∀ y ∈ Uy, G y = ENNReal.ofReal (H (c.val y)) := by
    intro y hy
    have hz : c.val y ∈ closedBall p r := hball4 hy.2
    obtain ⟨hzV, -, -⟩ := hrball _ hz
    have hφy : φ y = (g (c.val y) : EReal) := by
      have := hgφ (c.val y) hzV.1
      rwa [c.val.left_inv hy.1] at this
    have hyR : c.val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := hzV.2
    have hd := D.density_chart_eq k a hy.1 hyR (g (c.val y)) (F y)
    have hcf : (D.frameE k a).val.continuousLinearMapAt ℂ y (F y) = F₀ (c.val y) := by
      rw [hFdef, D.coef_chartSection hΩR' hy.1 hy.2, one_mul]
    simp only [hGdef, hHdef, hφy, multiplierWeight_coe]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hd, hcf]
    rfl
  have hHc : ContinuousOn H (ball p (4 * ε)) := by
    have hV4 : ball p (4 * ε) ⊆ V := fun z hz => (hrball z (hball4 hz)).1
    refine ((peakProfile_differentiable Φ p k).continuous.norm.pow 2).continuousOn.mul ?_
    exact Real.continuous_exp.comp_continuousOn
      (((continuousOn_const.mul (hΦs.continuousOn.mono hV4)).neg).sub
        (hfTs.continuousOn.mono hV4))
  have hH0 : ∀ z, 0 ≤ H z := fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  set E : ℝ := Real.exp (-((k : ℝ) * Φ p)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  -- the pointwise Gaussian bound
  have hHle : ∀ z ∈ ball p (4 * ε), H z * ρ z ≤
      E * M * Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p (z - p))) := by
    intro z hz
    obtain ⟨hzV, hzres, hzM⟩ := hrball z (hball4 hz)
    have hρz : 0 ≤ ρ z := by
      have h1 := D.one_le a z hzV.2
      by_contra hneg
      have hneg' : ρ z < 0 := not_le.mp hneg
      have := mul_neg_of_pos_of_neg D.Aμ_pos hneg'
      linarith
    have h1 := norm_peakProfile_sq_mul Φ p k z (fT z)
    have hLR : (1 - τ) * leviForm Φ p (z - p) ≤
        leviForm Φ p (z - p) + taylorResidual Φ p z := by
      have h2 := hlevi (z - p)
      have h3 := (abs_le.mp hzres).1
      have h4 : τ * c₀ * ‖z - p‖ ^ 2 ≤ τ * leviForm Φ p (z - p) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hτ0.le
      linarith
    have hexp : Real.exp (-((k : ℝ) * (leviForm Φ p (z - p) + taylorResidual Φ p z))) ≤
        Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p (z - p))) := by
      apply Real.exp_le_exp.mpr
      have h5 := mul_le_mul_of_nonneg_left hLR hkr.le
      rw [show -(((k : ℝ) * (1 - τ)) * leviForm Φ p (z - p)) =
        -((k : ℝ) * ((1 - τ) * leviForm Φ p (z - p))) by ring]
      linarith
    calc H z * ρ z = E * (Real.exp (-((k : ℝ) * (leviForm Φ p (z - p) +
          taylorResidual Φ p z))) * (Real.exp (-fT z) * ρ z)) := by
          simp only [hHdef]
          rw [h1, sub_eq_add_neg, Real.exp_add]
          ring
      _ ≤ E * (Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p (z - p))) * M) := by
          gcongr
      _ = _ := by ring
  -- the mass of `F` on the ball
  have hmeasH : AEMeasurable (fun z => ENNReal.ofReal (H z)) (volume.restrict (ball p (4 * ε))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hHc.aemeasurable measurableSet_ball)
  have hchart : ∀ f : ComplexModel n → ℝ≥0∞,
      AEMeasurable f (volume.restrict (ball p (4 * ε))) →
      ∫⁻ y in Uy, f (c.val y) ∂μ = ∫⁻ z in ball p (4 * ε), f z * ENNReal.ofReal (ρ z) := by
    intro f hf
    have hmeas : AEMeasurable (fun z => f (c.val (c.val.symm z)))
        (volume.restrict (ball p (4 * ε))) := by
      refine hf.congr ?_
      refine (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_)
      simp only [c.val.right_inv (hBt hz)]
    rw [setLIntegral_chart_ball c (D.dens_cont a) (D.dens_map a) isOpen_ball hBt hmeas]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    simp only [c.val.right_inv (hBt hz)]
    rfl
  have hIU : ∫⁻ y in Uy, G y ∂μ ≤ ENNReal.ofReal (E * M *
      ((n.factorial : ℝ) / (((k : ℝ) * (1 - τ)) ^ n * smoothDensity Φ p))) := by
    have hcongr : ∫⁻ y in Uy, G y ∂μ = ∫⁻ y in Uy, ENNReal.ofReal (H (c.val y)) ∂μ :=
      setLIntegral_congr_fun hUyo.measurableSet (fun y hy => hGeq y hy)
    have ht : 0 < (k : ℝ) * (1 - τ) := mul_pos hkr (by linarith)
    rw [hcongr, hchart _ hmeasH]
    calc ∫⁻ z in ball p (4 * ε), ENNReal.ofReal (H z) * ENNReal.ofReal (ρ z)
        ≤ ∫⁻ z in ball p (4 * ε), ENNReal.ofReal (E * M) *
            (fun w => ENNReal.ofReal (Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p w))))
              (z - p) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          rw [← ENNReal.ofReal_mul (hH0 z), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal ((hHle z hz).trans_eq (by ring))
      _ ≤ ∫⁻ z, ENNReal.ofReal (E * M) *
            (fun w => ENNReal.ofReal (Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p w))))
              (z - p) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (E * M) * ∫⁻ w, ENNReal.ofReal
            (Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p w))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun w => ENNReal.ofReal
              (Real.exp (-(((k : ℝ) * (1 - τ)) * leviForm Φ p w)))) p]
      _ = _ := by
          rw [lintegral_exp_neg_leviForm hΦ2 hlevipos ht, ← ENNReal.ofReal_mul (by positivity)]
  -- the mass of `F` on the annulus
  have hIK : ∫⁻ y in K, G y ∂μ ≤
      ENNReal.ofReal (E * M * Real.exp (-(β * k)) * Vol) := by
    set Ann : Set (ComplexModel n) := {z | ε ≤ ‖z - p‖} with hAnn
    have hAnnc : IsClosed Ann :=
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
    set G' : X → ℝ≥0∞ := fun y => Ann.indicator (fun z => ENNReal.ofReal (H z)) (c.val y)
      with hG'
    have h1 : ∫⁻ y in K, G y ∂μ ≤ ∫⁻ y in Uy, G' y ∂μ := by
      calc ∫⁻ y in K, G y ∂μ = ∫⁻ y in K, G' y ∂μ := by
            refine setLIntegral_congr_fun hK.isClosed.measurableSet fun y hy => ?_
            have hyAnn : c.val y ∈ Ann := hKann y hy
            simp only [hG', indicator_of_mem hyAnn]
            exact hGeq y (hKU hy)
        _ ≤ ∫⁻ y in Uy, G' y ∂μ := lintegral_mono_set hKU
    have hmeas : AEMeasurable (Ann.indicator fun z => ENNReal.ofReal (H z))
        (volume.restrict (ball p (4 * ε))) :=
      hmeasH.indicator hAnnc.measurableSet
    refine h1.trans ?_
    rw [hchart _ hmeas]
    have hvol : volume (ball p (4 * ε)) = ENNReal.ofReal Vol :=
      (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    calc ∫⁻ z in ball p (4 * ε), Ann.indicator (fun z => ENNReal.ofReal (H z)) z *
          ENNReal.ofReal (ρ z)
        ≤ ∫⁻ z in ball p (4 * ε), ENNReal.ofReal (E * M * Real.exp (-(β * k))) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          by_cases hzA : z ∈ Ann
          · rw [indicator_of_mem hzA, ← ENNReal.ofReal_mul (hH0 z)]
            refine ENNReal.ofReal_le_ofReal ((hHle z hz).trans ?_)
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            have hzA' : ε ≤ ‖z - p‖ := hzA
            have h2 := hlevi (z - p)
            have h3 : c₀ * ε ^ 2 ≤ c₀ * ‖z - p‖ ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hzA' 2) hc₀.le
            have h4 : (1 - τ) * (c₀ * ε ^ 2) ≤ (1 - τ) * leviForm Φ p (z - p) :=
              mul_le_mul_of_nonneg_left (h3.trans h2) (by linarith)
            have h5 := mul_le_mul_of_nonneg_left h4 hkr.le
            rw [hβ]
            calc -(((k : ℝ) * (1 - τ)) * leviForm Φ p (z - p)) =
                -((k : ℝ) * ((1 - τ) * leviForm Φ p (z - p))) := by ring
              _ ≤ -((k : ℝ) * ((1 - τ) * (c₀ * ε ^ 2))) := by linarith
              _ = -((1 - τ) * c₀ * ε ^ 2 * k) := by ring
          · rw [indicator_of_notMem hzA, zero_mul]
            exact zero_le
      _ = ENNReal.ofReal (E * M * Real.exp (-(β * k)) * Vol) := by
          rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (by positivity)]
  -- the sharp correction
  have hφx : φ x ≠ ⊥ := by
    have := hgφ p hxU
    rw [show c.val.symm p = x from c.val.left_inv hxa] at this
    rw [this]; exact EReal.coe_ne_bot _
  have hKfin : ∫⁻ y in K, ENNReal.ofReal (‖D.chartSection k a (ball ((D.chartA a).val x) (4 * ε))
      ((D.frameE k a).val.continuousLinearMapAt ℂ x v) F₀ y‖ ^ 2) *
      multiplierWeight (k : ℝ) (φ y) ∂μ ≠ ⊤ := by
    rw [hcoef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIK
  obtain ⟨σ, hσx, hσint⟩ := D.exists_section_through_point_sharp hL hT hkD hφ2 hφ' hn a hxa hε
    hΩR hψ0 hψpole hψlow hχ hχ0 hχ1 hχU hχone hK hKU hKann hconst hMχ0 hMχ hF₀ hF₀p hφx v
    hKfin
  rw [hcoef] at hσint
  -- the `L²` norm of `σ`
  have hmeasG : AEMeasurable (Uy.indicator G) μ := by
    refine (aemeasurable_indicator_iff hUyo.measurableSet).mpr ?_
    have hcH : ContinuousOn (fun y => H (c.val y)) Uy :=
      hHc.comp (c.val.continuousOn.mono inter_subset_left) (fun y hy => hy.2)
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcH.aemeasurable hUyo.measurableSet)).congr ?_
    refine (ae_restrict_iff' hUyo.measurableSet).mpr (Eventually.of_forall fun y hy => ?_)
    exact (hGeq y hy).symm
  set Dσ := ∫⁻ y, ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - σ y‖ ^ 2) *
    multiplierWeight (k : ℝ) (φ y) ∂μ with hDσ
  have hpt : ∀ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤
      ENNReal.ofReal (1 + τ) * Uy.indicator G y + ENNReal.ofReal (1 + 1 / τ) *
        (ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)) := by
    intro y
    set w := multiplierWeight (k : ℝ) (φ y) with hw
    set a₁ := ‖((χ y : ℝ) : ℂ) • F y‖ with ha₁def
    set b₁ := ‖((χ y : ℝ) : ℂ) • F y - σ y‖ with hb₁def
    have htri : ‖σ y‖ ≤ a₁ + b₁ := by
      have : σ y = ((χ y : ℝ) : ℂ) • F y - (((χ y : ℝ) : ℂ) • F y - σ y) := by abel
      rw [this]; exact norm_sub_le _ _
    have hyoung : ‖σ y‖ ^ 2 ≤ (1 + τ) * a₁ ^ 2 + (1 + 1 / τ) * b₁ ^ 2 := by
      have h0 : 0 ≤ ‖σ y‖ := norm_nonneg _
      have h1 : ‖σ y‖ ^ 2 ≤ (a₁ + b₁) ^ 2 := pow_le_pow_left₀ h0 htri 2
      have h2 : 0 ≤ (τ * a₁ - b₁) ^ 2 / τ := div_nonneg (sq_nonneg _) hτ0.le
      have e : (τ * a₁ - b₁) ^ 2 / τ = τ * a₁ ^ 2 - 2 * a₁ * b₁ + b₁ ^ 2 / τ := by
        field_simp; ring
      have e2 : (1 + 1 / τ) * b₁ ^ 2 = b₁ ^ 2 + b₁ ^ 2 / τ := by field_simp
      have e3 : (a₁ + b₁) ^ 2 = a₁ ^ 2 + 2 * a₁ * b₁ + b₁ ^ 2 := by ring
      linarith
    have ha₁ : ENNReal.ofReal (a₁ ^ 2) * w ≤ Uy.indicator G y := by
      by_cases hy : y ∈ Uy
      · rw [indicator_of_mem hy]
        show _ ≤ ENNReal.ofReal (‖F y‖ ^ 2) * w
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [ha₁def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 y), mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (hχ0 y) (hχ1 y))
      · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hχU h))
        simp [ha₁def, h0]
    calc ENNReal.ofReal (‖σ y‖ ^ 2) * w ≤
          ENNReal.ofReal ((1 + τ) * a₁ ^ 2 + (1 + 1 / τ) * b₁ ^ 2) * w :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hyoung) zero_le
      _ = ENNReal.ofReal (1 + τ) * (ENNReal.ofReal (a₁ ^ 2) * w) +
            ENNReal.ofReal (1 + 1 / τ) * (ENNReal.ofReal (b₁ ^ 2) * w) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (1 + τ) * Uy.indicator G y +
            ENNReal.ofReal (1 + 1 / τ) * (ENNReal.ofReal (b₁ ^ 2) * w) := by
          gcongr
  have hsplit : ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
      ENNReal.ofReal (1 + τ) * ∫⁻ y in Uy, G y ∂μ + ENNReal.ofReal (1 + 1 / τ) * Dσ := by
    calc ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ
        ≤ ∫⁻ y, (ENNReal.ofReal (1 + τ) * Uy.indicator G y + ENNReal.ofReal (1 + 1 / τ) *
          (ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - σ y‖ ^ 2) *
            multiplierWeight (k : ℝ) (φ y))) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (1 + τ) * ∫⁻ y in Uy, G y ∂μ + ENNReal.ofReal (1 + 1 / τ) * Dσ := by
          rw [lintegral_add_left' (hmeasG.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hUyo.measurableSet]
  set N : ℝ := (1 + τ) * (E * M * ((n.factorial : ℝ) /
      (((k : ℝ) * (1 - τ)) ^ n * smoothDensity Φ p))) +
      (1 + 1 / τ) * (Cs * (E * M * Real.exp (-(β * k)) * Vol)) with hNdef
  have h1τ : 0 < 1 - τ := by linarith
  have hNpos : 0 < N := by
    have : 0 < (1 + τ) * (E * M * ((n.factorial : ℝ) /
        (((k : ℝ) * (1 - τ)) ^ n * smoothDensity Φ p))) := by positivity
    have : 0 ≤ (1 + 1 / τ) * (Cs * (E * M * Real.exp (-(β * k)) * Vol)) := by positivity
    linarith
  have hσN : ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
      ENNReal.ofReal N := by
    refine hsplit.trans ?_
    have hDσ' : Dσ ≤ ENNReal.ofReal Cs *
        ENNReal.ofReal (E * M * Real.exp (-(β * k)) * Vol) := by
      refine hσint.trans ?_
      gcongr
      rw [hCs, ENNReal.ofReal_toReal hCsne]
    calc ENNReal.ofReal (1 + τ) * ∫⁻ y in Uy, G y ∂μ + ENNReal.ofReal (1 + 1 / τ) * Dσ
        ≤ ENNReal.ofReal (1 + τ) * ENNReal.ofReal (E * M * ((n.factorial : ℝ) /
            (((k : ℝ) * (1 - τ)) ^ n * smoothDensity Φ p))) +
          ENNReal.ofReal (1 + 1 / τ) * (ENNReal.ofReal Cs *
            ENNReal.ofReal (E * M * Real.exp (-(β * k)) * Vol)) := by gcongr
      _ = ENNReal.ofReal N := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
  have hB := div_le_bergmanDensity μ L T φ k x σ hNpos hσN
  have hσx' : ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) =
      ENNReal.ofReal (E * Real.exp (-fT p)) := by
    rw [hσx]
    have hφx' : φ x = (g p : EReal) := by
      have := hgφ p hxU; rwa [c.val.left_inv hxa] at this
    rw [hφx', multiplierWeight_coe, ← ENNReal.ofReal_mul (sq_nonneg _),
      D.density_chart_eq k a hxa hpR (g p) v, hcoef]
    congr 1
    rw [norm_one, one_pow, one_mul, hEdef, ← Real.exp_add]
    congr 1
  rw [hσx'] at hB
  have hsD' := hsD.ne'
  have hρp' := hρp.ne'
  have hfac' := hfac.ne'
  have hkr' := hkr.ne'
  have h1τ' := h1τ.ne'
  have hτ' := hτ0.ne'
  calc ENNReal.ofReal (1 / ((1 + τ) ^ 2 * ρ p / ((1 - τ) ^ n * smoothDensity Φ p) +
        C * ((k : ℝ) ^ n * Real.exp (-(β * k)))))
      = ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
          (ENNReal.ofReal (E * Real.exp (-fT p)) / ENNReal.ofReal N) := by
        rw [← ENNReal.ofReal_div_of_pos hNpos, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hNdef, hMdef, hCdef, mul_pow]
        field_simp
    _ ≤ _ := by gcongr

/-- **The pointwise sharp lower bound of the Bergman density** (blueprint
`claude-dx-low:pointwise`): at a point `x` near which `φ` is smooth (`φ ∘ z_a⁻¹ = g` on an open
`U ∋ z_a(x)`, `g` smooth), `smoothDensity Φ p / ρ(p) ≤ liminf_k (n!/kⁿ) B_k(x)`, where
`Φ = g - log |e_L|²`, `p = z_a(x)` and `ρ` is the density of `μ` in the chart. -/
theorem le_liminf_bergmanDensity (hn : 0 < n) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (D : CoverData ωb μ L T θ (δ / 2)) (a : Fin D.m) {x : X}
    (hxa : x ∈ (D.chartA a).val.source)
    (hxr : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4))
    {g : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hxU : (D.chartA a).val x ∈ U) (hg : ContDiffOn ℝ ∞ g U)
    (hgφ : ∀ z ∈ U, φ ((D.chartA a).val.symm z) = (g z : EReal)) :
    ENNReal.ofReal (smoothDensity (D.peakWeight a g) ((D.chartA a).val x) /
        D.dens a ((D.chartA a).val x)) ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        bergmanDensity μ L T φ k x) atTop := by
  set p := (D.chartA a).val x with hp
  set sD := smoothDensity (D.peakWeight a g) p with hsDdef
  set ρ := D.dens a p with hρdef
  set f := fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
    bergmanDensity μ L T φ k x with hf
  obtain ⟨hρ, hsD, -⟩ := eventually_peak_lower hn hL hT hδ hφ D a hxa hxr hU hxU hg hgφ
    (τ := 1 / 2) (by norm_num) (by norm_num)
  -- for each `τ`, the bound `(1-τ)ⁿ sD / ((1+τ)² ρ) ≤ liminf`
  have hτ : ∀ τ : ℝ, 0 < τ → τ < 1 →
      ENNReal.ofReal ((1 - τ) ^ n * sD / ((1 + τ) ^ 2 * ρ)) ≤ liminf f atTop := by
    intro τ hτ0 hτ1
    obtain ⟨-, -, C, β, hC, hβ, hev⟩ :=
      eventually_peak_lower hn hL hT hδ hφ D a hxa hxr hU hxU hg hgφ hτ0 hτ1
    set A : ℝ := (1 + τ) ^ 2 * ρ / ((1 - τ) ^ n * sD) with hA
    have hA0 : 0 < A := by
      have : 0 < 1 - τ := by linarith
      positivity
    have hlim0 : Tendsto (fun k : ℕ => C * ((k : ℝ) ^ n * Real.exp (-(β * k)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => β * (k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hβ
      have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp h1
      have h3 : (fun k : ℕ => C * ((k : ℝ) ^ n * Real.exp (-(β * k)))) =
          fun k : ℕ => C * (β ^ n)⁻¹ * ((fun x : ℝ => x ^ n * Real.exp (-x)) ∘
            (fun k : ℕ => β * (k : ℝ))) k := by
        funext k
        simp only [Function.comp, mul_pow]
        field_simp
      rw [h3]
      simpa using h2.const_mul (C * (β ^ n)⁻¹)
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / (A +
        C * ((k : ℝ) ^ n * Real.exp (-(β * k)))))) atTop (𝓝 (ENNReal.ofReal (1 / A))) := by
      refine ENNReal.tendsto_ofReal ?_
      have := ((tendsto_const_nhds (x := A)).add hlim0).inv₀ (by simpa using hA0.ne')
      simpa [one_div] using this
    have hle := liminf_le_liminf (u := fun k : ℕ => ENNReal.ofReal (1 / (A +
        C * ((k : ℝ) ^ n * Real.exp (-(β * k)))))) (v := f) hev
    rw [hlim.liminf_eq] at hle
    have hAeq : 1 / A = (1 - τ) ^ n * sD / ((1 + τ) ^ 2 * ρ) := by
      rw [hA, one_div_div]
    rw [← hAeq]
    exact hle
  -- let `τ → 0`
  have hcont : Tendsto (fun τ : ℝ => ENNReal.ofReal ((1 - τ) ^ n * sD / ((1 + τ) ^ 2 * ρ)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (sD / ρ))) := by
    refine ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have hc : ContinuousAt (fun τ : ℝ => (1 - τ) ^ n * sD / ((1 + τ) ^ 2 * ρ)) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      have := hρ.ne'
      simpa using this
    simpa using hc.tendsto
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with τ hτm
  exact hτ τ hτm.1 hτm.2

end SGPT.IGood.DXLow
