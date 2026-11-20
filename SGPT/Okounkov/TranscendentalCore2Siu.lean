import SGPT.Okounkov.TranscendentalCore2SiuLocal
import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Okounkov.GlobalDivisorResidual
import SGPT.Siu.SiuLemma
import SGPT.Siu.SiuDecompositionLelong
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension

/-!
# Subtracting a prime divisor from a current with analytic singularities

Source: blueprint node `tok:siu-analytic`, DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang,
*Transcendental Okounkov bodies*) Lemma 2.3, for a **possibly singular** prime divisor `D`
(`SGPT.PSH.GeometricPrimeCarrier`, an irreducible analytic hypersurface) and any rational
`0 ≤ a ≤ ν(T, D)` (sub-lemmas `tok-core2:chart-data`, `tok-core2:local-type`,
`tok-core2:residual` of `claude-tok-core2.tex`).

Let `T = θ + ddᶜ u` with `u ∈ 𝒜(θ)` (analytic singularities), `E` a smooth metric of `𝒪(D)` with
weight `ψ_E = log |s_D|²` and curvature `Θ_E`, and `a ∈ ℚ_{≥ 0}` with `a ≤ ν(u, x)` at every point
`x ∈ D` (squared-logarithmic normalization, i.e. `a ≤ ν(T, D)`). The residual
`W = (u - a ψ_E)`, extended across `D` (`extensionAcross D (smoothDivisorOffResidual E a u)`), is
`(θ - a Θ_E)`-psh with analytic singularities: `W ∈ 𝒜(θ - a Θ_E)`
(`extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents`). With
`T = (θ - a Θ_E) + ddᶜ W + a [D]` (`thetaPotentialCurrent_eq_add_smul_primeDivisorCurrent`), this is
`T - a[D] ∈ 𝒜(ξ - a{D})`, and `T - a[D]` is a closed positive current.

## The route

In a chart at a point of `D`, let `g` be a reduced local equation of `D` (a generator of the
vanishing ideal, from the divisor metric) and `u = c' log ∑ |f_i|² + O(1)`. Write `a / c' = k / L`
and let `F_β = ∏_{j < L} f_{β j}` (`β : Fin L → Fin K`), so that `u = (c'/L) log ∑ |F_β|² + O(1)`
and `(c'/L) k = a`. For `k ≥ 1` Siu's local bound below the generic Lelong number
(`SGPT.Siu.locallyBoundedAboveOff_sub_smul_weight`, applied with `c = a - c'/(2L) < a`) gives
`log |F_β|² ≤ (k - 1/2) log |g|² + O(1)`; dividing repeatedly by `g` (which generates the germs
vanishing on `D`) gives `F_β = g^k H_β` (`exists_eq_pow_mul_of_log_le`). Off `D`,
`u - a ψ_E = (c'/L) log ∑ |H_β|² + O(1)`; the same two-sided bound holds on `D` for the upper
regularization, since `log ∑ |H_β|²` is continuous and `D` has empty interior. The extension is
then psh by the removable singularity theorem for `θ`-psh functions bounded above
(`PshAnalyticRemovable`). CORE's `residual_rational_and_hasManifoldAnalyticSingularityType` is the
case of a smooth connected hypersurface and `a = ν(T, D)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore2

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open GlobalCurrents NaturalThetaPshGeometricCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- **Local data of a prime divisor in a chart** (blueprint `tok-core2:chart-data`): near every
point `z` of a chart, the metric weight is `log |G|² + h'` with `G` holomorphic (a reduced local
equation) and `h'` continuous, `D` is the zero set of `G`, the zero set of `G` has empty interior,
and `G` generates the holomorphic germs at `z` vanishing on `{G = 0}`. -/
theorem exists_chart_divisor_data (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) :
    ∃ (G : ComplexModel (m + 1) → ℂ) (h' : ComplexModel (m + 1) → ℝ),
      (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w) ∧ ContinuousAt h' z ∧
      (∀ᶠ w in 𝓝 z, E.weight (e.val.symm w) =
        ENNReal.log (ENNReal.ofReal (‖G w‖ ^ 2)) + (h' w : EReal)) ∧
      (∀ᶠ w in 𝓝 z, (e.val.symm w ∈ D.val ↔ G w = 0)) ∧
      (∀ᶠ w in 𝓝 z, ∀ U ∈ 𝓝 w, ∃ w' ∈ U, G w' ≠ 0) ∧
      ∀ F : ComplexModel (m + 1) → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) →
        (∀ᶠ w in 𝓝 z, G w = 0 → F w = 0) →
          ∃ A : ComplexModel (m + 1) → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ A w) ∧
            F =ᶠ[𝓝 z] fun w => A w * G w := by
  have hy0 : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨V', hV', hy0V', g, hg, hgen, h, hh, hwV⟩ := hE (e.val.symm z)
  have hdom : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V') := e.val.isOpen_inter_preimage_symm hV'
  have hzdom : z ∈ e.val.target ∩ e.val.symm ⁻¹' V' := ⟨hz, hy0V'⟩
  have hdomN : e.val.target ∩ e.val.symm ⁻¹' V' ∈ 𝓝 z := hdom.mem_nhds hzdom
  have hGd : DifferentiableOn ℂ (fun w => g (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' V') :=
    MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg
  have hwt : ∀ w ∈ e.val.target ∩ e.val.symm ⁻¹' V', E.weight (e.val.symm w) =
      ENNReal.log (ENNReal.ofReal (‖g (e.val.symm w)‖ ^ 2)) + (h (e.val.symm w) : EReal) :=
    fun w hw => by rw [hwV _ hw.2, TranscendentalCore.generatorLog_single]
  have hsupp : ∀ w ∈ e.val.target ∩ e.val.symm ⁻¹' V',
      (e.val.symm w ∈ D.val ↔ g (e.val.symm w) = 0) := by
    intro w hw
    rw [← hEsupp]
    change E.weight (e.val.symm w) = ⊥ ↔ _
    rw [hwt w hw]
    constructor
    · intro hbot
      rcases EReal.add_eq_bot_iff.mp hbot with h1 | h1
      · rw [ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero] at h1
        have h2 : ‖g (e.val.symm w)‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
        exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
      · exact absurd h1 (EReal.coe_ne_bot _)
    · intro h0
      rw [h0, norm_zero]
      simp
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE
  refine ⟨fun w => g (e.val.symm w), fun w => h (e.val.symm w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hdomN] with w hw'
    exact hGd.differentiableAt (hdom.mem_nhds hw')
  · exact ((hh e).continuousOn.continuousAt hdomN)
  · filter_upwards [hdomN] with w hw'
    exact hwt w hw'
  · filter_upwards [hdomN] with w hw'
    exact hsupp w hw'
  · -- the zero set of `G` has empty interior
    filter_upwards [hdomN] with w hw' U hU
    have hsw : e.val.symm w ∈ e.val.source := e.val.map_target hw'.1
    have hOpen : IsOpen (e.val.source ∩ e.val ⁻¹' (interior U ∩ (e.val.target ∩
        e.val.symm ⁻¹' V'))) :=
      e.val.continuousOn.isOpen_inter_preimage e.val.open_source (isOpen_interior.inter hdom)
    have hmem : e.val.symm w ∈ e.val.source ∩ e.val ⁻¹' (interior U ∩ (e.val.target ∩
        e.val.symm ⁻¹' V')) := by
      refine ⟨hsw, ?_⟩
      simp only [mem_preimage, e.val.right_inv hw'.1]
      exact ⟨mem_interior_iff_mem_nhds.mpr hU, hw'⟩
    obtain ⟨y, ⟨hys, hyU, hydom⟩, hy⟩ := hw.2 _ _ hOpen hmem
    refine ⟨e.val y, interior_subset hyU, fun h0 => hy ?_⟩
    have := (hsupp _ hydom).mpr h0
    rw [e.val.left_inv hys] at this
    rw [← hEsupp] at this
    exact this
  · -- the ideal property
    intro F hF hvan
    have hcont : Tendsto e.val (𝓝 (e.val.symm z)) (𝓝 z) := by
      have := (e.val.continuousAt hy0).tendsto
      rwa [e.val.right_inv hz] at this
    have hFe : ∀ᶠ y in 𝓝 (e.val.symm z), DifferentiableAt ℂ F (e.val y) := hcont.eventually hF
    have hvan' : ∀ᶠ y in 𝓝 (e.val.symm z), e.val y ∈ e.val.target ∩ e.val.symm ⁻¹' V' ∧
        (g (e.val.symm (e.val y)) = 0 → F (e.val y) = 0) :=
      (hcont.eventually hdomN).and (hcont.eventually hvan)
    have hmem : (vanishingIdeal (n := m + 1) D.val).mem (e.val.symm z) (fun y => F (e.val y)) := by
      refine ⟨?_, ?_⟩
      · filter_upwards [hFe, e.val.open_source.mem_nhds hy0] with y hy hys
        exact hy.mdifferentiableAt.comp y
          (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (m + 1))) e.property hys)
      · filter_upwards [hvan', e.val.open_source.mem_nhds hy0] with y hy hys hyD
        obtain ⟨hydom, hyF⟩ := hy
        apply hyF
        rw [e.val.left_inv hys]
        have := (hsupp _ hydom).mp (by rw [e.val.left_inv hys]; exact hyD)
        rwa [e.val.left_inv hys] at this
    have hmem' : (SGPT.Siu.primeEffectiveDivisor D).ideal.mem (e.val.symm z)
        (fun y => F (e.val y)) := by
      rw [SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal]
      exact hmem
    obtain ⟨-, N, s, a, hs, ha, heq⟩ := (hgen _ hy0V' _).mp hmem'
    have hsymm : Filter.Tendsto e.val.symm (𝓝 z) (𝓝 (e.val.symm z)) :=
      (e.val.continuousAt_symm hz).tendsto
    refine ⟨fun w => ∑ i, a i (e.val.symm w), ?_, ?_⟩
    · have hai : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => a i (e.val.symm w)) w := by
        intro i
        filter_upwards [hsymm.eventually (ha i), e.val.open_target.mem_nhds hz] with w hw hwt'
        exact mdifferentiableAt_iff_differentiableAt.mp (hw.comp w
          (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel (m + 1))) e.property hwt'))
      filter_upwards [eventually_all.mpr hai] with w hw
      exact DifferentiableAt.fun_sum fun i _ => hw i
    · filter_upwards [hsymm.eventually heq, e.val.open_target.mem_nhds hz] with w hw hwt'
      simp only [e.val.right_inv hwt'] at hw
      rw [hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs i]

/-- **The residual has analytic singularities where the potential has** (blueprint
`tok-core2:local-type`, the local part of DRWNXZ Lemma 2.3): for a `θ`-psh `u` and rational
`0 ≤ a ≤ ν(u, D)`, if `u` has analytic singularity type at the point `z` of the chart `e`, then so
has the extension `W` of `u - a ψ_E` across `D`: near `z`, `W = (c'/L) log ∑ |H_β|² + O(1)`. -/
theorem hasAnalyticSingularityTypeAt_residual {θ : ClosedRealOneOneForm (m + 1) M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E) {a : ℚ}
    (ha : 0 ≤ a) (hν : ∀ x ∈ D.val, ENNReal.ofReal a ≤ squaredLogLelongNumber (n := m + 1) u x)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    (hAz : HasAnalyticSingularityTypeAt (chartFunction u e) z) :
    HasAnalyticSingularityTypeAt
      (chartFunction (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) e)
        z := by
  classical
  obtain ⟨G, h', hGd, hh', hwt, hsupp, hnd, hideal⟩ := exists_chart_divisor_data D E hEsupp hE e hz
  obtain ⟨c', K, f, hc'pos, ⟨Of, hOf, hzOf, hfd⟩, b, ⟨Bb, hBb0, hBb⟩, heq⟩ := hAz
  have hc'Q : (0 : ℚ) < c' := by exact_mod_cast hc'pos
  have haR0 : (0 : ℝ) ≤ a := by exact_mod_cast ha
  -- `a / c' = k / L`
  set t : ℚ := a / c' with ht
  have ht0 : 0 ≤ t := div_nonneg ha hc'Q.le
  set k : ℕ := t.num.toNat with hk
  set L : ℕ := t.den with hL
  have hLpos : 0 < L := t.den_pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hkLQ : a * (L : ℚ) = c' * (k : ℚ) := by
    have hk' : (k : ℚ) = (t.num : ℚ) := by
      simp only [hk]
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht0)
    rw [hk', ← Rat.mul_den_eq_num t, hL, ht]
    field_simp
  have hkL : (a : ℝ) * L = (c' : ℝ) * k := by exact_mod_cast hkLQ
  -- the power family `F_β = ∏_j f_{β j}`
  have hfc : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (f i) w := fun i => by
    filter_upwards [hOf.mem_nhds hzOf] with w hw
    exact (hfd i).differentiableAt (hOf.mem_nhds hw)
  have hPd : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (powerFamily L f i) w := by
    intro i
    filter_upwards [eventually_all.mpr hfc] with w hw
    unfold powerFamily
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun j _ => (hw _).hasFDerivAt).differentiableAt
  obtain ⟨Bh, hBh0, hBh⟩ := boundedRealGermAt_of_continuousAt hh'
  -- the factorization `F_β = G^k H_β`
  have hfact : ∀ i, ∃ H : ComplexModel (m + 1) → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ H w) ∧
      powerFamily L f i =ᶠ[𝓝 z] fun w => G w ^ k * H w := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · intro i
      refine ⟨powerFamily L f i, hPd i, Eventually.of_forall fun w => ?_⟩
      simp only [hk0, pow_zero, one_mul]
    · -- Siu's bound below the generic Lelong number, with `c = a - c'/(2L)`
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      set c : ℝ := (a : ℝ) - (c' : ℝ) / (2 * L) with hc
      have haR : (a : ℝ) = (c' : ℝ) * k / L := by
        field_simp
        linarith [hkL]
      have hcpos : 0 < c := by
        have h1 : (c' : ℝ) / L ≤ (a : ℝ) := by
          rw [haR]
          exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc'pos.le hkR) hLR.le
        have h2 : (c' : ℝ) / (2 * L) < (c' : ℝ) / L :=
          div_lt_div_of_pos_left hc'pos hLR (by linarith)
        rw [hc]
        linarith
      have hca : c < a := by
        have : 0 < (c' : ℝ) / (2 * L) := by positivity
        rw [hc]
        linarith
      have hν' : ∀ x ∈ D.val, ENNReal.ofReal c < squaredLogLelongNumber (n := m + 1) u x :=
        fun x hx => lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hca)
          (hν x hx)
      obtain ⟨U, hU, C₁, hC₁⟩ :=
        SGPT.Siu.locallyBoundedAboveOff_sub_smul_weight hu D E hEsupp hE hcpos.le hν'
          (e.val.symm z)
      have hsymm : Tendsto e.val.symm (𝓝 z) (𝓝 (e.val.symm z)) :=
        (e.val.continuousAt_symm hz).tendsto
      have hbound : ∀ i, ∀ᶠ w in 𝓝 z, G w ≠ 0 → powerFamily L f i w ≠ 0 →
          Real.log (‖powerFamily L f i w‖ ^ 2) ≤
            ((L : ℝ) * c / c') * Real.log (‖G w‖ ^ 2) + (L : ℝ) * (C₁ + Bb + c * Bh) / c' := by
        intro i
        filter_upwards [hsymm.eventually hU, heq, hBb, hBh, hwt, hsupp] with
          w hwU hweq hbw hhw hwtw hsuppw hGw hPw
        have hyD : e.val.symm w ∉ E.support := by
          rw [hEsupp]
          exact fun h => hGw (hsuppw.mp h)
        have hGpos : 0 < ‖G w‖ ^ 2 := by positivity
        have hwt' : E.weight (e.val.symm w) = ((Real.log (‖G w‖ ^ 2) + h' w : ℝ) : EReal) := by
          rw [hwtw, ENNReal.log_ofReal_of_pos hGpos, EReal.coe_add]
        have hPle := norm_sq_powerFamily_le L f w i
        have hPpos : 0 < ‖powerFamily L f i w‖ ^ 2 := by positivity
        have hSpos : 0 < ∑ j, ‖f j w‖ ^ 2 := by
          by_contra hS0
          push Not at hS0
          have h0 : ∑ j, ‖f j w‖ ^ 2 = 0 :=
            le_antisymm hS0 (Finset.sum_nonneg fun j _ => by positivity)
          rw [h0, zero_pow hLpos.ne'] at hPle
          linarith
        have hgl : generatorLog f w = ((Real.log (∑ j, ‖f j w‖ ^ 2) : ℝ) : EReal) := by
          rw [generatorLog_eq_log_sum, ENNReal.log_ofReal_of_pos hSpos]
        have hineq : u (e.val.symm w) +
            ((-(c * (E.weight (e.val.symm w)).toReal) : ℝ) : EReal) ≤ (C₁ : EReal) :=
          hC₁ _ hwU hyD
        have hu' : u (e.val.symm w) =
            (((c' : ℝ) * Real.log (∑ j, ‖f j w‖ ^ 2) + b w : ℝ) : EReal) := by
          have h1 := hweq
          simp only [chartFunction] at h1
          rw [h1, hgl, ← EReal.coe_mul, ← EReal.coe_add]
        rw [hu', hwt', EReal.toReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff] at hineq
        have hlogP : Real.log (‖powerFamily L f i w‖ ^ 2) ≤
            L * Real.log (∑ j, ‖f j w‖ ^ 2) := by
          rw [← Real.log_pow]
          exact Real.log_le_log hPpos hPle
        have h1 := (abs_le.mp hbw).1
        have h2 : c * h' w ≤ c * Bh := mul_le_mul_of_nonneg_left (abs_le.mp hhw).2 hcpos.le
        have hlogS : Real.log (∑ j, ‖f j w‖ ^ 2) ≤
            (C₁ + Bb + c * Bh + c * Real.log (‖G w‖ ^ 2)) / c' := by
          rw [le_div_iff₀ hc'pos]
          nlinarith
        calc Real.log (‖powerFamily L f i w‖ ^ 2) ≤ L * Real.log (∑ j, ‖f j w‖ ^ 2) := hlogP
          _ ≤ L * ((C₁ + Bb + c * Bh + c * Real.log (‖G w‖ ^ 2)) / c') :=
            mul_le_mul_of_nonneg_left hlogS hLR.le
          _ = ((L : ℝ) * c / c') * Real.log (‖G w‖ ^ 2) + (L : ℝ) * (C₁ + Bb + c * Bh) / c' := by
            field_simp
            ring
      intro i
      refine exists_eq_pow_mul_of_log_le (hGd.mono fun w hw => hw.continuousAt) hnd hideal k
        (powerFamily L f i) _ _ ?_ (hPd i) (hbound i)
      have hval : (L : ℝ) * c / c' = k - 1 / 2 := by
        rw [hc, haR]
        field_simp
      rw [hval]
      linarith
  choose H hHd hPH using hfact
  -- the residual off `D`
  set A : ComplexModel (m + 1) → EReal :=
    fun w => (((c' : ℝ) / L : ℝ) : EReal) * generatorLog H w with hA
  set R : ComplexModel (m + 1) → ℝ := fun w => b w - (a : ℝ) * h' w with hR
  set B : ℝ := Bb + (a : ℝ) * Bh with hB
  have hB0 : 0 ≤ B := by positivity
  have hrep : ∀ᶠ w in 𝓝 z, G w ≠ 0 →
      chartFunction (SGPT.Okounkov.smoothDivisorOffResidual E a u) e w = A w + (R w : EReal) := by
    filter_upwards [heq, hwt, hsupp, eventually_all.mpr hPH] with w hweq hwtw hsuppw hPHw hGw
    have hyD : e.val.symm w ∉ E.support := by
      rw [hEsupp]
      exact fun h => hGw (hsuppw.mp h)
    have hGpos : 0 < ‖G w‖ ^ 2 := by positivity
    have hlogG : ENNReal.log (ENNReal.ofReal (‖G w‖ ^ 2)) =
        ((Real.log (‖G w‖ ^ 2) : ℝ) : EReal) := ENNReal.log_ofReal_of_pos hGpos
    have hgP : generatorLog (powerFamily L f) w =
        ((k : ℝ) : EReal) * ((Real.log (‖G w‖ ^ 2) : ℝ) : EReal) + generatorLog H w := by
      have : generatorLog (powerFamily L f) w = generatorLog (fun i w => G w ^ k * H i w) w := by
        rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by rw [hPHw i]
      rw [this, TranscendentalCore.generatorLog_pow_mul, hlogG]
    have hu' : u (e.val.symm w) =
        (((c' : ℝ) / L : ℝ) : EReal) * generatorLog (powerFamily L f) w + (b w : EReal) := by
      have h1 := hweq
      simp only [chartFunction] at h1
      rw [h1, generatorLog_powerFamily, ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ hLR.ne']
    simp only [chartFunction, SGPT.Okounkov.smoothDivisorOffResidual, if_neg hyD]
    rw [hu', hgP, hwtw, hlogG,
      TranscendentalCore.ereal_residual_identity (div_pos hc'pos hLR) (k : ℝ)
        (Real.log (‖G w‖ ^ 2)) (b w) (a : ℝ) (h' w)]
    have hzero : (c' : ℝ) / L * k - (a : ℝ) = 0 := by
      field_simp
      linarith [hkL]
    rw [hzero, EReal.coe_zero, zero_mul, add_zero]
  -- a neighbourhood of `z` where all the local data hold
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp (hrep.and (hsupp.and (hnd.and
    ((eventually_all.mpr hHd).and (hBb.and (hBh.and (e.val.open_target.mem_nhds hz)))))))
  have hAc : ∀ w ∈ O, ContinuousAt A w := fun w hw =>
    continuousAt_coe_mul_generatorLog (div_pos hc'pos hLR).ne'
      (fun i => ((hOsub hw).2.2.2.1 i).continuousAt)
  have hRB : ∀ w ∈ O, |R w| ≤ B := by
    intro w hw
    have h1 := (hOsub hw).2.2.2.2.1
    have h2 := (hOsub hw).2.2.2.2.2.1
    calc |R w| ≤ |b w| + |(a : ℝ) * h' w| := abs_sub _ _
      _ = |b w| + (a : ℝ) * |h' w| := by rw [abs_mul, abs_of_nonneg haR0]
      _ ≤ Bb + (a : ℝ) * Bh := add_le_add h1 (mul_le_mul_of_nonneg_left h2 haR0)
  have hbounds : ∀ w ∈ O,
      A w + ((-B : ℝ) : EReal) ≤
        chartFunction (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) e w ∧
      chartFunction (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) e w ≤
        A w + (B : EReal) := by
    intro w hw
    have hwt' : w ∈ e.val.target := (hOsub hw).2.2.2.2.2.2
    rw [chartFunction_extensionAcross_eq_extension_preimage hwt']
    constructor
    · refine le_uscRegularization_cut ?_ (continuousAt_add_coe (hAc w hw) _) ?_
      · intro V hV
        obtain ⟨w', hw'V, hGw'⟩ := (hOsub hw).2.2.1 (V ∩ O) (inter_mem hV (hO.mem_nhds hw))
        exact ⟨w', hw'V.1, fun hK => hGw' (((hOsub hw'V.2).2.1).mp hK)⟩
      · filter_upwards [hO.mem_nhds hw] with w' hw'O hw'K
        have hGw' : G w' ≠ 0 := fun h0 => hw'K (((hOsub hw'O).2.1).mpr h0)
        rw [(hOsub hw'O).1 hGw']
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (hRB w' hw'O)).1)
    · refine uscRegularization_cut_le (continuousAt_add_coe (hAc w hw) _).upperSemicontinuousAt ?_
      filter_upwards [hO.mem_nhds hw] with w' hw'O hw'K
      have hGw' : G w' ≠ 0 := fun h0 => hw'K (((hOsub hw'O).2.1).mpr h0)
      rw [(hOsub hw'O).1 hGw']
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (hRB w' hw'O)).2)
  have hAtop : ∀ w, A w ≠ ⊤ := fun w =>
    TranscendentalCore.ereal_coe_mul_ne_top (div_pos hc'pos hLR).le
      (TranscendentalCore.generatorLog_ne_top H w)
  have hex : ∀ w ∈ O, ∃ r : ℝ, |r| ≤ B ∧
      chartFunction (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) e w =
        A w + (r : EReal) := fun w hw =>
    TranscendentalCore.exists_remainder_of_bounds hB0 (hAtop w) (hbounds w hw).1 (hbounds w hw).2
  choose! r hr hrW using hex
  have hAtype : HasAnalyticSingularityTypeAt A z := by
    have h := TranscendentalCore.hasAnalyticSingularityTypeAt_generatorLog (H := H) hHd
      (c := c' / L) (div_pos hc'Q (by exact_mod_cast hLpos))
    have hcast : (((c' / L : ℚ) : ℝ)) = (c' : ℝ) / L := by push_cast; rfl
    rw [hcast] at h
    exact h
  refine DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded hAtype
    (b := r) ⟨B, hB0, ?_⟩ ?_
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hr w hw
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hrW w hw

/-- **`tok:siu-analytic`** (DRWNXZ Lemma 2.3, potential form; blueprint `tok-core2:residual`): let
`u ∈ 𝒜(θ)`, `D` a prime divisor with a smooth metric `E` of `𝒪(D)`, and `a ∈ ℚ_{≥ 0}` with
`a ≤ ν(u, x)` for every `x ∈ D` (squared-logarithmic normalization: `a ≤ ν(θ + ddᶜ u, D)`). Then the
potential `extensionAcross D (u - a ψ_E)` of `T - a[D]` lies in `𝒜(θ - a Θ_E)`: it is
`(θ - a Θ_E)`-psh with analytic singularities. -/
theorem extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : u ∈ TranscendentalCore.analyticCurrents θ)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E) {a : ℚ}
    (ha : 0 ≤ a) (hν : ∀ x ∈ D.val, ENNReal.ofReal a ≤ squaredLogLelongNumber (n := m + 1) u x) :
    extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) ∈
      TranscendentalCore.analyticCurrents (θ - (a : ℝ) • E.curvature) := by
  classical
  have htype : HasManifoldAnalyticSingularityType (n := m + 1)
      (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) :=
    fun e z hz => hasAnalyticSingularityTypeAt_residual hu.1 D E hEsupp hE ha hν e hz (hu.2 e z hz)
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE
  have hDclosed : IsClosed D.val := D.isClosed
  have hoff : ThetaPshOff (θ - (a : ℝ) • E.curvature).val D.val
      (SGPT.Okounkov.smoothDivisorOffResidual E a u) := by
    have := SGPT.Okounkov.thetaPshOff_smoothDivisorOffResidual hu.1 E (a : ℝ)
    rwa [hEsupp] at this
  have hWeq : ∀ y, y ∉ D.val →
      extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) y =
        SGPT.Okounkov.smoothDivisorOffResidual E a u y :=
    fun y hy => extensionAcross_eq_of_notMem hDclosed hoff hy
  -- locally bounded above off `D`
  have hbound : LocallyBoundedAboveOff D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) := by
    intro x
    have hxs := mem_complexChartAt_source (n := m + 1) x
    obtain ⟨C, hC⟩ := exists_eventually_le_of_hasAnalyticSingularityTypeAt
      (htype (complexChartAt (n := m + 1) x) _ ((complexChartAt (n := m + 1) x).val.map_source hxs))
    have hcont : Tendsto (complexChartAt (n := m + 1) x).val (𝓝 x)
        (𝓝 ((complexChartAt (n := m + 1) x).val x)) :=
      ((complexChartAt (n := m + 1) x).val.continuousAt hxs).tendsto
    refine ⟨_, (hcont.eventually hC).and
      ((complexChartAt (n := m + 1) x).val.open_source.mem_nhds hxs), C, fun y hy hyD => ?_⟩
    obtain ⟨hy1, hys⟩ := hy
    rw [← hWeq y hyD]
    simpa only [chartFunction, (complexChartAt (n := m + 1) x).val.left_inv hys] using hy1
  -- plurisubharmonic across `D` (removable singularities)
  have hAan : IsComplexAnalyticSubset (n := m + 1) D.val := by
    rw [← D.subvariety_carrier]
    exact D.subvariety.analytic
  have hAne : D.val ≠ univ := by
    obtain ⟨x, -⟩ := D.nonempty
    obtain ⟨y, -, hy⟩ := hw.2 x univ isOpen_univ trivial
    intro hA
    have hyA : y ∈ E.support := by
      rw [hEsupp, hA]
      trivial
    exact hy hyA
  have hclosure := PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed
    (θ - (a : ℝ) • E.curvature) D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) hAan hAne
    hoff hbound
  have hWpsh := thetaPlurisubharmonic_extensionAcross_of_localClosure hDclosed hoff hclosure
  -- locally nondegenerate
  have hWnd : LocallyNondegenerate
      (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u)) := by
    intro x U hU hxU
    obtain ⟨y0, hy0U, hy0⟩ := hw.2 x U hU hxU
    have hy0D : y0 ∉ D.val := by
      rw [← hEsupp]
      exact hy0
    obtain ⟨y, hyU, hy⟩ := hu.1.2 y0 (U ∩ D.valᶜ) (hU.inter hDclosed.isOpen_compl) ⟨hy0U, hy0D⟩
    refine ⟨y, hyU.1, ?_⟩
    rw [hWeq y hyU.2]
    have hyE : y ∉ E.support := by
      rw [hEsupp]
      exact hyU.2
    simp only [SGPT.Okounkov.smoothDivisorOffResidual, if_neg hyE]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, E.weight y = r :=
      ⟨_, (EReal.coe_toReal (hw.1.quasiPlurisubharmonic.ne_top _) hyE).symm⟩
    rw [hr, ← EReal.coe_mul, sub_eq_add_neg]
    intro hbot
    rcases EReal.add_eq_bot_iff.mp hbot with h | h
    · exact hy h
    · rw [← EReal.coe_neg] at h
      exact EReal.coe_ne_bot _ h
  exact ⟨⟨hWpsh, hWnd⟩, htype⟩

/-- **The current identity** `T = (θ - a Θ_E) + ddᶜ W + a [D]` for the residual
`W = extensionAcross D (u - a ψ_E)` of
`extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents`
(`T = θ + ddᶜ u`); so `T - a[D] = (θ - a Θ_E) + ddᶜ W` (blueprint `tok-core2:residual`). -/
theorem thetaPotentialCurrent_eq_add_smul_primeDivisorCurrent [CompactSpace M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : u ∈ TranscendentalCore.analyticCurrents θ)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E) {a : ℚ}
    (ha : 0 ≤ a) (hν : ∀ x ∈ D.val, ENNReal.ofReal a ≤ squaredLogLelongNumber (n := m + 1) u x) :
    thetaPotentialCurrent θ.val u hu.1 =
      thetaPotentialCurrent (θ - (a : ℝ) • E.curvature).val
          (extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u))
          (extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents hu D E hEsupp hE ha hν).1 +
        (a : ℝ) • SGPT.Siu.primeDivisorCurrent D := by
  classical
  have hmem := extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents hu D E hEsupp hE ha hν
  set W := extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) with hWdef
  have hW := hmem.1
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE
  have hDclosed : IsClosed D.val := D.isClosed
  have hoff : ThetaPshOff (θ - (a : ℝ) • E.curvature).val D.val
      (SGPT.Okounkov.smoothDivisorOffResidual E a u) := by
    have := SGPT.Okounkov.thetaPshOff_smoothDivisorOffResidual hu.1 E (a : ℝ)
    rwa [hEsupp] at this
  have hWeq : ∀ y, y ∉ E.support → W y = u y - ((a : ℝ) : EReal) * E.weight y := by
    intro y hy
    have hyD : y ∉ D.val := by rw [← hEsupp]; exact hy
    rw [hWdef, extensionAcross_eq_of_notMem hDclosed hoff hyD]
    simp only [SGPT.Okounkov.smoothDivisorOffResidual, if_neg hy]
  have hloc : ∀ x : M, ∃ V' : Set M, IsOpen V' ∧ x ∈ V' ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g V' ∧ ∃ h : M → ℝ,
        ∀ y ∈ V', E.weight y = generatorLog (fun _ : Fin 1 => g) y + (h y : EReal) := by
    intro x
    obtain ⟨V', hV', hxV', g, hg, -, h, -, hweq⟩ := hE x
    exact ⟨V', hV', hxV', g, hg, h, hweq⟩
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨hcw, hcw_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul hw haR
  obtain ⟨hsum, hsum_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hW hcw
  have hD : SGPT.Siu.primeDivisorCurrent D = thetaPotentialCurrent E.curvature.val E.weight hw :=
    SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent D E hE
  have hcongr : thetaPotentialCurrent (θ - (a : ℝ) • E.curvature + (a : ℝ) • E.curvature).val
      (fun x => W x + ((a : ℝ) : EReal) * E.weight x) hsum =
        thetaPotentialCurrent θ.val u hu.1 := by
    apply SGPT.Siu.thetaPotentialCurrent_congr_ae (by rw [sub_add_cancel])
    intro e
    filter_upwards [SGPT.Siu.ae_chart_notMem_support hw.2 hloc e] with z hz
    simp only [chartFunction]
    rw [hWeq _ hz]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, E.weight (e.val.symm z) = r :=
      ⟨_, (EReal.coe_toReal (hw.1.quasiPlurisubharmonic.ne_top _) hz).symm⟩
    rw [hr, ← EReal.coe_mul, EReal.sub_add_cancel]
  rw [← hcongr, hsum_eq, hcw_eq, hD]

/-- **`tok:siu-analytic`, current form** (DRWNXZ Lemma 2.3): for `T = θ + ddᶜ u ∈ 𝒜(ξ)`, a prime
divisor `D` and `a ∈ ℚ_{≥ 0}` with `a ≤ ν(T, D)`, `T - a[D]` is a closed positive current, equal to
`(θ - a Θ_E) + ddᶜ W` with `W ∈ 𝒜(θ - a Θ_E)`, i.e. `T - a[D] ∈ 𝒜(ξ - a{D})`, for every smooth
metric `E` of `𝒪(D)` (`Θ_E` represents `{D}`). -/
theorem sub_smul_primeDivisorCurrent_mem_analyticCurrents [CompactSpace M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : u ∈ TranscendentalCore.analyticCurrents θ)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E) {a : ℚ}
    (ha : 0 ≤ a)
    (hν : ENNReal.ofReal a ≤ SGPT.Siu.currentGenericLelong (thetaPotentialCurrent θ.val u hu.1)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu.1) D) :
    ∃ W : M → EReal, ∃ hW : W ∈ TranscendentalCore.analyticCurrents (θ - (a : ℝ) • E.curvature),
      thetaPotentialCurrent θ.val u hu.1 - (a : ℝ) • SGPT.Siu.primeDivisorCurrent D =
        thetaPotentialCurrent (θ - (a : ℝ) • E.curvature).val W hW.1 ∧
      SGPT.Siu.IsClosedPositiveCurrent
        (thetaPotentialCurrent θ.val u hu.1 - (a : ℝ) • SGPT.Siu.primeDivisorCurrent D) := by
  have hν' : ∀ x ∈ D.val, ENNReal.ofReal a ≤ squaredLogLelongNumber (n := m + 1) u x := by
    intro x hx
    have h1 := SGPT.Siu.currentGenericLelong_le
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu.1) D hx
    rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu.1) rfl] at h1
    exact hν.trans h1
  have hmem := extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents hu D E hEsupp hE ha hν'
  have hid := thetaPotentialCurrent_eq_add_smul_primeDivisorCurrent hu D E hEsupp hE ha hν'
  have hsub : thetaPotentialCurrent θ.val u hu.1 - (a : ℝ) • SGPT.Siu.primeDivisorCurrent D =
      thetaPotentialCurrent (θ - (a : ℝ) • E.curvature).val _ hmem.1 := by
    rw [hid]
    abel
  refine ⟨_, hmem, hsub, ?_⟩
  rw [hsub]
  exact SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ _

/-- **Positivity of `T - a[D]`** for every closed positive current `T` and real
`a ≤ ν(T, D)` (no analytic singularities needed): `T - a[D] = (T - ν(T, D)[D]) + (ν(T, D) - a)[D]`
with Siu's lemma `SGPT.Siu.isClosedPositiveCurrent_sub_currentGenericLelong_smul`. -/
theorem isClosedPositiveCurrent_sub_smul_primeDivisorCurrent_of_le [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M)
    {a : ℝ} (hν : ENNReal.ofReal a ≤ SGPT.Siu.currentGenericLelong T hT D) :
    SGPT.Siu.IsClosedPositiveCurrent (T - a • SGPT.Siu.primeDivisorCurrent D) := by
  set ν := (SGPT.Siu.currentGenericLelong T hT D).toReal with hνdef
  have hne := SGPT.Siu.currentGenericLelong_ne_top hT D
  have haν : a ≤ ν := by
    rw [hνdef, ← ENNReal.ofReal_le_iff_le_toReal hne]
    exact hν
  have h1 := SGPT.Siu.isClosedPositiveCurrent_sub_currentGenericLelong_smul hT D
  have h2 := (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).smul (sub_nonneg.mpr haν)
  have heq : T - a • SGPT.Siu.primeDivisorCurrent D =
      (T - ν • SGPT.Siu.primeDivisorCurrent D) + (ν - a) • SGPT.Siu.primeDivisorCurrent D := by
    module
  rw [heq]
  exact h1.add h2

end SGPT.Okounkov.TranscendentalCore2

namespace SGPT.Okounkov.TranscendentalCore

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- **`tok:siu-analytic`** (DRWNXZ Lemma 2.3; the name planned by the blueprint): for
`T = θ + ddᶜ u ∈ 𝒜(ξ)`, a (possibly singular) prime divisor `D` with a smooth metric `E` of `𝒪(D)`
and `a ∈ ℚ_{≥ 0}` with `a ≤ ν(T, D)`, the potential `extensionAcross D (u - a ψ_E)` of `T - a[D]`
(`TranscendentalCore2.thetaPotentialCurrent_eq_add_smul_primeDivisorCurrent`) lies in
`𝒜(θ - a Θ_E)`, i.e. `T - a[D] ∈ 𝒜(ξ - a{D})`. -/
theorem sub_divisor_mem_analyticCurrents {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : u ∈ analyticCurrents θ) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEsupp : E.support = D.val)
    (hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) E) {a : ℚ}
    (ha : 0 ≤ a) (hν : ∀ x ∈ D.val, ENNReal.ofReal a ≤ squaredLogLelongNumber (n := m + 1) u x) :
    extensionAcross D.val (SGPT.Okounkov.smoothDivisorOffResidual E a u) ∈
      analyticCurrents (θ - (a : ℝ) • E.curvature) :=
  TranscendentalCore2.extensionAcross_smoothDivisorOffResidual_mem_analyticCurrents hu D E hEsupp
    hE ha hν

end SGPT.Okounkov.TranscendentalCore
