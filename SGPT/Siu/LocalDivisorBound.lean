import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.Pending.DivisorSingularProjection
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.PshAddition

/-!
# The local Siu bound along a hypersurface

This file proves the analytic core of Siu's lemma (`lma:Siudec` of the book, following
Xia, *Foundations of pluripotential theory*, `thm:siu-divisorial-decomposition`, Step 1):

Let `u` be plurisubharmonic on an open set `Ω ⊆ ℂⁿ` and let `g` be holomorphic on `Ω`, vanishing
identically near no point.  Suppose that at every regular point `y` of the divisor of `g`
(presentation `g = hᵐ v`, `dh ≠ 0`, `v ≠ 0`) the function `u` admits a logarithmic exponent
`γ ≥ 2 c m`, i.e. `u(z) ≤ γ log ‖z - y‖ + C` near `y` (native normalization: this is the
condition `ν(u, y) ≥ c m` in the book's normalization `ν(log |z|², 0) = 1`).  Then
`u ≤ c log |g|² + C` near every point of `Ω` (`exists_nhds_le_mul_log_normSq_add`).

No hypothesis is made at the singular points of the divisor.  The proof slices by the complex
lines parallel to a direction `u₀` along which `g` does not vanish identically: almost every such
line meets the zero set of `g` only at transverse regular points
(`DivisorSingularProjection.measure_image_bad_eq_zero`), where the order of vanishing of `g` along
the line is the multiplicity `m`.  On such a line `u - c log |g|²` is subharmonic off finitely many
points and bounded above near them, so it extends across them
(`PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus`) and the maximum principle on a
disc (`PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere`) bounds it by its values on a
boundary circle, where `g` is uniformly bounded away from zero.  The bound then holds almost
everywhere, hence everywhere off the zeros of `g` (`PlurisubharmonicOn.le_of_ae_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorRegularLocus

/-! ### Elementary bounds -/

/-- A plurisubharmonic germ is bounded above by a real constant near its point. -/
theorem PlurisubharmonicOn.exists_real_bound_nhds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {u : E → EReal} {U : Set E} (hu : PlurisubharmonicOn u U) {x : E}
    (hx : x ∈ U) : ∃ C : ℝ, ∀ᶠ y in 𝓝 x, u y ≤ (C : EReal) := by
  obtain ⟨W, hW, hxW, hd⟩ := hu x hx
  have htop : u x < ⊤ := lt_top_iff_ne_top.mpr (hd.ne_top x hxW)
  obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt htop
  have husc := hd.upperSemicontinuousOn x hxW ((q : ℝ) : EReal) (by exact_mod_cast hq)
  rw [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hxW)] at husc
  exact ⟨q, husc.mono fun y hy => hy.le⟩

/-- A plurisubharmonic function is bounded above on every nonempty compact subset. -/
theorem PlurisubharmonicOn.exists_real_bound_of_isCompact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {u : E → EReal} {U K : Set E} (hu : PlurisubharmonicOn u U)
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ C : ℝ, ∀ y ∈ K, u y ≤ (C : EReal) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun y hy => absurd hy (notMem_empty y)⟩
  have hd := hu.discPshOn
  obtain ⟨a, haK, hmax⟩ := (hd.upperSemicontinuousOn.mono hKU).exists_isMaxOn hne hK
  have htop : u a < ⊤ := lt_top_iff_ne_top.mpr (hd.ne_top a (hKU haK))
  obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt htop
  exact ⟨q, fun y hy => (hmax hy).trans (by exact_mod_cast hq.le)⟩

/-- `a + (-r) ≤ C` gives `a ≤ C + r` in `EReal` for real `r`, `C`. -/
theorem EReal.le_add_of_add_neg_le {a : EReal} {r C : ℝ}
    (h : a + ((-r : ℝ) : EReal) ≤ (C : EReal)) : a ≤ ((C + r : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => simp at h
  | coe a =>
    rw [← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.mpr (by have := EReal.coe_le_coe_iff.mp h; linarith)

/-- Converse direction of `EReal.le_add_of_add_neg_le`. -/
theorem EReal.add_neg_le_of_le_add {a : EReal} {r C : ℝ}
    (h : a ≤ ((C + r : ℝ) : EReal)) : a + ((-r : ℝ) : EReal) ≤ (C : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => exact absurd h (not_le.mpr (EReal.coe_lt_top _))
  | coe a =>
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by have := EReal.coe_le_coe_iff.mp h; linarith)

/-! ### One complex variable: removing finitely many punctures -/

/-- The coordinate projection `ℂ¹ → ℂ`. -/
def proj0 : ComplexModel 1 →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin 1)

/-- The standard embedding `ℂ → ℂ¹`. -/
def emb0 : ℂ →L[ℂ] ComplexModel 1 :=
  ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))

@[simp] theorem proj0_emb0 (s : ℂ) : proj0 (emb0 s) = s := by
  simp [proj0, emb0, ContinuousLinearMap.toSpanSingleton_apply]

/-- **Maximum principle with removable zeros.**  Let `F` be plurisubharmonic on `O` off the zeros
of a holomorphic `G`, and locally bounded above (off those zeros) near every point of `O`.  If
`F ≤ B` on a circle where `G` has no zeros and the closed disc lies in `O`, then `F ≤ B` on the
disc, off the zeros of `G`. -/
theorem le_on_closedBall_of_removable {O : Set ℂ} (hO : IsOpen O) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G O) {F : ℂ → EReal}
    (hF : PlurisubharmonicOn F (O \ {s | G s = 0}))
    (hbound : ∀ x ∈ O, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, G y ≠ 0 → F y ≤ (C : EReal))
    {c : ℂ} {R B : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ O)
    (hsphere : ∀ s ∈ sphere c R, G s ≠ 0 ∧ F s ≤ (B : EReal)) :
    ∀ s ∈ closedBall c R, G s ≠ 0 → F s ≤ (B : EReal) := by
  classical
  -- transport to `ℂ¹`
  set O' : Set (ComplexModel 1) := proj0 ⁻¹' O with hO'def
  set A : Set (ComplexModel 1) := {t | G (proj0 t) = 0} with hAdef
  set ψ : ComplexModel 1 → EReal := fun t => F (proj0 t) with hψdef
  have hO'open : IsOpen O' := hO.preimage proj0.continuous
  have hψ : PlurisubharmonicOn ψ (O' \ A) := by
    have h1 := hF.comp_continuousLinearMap proj0
    have h2 : proj0 ⁻¹' (O \ {s | G s = 0}) = O' \ A := by
      ext t; simp [hO'def, hAdef]
    rw [h2] at h1
    exact h1
  have hψbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff A O' ψ := by
    intro x hx
    obtain ⟨U, hU, C, hC⟩ := hbound (proj0 x) hx
    exact ⟨proj0 ⁻¹' U, proj0.continuous.continuousAt.preimage_mem_nhds hU, C,
      fun y hy hyA => hC _ hy hyA⟩
  have hGt : ∀ _i : Fin 1, DifferentiableOn ℂ (fun t => G (proj0 t)) O' := fun _ =>
    hG.comp proj0.differentiable.differentiableOn (fun t ht => ht)
  have hext := PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hO'open hψ
    hψbound (g := fun _ t => G (proj0 t)) hGt (fun y _ => by simp [hAdef])
  -- back to `ℂ`
  set Φ : ℂ → EReal := fun s => PshCodimTwoExtension.extension A ψ (emb0 s) with hΦdef
  have hΦ : PlurisubharmonicOn Φ (emb0 ⁻¹' O') := hext.comp_continuousLinearMap emb0
  have hpre : emb0 ⁻¹' O' = O := by
    ext s; simp [hO'def]
  rw [hpre] at hΦ
  have hOA : IsOpen (O' \ A) := by
    have : O' \ A = O' ∩ (fun t => G (proj0 t)) ⁻¹' {0}ᶜ := by
      ext t; simp [hAdef]
    rw [this]
    exact (hGt 0).continuousOn.isOpen_inter_preimage hO'open isOpen_compl_singleton
  have heq : ∀ s ∈ O, G s ≠ 0 → Φ s = F s := by
    intro s hs hGs
    have hmem : emb0 s ∈ O' \ A := ⟨by simpa [hO'def] using hs, by simpa [hAdef] using hGs⟩
    have := PshCodimTwoExtension.extension_eq hψ hOA hmem
    simpa [hΦdef, hψdef] using this
  have hmax := PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere hΦ hR hD
    (fun s hs => by
      rw [heq s (hD (sphere_subset_closedBall hs)) (hsphere s hs).1]
      exact (hsphere s hs).2)
  intro s hs hGs
  rw [← heq s (hD hs) hGs]
  exact hmax s hs

/-! ### The bound near a transverse zero on a line -/

/-- Near a transverse regular zero `y = a + s₀ u₀` of `g`, of multiplicity `m`, a logarithmic
exponent `γ ≥ 2 c m` of `u` at `y` bounds `u - c log |g|²` above along the line. -/
theorem exists_line_bound_near_transverse_zero {n : ℕ} {u : ComplexModel n → EReal}
    {g : ComplexModel n → ℂ} {a u0 : ComplexModel n} (hu0 : ‖u0‖ = 1) {c : ℝ} (hc : 0 ≤ c)
    {s0 : ℂ} {y : ComplexModel n} (hs0 : a + s0 • u0 = y)
    (P : RegularPresentation g y) (htr : fderiv ℂ P.h y u0 ≠ 0)
    (hG : AnalyticAt ℂ (fun s : ℂ => g (a + s • u0)) s0)
    {γ C1 : ℝ} (hγ : 2 * c * P.m ≤ γ)
    (hC1 : ∀ᶠ z in 𝓝[≠] y, u z ≤ ((γ * Real.log ‖z - y‖ + C1 : ℝ) : EReal)) :
    ∃ U ∈ 𝓝 s0, ∃ C : ℝ, ∀ s ∈ U, g (a + s • u0) ≠ 0 →
      u (a + s • u0) + ((-(c * Real.log (‖g (a + s • u0)‖ ^ 2)) : ℝ) : EReal) ≤ (C : EReal) := by
  set L : ℂ → ComplexModel n := fun s => a + s • u0 with hL
  have hord : analyticOrderAt (fun s : ℂ => g (a + s • u0)) s0 = P.m :=
    P.analyticOrderAt_line a hs0 htr
  obtain ⟨h, hh, hh0, hev⟩ := hG.analyticOrderAt_eq_natCast.mp hord
  have hhpos : 0 < ‖h s0‖ := norm_pos_iff.mpr hh0
  have hhev : ∀ᶠ s in 𝓝 s0, ‖h s0‖ / 2 < ‖h s‖ :=
    continuousAt_const.eventually_lt hh.continuousAt.norm (half_lt_self hhpos)
  have hsub : ∀ s, L s - y = (s - s0) • u0 := by
    intro s; rw [← hs0, hL]; simp only [sub_smul]; abel
  have hnorm : ∀ s, ‖L s - y‖ = ‖s - s0‖ := by
    intro s; rw [hsub, norm_smul, hu0, mul_one]
  have hLcont : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have htend : Tendsto L (𝓝[≠] s0) (𝓝[≠] y) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto L (𝓝 s0) (𝓝 (L s0)) := hLcont.continuousAt
      have hy : L s0 = y := hs0
      rw [hy] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro hLs
      have h0 : ‖s - s0‖ = 0 := by rw [← hnorm, mem_singleton_iff.mp hLs, sub_self, norm_zero]
      exact hs (sub_eq_zero.mp (norm_eq_zero.mp h0))
  have hC1' := htend.eventually hC1
  have hlt1 : ∀ᶠ s in 𝓝 s0, ‖s - s0‖ < 1 := by
    have : Tendsto (fun s : ℂ => ‖s - s0‖) (𝓝 s0) (𝓝 0) := by
      have hc : Continuous (fun s : ℂ => ‖s - s0‖) := (continuous_id.sub continuous_const).norm
      simpa using hc.tendsto s0
    exact this.eventually (gt_mem_nhds one_pos)
  set C : ℝ := C1 - 2 * c * Real.log (‖h s0‖ / 2) with hCdef
  have hall : ∀ᶠ s in 𝓝[≠] s0, g (a + s • u0) ≠ 0 →
      u (a + s • u0) + ((-(c * Real.log (‖g (a + s • u0)‖ ^ 2)) : ℝ) : EReal) ≤ (C : EReal) := by
    filter_upwards [hC1', nhdsWithin_le_nhds hhev, nhdsWithin_le_nhds hlt1,
      nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs1 hs2 hs3 hs4 hs5 _hgs
    have hts : 0 < ‖s - s0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs5)
    have hlogt : Real.log ‖s - s0‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hs3.le
    have hgnorm : ‖g (a + s • u0)‖ = ‖s - s0‖ ^ P.m * ‖h s‖ := by
      rw [hs4, norm_smul, norm_pow]
    have hhs : 0 < ‖h s‖ := (half_pos hhpos).trans hs2
    have hlogg : Real.log (‖g (a + s • u0)‖ ^ 2) =
        2 * (P.m * Real.log ‖s - s0‖ + Real.log ‖h s‖) := by
      rw [hgnorm, Real.log_pow, Real.log_mul (pow_pos hts _).ne' hhs.ne', Real.log_pow]
      push_cast; ring
    have hlogh : Real.log (‖h s0‖ / 2) ≤ Real.log ‖h s‖ :=
      Real.log_le_log (half_pos hhpos) hs2.le
    have hu1 : u (a + s • u0) ≤ ((γ * Real.log ‖s - s0‖ + C1 : ℝ) : EReal) := by
      have := hs1; rwa [hnorm] at this
    calc u (a + s • u0) + ((-(c * Real.log (‖g (a + s • u0)‖ ^ 2)) : ℝ) : EReal)
        ≤ ((γ * Real.log ‖s - s0‖ + C1 : ℝ) : EReal) +
            ((-(c * Real.log (‖g (a + s • u0)‖ ^ 2)) : ℝ) : EReal) := add_le_add hu1 le_rfl
      _ = ((γ * Real.log ‖s - s0‖ + C1 - c * Real.log (‖g (a + s • u0)‖ ^ 2) : ℝ) : EReal) := by
          rw [← EReal.coe_add]; ring_nf
      _ ≤ (C : EReal) := by
          apply EReal.coe_le_coe_iff.mpr
          rw [hlogg, hCdef]
          have h1 : (γ - 2 * c * P.m) * Real.log ‖s - s0‖ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) hlogt
          have h2 : 2 * c * Real.log (‖h s0‖ / 2) ≤ 2 * c * Real.log ‖h s‖ :=
            mul_le_mul_of_nonneg_left hlogh (by linarith)
          nlinarith
  rw [eventually_nhdsWithin_iff] at hall
  refine ⟨_, hall, C, fun s hs hgs => ?_⟩
  by_cases hss : s = s0
  · subst hss
    exact absurd (by rw [hs0]; exact P.g_x) hgs
  · exact hs hss hgs

/-! ### The local Siu bound -/

/-- Plurisubharmonicity on an open set only depends on the values there. -/
theorem plurisubharmonicOn_congr_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u w : E → EReal} {U : Set E} (hU : IsOpen U) (hu : PlurisubharmonicOn u U)
    (heq : EqOn u w U) : PlurisubharmonicOn w U := by
  intro x hx
  obtain ⟨V, hVopen, hxV, hV⟩ := hu x hx
  exact ⟨V ∩ U, hVopen.inter hU, ⟨hxV, hx⟩,
    (hV.mono inter_subset_left).congr (heq.mono inter_subset_right)⟩

/-- **The local Siu bound along a hypersurface.**  Let `u` be plurisubharmonic and `g` holomorphic
on an open `Ω ⊆ ℂⁿ`, `g` vanishing identically near no point, and `c ≥ 0`.  If at every regular
point `y` of the divisor of `g`, of multiplicity `m`, the function `u` has a logarithmic exponent
`γ ≥ 2 c m` (`u(z) ≤ γ log ‖z - y‖ + C` near `y`), then near every point of `Ω`
`u ≤ c log |g|² + C` off the zeros of `g`.  No condition is imposed at singular points of the
divisor. -/
theorem exists_nhds_le_mul_log_normSq_add {n : ℕ} {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {g : ComplexModel n → ℂ} (hg : DifferentiableOn ℂ g Ω)
    (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hν : ∀ y ∈ Ω, ∀ P : RegularPresentation g y, ∃ γ : ℝ, 2 * c * P.m ≤ γ ∧ ∃ C : ℝ,
      ∀ᶠ z in 𝓝[≠] y, u z ≤ ((γ * Real.log ‖z - y‖ + C : ℝ) : EReal))
    {p : ComplexModel n} (hp : p ∈ Ω) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ z ∈ U, g z ≠ 0 →
      u z ≤ ((c * Real.log (‖g z‖ ^ 2) + C : ℝ) : EReal) := by
  classical
  -- the trivial case `c = 0`
  rcases hc.eq_or_lt with hc0 | hcpos
  · obtain ⟨C, hC⟩ := PlurisubharmonicOn.exists_real_bound_nhds hu hp
    refine ⟨_, hC, C, fun z hz _ => ?_⟩
    simpa [← hc0] using hz
  -- the case `g p ≠ 0`
  by_cases hgp : g p ≠ 0
  · obtain ⟨C, hC⟩ := PlurisubharmonicOn.exists_real_bound_nhds hu hp
    have hgcont : ContinuousAt g p := (hg.differentiableAt (hΩ.mem_nhds hp)).continuousAt
    have hgpos : 0 < ‖g p‖ := norm_pos_iff.mpr hgp
    have hev : ∀ᶠ z in 𝓝 p, ‖g p‖ / 2 < ‖g z‖ :=
      continuousAt_const.eventually_lt hgcont.norm (half_lt_self hgpos)
    refine ⟨_, hC.and hev, C - c * Real.log ((‖g p‖ / 2) ^ 2), fun z hz _ => ?_⟩
    refine hz.1.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hlog : Real.log ((‖g p‖ / 2) ^ 2) ≤ Real.log (‖g z‖ ^ 2) :=
      Real.log_le_log (by positivity) (pow_le_pow_left₀ (by positivity) hz.2.le 2)
    nlinarith [mul_le_mul_of_nonneg_left hlog hc]
  push Not at hgp
  -- a ball, and a direction along which `g` does not vanish identically
  obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  obtain ⟨z1, hz1g, hz1b⟩ := ((hg0 p hp).and_eventually (ball_mem_nhds p (half_pos hr0))).exists
  have hz1p : z1 ≠ p := fun h => hz1g (h ▸ hgp)
  set ρ1 : ℝ := ‖z1 - p‖ with hρ1def
  have hρ1 : 0 < ρ1 := norm_pos_iff.mpr (sub_ne_zero.mpr hz1p)
  have hρ1r : ρ1 < r0 / 2 := by
    rw [dist_eq_norm] at hz1b; exact hz1b
  set u0 : ComplexModel n := ((ρ1 : ℂ)⁻¹) • (z1 - p) with hu0def
  have hu0 : ‖u0‖ = 1 := by
    rw [hu0def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ1,
      ← hρ1def, inv_mul_cancel₀ hρ1.ne']
  have hz1eq : p + (ρ1 : ℂ) • u0 = z1 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ1.ne'), one_smul]; abel
  have hnormline : ∀ (b : ComplexModel n) (s : ℂ), ‖(b + s • u0) - b‖ = ‖s‖ := by
    intro b s; rw [add_sub_cancel_left, norm_smul, hu0, mul_one]
  -- the line through `p`
  set G0 : ℂ → ℂ := fun s => g (p + s • u0) with hG0def
  have hG0d : DifferentiableOn ℂ G0 (ball (0 : ℂ) r0) := by
    refine hg.comp ((differentiable_const _).add
      (differentiable_id.smul_const u0)).differentiableOn ?_
    intro s hs
    apply hball
    rw [mem_ball, dist_eq_norm, hnormline]
    simpa using hs
  have hiso : ∀ᶠ s in 𝓝[≠] (0 : ℂ), G0 s ≠ 0 := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), G0 s = 0 := hcon.mono fun s hs => not_not.mp hs
    have hzero := (hG0d.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) r0).isPreconnected (mem_ball_self hr0) hfreq
    have hmem : (ρ1 : ℂ) ∈ ball (0 : ℂ) r0 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ1]; linarith
    have := hzero hmem
    simp only [hG0def, Pi.zero_apply, hz1eq] at this
    exact hz1g this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨ε, hε, hεG⟩ := hiso
  set R : ℝ := min (ε / 2) (r0 / 4) with hRdef
  have hR : 0 < R := lt_min (half_pos hε) (by positivity)
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hRr : R ≤ r0 / 4 := min_le_right _ _
  have hGR : ∀ s ∈ sphere (0 : ℂ) R, G0 s ≠ 0 := by
    intro s hs
    have hsR : ‖s‖ = R := by simpa using hs
    refine hεG (by rw [dist_zero_right, hsR]; exact hRε) ?_
    intro h0; rw [mem_singleton_iff] at h0; rw [h0, norm_zero] at hsR; exact hR.ne hsR
  -- a uniform lower bound of `|g|` on the boundary circle
  have hsphne : (sphere (0 : ℂ) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  have hsphball : sphere (0 : ℂ) R ⊆ ball (0 : ℂ) r0 := by
    intro s hs; rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hs; linarith
  obtain ⟨sstar, hsstar, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn hsphne
    ((hG0d.continuousOn.mono hsphball).norm)
  set m0 : ℝ := ‖G0 sstar‖ with hm0def
  have hm0 : 0 < m0 := norm_pos_iff.mpr (hGR sstar hsstar)
  have hm0le : ∀ s ∈ sphere (0 : ℂ) R, m0 ≤ ‖G0 s‖ := fun s hs => hmin hs
  -- an orthogonal splitting along `u₀`
  obtain ⟨k, -, ⟨S⟩⟩ := DivisorRegularLocus.exists_splitting (V := ComplexModel n) hu0
  set E := EuclideanSpace ℂ (Fin k)
  have hLcont : Continuous (fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) :=
    (continuous_const.add (S.ι.continuous.comp continuous_fst)).add
      (continuous_snd.smul continuous_const)
  have hnormw : ∀ (w : E) (s : ℂ), ‖((p + S.ι w) + s • u0) - p‖ ≤ ‖w‖ + ‖s‖ := by
    intro w s
    have : ((p + S.ι w) + s • u0) - p = S.ι w + s • u0 := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [S.ι.norm_map, norm_smul, hu0, mul_one]
  have htube : ∀ᶠ w in 𝓝 (0 : E), ∀ s ∈ sphere (0 : ℂ) R,
      m0 / 2 < ‖g ((p + S.ι w) + s • u0)‖ := by
    apply (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro s hs
    have hpt : (p + S.ι (0 : E)) + s • u0 ∈ Ω := by
      apply hball
      rw [mem_ball, dist_eq_norm]
      refine (hnormw 0 s).trans_lt ?_
      rw [norm_zero, zero_add]
      have := hsphball hs; rw [mem_ball_zero_iff] at this; exact this
    have hcont : ContinuousAt (fun q : E × ℂ => ‖g ((p + S.ι q.1) + q.2 • u0)‖) (0, s) := by
      have h1 : ContinuousAt g ((fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) (0, s)) :=
        (hg.differentiableAt (hΩ.mem_nhds hpt)).continuousAt
      exact (ContinuousAt.comp (f := fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) h1
        hLcont.continuousAt).norm
    have hval : m0 / 2 < ‖g ((p + S.ι (0 : E)) + s • u0)‖ := by
      have h1 := hm0le s hs
      simp only [map_zero, add_zero] at h1 ⊢
      linarith
    exact hcont.eventually (lt_mem_nhds hval)
  rw [Metric.eventually_nhds_iff] at htube
  obtain ⟨δ1, hδ1, hδ1G⟩ := htube
  set δ : ℝ := min δ1 (r0 / 4) with hδdef
  have hδ : 0 < δ := lt_min hδ1 (by positivity)
  have hδr : δ ≤ r0 / 4 := min_le_right _ _
  -- an upper bound of `u` near `p`
  have hKΩ : closedBall p (r0 / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨A, hA⟩ := PlurisubharmonicOn.exists_real_bound_of_isCompact hu
    (isCompact_closedBall p (r0 / 2)) hKΩ
  set B : ℝ := A - c * Real.log ((m0 / 2) ^ 2) with hBdef
  -- the null set of bad lines
  set Bad : Set (ComplexModel n) :=
    {y | y ∈ ball p r0 ∧ g y = 0 ∧ y ∉ transverseLocus g u0} with hBaddef
  set Ynull : Set E := S.π '' Bad with hYdef
  have hnull : volume Ynull = 0 :=
    DivisorSingularProjection.measure_image_bad_eq_zero (volume : Measure E) isOpen_ball
      (hg.mono hball) (fun y hy => hg0 y (hball hy)) hu0 S
  -- the bound on a good line
  have hslice : ∀ w : E, ‖w‖ < δ → S.π p + w ∉ Ynull → ∀ s : ℂ, ‖s‖ < R →
      g ((p + S.ι w) + s • u0) ≠ 0 →
      u ((p + S.ι w) + s • u0) ≤
        ((c * Real.log (‖g ((p + S.ι w) + s • u0)‖ ^ 2) + B : ℝ) : EReal) := by
    intro w hw hgood s hs hgs
    set a : ComplexModel n := p + S.ι w with hadef
    set Lw : ℂ → ComplexModel n := fun s => a + s • u0 with hLwdef
    have hLwc : Continuous Lw := continuous_const.add (continuous_id.smul continuous_const)
    set O : Set ℂ := Lw ⁻¹' ball p r0 with hOdef
    have hOopen : IsOpen O := isOpen_ball.preimage hLwc
    set G : ℂ → ℂ := fun s => g (Lw s) with hGdef
    have hGd : DifferentiableOn ℂ G O :=
      hg.comp ((differentiable_const _).add (differentiable_id.smul_const u0)).differentiableOn
        (fun s hs => hball hs)
    set F : ℂ → EReal := fun s => u (Lw s) + ((-(c * Real.log (‖G s‖ ^ 2)) : ℝ) : EReal)
      with hFdef
    have hnormLw : ∀ s : ℂ, ‖Lw s - p‖ ≤ ‖w‖ + ‖s‖ := fun s => hnormw w s
    have hD : closedBall (0 : ℂ) R ⊆ O := by
      intro s hs
      rw [mem_closedBall_zero_iff] at hs
      show Lw s ∈ ball p r0
      rw [mem_ball, dist_eq_norm]
      refine (hnormLw s).trans_lt ?_
      linarith
    -- `F` is plurisubharmonic off the zeros of `G`
    have hOZ : IsOpen (O \ {s | G s = 0}) := by
      have : O \ {s | G s = 0} = O ∩ G ⁻¹' {0}ᶜ := by ext; simp
      rw [this]; exact hGd.continuousOn.isOpen_inter_preimage hOopen isOpen_compl_singleton
    have hFpsh : PlurisubharmonicOn F (O \ {s | G s = 0}) := by
      have h1 : PlurisubharmonicOn (fun s => u (Lw s)) (O \ {s | G s = 0}) := by
        have := (hu.mono hball).comp_affine (ContinuousLinearMap.toSpanSingleton ℂ u0) a
        simp only [ContinuousLinearMap.toSpanSingleton_apply] at this
        exact this.mono sdiff_subset
      have hinv : DifferentiableOn ℂ (fun s => (G s)⁻¹) (O \ {s | G s = 0}) :=
        (hGd.mono sdiff_subset).inv (fun s hs => hs.2)
      have h2 : PlurisubharmonicOn
          (fun s => (c : EReal) * generatorLog (fun _ : Fin 1 => fun s => (G s)⁻¹) s)
          (O \ {s | G s = 0}) := fun s hs =>
        plurisubharmonicAt_scaled_generatorLog ⟨_, hOZ, hs, fun _ => hinv⟩ hcpos
      refine plurisubharmonicOn_congr_of_isOpen hOZ (h1.add h2) ?_
      intro s hs
      have hGs : G s ≠ 0 := hs.2
      simp only [hFdef]
      congr 1
      rw [generatorLog_of_nonzero ⟨0, inv_ne_zero hGs⟩]
      simp only [generatorNormSq, Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, norm_inv, inv_pow, Real.log_inv]
      rw [← EReal.coe_mul]; congr 1; ring
    -- local upper bounds
    have hFbound : ∀ x ∈ O, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, G y ≠ 0 → F y ≤ (C : EReal) := by
      intro x hx
      by_cases hGx : G x = 0
      · set y : ComplexModel n := Lw x with hydef
        have hyb : y ∈ ball p r0 := hx
        have hπy : S.π y = S.π p + w := by
          simp only [hydef, hLwdef, hadef, map_add, map_smul, S.π_ι, S.π_u, smul_zero, add_zero]
        have htr : y ∈ transverseLocus g u0 := by
          by_contra hbad
          exact hgood (hπy ▸ ⟨y, ⟨hyb, hGx, hbad⟩, rfl⟩)
        obtain ⟨P⟩ := htr.1
        have hdh : fderiv ℂ P.h y u0 ≠ 0 :=
          (P.mem_transverseLocus_iff P.mem P.g_x u0).mp htr
        obtain ⟨γ, hγ, C1, hC1⟩ := hν y (hball hyb) P
        have hGa : AnalyticAt ℂ (fun s : ℂ => g (a + s • u0)) x :=
          hGd.analyticAt (hOopen.mem_nhds hx)
        obtain ⟨U, hU, C, hC⟩ := exists_line_bound_near_transverse_zero hu0 hc
          (rfl : a + x • u0 = y) P hdh hGa hγ hC1
        exact ⟨U, hU, C, hC⟩
      · obtain ⟨C, hC⟩ := PlurisubharmonicOn.exists_real_bound_nhds hFpsh ⟨hx, hGx⟩
        exact ⟨_, hC, C, fun y hy _ => hy⟩
    -- the boundary circle
    have hsph : ∀ s ∈ sphere (0 : ℂ) R, G s ≠ 0 ∧ F s ≤ (B : EReal) := by
      intro s hs
      have hwδ1 : dist w 0 < δ1 := by
        rw [dist_zero_right]; exact hw.trans_le (min_le_left _ _)
      have hGs : m0 / 2 < ‖G s‖ := hδ1G hwδ1 s hs
      have hGs0 : G s ≠ 0 := fun h => by rw [h, norm_zero] at hGs; linarith
      refine ⟨hGs0, ?_⟩
      have hsR : ‖s‖ = R := by simpa using hs
      have huA : u (Lw s) ≤ (A : EReal) := by
        apply hA
        rw [mem_closedBall, dist_eq_norm]
        refine (hnormLw s).trans ?_
        linarith
      have hlog : Real.log ((m0 / 2) ^ 2) ≤ Real.log (‖G s‖ ^ 2) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ (by positivity) hGs.le 2)
      calc F s ≤ (A : EReal) + ((-(c * Real.log (‖G s‖ ^ 2)) : ℝ) : EReal) :=
            add_le_add huA le_rfl
        _ = ((A - c * Real.log (‖G s‖ ^ 2) : ℝ) : EReal) := by
            rw [← EReal.coe_add]; ring_nf
        _ ≤ (B : EReal) := by
            apply EReal.coe_le_coe_iff.mpr
            rw [hBdef]
            nlinarith [mul_le_mul_of_nonneg_left hlog hc]
    have hmain := le_on_closedBall_of_removable hOopen hGd hFpsh hFbound hR hD hsph s
      (mem_closedBall_zero_iff.mpr hs.le) hgs
    have := EReal.le_add_of_add_neg_le hmain
    rw [add_comm B] at this
    exact this
  -- the bound almost everywhere, hence everywhere off the zeros of `g`
  set N : Set (ComplexModel n) :=
    {z | ‖⟪u0, z - p⟫_ℂ‖ < R ∧ ‖S.π (z - p)‖ < δ} with hNdef
  have hNopen : IsOpen N := by
    apply IsOpen.inter
    · exact isOpen_lt ((continuous_const.inner (continuous_id.sub continuous_const)).norm)
        continuous_const
    · exact isOpen_lt ((S.π.continuous.comp (continuous_id.sub continuous_const)).norm)
        continuous_const
  have hpN : p ∈ N := by
    simp only [hNdef, mem_ofPred_eq, sub_self, inner_zero_right, norm_zero, map_zero]
    exact ⟨hR, hδ⟩
  have hdecomp : ∀ z : ComplexModel n,
      z = (p + S.ι (S.π (z - p))) + ⟪u0, z - p⟫_ℂ • u0 := by
    intro z
    have h := S.decomp (z - p)
    calc z = p + (z - p) := by abel
      _ = p + (⟪u0, z - p⟫_ℂ • u0 + S.ι (S.π (z - p))) := by rw [← h]
      _ = _ := by abel
  have hNball : N ⊆ ball p r0 := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    have h := hnormw (S.π (z - p)) (⟪u0, z - p⟫_ℂ)
    rw [← hdecomp z] at h
    have := hz.1; have := hz.2
    linarith
  set Ω' : Set (ComplexModel n) := N ∩ g ⁻¹' {0}ᶜ with hΩ'def
  have hΩ'open : IsOpen Ω' :=
    (hg.continuousOn.mono (hNball.trans hball)).isOpen_inter_preimage hNopen
      isOpen_compl_singleton
  have hpre : volume (S.π ⁻¹' Ynull) = 0 := by
    have hmp := DivisorIntegrationCurrent.measurePreserving_splitMap hu0 S
    have hemb := DivisorIntegrationCurrent.measurableEmbedding_splitMap hu0 S
    rw [← hmp.map_eq, hemb.map_apply]
    have : DivisorIntegrationCurrent.splitMap S ⁻¹' (S.π ⁻¹' Ynull) = univ ×ˢ Ynull := by
      ext q
      simp [DivisorIntegrationCurrent.splitMap_apply, S.π_smul_add]
    rw [this, Measure.prod_prod, hnull, mul_zero]
  set v : ComplexModel n → EReal := fun z => ((c * Real.log (‖g z‖ ^ 2) + B : ℝ) : EReal)
    with hvdef
  have hvusc : UpperSemicontinuousOn v Ω' := by
    apply ContinuousOn.upperSemicontinuousOn
    apply continuous_coe_real_ereal.comp_continuousOn
    refine ContinuousOn.add (continuousOn_const.mul ?_) continuousOn_const
    refine ContinuousOn.log ((hg.continuousOn.mono ((inter_subset_left).trans
      (hNball.trans hball))).norm.pow 2) ?_
    intro z hz
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz.2)
  have hae : ∀ᵐ z ∂(volume.restrict Ω'), u z ≤ v z := by
    rw [ae_restrict_iff' hΩ'open.measurableSet]
    refine measure_mono_null ?_ hpre
    intro z hz
    have hz' : z ∈ Ω' ∧ ¬ u z ≤ v z := by simpa [Classical.not_imp] using hz
    obtain ⟨hzΩ', hzu⟩ := hz'
    by_contra hzY
    apply hzu
    have hw : S.π p + S.π (z - p) = S.π z := by rw [map_sub]; abel
    have hgood : S.π p + S.π (z - p) ∉ Ynull := by rw [hw]; exact hzY
    have hz' := hdecomp z
    have hgz : g ((p + S.ι (S.π (z - p))) + ⟪u0, z - p⟫_ℂ • u0) ≠ 0 := by
      rw [← hz']; exact hzΩ'.2
    have := hslice (S.π (z - p)) hzΩ'.1.2 hgood (⟪u0, z - p⟫_ℂ) hzΩ'.1.1 hgz
    rw [← hz'] at this
    exact this
  have hle := PlurisubharmonicOn.le_of_ae_le (hu.mono ((inter_subset_left).trans
    (hNball.trans hball))) hΩ'open hvusc volume hae
  refine ⟨N, hNopen.mem_nhds hpN, B, fun z hz hgz => hle z ⟨hz, hgz⟩⟩

end SGPT.Siu
