import SGPT.Okounkov.TranscendentalWNLegendre
import SGPT.Foundations.Analysis.FirstPass.PshSupremumRegularization

/-!
# Inverse partial Legendre transforms (package WN-LEG)

Blueprint nodes `tok-wn:legendre`, `tok-wn:legendre-usc` (chapter `claude-tok-wn`) and
`tok-wn-leg:duality`, `tok-wn-leg:lambda-continuity`, `tok-wn-leg:inverse-psh` (supplement
`claude-tok-wn-leg`); source WN21 §3 (`references/wn21-restricted-volume`):

> Let `v_λ`, `λ ∈ [a,b]` be a concave family of psh functions on `U`.  If
> `u(z,τ) := sup_{λ ∈ [a,b]} {v_λ(z) + λ ln |τ|²}` is psh then … A supremum of psh functions is
> psh as long as it is u.s.c, and it follows from the elementary lemma below [Lemma 3.2] that
> this will be the case here as long as a certain boundedness condition is met.

## Main results

* `iSup_eq_iSup_Icc_of_eq_bot`, `partialLegendre_duality_Icc`,
  `partialLegendre_duality_Icc_of_thetaPsh` — when `û_λ ≡ -∞` off `[a, b]`, Legendre duality
  `u = sup_{λ ∈ [a,b]} (û_λ + λ log |τ|²)` holds with the supremum over `[a, b]`.
* `upperSemicontinuous_partialLegendre_param` — `λ ↦ û_λ(x)` is upper semicontinuous.
* `plurisubharmonicOn_mul_logNormSq` — `(z, τ) ↦ c log |τ|²` is psh on `W × ℂ*` for every real
  `c` (it is locally the real part of the holomorphic `2c log(τ/τ₀) + c log |τ₀|²`).
* `inverseLegendre v a b` — `(x, τ) ↦ sup_{λ ∈ [a,b]} (v_λ(x) + λ log |τ|²)`;
  `plurisubharmonicOn_inverseLegendre` — for a concave family of psh functions `v_λ` on `W`,
  `λ ∈ [a,b]`, locally bounded for `λ ∈ [a', b']`, `a ≤ a' < b' ≤ b`, the inverse transform is
  psh on `W × ℂ*` (WN21 §3, via Lemma 3.2 = `upperSemicontinuousAt_iSup_concave` and TN's
  regularized-supremum theorem).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

/-! ### Duality over `[a, b]` -/

/-- A supremum of `g λ + c λ` over `ℝ` equals the supremum over `[a, b]` when `g λ = -∞` off
`[a, b]`. -/
theorem iSup_eq_iSup_Icc_of_eq_bot {g : ℝ → EReal} (c : ℝ → ℝ) {a b : ℝ}
    (hg : ∀ lam, lam ∉ Icc a b → g lam = ⊥) :
    (⨆ lam : ℝ, g lam + (c lam : EReal)) = ⨆ lam ∈ Icc a b, g lam + (c lam : EReal) := by
  apply le_antisymm
  · refine iSup_le fun lam => ?_
    by_cases hl : lam ∈ Icc a b
    · exact le_iSup₂ (f := fun lam _ => g lam + (c lam : EReal)) lam hl
    · rw [hg lam hl, EReal.bot_add]; exact bot_le
  · exact iSup₂_le fun lam _ => le_iSup (fun lam => g lam + (c lam : EReal)) lam

/-- **Legendre duality over `[a, b]`** (local form). -/
theorem partialLegendre_duality_Icc {m : ℕ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane))
    (hinv : IsCircleInvariant u) {a b : ℝ} {z : ComplexModel m} (hz : z ∈ W)
    (hbot : ∀ lam, lam ∉ Icc a b → partialLegendre u lam z = ⊥) {τ : ℂ} (hτ : τ ≠ 0) :
    u z τ = ⨆ lam ∈ Icc a b, partialLegendre u lam z + ((lam * logNormSq τ : ℝ) : EReal) := by
  rw [partialLegendre_duality hW hu hinv hz hτ]
  exact iSup_eq_iSup_Icc_of_eq_bot (fun lam => lam * logNormSq τ) hbot

/-- **Legendre duality over `[a, b]`** (manifold form). -/
theorem partialLegendre_duality_Icc_of_thetaPsh {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {θ : SmoothRealForm n M 2}
    {u : M → ℂ → EReal} (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u)
    {a b : ℝ} (x : M) (hbot : ∀ lam, lam ∉ Icc a b → partialLegendre u lam x = ⊥) {τ : ℂ}
    (hτ : τ ≠ 0) :
    u x τ = ⨆ lam ∈ Icc a b, partialLegendre u lam x + ((lam * logNormSq τ : ℝ) : EReal) := by
  rw [partialLegendre_duality_of_thetaPsh hu hinv x hτ]
  exact iSup_eq_iSup_Icc_of_eq_bot (fun lam => lam * logNormSq τ) hbot

/-! ### Upper semicontinuity in `λ` -/

/-- `λ ↦ x - λ c` is continuous on `ℝ` for every `x : EReal` (constant if `x = ±∞`). -/
theorem continuous_ereal_sub_mul (x : EReal) (c : ℝ) :
    Continuous (fun lam : ℝ => x - ((lam * c : ℝ) : EReal)) := by
  induction x using EReal.rec with
  | bot =>
      have : (fun lam : ℝ => (⊥ : EReal) - ((lam * c : ℝ) : EReal)) = fun _ => ⊥ := by
        funext lam; simp
      rw [this]; exact continuous_const
  | coe r =>
      have : (fun lam : ℝ => (r : EReal) - ((lam * c : ℝ) : EReal)) =
          fun lam : ℝ => (((r - lam * c : ℝ)) : EReal) := by
        funext lam; rw [EReal.coe_sub]
      rw [this]
      exact continuous_coe_real_ereal.comp (continuous_const.sub (continuous_id.mul continuous_const))
  | top =>
      have : (fun lam : ℝ => (⊤ : EReal) - ((lam * c : ℝ) : EReal)) = fun _ => ⊤ := by
        funext lam; exact EReal.top_sub_coe _
      rw [this]; exact continuous_const

/-- **`λ ↦ û_λ(x)` is upper semicontinuous** (`tok-wn-leg:lambda-continuity`): an infimum of
continuous functions of `λ`. -/
theorem upperSemicontinuous_partialLegendre_param {X : Type*} (u : X → ℂ → EReal) (x : X) :
    UpperSemicontinuous (fun lam : ℝ => partialLegendre u lam x) := by
  have h : ∀ τ : puncturedPlane,
      UpperSemicontinuous (fun lam : ℝ => u x τ - ((lam * logNormSq τ : ℝ) : EReal)) :=
    fun τ => (continuous_ereal_sub_mul _ _).upperSemicontinuous
  simpa [partialLegendre] using upperSemicontinuous_iInf h

/-- The chord lower bound, eventually: if `f` is concave at `x` on `[a, b]` with finite values
`f λ₀ = r₀` and `f e = r` at an endpoint `e ≠ λ₀` of `[a, b]`, then for every real `c < r₀`,
`c < f λ` for `λ` near `λ₀` between `λ₀` and `e`. -/
theorem eventually_lt_of_chord {X : Type*} {v : ℝ → X → EReal} {I : Set ℝ} {x : X}
    (hconc : IsConcaveFamilyAt v I x) {l₀ e r₀ r : ℝ} (hl₀ : l₀ ∈ I) (he : e ∈ I) (hle : l₀ ≠ e)
    (h₀ : v l₀ x = r₀) (hr : v e x = r) {c : ℝ} (hc : c < r₀) :
    ∀ᶠ lam in 𝓝 l₀, lam ∈ segment ℝ l₀ e → (c : EReal) < v lam x := by
  -- the chord value at the parameter `t` with `λ = t l₀ + (1 - t) e`
  have hd : e - l₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hle)
  have hcont : ContinuousAt (fun lam : ℝ => (e - lam) / (e - l₀) * r₀ +
      (1 - (e - lam) / (e - l₀)) * r) l₀ := by fun_prop
  have hval : (fun lam : ℝ => (e - lam) / (e - l₀) * r₀ + (1 - (e - lam) / (e - l₀)) * r) l₀ = r₀ := by
    simp [div_self hd]
  have hev := hcont.eventually (lt_mem_nhds (show c < _ by rw [hval]; exact hc))
  filter_upwards [hev] with lam hlam hseg
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hseg
  simp only [smul_eq_mul] at hlam ⊢
  have ht' : (e - (s * l₀ + t * e)) / (e - l₀) = s := by
    rw [show e - (s * l₀ + t * e) = s * (e - l₀) by
      have : t = 1 - s := by linarith
      subst this; ring]
    field_simp
  rw [ht'] at hlam
  have hch := hconc l₀ hl₀ e he s hs (by linarith)
  rw [h₀, hr, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hch
  have htt : t = 1 - s := by linarith
  rw [show s * l₀ + t * e = s * l₀ + (1 - s) * e by rw [htt]]
  exact (EReal.coe_lt_coe_iff.mpr hlam).trans_le hch

/-- **`λ ↦ û_λ(x)` is continuous on `[a, b]`** when `û_a(x)` and `û_b(x)` are `> -∞`
(`tok-wn-leg:lambda-continuity`): upper semicontinuity and the chord lower bounds. -/
theorem continuousOn_partialLegendre_param {X : Type*} (u : X → ℂ → EReal) (x : X) {a b : ℝ}
    (hab : a < b) (ha : partialLegendre u a x ≠ ⊥) (hb : partialLegendre u b x ≠ ⊥) :
    ContinuousOn (fun lam : ℝ => partialLegendre u lam x) (Icc a b) := by
  by_cases htop : partialLegendre u a x = ⊤
  · -- then `u x τ = ⊤` for all `τ`, and `û ≡ ⊤`
    have hall : ∀ τ : puncturedPlane, u x τ = ⊤ := by
      intro τ
      have h := (iInf_eq_top.mp htop) τ
      induction hux : u x τ using EReal.rec with
      | bot => rw [hux] at h; simp at h
      | coe r => rw [hux, ← EReal.coe_sub] at h; exact absurd h (EReal.coe_ne_top _)
      | top => rfl
    have hconst : (fun lam : ℝ => partialLegendre u lam x) = fun _ => ⊤ := by
      funext lam
      simp only [partialLegendre, hall, EReal.top_sub_coe, iInf_const]
    rw [hconst]; exact continuousOn_const
  -- finiteness on `[a, b]`
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : puncturedPlane, u x τ - ((a * logNormSq τ : ℝ) : EReal) < ⊤ := by
    by_contra hne
    push Not at hne
    exact htop (iInf_eq_top.mpr fun τ => top_le_iff.mp (hne τ))
  have hux : u x τ₀ ≠ ⊤ := by
    intro h; rw [h, EReal.top_sub_coe] at hτ₀; exact lt_irrefl _ hτ₀
  have hlt : ∀ lam, partialLegendre u lam x ≠ ⊤ := by
    intro lam h
    have := iInf_le (fun τ : puncturedPlane => u x τ - ((lam * logNormSq τ : ℝ) : EReal)) τ₀
    rw [← partialLegendre, h, top_le_iff] at this
    induction hu : u x τ₀ using EReal.rec with
    | bot => rw [hu] at this; simp at this
    | coe r => rw [hu, ← EReal.coe_sub] at this; exact EReal.coe_ne_top _ this
    | top => exact hux hu
  have hconc := isConcaveFamilyAt_partialLegendre u (Icc a b) x
  have hfin : ∀ lam ∈ Icc a b, partialLegendre u lam x ≠ ⊥ := by
    intro lam hl
    rcases eq_or_lt_of_le hl.1 with h | h
    · rw [← h]; exact ha
    have ra := (EReal.coe_toReal (hlt a) ha).symm
    have rb := (EReal.coe_toReal (hlt b) hb).symm
    set t : ℝ := (b - lam) / (b - a)
    have hch := hconc a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩ t
      (div_nonneg (by linarith [hl.2]) (by linarith)) ((div_le_one (by linarith)).mpr (by linarith))
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    have hpt : t * a + (1 - t) * b = lam := by simp only [t]; field_simp; ring
    beta_reduce at hch
    rw [hpt] at hch
    intro hbot
    rw [hbot, ra, rb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hch
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hch)
  intro l₀ hl₀
  have hr₀ := (EReal.coe_toReal (hlt l₀) (hfin l₀ hl₀)).symm
  refine (tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩)
  · -- lower bound from the chords to `a` and to `b`
    obtain ⟨c', hcc', hc'⟩ := EReal.exists_between_coe_real hc
    have hc'' : c' < (partialLegendre u l₀ x).toReal := by
      have h' : (c' : EReal) < partialLegendre u l₀ x := hc'
      rw [hr₀] at h'; exact EReal.coe_lt_coe_iff.mp h'
    have side : ∀ e ∈ Icc a b, ∀ᶠ lam in 𝓝 l₀, lam ∈ segment ℝ l₀ e →
        c < partialLegendre u lam x := by
      intro e he
      by_cases hle : l₀ = e
      · filter_upwards with lam hlam
        rw [← hle, segment_same] at hlam
        rw [hlam]; exact hc
      have hre := (EReal.coe_toReal (hlt e) (hfin e he)).symm
      filter_upwards [eventually_lt_of_chord hconc hl₀ he hle hr₀ hre hc''] with lam h hseg
      exact hcc'.trans (h hseg)
    filter_upwards [nhdsWithin_le_nhds (side a ⟨le_rfl, hab.le⟩),
      nhdsWithin_le_nhds (side b ⟨hab.le, le_rfl⟩), self_mem_nhdsWithin] with lam h1 h2 hl
    rcases le_total lam l₀ with h | h
    · exact h1 (by rw [segment_eq_Icc' ]; exact ⟨by simp [hl.1], by simp [h]⟩)
    · exact h2 (by rw [segment_eq_Icc']; exact ⟨by simp [h], by simp [hl.2]⟩)
  · exact nhdsWithin_le_nhds (upperSemicontinuous_partialLegendre_param u x l₀ c hc)

/-! ### `c log |τ|²` is pluriharmonic on `W × ℂ*` -/

theorem logNormSq_eq_re_log {τ τ₀ : ℂ} (hτ : τ ≠ 0) (hτ₀ : τ₀ ≠ 0) :
    logNormSq τ = (2 * Complex.log (τ / τ₀)).re + logNormSq τ₀ := by
  have h1 : (2 * Complex.log (τ / τ₀)).re = 2 * Real.log (‖τ‖ / ‖τ₀‖) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.log_re,
      norm_div]
  rw [h1, logNormSq, logNormSq, Real.log_div (norm_ne_zero_iff.mpr hτ) (norm_ne_zero_iff.mpr hτ₀),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **`(z, τ) ↦ c log |τ|²` is psh on `W × ℂ*`**, for every real `c`. -/
theorem plurisubharmonicOn_mul_logNormSq {m : ℕ} (c : ℝ) (W : Set (ComplexModel m)) :
    PlurisubharmonicOn (fun p : ComplexModel m × ℂ => ((c * logNormSq p.2 : ℝ) : EReal))
      (W ×ˢ puncturedPlane) := by
  rintro ⟨z₀, τ₀⟩ ⟨-, hτ₀⟩
  have hτ₀' : τ₀ ≠ 0 := hτ₀
  set U₀ : Set (ComplexModel m × ℂ) := {p | 0 < (p.2 / τ₀).re}
  have hU₀ : IsOpen U₀ :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.div_const τ₀))
  have hp₀ : ((z₀, τ₀) : ComplexModel m × ℂ) ∈ U₀ := by
    simp [U₀, div_self hτ₀']
  let F : ComplexModel m × ℂ → ComplexModel m × ℂ := fun p => (p.1, 2 * Complex.log (p.2 / τ₀))
  have hF : DifferentiableOn ℂ F U₀ := by
    intro p hp
    have hlog : DifferentiableAt ℂ (fun q : ComplexModel m × ℂ => Complex.log (q.2 / τ₀)) p := by
      have hslit : p.2 / τ₀ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hp)
      have hd : DifferentiableAt ℂ (fun q : ComplexModel m × ℂ => q.2 / τ₀) p := by fun_prop
      exact (Complex.differentiableAt_log hslit).comp p hd
    exact (differentiableAt_fst.prodMk (hlog.const_mul 2)).differentiableWithinAt
  set Ψ : ComplexModel m × ℂ → EReal := fun q => ((c * q.2.re + c * logNormSq τ₀ : ℝ) : EReal)
  have hΨ : PlurisubharmonicOn Ψ univ := by
    have := (plurisubharmonicOn_coe_affine_re c (c * logNormSq τ₀) univ).comp_continuousLinearMap
      (ContinuousLinearMap.snd ℂ (ComplexModel m) ℂ)
    exact this.mono fun _ _ => mem_univ _
  have hpull := plurisubharmonicOn_comp_holomorphic_strip hU₀ hF (mapsTo_univ _ _) hΨ
  refine (hpull _ hp₀).congr ?_
  filter_upwards [hU₀.mem_nhds hp₀] with p hp
  have hp2 : p.2 ≠ 0 := by
    intro h0
    simp [U₀, h0] at hp
  simp only [Ψ, F]
  rw [logNormSq_eq_re_log hp2 hτ₀']
  congr 1
  ring

/-! ### Concave families plus an affine term -/

/-- `t (A + r) = t A + t r` in `EReal` for `t ≥ 0` and real `r`. -/
theorem ereal_coe_mul_add_coe {t : ℝ} (ht : 0 ≤ t) (A : EReal) (r : ℝ) :
    (t : EReal) * (A + (r : EReal)) = (t : EReal) * A + ((t * r : ℝ) : EReal) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0; simp
  induction A using EReal.rec with
  | bot => rw [EReal.bot_add, EReal.coe_mul_bot_of_pos hpos, EReal.bot_add]
  | coe x => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hpos, EReal.top_add_coe]

/-- Adding `λ c` to a concave family keeps it concave. -/
theorem IsConcaveFamilyAt.add_affine {X : Type*} {v : ℝ → X → EReal} {I : Set ℝ} {x : X}
    (h : IsConcaveFamilyAt v I x) (c : ℝ) :
    IsConcaveFamilyAt (fun lam y => v lam y + ((lam * c : ℝ) : EReal)) I x := by
  intro l₁ hl₁ l₂ hl₂ t ht0 ht1
  have h1 := h l₁ hl₁ l₂ hl₂ t ht0 ht1
  simp only
  rw [ereal_coe_mul_add_coe ht0, ereal_coe_mul_add_coe (by linarith : (0 : ℝ) ≤ 1 - t),
    add_add_add_comm, ← EReal.coe_add]
  have e : t * (l₁ * c) + (1 - t) * (l₂ * c) = (t * l₁ + (1 - t) * l₂) * c := by ring
  rw [e]
  exact add_le_add h1 le_rfl

/-! ### The inverse transform -/

/-- The **inverse partial Legendre transform** `(x, τ) ↦ sup_{λ ∈ [a,b]} (v_λ(x) + λ log |τ|²)`. -/
def inverseLegendre {X : Type*} (v : ℝ → X → EReal) (a b : ℝ) (x : X) (τ : ℂ) : EReal :=
  ⨆ lam ∈ Icc a b, v lam x + ((lam * logNormSq τ : ℝ) : EReal)

/-- A function upper semicontinuous at `x` is not lowered by its regularization there. -/
theorem uscRegularization_le_of_upperSemicontinuousAt {X : Type*} [TopologicalSpace X]
    {f : X → EReal} {x : X} (hf : UpperSemicontinuousAt f x) : uscRegularization f x ≤ f x := by
  apply le_of_forall_gt
  intro c hc
  obtain ⟨d, hxd, hdc⟩ := exists_between hc
  have hU : {y | f y < d} ∈ 𝓝 x := hf d hxd
  exact ((uscRegularization_le_localSup f hU).trans
    (iSup₂_le fun y hy => le_of_lt hy)).trans_lt hdc

/-- A supremum over `[a, b]` of a concave family with finite values at `a' < (a'+b')/2 < b'`
is `< ⊤`. -/
theorem iSup_Icc_lt_top_of_concave {X : Type*} {v : ℝ → X → EReal} {a b a' b' : ℝ} {x : X}
    (haa : a ≤ a') (hab' : a' < b') (hbb : b' ≤ b) (hconc : IsConcaveFamilyAt v (Icc a b) x)
    (hne : ∀ lam ∈ Icc a b, v lam x ≠ ⊤) {p q r : ℝ} (hp : v a' x = p)
    (hq : v ((a' + b') / 2) x = q) (hr : v b' x = r) :
    (⨆ lam ∈ Icc a b, v lam x) < ⊤ := by
  set m : ℝ := (a' + b') / 2
  have ham : a' < m := by simp only [m]; linarith
  have hmb : m < b' := by simp only [m]; linarith
  have ha'I : a' ∈ Icc a b := ⟨haa, by linarith⟩
  have hb'I : b' ∈ Icc a b := ⟨by linarith, hbb⟩
  set D : ℝ := q + (b - a) * (|q - p| / (m - a') + |q - r| / (b' - m))
  have hbound : ∀ lam ∈ Icc a b, v lam x ≤ (D : EReal) := by
    intro lam hl
    have hD1 : 0 ≤ |q - p| / (m - a') := div_nonneg (abs_nonneg _) (by linarith)
    have hD2 : 0 ≤ |q - r| / (b' - m) := div_nonneg (abs_nonneg _) (by linarith)
    rcases le_total m lam with hml | hlm
    · have h := concave_right_slope_bound hconc hne ham le_rfl hml ha'I
        ⟨by linarith, by linarith⟩ hl hp hq
      refine h.trans ?_
      rw [hq, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have : (lam - m) * (q - p) / (m - a') ≤ (b - a) * (|q - p| / (m - a')) := by
        rw [mul_div_assoc]
        calc (lam - m) * ((q - p) / (m - a')) ≤ (lam - m) * (|q - p| / (m - a')) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self _)
                (by linarith)) (by linarith)
          _ ≤ (b - a) * (|q - p| / (m - a')) :=
              mul_le_mul_of_nonneg_right (by linarith [hl.2]) hD1
      nlinarith
    · have h := concave_left_slope_bound hconc hne hmb le_rfl hlm hb'I
        ⟨by linarith, by linarith⟩ hl hr hq
      refine h.trans ?_
      rw [hq, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have : (m - lam) * (q - r) / (b' - m) ≤ (b - a) * (|q - r| / (b' - m)) := by
        rw [mul_div_assoc]
        calc (m - lam) * ((q - r) / (b' - m)) ≤ (m - lam) * (|q - r| / (b' - m)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self _)
                (by linarith)) (by linarith)
          _ ≤ (b - a) * (|q - r| / (b' - m)) :=
              mul_le_mul_of_nonneg_right (by linarith [hl.1]) hD2
      nlinarith
  exact (iSup₂_le hbound).trans_lt (EReal.coe_lt_top D)

/-- **The inverse transform of a concave family of psh functions is psh** (WN21 §3, via
Lemma 3.2): let `v_λ`, `λ ∈ [a, b]`, be psh on `W`, concave in `λ`, with `v_λ` locally bounded
for `λ ∈ [a', b']`, `a ≤ a' < b' ≤ b`.  Then `(z, τ) ↦ sup_{λ ∈ [a,b]} (v_λ(z) + λ log |τ|²)` is
psh on `W × ℂ*`. -/
theorem plurisubharmonicOn_inverseLegendre {m : ℕ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    {v : ℝ → ComplexModel m → EReal} {a b a' b' : ℝ} (haa : a ≤ a') (hab' : a' < b')
    (hbb : b' ≤ b) (hpsh : ∀ lam ∈ Icc a b, PlurisubharmonicOn (v lam) W)
    (hconc : ∀ z ∈ W, IsConcaveFamilyAt v (Icc a b) z)
    (hbdd : ∀ lam ∈ Icc a' b', ∀ z ∈ W, ∃ C : ℝ, ∀ᶠ w in 𝓝 z,
      ((-C : ℝ) : EReal) ≤ v lam w ∧ v lam w ≤ (C : EReal)) :
    PlurisubharmonicOn (fun p : ComplexModel m × ℂ => inverseLegendre v a b p.1 p.2)
      (W ×ˢ puncturedPlane) := by
  set Ω : Set (ComplexModel m × ℂ) := W ×ˢ puncturedPlane
  have hΩ : IsOpen Ω := hW.prod isOpen_puncturedPlane
  -- the members
  set V : ℝ → ComplexModel m × ℂ → EReal :=
    fun lam p => v lam p.1 + ((lam * logNormSq p.2 : ℝ) : EReal) with hVdef
  have hVpsh : ∀ lam ∈ Icc a b, PlurisubharmonicOn (V lam) Ω := by
    intro lam hl
    have h1 : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => v lam p.1) Ω := by
      have := (hpsh lam hl).comp_continuousLinearMap
        (ContinuousLinearMap.fst ℂ (ComplexModel m) ℂ)
      exact this.mono fun p hp => hp.1
    exact h1.add (plurisubharmonicOn_mul_logNormSq lam W)
  have hVne : ∀ p ∈ Ω, ∀ lam ∈ Icc a b, V lam p ≠ ⊤ :=
    fun p hp lam hl => (hVpsh lam hl p hp).ne_top
  have hVconc : ∀ p ∈ Ω, IsConcaveFamilyAt V (Icc a b) p := by
    intro p hp
    have := (hconc p.1 hp.1).add_affine (logNormSq p.2)
    intro l₁ hl₁ l₂ hl₂ t ht0 ht1
    exact this l₁ hl₁ l₂ hl₂ t ht0 ht1
  have hlogcont : ContinuousOn (fun p : ComplexModel m × ℂ => logNormSq p.2) Ω := by
    intro p hp
    have hp2 : p.2 ≠ 0 := hp.2
    apply ContinuousAt.continuousWithinAt
    unfold logNormSq
    exact ContinuousAt.log (by fun_prop) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hp2))
  have hVbdd : ∀ lam ∈ Icc a' b', ∀ p ∈ Ω, ∃ C : ℝ, ∀ᶠ q in 𝓝 p,
      ((-C : ℝ) : EReal) ≤ V lam q ∧ V lam q ≤ (C : EReal) := by
    intro lam hl p hp
    obtain ⟨C, hC⟩ := hbdd lam hl p.1 hp.1
    have hcont : ContinuousAt (fun q : ComplexModel m × ℂ => lam * logNormSq q.2) p :=
      (continuousAt_const.mul (hlogcont.continuousAt (hΩ.mem_nhds hp)))
    have hev : ∀ᶠ q in 𝓝 p, |lam * logNormSq q.2 - lam * logNormSq p.2| < 1 := by
      have := Metric.tendsto_nhds.mp hcont 1 one_pos
      filter_upwards [this] with q hq
      simpa [Real.dist_eq] using hq
    refine ⟨C + |lam * logNormSq p.2| + 1, ?_⟩
    filter_upwards [(continuous_fst.tendsto p).eventually hC, hev] with q hq hq'
    have hb1 : -(|lam * logNormSq p.2| + 1) ≤ lam * logNormSq q.2 := by
      have := neg_abs_le (lam * logNormSq p.2); linarith [(abs_lt.mp hq').1]
    have hb2 : lam * logNormSq q.2 ≤ |lam * logNormSq p.2| + 1 := by
      have := le_abs_self (lam * logNormSq p.2); linarith [(abs_lt.mp hq').2]
    simp only [V]
    constructor
    · have := add_le_add hq.1 (EReal.coe_le_coe_iff.mpr hb1)
      rw [← EReal.coe_add] at this
      refine le_trans (le_of_eq ?_) this
      congr 1; ring
    · have := add_le_add hq.2 (EReal.coe_le_coe_iff.mpr hb2)
      rw [← EReal.coe_add] at this
      refine this.trans (le_of_eq ?_)
      congr 1; ring
  -- upper semicontinuity of the supremum
  have husc := upperSemicontinuousOn_iSup_concave hΩ haa hab' hbb hVconc hVne
    (fun lam hl p hp => (hVpsh lam hl p hp).upperSemicontinuousAt) hVbdd
  -- the supremum is `< ⊤`
  set S : ComplexModel m × ℂ → EReal := fun p => ⨆ lam ∈ Icc a b, V lam p
  have hSfun : (fun p : ComplexModel m × ℂ => inverseLegendre v a b p.1 p.2) = S := rfl
  have hSlt : ∀ p ∈ Ω, S p < ⊤ := by
    intro p hp
    have fin : ∀ lam ∈ Icc a' b', ∃ r : ℝ, V lam p = r := by
      intro lam hl
      obtain ⟨C, hC⟩ := hVbdd lam hl p hp
      have h := hC.self_of_nhds
      have hb : V lam p ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h.1
      have ht : V lam p ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h.2
      exact ⟨(V lam p).toReal, (EReal.coe_toReal ht hb).symm⟩
    obtain ⟨p₁, hp₁⟩ := fin a' ⟨le_rfl, hab'.le⟩
    obtain ⟨q₁, hq₁⟩ := fin ((a' + b') / 2) ⟨by linarith, by linarith⟩
    obtain ⟨r₁, hr₁⟩ := fin b' ⟨hab'.le, le_rfl⟩
    exact iSup_Icc_lt_top_of_concave haa hab' hbb (hVconc p hp) (hVne p hp) hp₁ hq₁ hr₁
  -- local uniform upper bounds
  set F : Set (ComplexModel m × ℂ → EReal) := V '' Icc a b
  have hFne : F.Nonempty := ⟨V a, a, ⟨le_rfl, by linarith⟩, rfl⟩
  have hFpsh : ∀ f ∈ F, PlurisubharmonicOn f Ω := by
    rintro f ⟨lam, hl, rfl⟩; exact hVpsh lam hl
  have hsSup : sSup F = S := by
    funext p
    simp only [F, S, sSup_image, iSup_apply]
  have hFbdd : LocallyUniformlyBoundedAbove F Ω := by
    intro p hp
    obtain ⟨C, hSC, -⟩ := EReal.exists_between_coe_real (hSlt p hp)
    refine ⟨{q | S q < C}, mem_nhdsWithin_of_mem_nhds (husc p hp C hSC), C, ?_⟩
    rintro f ⟨lam, hl, rfl⟩ q ⟨hq, -⟩
    exact (le_iSup₂ (f := fun lam _ => V lam q) lam hl).trans (le_of_lt hq)
  have hreg := plurisubharmonicOn_uscRegularization_sSup hΩ hFne hFpsh hFbdd
  rw [hsSup] at hreg
  rw [hSfun]
  intro p hp
  refine (hreg p hp).congr ?_
  filter_upwards [hΩ.mem_nhds hp] with q hq
  exact le_antisymm (uscRegularization_le_of_upperSemicontinuousAt (husc q hq))
    (le_uscRegularization S q)

/-! ### The hypotheses of the Monge–Ampère statement are self-sufficient -/

section MAData

variable {N : ℕ} {Ω : TopologicalSpace.Opens (ComplexModel N)} {u : ComplexModel N → ℂ → EReal} {a b : ℝ}
  {A : Set (ComplexModel N)}

/-- The data's psh hypothesis on `Ω × ℂ*` (product form) gives the one on the model `ℂᴺ⁺¹`. -/
theorem IsLegendreMAData.plurisubharmonicOn_productModelFunction
    (h : IsLegendreMAData Ω u a b A) :
    PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω) :=
  plurisubharmonicOn_comp_stripModelEquiv (Ψ := fun p : ComplexModel N × ℂ => u p.1 p.2) h.psh

/-- Kiselman: under the data, every `û_λ` is psh on `Ω`. -/
theorem IsLegendreMAData.plurisubharmonicOn_partialLegendre (h : IsLegendreMAData Ω u a b A)
    (lam : ℝ) : PlurisubharmonicOn (partialLegendre u lam) Ω :=
  SGPT.Okounkov.TranscendentalWN.plurisubharmonicOn_partialLegendre Ω.isOpen h.psh
    h.circleInvariant lam

/-- **The Monge–Ampère identity in applicable form**: from `PartialLegendreMALocalStatement N`
and the data alone (the plurisubharmonicity proofs are supplied by
`plurisubharmonicOn_productModelFunction` and Kiselman's principle). -/
theorem IsLegendreMAData.mongeAmpere_eq (hMA : PartialLegendreMALocalStatement N)
    (h : IsLegendreMAData Ω u a b A) {E : Set (ComplexModel N)} (hE : MeasurableSet E) :
    MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u)
        h.plurisubharmonicOn_productModelFunction (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
      ((N + 1 : ℕ) : ENNReal) * ∫⁻ lam in Icc a b,
        MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam)
          (h.plurisubharmonicOn_partialLegendre lam) E :=
  hMA Ω u a b A h _ _ E hE

end MAData

end SGPT.Okounkov.TranscendentalWN
