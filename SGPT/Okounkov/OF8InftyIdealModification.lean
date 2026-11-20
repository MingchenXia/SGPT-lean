import SGPT.Projective.OkoNov16AttributedGlobalLogGermReuse
import SGPT.Projective.OkounkovOriginalLogCartierPowers
import SGPT.PSH.LogResolution
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.HadamardBridge
import SGPT.Foundations.Analysis.Pending.HironakaEffectiveDivisorSum
import SGPT.Foundations.Analysis.Pending.HironakaSNCComponentCoefficients
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-!
# `𝓘_∞` along modifications and along logarithmic `ℚ`-divisors

Source: chapter *The theory of Okounkov bodies*, proof of `prop:GammaepsSp` and remark
`rmk:DeltaanaW0`: *if `π : Y → X` is a modification such that `π^*φ` has log singularities
along an effective `ℚ`-divisor `D`, then by the definition of `𝓘_∞` the section spaces
`H⁰(X, L^k ⊗ 𝓘_∞(kφ))` are naturally identified with `H⁰(Y, π^*L^k ⊗ 𝒪_Y(-⌈kD⌉))`.*

This file proves the two local facts behind this identification.

* `inftyIdeal_mem_comp`, `inftyIdeal_mem_of_forall_comp_mem`: `𝓘_∞` (germs `g` with
  `|g|² e^{-w}` locally bounded, `SGPT.PSH.inftyIdeal`) pulls back along every holomorphic map,
  and descends along every proper surjective map: `g ∈ 𝓘_∞(w)_p` as soon as `g` is holomorphic
  at `p` and `π^*g ∈ 𝓘_∞(π^*w)_z` at every point `z` of the (compact) fibre `π⁻¹(p)`.
* `nsmul_ideal_mem_iff_inftyIdeal`: if `u` has log singularities along the effective
  `ℚ`-divisor `D` (book Definition 1.6.2, `SGPT.PSH.NativeHasLogSingularitiesAlong`) and
  `D = (1/d) F` with `F` an effective (Cartier) divisor, then for every `k ∈ ℕ`
  `𝒪(-kF) = 𝓘_∞(k d u)`, i.e. the ideal of `kF` is the `𝓘_∞`-ideal of the potential `k d u`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF8

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH
open scoped Topology Manifold ContDiff

/-! ### Pulling back and pushing down `𝓘_∞` -/

section Transfer

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

omit [TopologicalSpace X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z] in
/-- The pointwise density `|g|² e^{-w}` commutes with pullbacks. -/
theorem multiplierDensity_comp (w : X → EReal) (g : X → ℂ) (π : Z → X) (y : Z) :
    multiplierDensity (fun y => w (π y)) 1 (fun y => g (π y)) y =
      multiplierDensity w 1 g (π y) := rfl

/-- **`𝓘_∞` pulls back**: if `g ∈ 𝓘_∞(w)` at `π z` and `π` is holomorphic, then
`π^*g ∈ 𝓘_∞(π^*w)` at `z`. -/
theorem inftyIdeal_mem_comp {π : Z → X}
    (hπ : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) π z)
    {w : X → EReal} {g : X → ℂ} {z : Z} (h : (inftyIdeal (n := n) w).mem (π z) g) :
    (inftyIdeal (n := m) (fun y => w (π y))).mem z (fun y => g (π y)) := by
  obtain ⟨hg, K, hK, hev⟩ := h
  exact ⟨HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπ) hg, K, hK,
    (hπ z).continuousAt.tendsto.eventually hev⟩

/-- **`𝓘_∞` descends along proper surjective maps**: if `g` is holomorphic at `p` and
`π^*g ∈ 𝓘_∞(π^*w)` at every point of the fibre `π⁻¹(p)`, then `g ∈ 𝓘_∞(w)` at `p`
(the fibre is compact, so finitely many local bounds cover a neighbourhood of it, and this
neighbourhood contains `π⁻¹(V)` for a neighbourhood `V` of `p` since `π` is closed). -/
theorem inftyIdeal_mem_of_forall_comp_mem {π : Z → X} (hprop : IsProperMap π)
    (hsurj : Function.Surjective π) {w : X → EReal} {g : X → ℂ} {p : X}
    (hg : HolomorphicAt n g p)
    (h : ∀ z, π z = p → (inftyIdeal (n := m) (fun y => w (π y))).mem z (fun y => g (π y))) :
    (inftyIdeal (n := n) w).mem p g := by
  classical
  have hK : IsCompact (π ⁻¹' {p}) := hprop.isCompact_preimage isCompact_singleton
  have h' : ∀ z, π z = p → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ y in 𝓝 z, multiplierDensity w 1 g (π y) ≤ ENNReal.ofReal C :=
    fun z hz => (h z hz).2
  choose! C hC hev using h'
  obtain ⟨t, ht, hcover⟩ := hK.elim_nhds_subcover
    (fun z => interior {y | multiplierDensity w 1 g (π y) ≤ ENNReal.ofReal (C z)})
    (fun z hz => interior_mem_nhds.mpr (hev z hz))
  set W : Set Z := ⋃ z ∈ t, interior {y | multiplierDensity w 1 g (π y) ≤ ENNReal.ofReal (C z)}
    with hWdef
  have hWo : IsOpen W := isOpen_biUnion fun z _ => isOpen_interior
  have hCt : ∀ z ∈ t, 0 < C z := fun z hz => hC z (ht z hz)
  set B : ℝ := (∑ z ∈ t, C z) + 1 with hBdef
  have hsum : 0 ≤ ∑ z ∈ t, C z := Finset.sum_nonneg fun z hz => (hCt z hz).le
  have hB : 0 < B := by rw [hBdef]; linarith
  refine ⟨hg, B, hB, ?_⟩
  have hVo : IsOpen (π '' Wᶜ)ᶜ := (hprop.isClosedMap _ hWo.isClosed_compl).isOpen_compl
  have hpV : p ∈ (π '' Wᶜ)ᶜ := by
    rintro ⟨y, hyW, hyp⟩
    exact hyW (hcover (show y ∈ π ⁻¹' {p} from hyp))
  filter_upwards [hVo.mem_nhds hpV] with x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have hyW : y ∈ W := by
    by_contra hy
    exact hx ⟨y, hy, rfl⟩
  rw [hWdef] at hyW
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp hyW
  have hle : y ∈ {y | multiplierDensity w 1 g (π y) ≤ ENNReal.ofReal (C z)} :=
    interior_subset hyz
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have hz := Finset.single_le_sum (fun i hi => (hCt i hi).le) hzt
  rw [hBdef]
  linarith

end Transfer

/-! ### The ideal of `kF` as an `𝓘_∞`-ideal -/

section Cartier

/-- The ideal of `k F` in terms of a local generator `h` of the ideal of `F`:
`f ∈ 𝒪(-kF)_z` iff `f` is holomorphic and `f = a h^k` near `z` with `a` holomorphic. -/
theorem nsmul_ideal_mem_iff_of_generator {N : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel N) Z] [IsComplexManifold N Z] (F : EffectiveDivisor N Z)
    {z : Z} {h : Z → ℂ} (hh : HolomorphicAt N h z)
    (hgen : ∀ b, F.ideal.mem z b ↔ IsInSpanAt (n := N) (· = h) z b) (k : ℕ) (f : Z → ℂ) :
    (k • F).ideal.mem z f ↔ HolomorphicAt N f z ∧
      ∃ a, HolomorphicAt N a z ∧ f =ᶠ[𝓝 z] fun y => a y * h y ^ k := by
  rw [HironakaEffectiveDivisorSum.ideal_nsmul,
    HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator hh hgen, isInSpanAt_eq_iff]

/-- `d · ((1/d) L + b) = L + d b` in `EReal`, for `L ≠ +∞`. -/
theorem natCast_mul_inv_mul_add (d : ℕ) (hd : 0 < d) {L : EReal} (hL : L ≠ ⊤) (b : ℝ) :
    (d : EReal) * ((((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * L + (b : EReal)) =
      L + (((d : ℝ) * b : ℝ) : EReal) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcR : (0 : ℝ) < ((1 / (d : ℚ) : ℚ) : ℝ) := by
    have : (0 : ℚ) < 1 / (d : ℚ) := by positivity
    exact_mod_cast this
  change ((d : ℝ) : EReal) * _ = _
  induction L using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hcR, EReal.bot_add, EReal.coe_mul_bot_of_pos hdR, EReal.bot_add]
  | top => exact absurd rfl hL
  | coe t =>
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    push_cast
    field_simp

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- **The ideal of `kF` is `𝓘_∞(k d u)`.** If `u` has log singularities along the effective
`ℚ`-divisor `D` (book Definition 1.6.2) and `D = (1/d) F` for an effective divisor `F`, then
`𝒪(-kF) = 𝓘_∞(k d u)` at every point, for every `k ∈ ℕ`. -/
theorem nsmul_ideal_mem_iff_inftyIdeal {D : EffectiveGeometricQDivisor (m + 1) Z}
    {u : Z → EReal} (hu : NativeHasLogSingularitiesAlong D u) (F : EffectiveDivisor (m + 1) Z)
    {d : ℕ} (hd : 0 < d)
    (hDF : D = cartierGeometricQDivisor F (1 / (d : ℚ)) (by positivity)) (k : ℕ) (z : Z)
    (f : Z → ℂ) :
    (k • F).ideal.mem z f ↔
      (inftyIdeal (n := m + 1) (fun y => (k : EReal) * ((d : EReal) * u y))).mem z f := by
  obtain ⟨U, hU, hzU, h, hhol, hdense, hgen⟩ := F.isInvertible z
  have hhz : HolomorphicAt (m + 1) h z :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hhol hzU
  have hcoeff : ∀ Q, D.coefficient Q = (cartierGeometricPrimeCoefficient F Q : ℚ) / (d : ℚ) := by
    intro Q
    rw [hDF, cartierGeometricQDivisor_coefficient]
    ring
  obtain ⟨b, hb, hlog⟩ :=
    OkoNov16.AttributedGeometricLogReuse.exists_log_germ_of_global_cartier_coefficients
      hu F d hd hcoeff z h hhz (hgen z hzU)
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb' : BoundedRealGermAt (fun y => (d : ℝ) * b y) z := by
    obtain ⟨C, hC, hbound⟩ := hb
    refine ⟨(d : ℝ) * C, mul_nonneg hdR hC, ?_⟩
    filter_upwards [hbound] with y hy
    rw [abs_mul, abs_of_nonneg hdR]
    exact mul_le_mul_of_nonneg_left hy hdR
  have heq : (fun y => (d : EReal) * u y) =ᶠ[𝓝 z]
      fun y => logNormSq (h y) + (((d : ℝ) * b y : ℝ) : EReal) := by
    filter_upwards [hlog] with y hy
    rw [hy]
    exact natCast_mul_inv_mul_add d hd (logNormSq_ne_top _) (b y)
  have hI := OriginalLogCartier.mem_inftyIdeal_nat_log_iff_holomorphic_power_quotient
    hU hzU hhz hdense hb' heq k f
  rw [nsmul_ideal_mem_iff_of_generator F hhz (hgen z hzU)]
  constructor
  · rintro ⟨-, a, ha, hfa⟩
    exact hI.mpr ⟨a, ha, hfa⟩
  · intro hf
    exact ⟨hf.1, hI.mp hf⟩

end Cartier

end SGPT.Okounkov.OF8
