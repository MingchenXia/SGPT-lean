import SGPT.PSH.GlobalL2CoverData

/-!
# The gluing system of `L^k ⊗ T` with the weight `e^{-kφ}`

Blueprint `claude-global-l2:local-weights`.  For cover data `D` (`claude-global-l2:cover`), a power
`k` large enough (`CoverData.GoodPower`) and `φ ∈ PSH(X, θ - δω)`, `CoverData.toGluingSystem`
is the `GluingSystem` of the line bundle `L^k ⊗ T` (Bergman's `twistedPower L T k`, frames the
products of the preferred frames of `L` and `T`) for the weight `e^{-kφ}`, with the local
weights `k(φ ∘ z_a⁻¹ + ρ'_a) + [k(ρ_L - ρ'_a) + ρ_T - λ|z - z_a|²] + λ|z - z_a|²`; its
contraction factor is at most `1/4` (`CoverData.kappa_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Trivializations of a line bundle -/

section Triv

variable {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

theorem trivialization_coef_frame (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] {x : X} (hx : x ∈ e.baseSet) :
    e.continuousLinearMapAt ℂ x (e.symm x 1) = 1 := by
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hx]
  exact congrArg Prod.snd (e.apply_mk_symm hx (1 : ℂ))

theorem trivialization_eq_coef_smul_frame
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    {x : X} (hx : x ∈ e.baseSet) (u : V x) :
    u = e.continuousLinearMapAt ℂ x u • e.symm x 1 := by
  have h1 := e.symmL_continuousLinearMapAt (R := ℂ) hx u
  have h2 : e.symmL ℂ x (e.continuousLinearMapAt ℂ x u) =
      e.continuousLinearMapAt ℂ x u • e.symmL ℂ x 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h2, Trivialization.symmL_apply e hx] at h1
  exact h1.symm

theorem norm_eq_coef_mul_norm_frame
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    {x : X} (hx : x ∈ e.baseSet) (u : V x) :
    ‖u‖ = ‖e.continuousLinearMapAt ℂ x u‖ * ‖e.symm x 1‖ := by
  conv_lhs => rw [trivialization_eq_coef_smul_frame e hx u]
  rw [norm_smul]

theorem coef_frame_eq_coordChange (e e' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {x : X}
    (hx : x ∈ e.baseSet ∩ e'.baseSet) :
    e'.continuousLinearMapAt ℂ x (e.symm x 1) = e.coordChangeL ℂ e' x 1 := by
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e' hx.2,
    Trivialization.coordChangeL_apply e e' hx]

variable [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- Frame transitions are holomorphic in the coordinates of an atlas chart. -/
theorem differentiableOn_coef_frame
    (e e' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (c : ComplexChart n X)
    {S : Set (ComplexModel n)} (hS : S ⊆ c.val.target)
    (hSe : ∀ z ∈ S, c.val.symm z ∈ e.baseSet ∩ e'.baseSet) :
    DifferentiableOn ℂ (fun z => e'.continuousLinearMapAt ℂ (c.val.symm z) (e.symm (c.val.symm z) 1))
      S := by
  have hcc : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (fun x : X => (e.coordChangeL ℂ e' x : ℂ →L[ℂ] ℂ)) (e.baseSet ∩ e'.baseSet) :=
    contMDiffOn_coordChangeL e e'
  have hsymm : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c.val.symm S :=
    (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.property)).mono hS
  have hcomp : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (fun z => (e.coordChangeL ℂ e' (c.val.symm z) : ℂ →L[ℂ] ℂ)) S :=
    hcc.comp hsymm fun z hz => hSe z hz
  have happ : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun z => (e.coordChangeL ℂ e' (c.val.symm z) : ℂ →L[ℂ] ℂ) 1) S :=
    hcomp.clm_apply contMDiffOn_const
  have hd : DifferentiableOn ℂ (fun z => (e.coordChangeL ℂ e' (c.val.symm z) : ℂ →L[ℂ] ℂ) 1) S :=
    (contMDiffOn_iff_contDiffOn.mp happ).differentiableOn (by simp)
  refine hd.congr fun z hz => ?_
  exact coef_frame_eq_coordChange e e' (hSe z hz)

end Triv

variable [MeasurableSpace X] [BorelSpace X]

namespace CoverData

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- The chart of the cover at index `a`. -/
def chartA (a : Fin D.m) : ComplexChart n X := complexChartAt (n := n) (D.pt a)

/-- The frame `e_L^k ⊗ e_T` of `L^k ⊗ T` at index `a`. -/
def frameE (k : ℕ) (a : Fin D.m) : AtlasFrame (twistedPower L T k) :=
  twistedPowerAtlasFrame (prefFrame L (D.pt a)) (prefFrame T (D.pt a)) k

/-- The curvature bound used in the local weights. -/
def lam : ℝ := 8 * (D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2 + 1

theorem lam_pos : 0 < D.lam := by unfold lam; positivity

/-- `k` is large enough for the local weights to carry the curvature bound `λ`. -/
def GoodPower (k : ℕ) : Prop := 1 ≤ k ∧ ∀ a, D.lam + D.CT a ≤ (k : ℝ) * δ * D.cω a

theorem exists_goodPower (hδ : 0 < δ) : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → D.GoodPower k := by
  refine ⟨1 + ∑ a, ⌈(D.lam + D.CT a) / (δ * D.cω a)⌉₊, fun k hk => ⟨by omega, fun a => ?_⟩⟩
  have hpos : 0 < δ * D.cω a := mul_pos hδ (D.cω_pos a)
  have h1 : ⌈(D.lam + D.CT a) / (δ * D.cω a)⌉₊ ≤ k := by
    have : ⌈(D.lam + D.CT a) / (δ * D.cω a)⌉₊ ≤ ∑ a, ⌈(D.lam + D.CT a) / (δ * D.cω a)⌉₊ :=
      Finset.single_le_sum (f := fun a => ⌈(D.lam + D.CT a) / (δ * D.cω a)⌉₊)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  have h2 : (D.lam + D.CT a) / (δ * D.cω a) ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  rw [div_le_iff₀ hpos] at h2
  linarith

theorem symm_mem_baseSets (a : Fin D.m) {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :
    (D.chartA a).val.symm z ∈ (prefFrame L (D.pt a)).val.baseSet ∧
      (D.chartA a).val.symm z ∈ (prefFrame T (D.pt a)).val.baseSet :=
  (D.hball a hz).2

theorem ball_subset_two (a : Fin D.m) :
    ball (ctr (n := n) (D.pt a)) (D.R a) ⊆ ball (ctr (n := n) (D.pt a)) (2 * D.R a) :=
  ball_subset_ball (by linarith [D.R_pos a])

theorem mem_baseSets_of_mem {a : Fin D.m} {x : X} (hx : x ∈ (D.chartA a).val.source)
    (hxz : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    x ∈ (prefFrame L (D.pt a)).val.baseSet ∧ x ∈ (prefFrame T (D.pt a)).val.baseSet := by
  have h := D.symm_mem_baseSets a (D.ball_subset_two a hxz)
  rwa [(D.chartA a).val.left_inv hx] at h

theorem mem_frameE_baseSet {k : ℕ} {a : Fin D.m} {x : X} (hx : x ∈ (D.chartA a).val.source)
    (hxz : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    x ∈ (D.frameE k a).val.baseSet :=
  twistedPowerAtlasFrame_mem _ _ (D.mem_baseSets_of_mem hx hxz).1
    (D.mem_baseSets_of_mem hx hxz).2 k

/-- The smooth part of the local weight. -/
def gWeight (k : ℕ) (a : Fin D.m) (z : ComplexModel n) : ℝ :=
  (k : ℝ) * (frameWeight (prefFrame L (D.pt a)) (D.chartA a) z - D.ρ' a z) +
    frameWeight (prefFrame T (D.pt a)) (D.chartA a) z - D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2

/-- The psh part `Ψ_a = k (ρ'_a + φ ∘ z_a⁻¹) + g_a` of the local weight. -/
def psiW (k : ℕ) (φ : X → EReal) (a : Fin D.m) (z : ComplexModel n) : EReal :=
  ((k : ℝ) : EReal) * ((D.ρ' a z : EReal) + φ ((D.chartA a).val.symm z)) + (D.gWeight k a z : EReal)

theorem contDiffOn_frameWeight_L (hL : IsSourceSmoothHermitianMetric L) (a : Fin D.m) :
    ContDiffOn ℝ ∞ (frameWeight (prefFrame L (D.pt a)) (D.chartA a))
      (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
  (contDiffOn_frameWeight hL _ _).mono fun _z hz => ⟨(D.hball a hz).1, (D.hball a hz).2.1⟩

theorem contDiffOn_frameWeight_T (hT : IsSourceSmoothHermitianMetric T) (a : Fin D.m) :
    ContDiffOn ℝ ∞ (frameWeight (prefFrame T (D.pt a)) (D.chartA a))
      (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
  (contDiffOn_frameWeight hT _ _).mono fun _z hz => ⟨(D.hball a hz).1, (D.hball a hz).2.2⟩

theorem contDiffOn_gWeight (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (k : ℕ) (a : Fin D.m) :
    ContDiffOn ℝ ∞ (D.gWeight k a) (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) := by
  have hn : ContDiff ℝ ∞ fun z : ComplexModel n => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2 :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  exact ((contDiffOn_const.mul ((D.contDiffOn_frameWeight_L hL a).sub (D.pot a).2.2.1)).add
    (D.contDiffOn_frameWeight_T hT a)).sub hn.contDiffOn

theorem leviForm_gWeight_nonneg (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) {k : ℕ} (hk : D.GoodPower k) (a : Fin D.m)
    {w : ComplexModel n} (hw : w ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) (v : ComplexModel n) :
    0 ≤ leviForm (D.gWeight k a) w v := by
  have hw2 := D.ball_subset_two a hw
  have hO : ball (ctr (n := n) (D.pt a)) (2 * D.R a) ∈ 𝓝 w := isOpen_ball.mem_nhds hw2
  have c2 : ∀ {u : ComplexModel n → ℝ}, ContDiffOn ℝ ∞ u (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) →
      ContDiffAt ℝ 2 u w := fun hu =>
    ((hu w hw2).contDiffAt hO).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hLρ : ContDiffOn ℝ ∞ (fun z => frameWeight (prefFrame L (D.pt a)) (D.chartA a) z - D.ρ' a z)
      (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
    (D.contDiffOn_frameWeight_L hL a).sub (D.pot a).2.2.1
  have hn2 : ContDiffAt ℝ 2 (fun z : ComplexModel n => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2) w :=
    ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hLeviN : leviForm (fun z : ComplexModel n => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2) w v =
      D.lam * ‖v‖ ^ 2 := by
    have e : (fun z : ComplexModel n => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2) =
        fun y => (D.lam • fun u : ComplexModel n => ‖u‖ ^ 2) (y - ctr (n := n) (D.pt a)) := by
      funext y; simp [smul_eq_mul]
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul
      (contDiff_norm_sq ℝ).contDiffAt, leviForm_norm_sq]
  have hsplit : D.gWeight k a = ((k : ℝ) • fun z => frameWeight (prefFrame L (D.pt a)) (D.chartA a) z -
      D.ρ' a z) + frameWeight (prefFrame T (D.pt a)) (D.chartA a) +
      -(fun z : ComplexModel n => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2) := by
    funext z; simp only [gWeight, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  set F : ComplexModel n → ℝ := fun z => frameWeight (prefFrame L (D.pt a)) (D.chartA a) z -
    D.ρ' a z with hFdef
  set G : ComplexModel n → ℝ := frameWeight (prefFrame T (D.pt a)) (D.chartA a) with hGdef
  set N : ComplexModel n → ℝ := fun z => D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2 with hNdef
  have hF : ContDiffAt ℝ 2 F w := c2 hLρ
  have hG : ContDiffAt ℝ 2 G w := c2 (D.contDiffOn_frameWeight_T hT a)
  have hkF : ContDiffAt ℝ 2 ((k : ℝ) • F) w := by
    have := hF.const_smul (k : ℝ); exact this
  have hkFG : ContDiffAt ℝ 2 ((k : ℝ) • F + G) w := hkF.add hG
  have hNn : ContDiffAt ℝ 2 (-N) w := hn2.neg
  rw [hsplit, leviForm_add hkFG hNn, leviForm_neg, leviForm_add hkF hG, leviForm_smul hF, hLeviN]
  have h1 : δ * D.cω a * ‖v‖ ^ 2 ≤ leviForm F w v := D.levi_L a w hw v
  have h2 : -(D.CT a * ‖v‖ ^ 2) ≤ leviForm G w v := D.levi_T a w hw v
  have h3 := hk.2 a
  have hv : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h1 hk0, mul_le_mul_of_nonneg_right h3 hv]

theorem psiW_psh (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ) (a : Fin D.m) :
    PlurisubharmonicOn (D.psiW k φ a) (ball (ctr (n := n) (D.pt a)) (D.R a)) := by
  have h1 : PlurisubharmonicOn (fun z => (D.ρ' a z : EReal) + φ ((D.chartA a).val.symm z))
      (ball (ctr (n := n) (D.pt a)) (D.R a)) :=
    (plurisubharmonicOn_add_localPotential hφ (D.chartA a) (D.pot a)).mono (D.ball_subset_two a)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk.1
  have h2 := h1.const_mul hk
  have h3 : PlurisubharmonicOn (fun z => (D.gWeight k a z : EReal))
      (ball (ctr (n := n) (D.pt a)) (D.R a)) :=
    plurisubharmonicOn_of_contDiffOn_levi_nonneg isOpen_ball
      ((D.contDiffOn_gWeight hL hT k a).mono (D.ball_subset_two a))
      fun w hw v => D.leviForm_gWeight_nonneg hL hT ‹D.GoodPower k› a hw v
  exact h2.add h3

theorem ereal_weight_identity {K : ℝ} (hK : 0 < K) {e : EReal} (he : e ≠ ⊤) (ρ wL wT Q : ℝ) :
    ((K : ℝ) : EReal) * ((ρ : EReal) + e) + ((K * (wL - ρ) + wT - Q : ℝ) : EReal) + (Q : EReal) =
      ((K : ℝ) : EReal) * e + ((K * wL + wT : ℝ) : EReal) := by
  induction e using EReal.rec with
  | bot =>
      rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hK, EReal.bot_add, EReal.bot_add,
        EReal.bot_add]
  | coe s =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul,
        ← EReal.coe_add]
      congr 1
      ring
  | top => exact absurd rfl he

theorem multiplierWeight_one_mul (K : ℝ) (e : EReal) :
    multiplierWeight 1 ((K : EReal) * e) = multiplierWeight K e := by
  simp only [multiplierWeight, EReal.coe_one, one_mul]

/-- **The density identity** `|u|² e^{-kφ} = |coef u|² e^{-Ψ_a - λ|z - z_a|²}`. -/
theorem density_eq {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal} (hφ : ∀ x, φ x ≠ ⊤)
    (a : Fin D.m) (x : X) (u : (twistedPower L T k).Fiber x) (hx : x ∈ (D.chartA a).val.source)
    (hxz : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    ENNReal.ofReal (‖u‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) =
      ENNReal.ofReal (‖(D.frameE k a).val.continuousLinearMapAt ℂ x u‖ ^ 2) *
        ballWeight (D.psiW k φ a) D.lam (ctr (n := n) (D.pt a)) ((D.chartA a).val x) := by
  have hbs := D.mem_baseSets_of_mem hx hxz
  have hE := D.mem_frameE_baseSet (k := k) hx hxz
  have hsz : (D.chartA a).val.symm ((D.chartA a).val x) = x := (D.chartA a).val.left_inv hx
  set NL := ‖(prefFrame L (D.pt a)).val.symm x 1‖ with hNL
  set NT := ‖(prefFrame T (D.pt a)).val.symm x 1‖ with hNT
  have hNL0 : 0 < NL := frameNorm_pos L.Fiber (prefFrame L (D.pt a)).val hbs.1
  have hNT0 : 0 < NT := frameNorm_pos T.Fiber (prefFrame T (D.pt a)).val hbs.2
  have hnorm : ‖u‖ = ‖(D.frameE k a).val.continuousLinearMapAt ℂ x u‖ * (NL ^ k * NT) := by
    rw [norm_eq_coef_mul_norm_frame (D.frameE k a).val hE u]
    congr 1
    exact twistedPower_frame_norm _ _ hbs.1 hbs.2 k
  have hwL : frameWeight (prefFrame L (D.pt a)) (D.chartA a) ((D.chartA a).val x) =
      -Real.log (NL ^ 2) := by rw [frameWeight, hsz]
  have hwT : frameWeight (prefFrame T (D.pt a)) (D.chartA a) ((D.chartA a).val x) =
      -Real.log (NT ^ 2) := by rw [frameWeight, hsz]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hid := ereal_weight_identity hk0 (hφ x) (D.ρ' a ((D.chartA a).val x))
    (frameWeight (prefFrame L (D.pt a)) (D.chartA a) ((D.chartA a).val x))
    (frameWeight (prefFrame T (D.pt a)) (D.chartA a) ((D.chartA a).val x))
    (D.lam * ‖(D.chartA a).val x - ctr (n := n) (D.pt a)‖ ^ 2)
  have hne : ((k : ℝ) : EReal) * φ x ≠ ⊤ := by
    induction h : φ x using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos hk0]; exact bot_ne_top
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    | top => exact absurd h (hφ x)
  have hexp : Real.exp (-((k : ℝ) * frameWeight (prefFrame L (D.pt a)) (D.chartA a)
      ((D.chartA a).val x) + frameWeight (prefFrame T (D.pt a)) (D.chartA a) ((D.chartA a).val x))) =
      (NL ^ 2) ^ k * NT ^ 2 := by
    rw [hwL, hwT, show -((k : ℝ) * -Real.log (NL ^ 2) + -Real.log (NT ^ 2)) =
      (k : ℝ) * Real.log (NL ^ 2) + Real.log (NT ^ 2) by ring, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
  have hball : ballWeight (D.psiW k φ a) D.lam (ctr (n := n) (D.pt a)) ((D.chartA a).val x) =
      multiplierWeight (k : ℝ) (φ x) * ENNReal.ofReal ((NL ^ 2) ^ k * NT ^ 2) := by
    rw [ballWeight, psiW, gWeight, hsz, hid, multiplierWeight_one_add_coe_real hne,
      multiplierWeight_one_mul, hexp]
  rw [hball, hnorm, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have : (NL ^ k * NT) ^ 2 = (NL ^ 2) ^ k * NT ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  rw [this]
  ring

theorem closedBall_subset_target (a : Fin D.m) :
    closedBall (ctr (n := n) (D.pt a)) (D.R a) ⊆ (D.chartA a).val.target :=
  (closedBall_subset_ball (by linarith [D.R_pos a])).trans fun z hz => (D.hball a hz).1

theorem ball_subset_target (a : Fin D.m) :
    ball (ctr (n := n) (D.pt a)) (D.R a) ⊆ (D.chartA a).val.target :=
  ball_subset_closedBall.trans (D.closedBall_subset_target a)

/-- **The gluing system of `L^k ⊗ T` with the weight `e^{-kφ}`** (`claude-global-l2:local-weights`). -/
def toGluingSystem (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ) :
    GluingSystem n X μ (twistedPower L T k).Fiber (fun x => multiplierWeight (k : ℝ) (φ x))
      (Fin D.m) where
  chart a := (D.chartA a).val
  center a := ctr (n := n) (D.pt a)
  r' a := D.R a / 4
  r a := D.R a / 2
  R := D.R
  r'_pos a := by linarith [D.R_pos a]
  r'_lt_r a := by linarith [D.R_pos a]
  r_lt_R a := by linarith [D.R_pos a]
  closedBall_subset := D.closedBall_subset_target
  cover x := by
    have hne : ∑ a, D.χ a x ≠ 0 := by rw [D.sum_χ x]; exact one_ne_zero
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨a, D.tsupport_χ a (subset_tsupport _ ha)⟩
  coef a x := (D.frameE k a).val.continuousLinearMapAt ℂ x
  frame a x := (D.frameE k a).val.symm x 1
  coef_frame a x hx hxz := trivialization_coef_frame _ (D.mem_frameE_baseSet hx hxz)
  eq_coef_smul_frame a x u hx hxz := trivialization_eq_coef_smul_frame _ (D.mem_frameE_baseSet hx hxz) u
  transition_holo i l := by
    refine differentiableOn_coef_frame (D.frameE k i).val (D.frameE k l).val (D.chartA l)
      (fun z hz => D.ball_subset_target l hz.1) fun z hz => ⟨D.mem_frameE_baseSet hz.2.1 hz.2.2, ?_⟩
    have hs : (D.chartA l).val.symm z ∈ (D.chartA l).val.source :=
      (D.chartA l).val.map_target (D.ball_subset_target l hz.1)
    exact D.mem_frameE_baseSet hs (by rw [(D.chartA l).val.right_inv (D.ball_subset_target l hz.1)]; exact hz.1)
  chart_holo i l := by
    refine (RegularPatchNeighborhood.differentiableOn_chartTransition (D.chartA l) (D.chartA i)).mono
      fun z hz => ?_
    exact ⟨D.ball_subset_target l hz.1, hz.2.1⟩
  dens a z := ENNReal.ofReal (D.dens a z)
  A := ENNReal.ofReal D.Aμ
  A_ne_top := ENNReal.ofReal_ne_top
  dens_le a z hz := ENNReal.ofReal_le_ofReal (D.dens_le a z hz)
  one_le_A_mul_dens a z hz := by
    rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (D.one_le a z hz)
  map_measure a f hf :=
    setLIntegral_chart_ball (D.chartA a) (D.dens_cont a) (D.dens_map a) isOpen_ball
      (D.ball_subset_target a) hf
  Ψ := D.psiW k φ
  Ψ_psh := D.psiW_psh hL hT hk hφ
  lam := D.lam
  lam_pos := D.lam_pos
  density_eq a x u hx hxz := D.density_eq hk (fun x => hφ.1.quasiPlurisubharmonic.ne_top x) a x u hx hxz
  χ := D.χ
  χ_smooth i l := D.χ_smooth i (D.chartA l)
  χ_nonneg := D.χ_nonneg
  sum_χ := D.sum_χ
  tsupport_χ a := (D.tsupport_χ a).trans fun x hx =>
    ⟨hx.1, ball_subset_ball (by linarith [D.R_pos a]) hx.2⟩
  M := D.M
  dbar_χ_le := D.dbar_χ_le

/-- **The contraction factor is at most `1/4`.** -/
theorem kappa_le (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ) :
    (D.toGluingSystem hL hT hk hφ).kappa ≤ ENNReal.ofReal (1 / 4) := by
  simp only [GluingSystem.kappa, toGluingSystem, Fintype.card_fin]
  have hlam := D.lam_pos
  have hA := D.Aμ_pos
  have hM : (D.m : ℝ) * D.M ≤ (D.m : ℝ) * |D.M| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)
  calc (D.m : ℝ≥0∞) * (ENNReal.ofReal ((D.m : ℝ) * D.M) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam))))
      ≤ ENNReal.ofReal (D.m : ℝ) * (ENNReal.ofReal ((D.m : ℝ) * |D.M|) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam)))) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
    _ = ENNReal.ofReal ((D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam))))) := by
        rw [← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hA.le,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ) * |D.M|),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ))]
    _ ≤ ENNReal.ofReal (1 / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hx : 0 ≤ (D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2 := by positivity
        have hle : 8 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) ≤ D.lam := by
          rw [lam]; linarith
        have : (D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam)))) =
            2 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) / D.lam := by
          field_simp
        rw [this, div_le_iff₀ hlam]
        linarith

end CoverData

end SGPT.PSH.GlobalL2
