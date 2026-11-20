import SGPT.Trace.OTMarginAssembly
import SGPT.Trace.OTExtGlobalReduction
import SGPT.Okounkov.TranscendentalPoleExtension

/-!
# The existence part of `thm:OT_ext` with a margin, for proper submanifolds

Blueprint `claude-ot3.tex`, node `claude-ot3:margin-existence`.

`otExtMarginExistenceAlong_of_lt`: for a closed connected submanifold `W` of dimension `m < n`,
`OTExtMarginExistenceAlong ωb L T θ hW δ` holds.  Ingredients:

* the normal pole `F` of `W` (`exists_submanifold_pole`, DP04 Lemma 2.1, proved in the
  Okounkov chapter), normalized to `Λ = F - sup F ≤ 0`, and the pole weight
  `φ' = ψ + rΛ/k ∈ PSH(X, θ - δω/2)` for `k ≥ 2rC/δ` (`isThetaPshPotential_poleWeight'`);
* the cover data of lane S54 for `δ/2` and its threshold `k₁`;
* `N > r/(t-1)`, `a = r(1-1/N)`, `b = r + r/(N(t-1))`;
* the local packages (`exists_marginPatch`) and the assembly (`exists_section_of_patches`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2 SGPT.Trace.TwistedL2 SGPT.Trace.OTExt

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The pole weight `φ + ψ/k` of a pole `ψ ∈ PSH(X, Bω)`, `ψ ≤ 0`, whose pole set lies in a closed
set with empty interior, is in `PSH(X, θ - δω/2)` when `2B ≤ kδ` (the point-pole lemma
`isThetaPshPotential_poleWeight` of lane S62, for poles along a submanifold). -/
theorem isThetaPshPotential_poleWeight' (ωb : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} {δ B : ℝ} {φ ψ : X → EReal} {k : ℕ}
    (hk : 0 < k) (hkB : 2 * B ≤ k * δ)
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hψ : ThetaPlurisubharmonic (B • ωb.form).val ψ) {W : Set X} (hWc : IsClosed W)
    (hWi : interior W = ∅) (hψW : ∀ y, ψ y = ⊥ → y ∈ W) :
    IsThetaPshPotential (θ - (δ / 2) • ωb.form).val (poleWeight φ ψ k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
    (c := 1 / (k : ℝ)) (by positivity) hψ
  have h2 := FirstPass.LocalPotentials.thetaPlurisubharmonic_add hφ.1 h1
  have hsemi : ((δ / 2 - B / k) • ωb.form).val.IsSemipositive := by
    refine Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive ?_
    rw [sub_nonneg, div_le_iff₀ hk']
    linarith
  have h3 := Pending.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive h2 hsemi
  have hform : θ - δ • ωb.form + (1 / (k : ℝ)) • (B • ωb.form) +
      (δ / 2 - B / k) • ωb.form = θ - (δ / 2) • ωb.form := by
    rw [smul_smul]
    have : (1 / (k : ℝ)) * B = B / k := by ring
    rw [this]
    module
  rw [hform] at h3
  refine ⟨h3, fun y U hU hyU => ?_⟩
  -- a point of `U` off `W`, then a point where `φ` is finite
  obtain ⟨y₀, hy₀U, hy₀W⟩ : ∃ y₀ ∈ U, y₀ ∉ W := by
    by_contra h
    push Not at h
    have : U ⊆ interior W := interior_maximal (fun z hz => h z hz) hU
    rw [hWi] at this
    exact this hyU
  obtain ⟨y₁, hy₁, hy₁φ⟩ := hφ.2 y₀ (U ∩ Wᶜ) (hU.inter hWc.isOpen_compl) ⟨hy₀U, hy₀W⟩
  refine ⟨y₁, hy₁.1, ?_⟩
  have hψ1 : ψ y₁ ≠ ⊥ := fun h => hy₁.2 (hψW y₁ h)
  have hmul : ((1 / (k : ℝ) : ℝ) : EReal) * ψ y₁ ≠ ⊥ := by
    induction h : ψ y₁ using EReal.rec with
    | bot => exact absurd h hψ1
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
  rw [poleWeight]
  exact fun h => (EReal.add_eq_bot_iff.mp h).elim hy₁φ hmul

/-- The local form of the normalized pole in the flattening coordinates of `SubmanifoldChartedSpace`. -/
theorem localForm_normalized {W : Set X} {m : ℕ} (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {ωb : KahlerBackground n X} {F : X → EReal}
    (hF : SGPT.Okounkov.TranscendentalPole.IsSubmanifoldPole ωb W F) (M : ℝ) (p : W) :
    ∃ U ∈ 𝓝 p.1, ∃ C : ℝ, ∀ y ∈ U, y ∉ W →
      |(F y + ((-M : ℝ) : EReal)).toReal -
        Real.log (normalWeight n m (fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) y))| ≤ C := by
  have hreg := hW p.1 p.2
  set Φ := hreg.2.2.choose with hΦ
  have hflat : SGPT.Okounkov.TranscendentalPole.IsFlatteningOf W Φ m :=
    ⟨hreg.2.2.choose_spec.1, fun hy hyΦ => hreg.2.2.choose_spec.2.2 hy hyΦ⟩
  obtain ⟨U, hU, C, hC⟩ := hF.localForm p.1 p.2 m Φ hflat
  refine ⟨U, hU, C + |M|, fun y hy hyW => ?_⟩
  have hne : F y ≠ ⊥ := fun h => hyW ((hF.eq_bot_iff y).mp h)
  have hnt : F y ≠ ⊤ := hF.ne_top y
  have hnw : SGPT.Okounkov.TranscendentalPole.flatNormalWeight Φ m y =
      normalWeight n m (fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) y) := by
    unfold SGPT.Okounkov.TranscendentalPole.flatNormalWeight normalWeight
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [Complex.normSq_eq_norm_sq]; rfl
    · rfl
  have h1 := hC y hy hyW
  rw [hnw] at h1
  rw [← EReal.coe_toReal hnt hne, ← EReal.coe_add, EReal.toReal_coe]
  calc |(F y).toReal + -M - Real.log (normalWeight n m (fcoord _ y))|
      = |((F y).toReal - Real.log (normalWeight n m (fcoord _ y))) + -M| := by ring_nf
    _ ≤ |(F y).toReal - Real.log (normalWeight n m (fcoord _ y))| + |-M| := abs_add_le _ _
    _ ≤ C + |M| := by rw [abs_neg]; linarith

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **The margin existence part of `thm:OT_ext` for submanifolds of positive codimension.** -/
theorem otExtMarginExistenceAlong_of_lt (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (hmn : m < n) {δ : ℝ} (hδ : 0 < δ) : OTExtMarginExistenceAlong ωb L T θ hW δ := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hWc : IsCompact W := hW.1.isCompact
  obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
  have : Nonempty X := ⟨x₀⟩
  -- the normalized pole
  obtain ⟨F, hF⟩ := SGPT.Okounkov.TranscendentalPole.exists_submanifold_pole_of_isClosedConnectedSubmanifold
    ωb hW hmn
  obtain ⟨CF, hCF0, hFpsh⟩ := hF.exists_thetaPsh
  obtain ⟨MF, hMF⟩ := exists_real_upper_bound_of_upperSemicontinuous
    hF.continuous.upperSemicontinuous hF.ne_top
  set Λ : X → EReal := fun x => F x + ((-MF : ℝ) : EReal) with hΛdef
  have hΛ0 : ∀ x, Λ x ≤ 0 := by
    intro x
    have h := hMF x
    induction hFx : F x using EReal.rec with
    | bot => simp [hΛdef, hFx]
    | top => exact absurd hFx (hF.ne_top x)
    | coe s =>
      simp only [hΛdef, hFx, ← EReal.coe_add]
      rw [hFx] at h
      exact EReal.coe_nonpos.mpr (by have := EReal.coe_le_coe_iff.mp h; linarith)
  have hΛtop : ∀ x, Λ x ≠ ⊤ := fun x h => by
    have := hΛ0 x; rw [h] at this; exact absurd this (by simp)
  have hΛbot : ∀ x, Λ x = ⊥ → x ∈ W := fun x h =>
    (hF.eq_bot_iff x).mp ((EReal.add_eq_bot_iff.mp h).resolve_right (EReal.coe_ne_bot _))
  have hΛc : Continuous Λ := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
      (hF.continuous.continuousAt.prodMk continuousAt_const)
  have hΛm : Measurable Λ := hΛc.measurable
  set r : ℝ := ((n - m : ℕ) : ℝ) with hrdef
  have hr1 : 1 ≤ r := by rw [hrdef]; exact_mod_cast (by omega : 1 ≤ n - m)
  have hr0 : 0 < r := by linarith
  have hpole : ThetaPlurisubharmonic ((r * CF) • ωb.form).val (fun x => (r : EReal) * Λ x) := by
    have := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
      (γ := CF • ωb.form) hr0 (hFpsh.add_const (-MF)).1
    rwa [smul_smul] at this
  -- cover data and the threshold
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ (half_pos hδ)
  obtain ⟨k₁, hk₁⟩ := D.exists_goodPower (half_pos hδ)
  refine ⟨max (max k₁ 1) ⌈2 * (r * CF) / δ⌉₊, fun k hk' ψ hψ _ _ _ t ht s hs => ?_⟩
  have hk1 : 1 ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk')
  have hk0 : 0 < k := hk1
  have hkg : D.GoodPower k := hk₁ k ((le_max_left _ _).trans ((le_max_left _ _).trans hk'))
  have hkB : 2 * (r * CF) ≤ k * δ := by
    have h1 : 2 * (r * CF) / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hk')
    rwa [div_le_iff₀ hδ] at h1
  have hφ' := isThetaPshPotential_poleWeight' ωb hk0 hkB hψ hpole hW.1
    (SGPT.Okounkov.TranscendentalPole.interior_eq_empty_of_lt hW hmn) (fun y hy => by
      have : Λ y = ⊥ := by
        induction h : Λ y using EReal.rec with
        | bot => rfl
        | coe s => rw [h, ← EReal.coe_mul] at hy; exact absurd hy (EReal.coe_ne_bot _)
        | top => exact absurd h (hΛtop y)
      exact hΛbot y this)
  -- `ψ`
  have hψq := hψ.quasiPshPotential
  have hψmq : ManifoldQuasiPlurisubharmonic (n := n) ψ := hψ.1.quasiPlurisubharmonic
  have hψm : Measurable ψ := hψmq.upperSemicontinuous.measurable
  obtain ⟨Mψ, hMψ⟩ := exists_real_upper_bound_of_upperSemicontinuous hψmq.upperSemicontinuous
    hψmq.ne_top
  have hmult : ∀ x, multiplierWeight (k : ℝ) (poleWeight ψ (fun y => (r : EReal) * Λ y) k x) =
      multiplierWeight (k : ℝ) (ψ x) * multiplierWeight r (Λ x) := fun x =>
    multiplierWeight_poleWeight hk0 hr0 (hψmq.ne_top x) (hΛ0 x)
  -- the exponents
  have ht0 : 0 < t - 1 := by linarith
  set N : ℕ := ⌊r / (t - 1)⌋₊ + 1 with hNdef
  have hN : N ≠ 0 := Nat.succ_ne_zero _
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNr : r < N * (t - 1) := by
    have h := Nat.lt_floor_add_one (r / (t - 1))
    rw [div_lt_iff₀ ht0] at h
    simpa [hNdef] using h
  set a : ℝ := r * (1 - 1 / (N : ℝ)) with hadef
  set b : ℝ := r + r / (N * (t - 1)) with hbdef
  have ha : 0 ≤ a := by
    have : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNR]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    exact mul_nonneg hr0.le (by linarith)
  have hb : 1 ≤ b := by
    have : 0 ≤ r / (N * (t - 1)) := by positivity
    linarith
  have hbr : b - 1 < r := by
    have : r / (N * (t - 1)) < 1 := by rw [div_lt_one (by positivity)]; exact hNr
    linarith
  have hreq : a / t + b * (1 - 1 / t) = r := by
    rw [hadef, hbdef]; field_simp; ring
  -- the local packages
  have hP : ∀ p : W, Nonempty (MarginPatch (n := n) (twistedPower L T k).Fiber μ W Λ ψ
      ((k : ℝ) * t) a r s p.1) := by
    intro p
    obtain ⟨B', K', B, K, S, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
      exists_marginPatch (twistedPower L T k).Fiber hμ hk hmn hW.2.2 hΛm hΛtop hΛbot
        (localForm_normalized hW.2.2 hF MF) hψmq (by positivity : (0 : ℝ) < k * t) hN hs p
    exact ⟨⟨B', K', B, K, S, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩⟩
  obtain ⟨σ, hσmem, hσW⟩ := exists_section_of_patches hμ hL hT D hk0 hkg hφ' hWc
    (fun p => Classical.choice (hP p)) hmult hψq hψm hΛm hΛc hMψ hΛ0 hΛbot ht rfl ha hb hbr hreq
  exact ⟨σ, hσmem, hσW⟩

/-- **The margin existence part of `thm:OT_ext` for submanifolds of full dimension** (an open and
closed `W`): the section `s` extended by zero. -/
theorem otExtMarginExistenceAlong_of_eq (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (θ : ClosedRealOneOneForm n X)
    {W : Set X} (hW : IsClosedConnectedSubmanifold n W n) {δ : ℝ} :
    OTExtMarginExistenceAlong ωb L T θ hW δ := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel n) W := chartedSpace hk hW.2.2
  have : IsComplexManifold n W := isComplexManifold_chartedSpace hk hW.2.2
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hWc : IsCompact W := hW.1.isCompact
  obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
  have : Nonempty X := ⟨x₀⟩
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hreg := hW.2.2 x hx
    filter_upwards [(FlatData.ofRegularAtDim hreg).isOpen_ambSource.mem_nhds
      (FlatData.mem_ambSource_ofRegularAtDim hreg)] with y hy
    exact (mem_iff_fcoord (FlatData.ofRegularAtDim hreg) hy).mpr fun i hi => absurd i.2 (by omega)
  refine ⟨1, fun k hk' ψ hψ _ _ _ t ht s hs => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk'
  have hψq := hψ.quasiPshPotential
  have hψmq : ManifoldQuasiPlurisubharmonic (n := n) ψ := hψ.1.quasiPlurisubharmonic
  have hψm : Measurable ψ := hψmq.upperSemicontinuous.measurable
  obtain ⟨Mψ, hMψ⟩ := exists_real_upper_bound_of_upperSemicontinuous hψmq.upperSemicontinuous
    hψmq.ne_top
  have hc : (0 : ℝ) < k * t := by positivity
  choose B' K B S hB'o hBo hKc hmem hB'K hKB hsm hagree hgain using
    fun p : W => exists_gainPatch_intrinsic (twistedPower L T k).Fiber hμ hk hW.2.2 hψmq hc hs p
  obtain ⟨t₀, ht₀⟩ := hWc.elim_finite_subcover (fun p : W => B' p) hB'o
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  classical
  set σf : (x : X) → (twistedPower L T k).Fiber x := fun x => if hx : x ∈ W then s ⟨x, hx⟩ else 0 with hσf
  have hσsm : ContMDiff 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (σf x)) := by
    intro x
    by_cases hx : x ∈ W
    · set p : W := ⟨x, hx⟩
      have hxB : x ∈ B p := hKB p (hB'K p (hmem p))
      refine (hsm p x hxB).congr_of_eventuallyEq ?_
      filter_upwards [(hBo p).mem_nhds hxB, hWo.mem_nhds hx] with y hyB hyW
      simp only [hσf, dif_pos hyW]
      rw [hagree p ⟨y, hyW⟩ hyB]
    · refine ((Bundle.contMDiff_zeroSection ℂ (twistedPower L T k).Fiber (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)) x).congr_of_eventuallyEq ?_
      filter_upwards [hW.1.isOpen_compl.mem_nhds hx] with y hy
      simp only [hσf, dif_neg (show y ∉ W from hy)]
      rfl
  set σ : twistedSections L T k := ⟨σf, hσsm⟩ with hσ
  refine ⟨σ, (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) (twistedPower L T k).Fiber k hψq σ hμ).mpr ?_,
    fun y => by show σf y.1 = s y; simp only [hσf, dif_pos y.2]⟩
  -- the integral
  have hcont : ∀ p : W, ContinuousOn (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) (B p) := fun p =>
    ENNReal.continuous_ofReal.comp_continuousOn (((ContinuousFiberNorm.continuous.comp_continuousOn
      (fun x hx => (hsm p x hx).continuousAt.continuousWithinAt))).pow 2)
  have hwψ : Measurable fun x => multiplierWeight (k : ℝ) (ψ x) :=
    (multiplierWeight_antitone hk0.le).measurable.comp hψm
  set g : X → ℝ≥0∞ := fun x => ∑ p ∈ t₀, (K p).indicator (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) x *
    multiplierWeight (k : ℝ) (ψ x) with hg
  have hgm_p : ∀ p : W, Measurable fun x => (K p).indicator (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) x *
      multiplierWeight (k : ℝ) (ψ x) := fun p =>
    (measurable_indicator_closed_of_continuousOn (hBo p) (hKc p).isClosed (hKB p) (hcont p)).mul hwψ
  have hpt : ∀ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber ψ k σ x ≤ g x := by
    intro x
    unfold originalSectionDensity
    by_cases hx : x ∈ W
    · obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp (ht₀ hx)
      have hσx : σ x = S p x := by
        show σf x = S p x
        simp only [hσf, dif_pos hx]
        exact (hagree p ⟨x, hx⟩ (hKB p (hB'K p hxp))).symm
      rw [hσx, hg]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun p => (K p).indicator
        (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x))
        (fun _ _ => zero_le) hpt)
      rw [indicator_of_mem (hB'K p hxp)]
    · have : σ x = 0 := by show σf x = 0; simp only [hσf, dif_neg hx]
      rw [this, norm_zero]; simp
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [hg]
  beta_reduce
  rw [lintegral_finsetSum' (f := fun p x => (K p).indicator (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) x *
    multiplierWeight (k : ℝ) (ψ x)) _ fun p _ => (hgm_p p).aemeasurable]
  refine ENNReal.sum_lt_top.mpr fun p _ => lt_top_iff_ne_top.mpr ?_
  have hind : (fun x => (K p).indicator (fun x => ENNReal.ofReal (‖S p x‖ ^ 2)) x *
      multiplierWeight (k : ℝ) (ψ x)) = (K p).indicator
        (fun x => ENNReal.ofReal (‖S p x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x)) := by
    funext x
    by_cases hx : x ∈ K p
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  rw [hind, lintegral_indicator (hKc p).isClosed.measurableSet]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top
    (r := Real.exp (k * (t - 1) * Mψ))) (hgain p)) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  calc ENNReal.ofReal (‖S p x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x)
      ≤ ENNReal.ofReal (‖S p x‖ ^ 2) * (ENNReal.ofReal (Real.exp (k * (t - 1) * Mψ)) *
          multiplierWeight (k * t) (ψ x)) :=
        mul_le_mul' le_rfl (multiplierWeight_le_mul_of_le hk0.le ht.le (hMψ x))
    _ = _ := by ring

/-- **`OTExtMarginExistenceStatement` holds**: the margin existence part of `thm:OT_ext`, the only
remaining input of `thm:OT_ext_global` (`otExtGlobalStatement_of_marginExistence`). -/
theorem otExtMarginExistenceStatement : OTExtMarginExistenceStatement n X := by
  intro ωb L T hL hT θ hθ W m hW δ hδ
  rcases (le_of_isClosedConnectedSubmanifold hW).lt_or_eq with hmn | rfl
  · exact otExtMarginExistenceAlong_of_lt ωb L T hL hT θ hθ hW hmn hδ
  · exact otExtMarginExistenceAlong_of_eq ωb L T θ hW

end SGPT.Trace.OTMargin
