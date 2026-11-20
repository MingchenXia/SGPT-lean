import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityFullQea
import SGPT.Foundations.Analysis.Pending.ActualResolvedSquaredBergmanDensity
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.AdmissiblePrincipalizationAnalyticModification

set_option autoImplicit false

/-! # Gentle analytic singularities of the SAME original squared sum

The complete source-facing proof is written before this SOURCE. No sequence
is replaced by its ideal type. Both exponential and resolved residual retain
all common-zero values, and a germ equation is extended to all nearby stalks.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
universe u
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.QuasiEquisingularApproximation FirstPass.BlowupSequences
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  ActualGlobalSquaredBergmanDensity ActualOriginalSquaredDensityThetaPsh
  ActualOriginalSquaredDensityFullQea ActualResolvedSquaredBergmanDensity
  RelativePrincipalizationSpan InvertibleIdealQuotient HironakaAdmissibleSequence
  AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Definition 1.6.5, with finite actual exponential and a genuine local
all-stalk equation on each whole adapted coordinate neighborhood. -/
def HasGentleAnalyticSingularitiesOfType (v : X → EReal) (c : ℚ)
    (𝔞 : GermIdeal n X) : Prop :=
  IsGlobalQuasiPshPotential (n := n) v ∧ HasAnalyticSingularitiesOfType (n := n) v c 𝔞 ∧
    (∀ x, EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * v x) ≠ ⊤) ∧
    ChartSmooth (n := n) (fun x =>
      (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * v x)).toReal) ∧
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (f : Y → X) (D : EffectiveDivisor n Y),
      IsAnalyticModification (n := n) f ∧ Nonempty (KahlerBackground n Y) ∧
      ∀ y : Y, ∃ (V : Set Y), IsOpen V ∧ y ∈ V ∧ ∃ g : Y → ℂ,
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g V ∧
        (∀ W : Set Y, IsOpen W → W ⊆ V → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
        (∀ t ∈ V, ∀ a : Y → ℂ, D.ideal.mem t a ↔ IsInSpanAt (n := n) (· = g) t a) ∧
        ∃ Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y),
          Φ.source ⊆ (complexChartAt (n := n) y).val.target ∧
          Φ.toFun ((complexChartAt (n := n) y).val y) = 0 ∧
          ∃ (h : ComplexModel n → ℝ) (r : ℝ), 0 < r ∧ ball 0 r ⊆ Φ.target ∧
            ContDiffOn ℝ ∞ h (ball 0 r) ∧
            ∀ z ∈ ball 0 r,
              (complexChartAt (n := n) y).val.symm (Φ.invFun z) ∈ V ∧
              v (f ((complexChartAt (n := n) y).val.symm (Φ.invFun z))) =
                ((c : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal
                  (‖g ((complexChartAt (n := n) y).val.symm (Φ.invFun z))‖ ^ 2)) +
                  (h z : EReal)

private theorem density_nonneg (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (m : ℕ) (x : X) :
    0 ≤ density F ρ u m x := by
  apply Finset.sum_nonneg
  intro j _
  exact GlobalTubeFunction.bumpExtend_nonneg (fun y => mul_self_nonneg (F.cover.χ j y))
    (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) x

private theorem exponential_originalWeight (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) {m : ℕ} (hm : 0 < m)
    (a : ℝ) (x : X) :
    EReal.exp ((m : ℝ) * (originalWeight F ρ u m x + (a : EReal))) =
      ENNReal.ofReal (Real.exp ((m : ℝ) * a) * density F ρ u m x) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [originalWeight, EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr hmR.le) (EReal.coe_ne_top _),
    ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hmR.ne', EReal.coe_one, one_mul,
    ← EReal.coe_mul, EReal.exp_add, ENNReal.exp_log, EReal.exp_coe,
    ← ENNReal.ofReal_mul (density_nonneg F ρ u m x)]
  congr 1
  ring

/-- The same germ equation becomes the actual divisor equation at ALL stalks
on one open neighborhood; both span relations are internally transported. -/
theorem exists_local_equation_of_germ_generator {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (D : EffectiveDivisor n Y) {y : Y} {g : Y → ℂ} (hg : HolomorphicAt n g y)
    (hgen : ∀ a : Y → ℂ, D.ideal.mem y a ↔ IsInSpanAt (n := n) (· = g) y a) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g V ∧
      (∀ W : Set Y, IsOpen W → W ⊆ V → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      ∀ t ∈ V, ∀ a : Y → ℂ, D.ideal.mem t a ↔ IsInSpanAt (n := n) (· = g) t a := by
  obtain ⟨U, hU, hyU, h, hh, hnon, hstalk⟩ := D.isInvertible y
  have hhy : HolomorphicAt n h y := holomorphicAt_of_mdifferentiableOn hU hh hyU
  have hgD := (hgen g).mpr (isInSpanAt_self rfl hg)
  have hhD := (hstalk y hyU h).mpr (isInSpanAt_self rfl hhy)
  obtain ⟨-, a, ha, heqa⟩ := isInSpanAt_eq_iff.mp ((hstalk y hyU g).mp hgD)
  obtain ⟨-, b, hb, heqb⟩ := isInSpanAt_eq_iff.mp ((hgen h).mp hhD)
  have he : {t | t ∈ U ∧ MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g t ∧
      HolomorphicAt n a t ∧ HolomorphicAt n b t ∧
      g t = a t * h t ∧ h t = b t * g t} ∈ 𝓝 y := by
    filter_upwards [hU.mem_nhds hyU, hg, ha.eventually, hb.eventually, heqa, heqb]
      with t ht hgt hat hbt heat hebt
    exact ⟨ht, hgt, hat, hbt, heat, hebt⟩
  obtain ⟨V, hVU, hV, hyV⟩ := _root_.mem_nhds_iff.mp he
  refine ⟨V, hV, hyV, fun t ht => (hVU ht).2.1.mdifferentiableWithinAt, ?_, ?_⟩
  · intro W hW hWV hWne
    obtain ⟨t, ht, hht⟩ := hnon W hW (fun t ht => (hVU (hWV ht)).1) hWne
    refine ⟨t, ht, fun hgt => ?_⟩
    exact hht (by rw [(hVU (hWV ht)).2.2.2.2.2, hgt, mul_zero])
  · intro t ht q
    have hgT : HolomorphicAt n g t := by
      filter_upwards [hV.mem_nhds ht] with z hz
      exact (hVU hz).2.1
    have hhT := holomorphicAt_of_mdifferentiableOn hU hh (hVU ht).1
    have haT := (hVU ht).2.2.1
    have hbT := (hVU ht).2.2.2.1
    have heaT : g =ᶠ[𝓝 t] fun z => a z * h z := by
      filter_upwards [hV.mem_nhds ht] with z hz
      exact (hVU hz).2.2.2.2.1
    have hebT : h =ᶠ[𝓝 t] fun z => b z * g z := by
      filter_upwards [hV.mem_nhds ht] with z hz
      exact (hVU hz).2.2.2.2.2
    rw [hstalk t (hVU ht).1]
    constructor
    · intro hq
      exact IsInSpanAt.trans (fun s hs => by
        rw [hs]; exact isInSpanAt_eq_iff.mpr ⟨hhT, b, hbT, hebT⟩) hq
    · intro hq
      exact IsInSpanAt.trans (fun s hs => by
        rw [hs]; exact isInSpanAt_eq_iff.mpr ⟨hgT, a, haT, heaT⟩) hq

private theorem adaptedInverse_tendsto {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) :
    Tendsto (fun z => (complexChartAt (n := n) y).val.symm (Φ.invFun z)) (𝓝 0) (𝓝 y) := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hcont := ((complexChartAt (n := n) y).val.continuousAt_symm
    (hsrc (Φ.mapsTo_invFun ht))).comp
    ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds ht)).continuousAt)
  have heq : (complexChartAt (n := n) y).val.symm (Φ.invFun 0) = y := by
    rw [← h0, Φ.left_inv _ Φ.center_mem_source]
    exact (complexChartAt (n := n) y).val.left_inv (mem_complexChartAt_source y)
  simpa only [Function.comp_def, heq] using hcont.tendsto

private theorem resolved_log_identity (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) {m : ℕ} (hm : 0 < m)
    (a : ℝ) (x : X) (q : ℂ) (H : ℝ) (hH : 0 < H)
    (hS : density F ρ u m x = ‖q‖ ^ 2 * H) :
    originalWeight F ρ u m x + (a : EReal) =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖q‖ ^ 2)) +
        (((m : ℝ)⁻¹ * Real.log H + a : ℝ) : EReal) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [originalWeight, hS, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos hH,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (inv_nonneg.mpr hmR.le))
      (EReal.coe_ne_top _), ← EReal.coe_mul, add_assoc, ← EReal.coe_add]

/-- One actual resolved cover and its prescribed potentials give gentle
singularities at every dyadic level of the SAME full QEA. -/
theorem exists_fixed_cover_full_gentle_qea {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X] [CompactSpace X] (omega : KahlerBackground (m + 1) X) :
    ∃ (F : FixedChartCover (m + 1) X) (C E : ℝ), 0 < C ∧ 0 ≤ E ∧
      ∀ (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal),
        IsThetaPshPotential θ.val u → ∃ ρ : F.t → ComplexModel (m + 1) → ℝ,
          (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
            (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
          IsQuasiEquisingularApproximation omega θ u
            (fun ℓ => C * ((2 : ℝ) ^ ℓ)⁻¹)
            (fun ℓ x => originalWeight F ρ u (2 ^ ℓ) x +
              ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) ∧
          ∀ ℓ : ℕ, HasGentleAnalyticSingularitiesOfType (n := m + 1)
            (fun x => originalWeight F ρ u (2 ^ ℓ) x +
              ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) (((2 ^ ℓ : ℕ) : ℚ)⁻¹)
            (multiplierIdeal (n := m + 1) ((2 ^ ℓ : ℕ) : ℝ) u) := by
  obtain ⟨F, hF⟩ := exists_fixed_cover_resolved_smooth_positive_density (m := m) (X := X)
  obtain ⟨C, E, hC, hE, hqea⟩ := exists_uniform_original_density_full_qea F omega
  refine ⟨F, C, E, hC, hE, fun θ u hu => ?_⟩
  obtain ⟨ρ, hρ, hres⟩ := hF θ u hu
  obtain ⟨htype, happrox⟩ := hqea θ ρ hρ u hu
  refine ⟨ρ, hρ, happrox, fun ℓ => ?_⟩
  have hk : 0 < 2 ^ ℓ := by positivity
  let k : ℕ := 2 ^ ℓ
  let a : ℝ := E * ((2 : ℝ) ^ ℓ)⁻¹
  have hcoeff : (((((2 ^ ℓ : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)) = (k : ℝ)⁻¹ := by
    dsimp only [k]; push_cast; rfl
  have hinv : (((((((2 ^ ℓ : ℕ) : ℚ)⁻¹ : ℚ) : ℝ))⁻¹ : ℝ)) = (k : ℝ) := by
    rw [hcoeff, inv_inv]
  obtain ⟨hSmooth, Y, tY, chY, mY, f, D, Ediv, hseq, _, _, _, hsupp, _, hfactor⟩ :=
    hres k hk
  let := tY
  let := chY
  let := mY
  have hmod := AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    (htype ℓ).2.1 hseq D hsupp
  obtain ⟨_, hK⟩ := DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence
    ⟨omega⟩ hseq.isBlowupSequence
  refine ⟨⟨(happrox.term ℓ).1.quasiPlurisubharmonic, (happrox.term ℓ).2⟩,
    htype ℓ, ?_, ?_, Y, tY, chY, mY, f, D, hmod, hK, ?_⟩
  · intro x
    rw [hinv, exponential_originalWeight F ρ u hk a x]
    exact ENNReal.ofReal_ne_top
  · intro e
    have heq : (fun z => (EReal.exp
        (((((((2 ^ ℓ : ℕ) : ℚ)⁻¹ : ℚ) : ℝ))⁻¹ : ℝ) *
          (originalWeight F ρ u k (e.val.symm z) + (a : EReal)))).toReal) =
        fun z => Real.exp ((k : ℝ) * a) * density F ρ u k (e.val.symm z) := by
      funext z
      rw [hinv, exponential_originalWeight F ρ u hk a, ENNReal.toReal_ofReal
        (mul_nonneg (Real.exp_pos _).le (density_nonneg F ρ u k _))]
    change ContDiffOn ℝ ∞ _ e.val.target
    rw [heq]
    exact contDiffOn_const.mul (hSmooth e)
  · intro y
    obtain ⟨Φ, hsrc, h0, g, hg, hgen, H, r, hr, hH, hlogH, hall⟩ := hfactor y
    obtain ⟨V, hV, hyV, hgV, hnon, hgenV⟩ := exists_local_equation_of_germ_generator D hg hgen
    have hT := adaptedInverse_tendsto y Φ hsrc h0
    have ht : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
      rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
    have he : ∀ᶠ z in 𝓝 0, z ∈ Φ.target ∧
        (complexChartAt (n := m + 1) y).val.symm (Φ.invFun z) ∈ V := by
      filter_upwards [Φ.isOpen_target.mem_nhds ht, hT.eventually (hV.mem_nhds hyV)]
        with z hzt hzV
      exact ⟨hzt, hzV⟩
    obtain ⟨b, hb, hcond⟩ := Metric.eventually_nhds_iff_ball.mp he
    let r' := min r b
    have hr' : 0 < r' := lt_min hr hb
    have hrr : ball (0 : ComplexModel (m + 1)) r' ⊆ ball 0 r :=
      ball_subset_ball (min_le_left _ _)
    have hrb : ball (0 : ComplexModel (m + 1)) r' ⊆ ball 0 b :=
      ball_subset_ball (min_le_right _ _)
    refine ⟨V, hV, hyV, g, hgV, hnon, hgenV, Φ, hsrc, h0,
      fun z => (k : ℝ)⁻¹ * Real.log (H z) + a, r', hr',
      fun z hz => (hcond z (hrb hz)).1,
      contDiffOn_const.mul (hlogH.mono hrr) |>.add contDiffOn_const, ?_⟩
    intro z hz
    refine ⟨(hcond z (hrb hz)).2, ?_⟩
    rw [hcoeff]
    exact resolved_log_identity F ρ u hk a _ _ _ (hall z (hrr hz)).1
      (hall z (hrr hz)).2

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
