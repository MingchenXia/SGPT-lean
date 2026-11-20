import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Actual max approximations with coincidence near the common poles

Lu, Comparison of Monge–Ampère capacities, Lemma 4.1 Step 1.2:
`max u ((1 + ε) * v)` agrees with `u` on a deep sublevel and converges
to `v`. These are genuine potentials with controlled curvature and
uniformly bounded signed differences. Fixed-measure convergence is
proved here; varying-measure convergence remains a separate input.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing

open FirstPass FirstPass.PositiveClasses RelativeEnergyIntegrability

noncomputable section

/-- Lu's actual max approximation. -/
def poleCoalescingApprox {X : Type*} (ε : ℝ) (u v : X → EReal) : X → EReal :=
  fun x => max (u x) (((1 + ε : ℝ) : EReal) * v x)

private theorem scale_le_self_of_nonpos {v : EReal} (hv : v ≤ 0)
    {ε : ℝ} (hε : 0 ≤ ε) : ((1 + ε : ℝ) : EReal) * v ≤ v := by
  induction v using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (by linarith : 0 < 1 + ε)]
  | top => simp at hv
  | coe r =>
    rw [← EReal.coe_mul]
    apply EReal.coe_le_coe_iff.mpr
    have hr : r ≤ 0 := by simpa using hv
    nlinarith

/-- The approximation stays in the actual order interval. -/
theorem poleCoalescingApprox_bounds {X : Type*} {u v : X → EReal} {B ε : ℝ}
    (hε : 0 ≤ ε) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) (x : X) :
    u x ≤ poleCoalescingApprox ε u v x ∧
      poleCoalescingApprox ε u v x ≤ v x ∧
        poleCoalescingApprox ε u v x ≤ u x + (B : EReal) := by
  have hle : poleCoalescingApprox ε u v x ≤ v x :=
    max_le (huv x) (scale_le_self_of_nonpos (hv x) hε)
  exact ⟨le_max_left _ _, hle, hle.trans (hgap x)⟩

/-- Both additive comparisons follow from the interval bound. -/
theorem sameSingularityType_poleCoalescingApprox {X : Type*} {u v : X → EReal}
    {B ε : ℝ} (hε : 0 ≤ ε) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) :
    SameSingularityTypeOn (poleCoalescingApprox ε u v) u univ :=
  ⟨⟨B, fun x _ => (poleCoalescingApprox_bounds hε huv hv hgap x).2.2⟩,
    MoreSingularOn.of_le fun x _ =>
      (poleCoalescingApprox_bounds hε huv hv hgap x).1⟩

/-- Coincidence on the explicit deep sublevel, including poles. -/
theorem poleCoalescingApprox_eq_of_deep_sublevel {X : Type*} {u v : X → EReal}
    {B ε : ℝ} (hε : 0 < ε) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) {x : X}
    (hx : u x ≤ ((-(B + B / ε) : ℝ) : EReal)) :
    poleCoalescingApprox ε u v x = u x := by
  have huvx := huv x
  have hgapx := hgap x
  have hvx := hv x
  induction hux : u x using EReal.rec with
  | bot =>
    have hvb : v x = ⊥ := by simpa [hux] using hgapx
    simp only [poleCoalescingApprox, hux, hvb, max_self,
      EReal.coe_mul_bot_of_pos (by linarith : 0 < 1 + ε)]
  | top =>
    have hc := top_le_iff.mp (show (⊤ : EReal) ≤ ((-(B + B / ε) : ℝ) : EReal) by
      rwa [hux] at hx)
    exact False.elim (EReal.coe_ne_top _ hc)
  | coe a =>
    have hvt : v x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hvx
    have hvb : v x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (by simpa [hux] using huvx)
    have hvc := EReal.coe_toReal hvt hvb
    have ha : a ≤ -(B + B / ε) := EReal.coe_le_coe_iff.mp (by rwa [hux] at hx)
    have hb : (v x).toReal ≤ a + B := by
      rw [← hvc, hux, ← EReal.coe_add] at hgapx
      exact EReal.coe_le_coe_iff.mp hgapx
    have hdiv : ε * (B / ε) = B := by field_simp
    have hmul : (1 + ε) * (v x).toReal ≤ a := by
      nlinarith [mul_le_mul_of_nonneg_left ha hε.le,
        mul_le_mul_of_nonneg_left hb hε.le]
    change max (u x) (((1 + ε : ℝ) : EReal) * v x) = (a : EReal)
    rw [hux]
    apply max_eq_left
    rw [← hvc, ← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr hmul

/-- Increasing the positive parameter decreases the approximation. -/
theorem poleCoalescingApprox_antitone {X : Type*} {u v : X → EReal}
    (hv : v ≤ 0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hεη : ε ≤ η) :
    poleCoalescingApprox η u v ≤ poleCoalescingApprox ε u v := by
  intro x
  apply max_le_max_left
  have hvx := hv x
  induction hvdef : v x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (by linarith : 0 < 1 + ε),
      EReal.coe_mul_bot_of_pos (by linarith : 0 < 1 + η)]
  | top => simp [hvdef] at hvx
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    apply EReal.coe_le_coe_iff.mpr
    have hr : r ≤ 0 := by simpa [hvdef] using hvx
    nlinarith

/-- Positive parameters tending to zero give pointwise limits, also at poles. -/
theorem tendsto_poleCoalescingApprox {X ι : Type*} {u v : X → EReal}
    {ε : ι → ℝ} {l : Filter ι} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε l (𝓝 0)) (huv : u ≤ v) (hv : v ≤ 0) (x : X) :
    Tendsto (fun j => poleCoalescingApprox (ε j) u v x) l (𝓝 (v x)) := by
  have hvx := hv x
  induction hvdef : v x using EReal.rec with
  | bot =>
    have hub : u x = ⊥ := by simpa [hvdef] using huv x
    have heq : (fun j => poleCoalescingApprox (ε j) u v x) = fun _ => (⊥ : EReal) := by
      funext j
      simp only [poleCoalescingApprox, hub, hvdef, max_self,
        EReal.coe_mul_bot_of_pos (by linarith [hε j] : 0 < 1 + ε j)]
    rw [heq]
    exact tendsto_const_nhds
  | top => simp [hvdef] at hvx
  | coe r =>
    have hr : Tendsto (fun j => (1 + ε j) * r) l (𝓝 r) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hlim).mul (tendsto_const_nhds (x := r))
    have hc := (continuous_coe_real_ereal.tendsto r).comp hr
    have hm := (tendsto_const_nhds (x := u x)).max hc
    have heq : (fun j => poleCoalescingApprox (ε j) u v x) =
        fun j => max (u x) (((1 + ε j) * r : ℝ) : EReal) := by
      funext j
      simp only [poleCoalescingApprox, hvdef, ← EReal.coe_mul]
    rw [heq]
    simpa only [Function.comp_def, max_eq_right (by simpa [hvdef] using huv x)] using hm

/-- The corrected signed differences have the uniform bound `B`. -/
theorem abs_canonicalDiff_poleCoalescingApprox_le {X : Type*} {u v : X → EReal}
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) (x : X) :
    |canonicalERealDiffToReal (u x) (poleCoalescingApprox ε u v x)| ≤ B := by
  obtain ⟨hlo, hhi, hbd⟩ := poleCoalescingApprox_bounds hε huv hv hgap x
  have htype := (sameSingularityType_poleCoalescingApprox hε huv hv hgap).symm
  have hpt : poleCoalescingApprox ε u v x ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hhi.trans (hv x))
  have hut : u x ≠ ⊤ := ne_top_of_le_ne_top hpt hlo
  by_cases hub : u x = ⊥
  · have hpb : poleCoalescingApprox ε u v x = ⊥ :=
      (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp hub
    simpa [hub, hpb, canonicalERealDiffToReal, poleModifiedERealDiffToReal] using hB
  · have hpb : poleCoalescingApprox ε u v x ≠ ⊥ := ne_bot_of_le_ne_bot hub hlo
    rw [canonicalDiff_eq_sub_toReal hut hpt
      (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))]
    have hreal := EReal.toReal_le_toReal hlo hub hpt
    have hb : (poleCoalescingApprox ε u v x).toReal ≤ (u x).toReal + B := by
      rw [← EReal.coe_toReal hpt hpb, ← EReal.coe_toReal hut hub,
        ← EReal.coe_add] at hbd
      exact EReal.coe_le_coe_iff.mp hbd
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Corrected differences converge everywhere, including common poles. -/
theorem tendsto_canonicalDiff_poleCoalescingApprox {X ι : Type*} {u v : X → EReal}
    {B : ℝ} {ε : ι → ℝ} {l : Filter ι} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε l (𝓝 0)) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) (x : X) :
    Tendsto (fun j => canonicalERealDiffToReal (u x) (poleCoalescingApprox (ε j) u v x))
      l (𝓝 (canonicalERealDiffToReal (u x) (v x))) := by
  have htype : SameSingularityTypeOn u v univ :=
    ⟨MoreSingularOn.of_le fun y _ => huv y, ⟨B, fun y _ => hgap y⟩⟩
  have hvt : v x ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hv x)
  have hut : u x ≠ ⊤ := ne_top_of_le_ne_top hvt (huv x)
  by_cases hub : u x = ⊥
  · have hvb : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp hub
    have hpb : ∀ j, poleCoalescingApprox (ε j) u v x = ⊥ := fun j => by
      simp only [poleCoalescingApprox, hub, hvb, max_self,
        EReal.coe_mul_bot_of_pos (by linarith [hε j] : 0 < 1 + ε j)]
    simp_rw [hub, hvb, hpb]
    exact tendsto_const_nhds
  · have hvb : v x ≠ ⊥ := ne_bot_of_le_ne_bot hub (huv x)
    have hpt : ∀ j, poleCoalescingApprox (ε j) u v x ≠ ⊤ := fun j =>
      ne_top_of_le_ne_top hvt (poleCoalescingApprox_bounds (hε j).le huv hv hgap x).2.1
    have hcommon : ∀ j, u x = ⊥ ↔ poleCoalescingApprox (ε j) u v x = ⊥ := fun j =>
      sameSingularityTypeOn_eq_bot_iff
        (sameSingularityType_poleCoalescingApprox (hε j).le huv hv hgap).symm (mem_univ x)
    simp_rw [canonicalDiff_eq_sub_toReal hut hvt
      (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)),
      canonicalDiff_eq_sub_toReal hut (hpt _) (hcommon _)]
    exact tendsto_const_nhds.sub
      ((EReal.tendsto_toReal hvt hvb).comp (tendsto_poleCoalescingApprox hε hlim huv hv x))

/-- Dominated convergence for actual signed integrals under a fixed finite measure. -/
theorem tendsto_integral_canonicalDiff_poleCoalescingApprox
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u v : X → EReal} (hum : Measurable u) (hvm : Measurable v)
    {B : ℝ} (hB : 0 ≤ B) {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (u x)
      (poleCoalescingApprox (ε j) u v x) ∂μ) atTop
      (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro j
    exact (measurable_canonicalERealDiffToReal.comp
      (hum.prodMk (hum.max (measurable_const.mul hvm)))).aestronglyMeasurable
  · exact integrable_const B
  · intro j
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_canonicalDiff_poleCoalescingApprox_le hB (hε j).le huv hv hgap x
  · exact Eventually.of_forall
      (tendsto_canonicalDiff_poleCoalescingApprox hε hlim huv hv hgap)

/-- An explicit positive parameter schedule retaining a fixed strict curvature margin. -/
def strictKahlerParameter (lam : ℝ) (k : ℕ) : ℝ :=
  ((1 - lam) / (2 * lam)) / ((k : ℝ) + 1)

/-- The schedule decreases to zero and all levels fit below `(1+lam)/2`. -/
theorem strictKahlerParameter_spec {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) :
    (∀ k, 0 < strictKahlerParameter lam k) ∧
      Antitone (strictKahlerParameter lam) ∧
      Tendsto (strictKahlerParameter lam) atTop (𝓝 0) ∧
      ∀ k, (1 + strictKahlerParameter lam k) * lam ≤ (1 + lam) / 2 := by
  let A : ℝ := (1 - lam) / (2 * lam)
  have hA : 0 < A := by dsimp [A]; positivity
  have hden : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hAd : A * (2 * lam) = 1 - lam := div_mul_cancel₀ _ (by positivity)
  refine ⟨fun k => div_pos hA (hden k), ?_, ?_, ?_⟩
  · intro i j hij
    exact div_le_div_of_nonneg_left hA.le (hden i)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  · change Tendsto (fun k : ℕ => A / ((k : ℝ) + 1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := A)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro k
    have hk : strictKahlerParameter lam k ≤ A := by
      apply (div_le_iff₀ (hden k)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hmul := mul_le_mul_of_nonneg_right hk hlam.le
    nlinarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Increasing a Kähler coefficient preserves genuine potentials. -/
theorem isThetaPshPotential_smul_kahler_mono (omega : KahlerBackground n M)
    {a b : ℝ} (hab : a ≤ b) {u : M → EReal}
    (hu : IsThetaPshPotential (a • omega.form).val u) :
    IsThetaPshPotential (b • omega.form).val u := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu
    (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hab))
  have heq : a • omega.form + (b - a) • omega.form = b • omega.form := by
    rw [← add_smul, add_sub_cancel]
  rwa [heq] at h

/-- The pair agrees on an actual open deep sublevel of its minimum. -/
theorem exists_isOpen_deep_sublevel_eq {theta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential theta u)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (huv : u ≤ v) (hv : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) :
    ∃ C : ℝ, 0 < C ∧
      IsOpen {x | min (u x) (poleCoalescingApprox ε u v x) < ((-C : ℝ) : EReal)} ∧
      EqOn (poleCoalescingApprox ε u v) u
        {x | min (u x) (poleCoalescingApprox ε u v x) < ((-C : ℝ) : EReal)} := by
  let C : ℝ := 1 + B + B / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hset : {x | min (u x) (poleCoalescingApprox ε u v x) < ((-C : ℝ) : EReal)} =
      {x | u x < ((-C : ℝ) : EReal)} := by
    ext x
    change min (u x) (poleCoalescingApprox ε u v x) < ((-C : ℝ) : EReal) ↔
      u x < ((-C : ℝ) : EReal)
    rw [min_eq_left (poleCoalescingApprox_bounds hε.le huv hv hgap x).1]
  refine ⟨C, hC, ?_, ?_⟩
  · rw [hset, isOpen_iff_mem_nhds]
    intro x hx
    exact hu.1.quasiPlurisubharmonic.upperSemicontinuous x _ hx
  · rw [hset]
    intro x hx
    apply poleCoalescingApprox_eq_of_deep_sublevel hε huv hv hgap
    have hc : -C ≤ -(B + B / ε) := by dsimp [C]; linarith
    exact hx.le.trans (EReal.coe_le_coe_iff.mpr hc)

/-- The actual max has the curvature required by Lu's strict Kähler case. -/
theorem isThetaPshPotential_poleCoalescingApprox (omega : KahlerBackground n M)
    {a b ε : ℝ} (hε : 0 < ε) (hab : a ≤ b) (hscaled : (1 + ε) * a ≤ b)
    {u v : M → EReal} (hu : IsThetaPshPotential (a • omega.form).val u)
    (hv : IsThetaPshPotential (a • omega.form).val v) :
    IsThetaPshPotential (b • omega.form).val (poleCoalescingApprox ε u v) := by
  have hs := GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
    (by linarith : 0 < 1 + ε) hv.1
  have heq : (1 + ε) • (a • omega.form) = ((1 + ε) * a) • omega.form := smul_smul _ _ _
  rw [heq] at hs
  have hvs : IsThetaPshPotential (((1 + ε) * a) • omega.form).val
      (fun x => ((1 + ε : ℝ) : EReal) * v x) := by
    refine ⟨hs, ?_⟩
    intro x U hU hx
    obtain ⟨y, hy, hne⟩ := hv.2 x U hU hx
    exact ⟨y, hy, fun h => hne
      (ThetaPshConvexCombination.eq_bot_of_coe_mul_eq_bot (by linarith : 0 < 1 + ε) h)⟩
  exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
    (isThetaPshPotential_smul_kahler_mono omega hab hu)
    (isThetaPshPotential_smul_kahler_mono omega hscaled hvs)

/-- Every member of the explicit sequence has the same strict Kähler margin. -/
theorem isThetaPshPotential_poleCoalescingSequence (omega : KahlerBackground n M)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) {u v : M → EReal}
    (hu : IsThetaPshPotential (lam • omega.form).val u)
    (hv : IsThetaPshPotential (lam • omega.form).val v) (k : ℕ) :
    IsThetaPshPotential (((1 + lam) / 2) • omega.form).val
      (poleCoalescingApprox (strictKahlerParameter lam k) u v) := by
  obtain ⟨hpos, -, -, hscaled⟩ := strictKahlerParameter_spec hlam hlam1
  exact isThetaPshPotential_poleCoalescingApprox omega (hpos k)
    (by linarith) (hscaled k) hu hv

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing
