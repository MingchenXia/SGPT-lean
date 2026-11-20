import SGPT.Trace.BertiniLocalDiscSubmean

/-! A centre/direction dependent radius is sufficient for determinant PSH. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Real
namespace SGPT.PSH.DirImg2
open SGPT.Foundations.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}
  {q : E → (Fin r → ℂ) → ℝ≥0∞} {U : Set E}

/-- Actual simultaneous circle extensions at one outer radius. -/
def HasCircleExtensionsAtRadius (q : E → (Fin r → ℂ) → ℝ≥0∞)
    (x w : E) (ρ : ℝ) : Prop :=
  ∀ e : Fin r → Fin r → ℂ, (∀ j, q x (e j) ≠ ⊤) →
    ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ → ∀ η : ℝ, 0 < η →
      ∃ s ∈ Ioc ρ' ρ, ∃ (O : Set ℂ) (F : Fin r → ℂ → Fin r → ℂ),
        IsOpen O ∧ closedBall (0 : ℂ) s ⊆ O ∧ (∀ j, DifferentiableOn ℂ (F j) O) ∧
        (∀ j, F j 0 = e j) ∧
        ∑ j, ∫⁻ θ in Ioc 0 (2 * π), q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ))
          ≤ ENNReal.ofReal ((1 + η) * (2 * π)) * ∑ j, q x (e j)

/-- Radius chosen after centre/direction, BEFORE every frame and slack. -/
def HasLocalCircleMEP (q : E → (Fin r → ℂ) → ℝ≥0∞) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ w : E, ∃ R : ℝ, 0 < R ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → affineClosedDisc x w ρ ⊆ U →
      HasCircleExtensionsAtRadius q x w ρ

/-- Fatou at one fixed outer radius only uses actual extensions at that radius. -/
theorem IsSingularNormFamily.circleDeficit_le_of_circle_extensions
    (hq : IsSingularNormFamily q U) (hU : IsOpen U) {x w : E} {ρ : ℝ}
    (hcircle : HasCircleExtensionsAtRadius q x w ρ) (hρ : 0 < ρ)
    (hD : affineClosedDisc x w ρ ⊆ U) {C : ℝ}
    (hC : ∀ y ∈ affineClosedDisc x w ρ, logDetDual q y ≤ C) {e : Fin r → Fin r → ℂ}
    (he : ∀ j, q x (e j) = 1) :
    circleDeficit (logDetDual q) x w ρ C ≤
      ENNReal.ofReal (2 * π) * ((C : EReal) - logNormSq (colDet e)).toENNReal := by
  set u := logDetDual q
  set K := ENNReal.ofReal (2 * π) * ((C : EReal) - logNormSq (colDet e)).toENNReal
  have hsum : ∑ j, q x (e j) = r := by simp [he]
  have hfin : ∀ j, q x (e j) ≠ ⊤ := fun j => by simp [he j]
  -- radii `s n → ρ` with good extensions
  have hstep : ∀ n : ℕ, ∃ s ∈ Ioc (ρ * (1 - 1 / ((n : ℝ) + 2))) ρ,
      circleDeficit u x w s C ≤ K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r) := by
    intro n
    have h1 : 0 < ρ * (1 - 1 / ((n : ℝ) + 2)) := by
      have : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      exact mul_pos hρ (by linarith)
    have h2 : ρ * (1 - 1 / ((n : ℝ) + 2)) < ρ := by
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    obtain ⟨s, hs, O, F, hO, hsO, hF, hF0, hB⟩ :=
      hcircle e hfin _ h1 h2 (1 / ((n : ℝ) + 1)) (by positivity)
    have hs0 : 0 < s := h1.trans hs.1
    have hDs : affineClosedDisc x w s ⊆ affineClosedDisc x w ρ := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, closedBall_subset_closedBall hs.2 hz, rfl⟩
    refine ⟨s, hs, hq.circleDeficit_le_of_extension hs0 (hDs.trans hD)
      (fun y hy => hC y (hDs hy)) hO hsO hF hF0 (by positivity) ?_⟩
    rwa [hsum] at hB
  choose s hs hbound using hstep
  have hlim : Tendsto s atTop (𝓝 ρ) := by
    have hl : Tendsto (fun n : ℕ => ρ * (1 - 1 / ((n : ℝ) + 2))) atTop (𝓝 ρ) := by
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h' := h.comp (tendsto_add_atTop_nat 1)
        refine h'.congr fun n => ?_
        simp only [Function.comp, Nat.cast_add, Nat.cast_one]
        ring_nf
      simpa using (this.const_sub 1).const_mul ρ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
      (fun n => (hs n).1.le) fun n => (hs n).2
  -- the deficit function `(C - u)⁺` is lower semicontinuous at the points of `U`
  have hΦ : ∀ y ∈ U, LowerSemicontinuousAt (fun z => ((C : EReal) - u z).toENNReal) y := by
    intro y hy
    have husc : UpperSemicontinuousAt u y := fun b hb => by
      have h := hq.upperSemicontinuousOn_logDetDual y hy b hb
      rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hy)] at h
    exact ContinuousAt.comp_upperSemicontinuousAt_antitone (g := fun v : EReal =>
      ((C : EReal) - v).toENNReal) (continuous_deficit C).continuousAt husc
      fun a b hab => EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hab)
  have hyD : ∀ (t : ℝ) (θ : ℝ), 0 < t → t ≤ ρ → x + circleMap 0 t θ • w ∈ U := by
    intro t θ ht htρ
    refine hD ⟨circleMap 0 t θ, ?_, rfl⟩
    exact closedBall_subset_closedBall htρ (sphere_subset_closedBall
      (circleMap_mem_sphere 0 ht.le θ))
  have hs0 : ∀ n, 0 < s n := fun n => (lt_of_le_of_lt (by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact (mul_pos hρ (by linarith)).le) (hs n).1)
  -- measurability of the deficits
  have hmeas : ∀ n, Measurable fun θ : ℝ =>
      ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal := by
    intro n
    refine LowerSemicontinuous.measurable fun θ => ?_
    exact LowerSemicontinuousAt.comp (f := fun z => ((C : EReal) - u z).toENNReal)
      (g := fun θ : ℝ => x + circleMap 0 (s n) θ • w) (hΦ _ (hyD _ θ (hs0 n) (hs n).2))
      (by fun_prop)
  -- pointwise liminf
  have hpt : ∀ θ : ℝ, ((C : EReal) - u (x + circleMap 0 ρ θ • w)).toENNReal ≤
      liminf (fun n => ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal) atTop := by
    intro θ
    have ht : Tendsto (fun n => x + circleMap 0 (s n) θ • w) atTop
        (𝓝 (x + circleMap 0 ρ θ • w)) := by
      have hc : Continuous fun t : ℝ => x + circleMap 0 t θ • w := by
        simp only [circleMap, zero_add]
        fun_prop
      exact (hc.tendsto ρ).comp hlim
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    exact le_liminf_of_le (by isBoundedDefault)
      ((ht.eventually (hΦ _ (hyD ρ θ hρ le_rfl) b hb)).mono fun n hn => hn.le)
  -- Fatou
  have hK : Tendsto (fun n : ℕ => K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r)) atTop
      (𝓝 K) := by
    have h0 : Tendsto (fun n : ℕ => 2 * π * (1 / ((n : ℝ) + 1)) * r) atTop (𝓝 0) := by
      simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * π)).mul_const (r : ℝ)
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_ofReal h0)
  calc circleDeficit u x w ρ C
      ≤ ∫⁻ θ in Ioc 0 (2 * π),
          liminf (fun n => ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal) atTop :=
        lintegral_mono hpt
    _ ≤ liminf (fun n => circleDeficit u x w (s n) C) atTop :=
        lintegral_liminf_le' fun n => (hmeas n).aemeasurable
    _ ≤ liminf (fun n : ℕ => K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r)) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = K := hK.liminf_eq


/-- The SAME point/direction radius works for every normalized determinant frame. -/
theorem IsSingularNormFamily.localDiscSubmean_logDetDual (hq : IsSingularNormFamily q U)
    (hU : IsOpen U) (hlocal : HasLocalCircleMEP q U) :
    HasLocalDiscSubmeanOn (logDetDual q) U := by
  intro x hx w
  obtain ⟨R,hR,hmep⟩ := hlocal x hx w
  refine ⟨R,hR,?_⟩
  intro ρ hρ hρR hD C hC
  have h2π : ENNReal.ofReal (2 * π) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsup : logDetDual q x = ⨆ C' : unitFrames r, ENNReal.log (detRatio (q x) C') := by
    rw [logDetDual, detDual, iSup_subtype']
    exact Pending.BergmanSupWeight.log_iSup _
  have : Nonempty (unitFrames r) := ⟨⟨_, stdFrame_mem_unitFrames⟩⟩
  have key : ∀ C' : unitFrames r, circleDeficit (logDetDual q) x w ρ C ≤
      ENNReal.ofReal (2 * π) * ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal := by
    rintro ⟨C', hC'⟩
    by_cases h0 : detRatio (q x) C' = 0
    · rw [h0, ENNReal.log_zero, EReal.sub_bot (EReal.coe_ne_bot C), EReal.toENNReal_top,
        ENNReal.mul_top h2π]
      exact le_top
    have hne0 : ∀ j, q x (C' j) ≠ 0 := fun j => hq.pos x hx _ fun h => by
      have := hC' j (mem_univ j)
      rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
      exact zero_ne_one this
    have hP : ∏ j, q x (C' j) ≠ ⊤ := fun hP => h0 (by simp [detRatio, hP])
    have hnetop : ∀ j, q x (C' j) ≠ ⊤ := fun j hj => hP (by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hj]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr fun i _ => hne0 i))
    set qj : Fin r → ℝ := fun j => (q x (C' j)).toReal
    have hqj : ∀ j, 0 < qj j := fun j => ENNReal.toReal_pos (hne0 j) (hnetop j)
    set c : Fin r → ℂ := fun j => (((Real.sqrt (qj j))⁻¹ : ℝ) : ℂ)
    have hc : ∀ j, c j ≠ 0 := fun j => by
      simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero', not_le]
      exact hqj j
    set e : Fin r → Fin r → ℂ := fun j => c j • C' j
    have he : ∀ j, q x (e j) = 1 := by
      intro j
      simp only [e]
      rw [hq.smul, ← ENNReal.ofReal_toReal (hnetop j), ← ENNReal.ofReal_mul (by positivity)]
      have hn : ‖c j‖ ^ 2 = (qj j)⁻¹ := by
        simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (hqj j).le]
      rw [hn, inv_mul_cancel₀ (hqj j).ne', ENNReal.ofReal_one]
    have hratio : detRatio (q x) C' = ENNReal.ofReal (‖colDet e‖ ^ 2) := by
      rw [← hq.detRatio_smul x hc C']
      simp [detRatio, e, he]
    rw [hratio]
    exact hq.circleDeficit_le_of_circle_extensions hU (hmep ρ hρ hρR hD) hρ hD hC he
  calc circleDeficit (logDetDual q) x w ρ C
      ≤ ⨅ C' : unitFrames r,
          ENNReal.ofReal (2 * π) * ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal :=
        le_iInf key
    _ = ENNReal.ofReal (2 * π) *
          ⨅ C' : unitFrames r, ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal :=
        (ENNReal.mul_iInf_of_ne h2π ENNReal.ofReal_ne_top).symm
    _ ≤ ENNReal.ofReal (2 * π) * ((C : EReal) - logDetDual q x).toENNReal := by
        rw [hsup]
        exact mul_le_mul_right (Pending.BergmanSupWeight.iInf_sub_toENNReal_le C _) _


/-- Genuine local-circle MEP implies the full determinant disc criterion. -/
theorem IsSingularNormFamily.discPshOn_logDetDual_of_local_mep
    (hq : IsSingularNormFamily q U) (hU : IsOpen U) (hlocal : HasLocalCircleMEP q U) :
    DiscPshOn (logDetDual q) U :=
  discPshOn_of_local_disc_submean hq.upperSemicontinuousOn_logDetDual
    (fun _ ht => hq.logDetDual_ne_top ht) (hq.localDiscSubmean_logDetDual hU hlocal)

/-- A genuine finite fibre prevents the produced determinant PSH potential being all poles. -/
theorem IsSingularNormFamily.locallyPluripolarOn_infiniteNormSet_of_local_mep
    (hq : IsSingularNormFamily q U) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hlocal : HasLocalCircleMEP q U) (hgood : ∃ t ∈ U, ∀ v, q t v ≠ ⊤) :
    LocallyPluripolarOn {t | ∃ v, q t v = ⊤} U := by
  have hpsh := (hq.discPshOn_logDetDual_of_local_mep hU hlocal).plurisubharmonicOn hU
  obtain ⟨t,ht,hfin⟩ := hgood
  intro x hx
  exact ⟨U,logDetDual q,hU,hx,hUc,hpsh,⟨t,ht,hq.logDetDual_ne_bot t hfin⟩,
    fun y hyU hy => hq.logDetDual_eq_bot_of_exists_eq_top hyU hy⟩

/-- Finite fibres in every actual open subset give local witnesses on genuine balls. -/
theorem IsSingularNormFamily.locallyPluripolarOn_infiniteNormSet_of_local_mep_of_dense_finite
    (hq : IsSingularNormFamily q U) (hU : IsOpen U) (hlocal : HasLocalCircleMEP q U)
    (hgood : ∀ V : Set E, IsOpen V → V ⊆ U → V.Nonempty →
      ∃ t ∈ V, ∀ v, q t v ≠ ⊤) :
    LocallyPluripolarOn {t | ∃ v, q t v = ⊤} U := by
  have hpsh := (hq.discPshOn_logDetDual_of_local_mep hU hlocal).plurisubharmonicOn hU
  intro x hx
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨t,ht,hfin⟩ := hgood (ball x a) isOpen_ball hball (nonempty_ball.mpr ha)
  exact ⟨ball x a,logDetDual q,isOpen_ball,mem_ball_self ha,isPreconnected_ball,
    hpsh.mono hball,⟨t,ht,hq.logDetDual_ne_bot t hfin⟩,
    fun y hy hyinf => hq.logDetDual_eq_bot_of_exists_eq_top (hball hy) hyinf⟩

end SGPT.PSH.DirImg2
